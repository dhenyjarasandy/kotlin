/*
 * Copyright 2010-2017 JetBrains s.r.o.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package org.jetbrains.kotlin.js.dce

import org.jetbrains.kotlin.js.backend.ast.*
import org.jetbrains.kotlin.js.inline.util.collectDefinedNames
import org.jetbrains.kotlin.js.inline.util.collectLocalVariables
import org.jetbrains.kotlin.js.translate.context.Namer
import org.jetbrains.kotlin.js.translate.utils.jsAstUtils.array
import org.jetbrains.kotlin.js.translate.utils.jsAstUtils.index

class DeadCodeElimination(val root: JsNode) {
    private val globalScope = Node()
    private val nodes = mutableMapOf<JsName, Node>()
    private var returnNodes = mutableListOf<Node>()
    private val nodeMap = mutableMapOf<JsNode, Node>()
    private val functionsToEnter = mutableSetOf<JsFunction>()
    private val astNodesToSkip = mutableSetOf<JsNode>()
    private var depth = 0

    fun apply() {
        addLocalVars(collectDefinedNames(root))
        root.accept(visitor)

        root.accept(usageFinder)

        eliminator.accept(root)
    }

    private fun addLocalVars(names: Collection<JsName>) {
        nodes += names.filter { it !in nodes }.associate { it to Node(it) }
    }

    private val visitor = object : JsVisitor() {
        override fun visitVars(x: JsVars) {
            x.vars.forEach { accept(it) }
        }

        override fun visit(x: JsVars.JsVar) {
            val rhs = x.initExpression
            if (rhs != null) {
                processAssignment(x, x.name.makeRef(), rhs)?.let { nodeMap[x] = it }
            }
        }

        override fun visitExpressionStatement(x: JsExpressionStatement) {
            val expression = x.expression
            if (expression is JsBinaryOperation) {
                if (expression.operator == JsBinaryOperator.ASG) {
                    processAssignment(x, expression.arg1, expression.arg2)?.let {
                        nodeMap[x] = it
                    }
                }
            }
            else if (expression is JsFunction) {
                expression.name?.let { nodes[it]?.original }?.let {
                    nodeMap[x] = it
                    it.expressions += expression
                }
            }
            else if (expression is JsInvocation) {
                val function = expression.qualifier
                if (function is JsFunction) {
                    enterFunction(function, expression.arguments)
                }
                else if (isObjectDefineProperty(function)) {
                    handleObjectDefineProperty(x, expression.arguments.getOrNull(0), expression.arguments.getOrNull(1),
                                               expression.arguments.getOrNull(2))
                }
                else if (isDefineModule(function)) {
                    astNodesToSkip += x
                }
            }
        }

        private fun isObjectDefineProperty(function: JsExpression) = isObjectFunction(function, "defineProperty")

        private fun isObjectGetOwnPropertyDescriptor(function: JsExpression) = isObjectFunction(function, "getOwnPropertyDescriptor")

        private fun isObjectFunction(function: JsExpression, functionName: String): Boolean {
            if (function !is JsNameRef) return false
            if (function.ident != functionName) return false

            val receiver = function.qualifier as? JsNameRef ?: return false
            if (receiver.name?.let { nodes[it] } != null) return false

            return receiver.ident == "Object"
        }

        private fun isDefineModule(function: JsExpression): Boolean {
            if (function !is JsNameRef) return false
            if (function.ident != "defineModule") return false

            val receiver = (function.qualifier as? JsNameRef)?.name ?: return false
            return receiver in nodes
        }

        private fun handleObjectDefineProperty(statement: JsStatement, target: JsExpression?, propertyName: JsExpression?,
                                               propertyDescriptor: JsExpression?) {
            if (target == null || propertyName !is JsStringLiteral || propertyDescriptor == null) return
            val targetNode = extractNode(target) ?: return

            val memberNode = targetNode.member(propertyName.value)
            nodeMap[statement] = memberNode
            memberNode.original.hasSideEffects = true

            if (propertyDescriptor is JsObjectLiteral) {
                for (initializer in propertyDescriptor.propertyInitializers) {
                    processAssignment(statement, JsNameRef(propertyName.value, target), initializer.valueExpr)
                }
            }
            else if (propertyDescriptor is JsInvocation) {
                val function = propertyDescriptor.qualifier
                if (isObjectGetOwnPropertyDescriptor(function)) {
                    val source = propertyDescriptor.arguments.getOrNull(0)
                    val sourcePropertyName = propertyDescriptor.arguments.getOrNull(1)
                    if (source != null && sourcePropertyName is JsStringLiteral) {
                        processAssignment(statement, JsNameRef(propertyName.value, target), JsNameRef(sourcePropertyName.value, source))
                    }
                }
            }
        }

        override fun visitBlock(x: JsBlock) {
            x.statements.forEach { accept(it) }
        }

        override fun visitIf(x: JsIf) {
            accept(x.thenStatement)
            x.elseStatement?.accept(this)
        }

        override fun visitReturn(x: JsReturn) {
            val expr = x.expression
            if (expr != null) {
                extractNode(expr)?.let {
                    returnNodes.add(it)
                    nodeMap[x] = it
                }
            }
        }

        private fun processAssignment(node: JsNode?, lhs: JsExpression, rhs: JsExpression): Node? {
            val leftNode = extractNode(lhs)
            val rightNode = extractNode(rhs)

            if (leftNode != null && rightNode != null) {
                leftNode.alias(rightNode)
                return leftNode
            }
            else if (leftNode != null) {
                if (rhs is JsInvocation) {
                    val function = rhs.qualifier
                    if (function is JsFunction) {
                        enterFunction(function, rhs.arguments)
                        return null
                    }
                    else if (isObjectFunction(function, "create")) {
                        handleObjectCreate(leftNode, rhs.arguments.getOrNull(0))
                        return leftNode
                    }
                }
                else if (rhs is JsBinaryOperation) {
                    if (rhs.operator == JsBinaryOperator.OR) {
                        val secondNode = extractNode(rhs.arg1)
                        val reassignment = rhs.arg2
                        if (reassignment is JsBinaryOperation && reassignment.operator == JsBinaryOperator.ASG) {
                            val reassignNode = extractNode(reassignment.arg1)
                            val reassignValue = reassignment.arg2
                            if (reassignNode == secondNode && reassignNode != null && reassignValue is JsObjectLiteral &&
                                reassignValue.propertyInitializers.isEmpty()
                            ) {
                                return processAssignment(node, lhs, rhs.arg1)
                            }
                        }
                    }
                    else if (rhs.operator == JsBinaryOperator.COMMA) {
                        if (rhs.arg1 is JsStringLiteral) {
                            return processAssignment(node, lhs, rhs.arg2)
                        }
                    }
                }
                else if (rhs is JsFunction) {
                    leftNode.expressions += rhs
                    return leftNode
                }
                else if (leftNode.qualifier?.memberName == Namer.METADATA) {
                    leftNode.expressions += rhs
                    return leftNode
                }
                else if (rhs is JsObjectLiteral && rhs.propertyInitializers.isEmpty()) {
                    return leftNode
                }
            }
            return null
        }

        private fun handleObjectCreate(target: Node, arg: JsExpression?) {
            if (arg == null) return

            val prototypeNode = extractNode(arg) ?: return
            target.original.dependencies += prototypeNode.original
            target.original.expressions += arg
        }

        private fun enterFunction(function: JsFunction, arguments: List<JsExpression>): List<Node> {
            functionsToEnter += function
            addLocalVars(function.collectLocalVariables())

            for ((param, arg) in function.parameters.zip(arguments)) {
                processAssignment(function, param.name.makeRef(), arg)
            }
            val oldReturnNodes = returnNodes
            val newReturnNodes = mutableListOf<Node>()
            returnNodes = newReturnNodes

            accept(function.body)

            returnNodes = oldReturnNodes
            return newReturnNodes
        }
    }

    private val usageFinder = object : RecursiveJsVisitor() {
        private var currentNodeWithLocation: JsNode? = null
        private val localVars = mutableSetOf<JsName>()

        override fun visit(x: JsVars.JsVar) {
            if (nodeMap[x] == null && x !in astNodesToSkip) {
                super.visit(x)
            }
        }

        override fun visitExpressionStatement(x: JsExpressionStatement) {
            if (nodeMap[x] == null && x !in astNodesToSkip) {
                super.visitExpressionStatement(x)
            }
        }

        override fun visitReturn(x: JsReturn) {
            if (nodeMap[x] == null && x !in astNodesToSkip) {
                super.visitReturn(x)
            }
        }

        override fun visitNameRef(nameRef: JsNameRef) {
            val node = extractNode(nameRef)
            if (node != null) {
                if (!node.original.used && node.root().localName?.let { it !in localVars } ?: true) {
                    reportAndNest("use: referenced name $node", currentNodeWithLocation) {
                        use(node)
                    }
                }
            }
            else {
                super.visitNameRef(nameRef)
            }
        }

        override fun visitInvocation(invocation: JsInvocation) {
            val function = invocation.qualifier
            if (function is JsFunction && function in functionsToEnter) {
                accept(function.body)
            }
            else {
                super.visitInvocation(invocation)
            }
        }

        private fun use(node: Node) {
            if (node.original.used) return
            node.original.used = true

            useDeclaration(node)

            for (dependency in node.original.dependencies) {
                if (!dependency.original.used) {
                    reportAndNest("use: dependency $dependency", null) { use(dependency) }
                }
            }
            node.members.toList().forEach { (name, member) ->
                if (!member.original.used) {
                    reportAndNest("use: member $name", null) { use(member) }
                }
            }

            for (expr in node.original.expressions.filterIsInstance<JsFunction>()) {
                reportAndNest("traverse: function", expr) {
                    expr.collectLocalVariables().let {
                        addLocalVars(it)
                        localVars += it
                    }
                    expr.body.accept(this)
                }
            }
        }

        private fun useDeclaration(node: Node) {
            if (node.original.hasSideEffects && !node.original.used) {
                reportAndNest("use: because of side effect", null) {
                    use(node)
                }
            }
            else if (!node.original.declarationUsed) {
                node.original.declarationUsed = true

                node.original.qualifier?.parent?.let {
                    reportAndNest("use-decl: parent $it", null) {
                        useDeclaration(it)
                    }
                }

                for (expr in node.original.expressions) {
                    reportAndNest("traverse: value", expr) {
                        expr.accept(this)
                    }
                }
            }
        }

        override fun visitPrefixOperation(x: JsPrefixOperation) {
            if (x.operator == JsUnaryOperator.TYPEOF) {
                val arg = x.arg
                if (arg is JsNameRef && arg.qualifier == null) return
            }
            super.visitPrefixOperation(x)
        }

        override fun visitFunction(x: JsFunction) {
            if (x in functionsToEnter) {
                super.visitFunction(x)
            }
        }

        override fun visitElement(node: JsNode) {
            val newLocation = node.extractLocation()
            val old = currentNodeWithLocation
            if (newLocation != null) {
                currentNodeWithLocation = node
            }
            super.visitElement(node)
            currentNodeWithLocation = old
        }
    }

    private val eliminator = object : JsVisitorWithContextImpl() {
        override fun visit(x: JsVars.JsVar, ctx: JsContext<*>): Boolean = removeIfNecessary(x, ctx)

        override fun visit(x: JsExpressionStatement, ctx: JsContext<*>): Boolean = removeIfNecessary(x, ctx)

        override fun visit(x: JsReturn, ctx: JsContext<*>): Boolean = removeIfNecessary(x, ctx)

        private fun removeIfNecessary(x: JsNode, ctx: JsContext<*>): Boolean {
            if (x in astNodesToSkip) {
                ctx.removeMe()
                return false
            }
            val node = nodeMap[x]?.original
            return if (!isUsed(node)) {
                ctx.removeMe()
                false
            }
            else {
                true
            }
        }

        override fun endVisit(x: JsVars, ctx: JsContext<*>) {
            if (x.vars.isEmpty()) {
                ctx.removeMe()
            }
        }
    }

    private fun report(message: String) {
        println("  ".repeat(depth) + "=> " + message)
    }

    private fun reportAndNest(message: String, dueTo: JsNode?, action: () -> Unit) {
        val location = dueTo?.extractLocation()
        val fullMessage = if (location != null) "$message (due to ${location.lineNumber + 1})" else message
        report(fullMessage)
        nested(action)
    }

    private fun JsNode.extractLocation(): JsLocation? {
        return when (this) {
            is SourceInfoAwareJsNode -> source as? JsLocation
            is JsExpressionStatement -> expression.source as? JsLocation
            else -> null
        }
    }

    private fun nested(action: () -> Unit) {
        depth++
        action()
        depth--
    }

    private fun isUsed(node: Node?): Boolean = node == null || node.original.declarationUsed

    private fun extractNode(expression: JsExpression): Node? {
        return when (expression) {
            is JsNameRef -> {
                val qualifier = expression.qualifier
                if (qualifier == null) {
                    expression.name?.let { nodes[it]?.original } ?: globalScope.original.member(expression.ident)
                }
                else {
                    extractNode(qualifier)?.member(expression.ident)?.original
                }
            }
            is JsArrayAccess -> {
                val index = expression.index
                if (index is JsStringLiteral) extractNode(expression.array)?.member(index.value)?.original else null
            }
            else -> {
                null
            }
        }
    }

    private class Node private constructor(val localName: JsName?, qualifier: Qualifier?) {
        val dependencies = mutableSetOf<Node>()
        val expressions = mutableSetOf<JsExpression>()
        var hasSideEffects = false
        var used = false
        var declarationUsed = false
        private val membersImpl = mutableMapOf<String, Node>()
        private var rank = 0

        var qualifier: Qualifier? = qualifier
            get
            private set

        constructor(localName: JsName? = null) : this(localName, null)

        var original: Node = this
            get() {
                if (field != this) {
                    field = field.original
                }
                return field
            }
            private set

        val members: Map<String, Node> get() = original.membersImpl

        fun member(name: String): Node = original.membersImpl.getOrPut(name) { Node(null, Qualifier(this, name)) }.original

        fun alias(other: Node) {
            val a = original
            val b = other.original
            if (a == b) return

            if (a.qualifier == null && b.qualifier == null) {
                a.merge(b)
            }
            else if (a.qualifier == null) {
                if (b.root() == a) a.makeDependencies(b) else b.evacuateFrom(a)
            }
            else if (b.qualifier == null) {
                if (a.root() == b) a.makeDependencies(b) else a.evacuateFrom(b)
            }
            else {
                a.makeDependencies(b)
            }
        }

        private fun makeDependencies(other: Node) {
            dependencies += other
            other.dependencies += this
        }

        private fun evacuateFrom(other: Node) {
            val (existingMembers, newMembers) = other.members.toList().partition { (name, _) -> name in membersImpl }
            other.original = this

            for ((name, member) in newMembers) {
                membersImpl[name] = member
            }
            for ((name, member) in existingMembers) {
                membersImpl[name]!!.original.merge(member.original)
                membersImpl[name] = member.original
            }
            hasSideEffects = hasSideEffects || other.hasSideEffects
            expressions += other.expressions
            dependencies += other.dependencies
        }

        private fun merge(other: Node) {
            if (this == other) return

            if (rank < other.rank) {
                other.evacuateFrom(this)
            }
            else {
                evacuateFrom(other)
            }

            if (rank == other.rank) {
                rank++
            }
        }

        fun root(): Node = generateSequence(original) { it.qualifier?.parent }.last()

        fun pathFromRoot(): List<String> =
                generateSequence(original) { it.qualifier?.parent }.mapNotNull { it.qualifier?.memberName }
                        .toList().asReversed()

        override fun toString(): String = (root().localName?.ident ?: "<unknown>") + pathFromRoot().joinToString("") { ".$it" }
    }

    private class Qualifier(val parent: Node, val memberName: String)
}