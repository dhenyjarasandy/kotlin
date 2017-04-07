/*
 * Copyright 2010-2015 JetBrains s.r.o.
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

package org.jetbrains.kotlin.idea.refactoring.inline

import com.intellij.codeInsight.TargetElementUtil
import com.intellij.lang.Language
import com.intellij.lang.refactoring.InlineActionHandler
import com.intellij.openapi.application.ApplicationManager
import com.intellij.openapi.editor.Editor
import com.intellij.openapi.editor.ex.EditorSettingsExternalizable
import com.intellij.openapi.project.Project
import com.intellij.openapi.wm.WindowManager
import com.intellij.psi.PsiElement
import com.intellij.psi.PsiReference
import com.intellij.psi.PsiWhiteSpace
import com.intellij.psi.impl.source.resolve.reference.impl.PsiMultiReference
import com.intellij.psi.search.GlobalSearchScope
import com.intellij.psi.search.PsiSearchHelper
import com.intellij.psi.search.searches.ReferencesSearch
import com.intellij.refactoring.HelpID
import com.intellij.refactoring.JavaRefactoringSettings
import com.intellij.refactoring.RefactoringBundle
import com.intellij.refactoring.util.CommonRefactoringUtil
import com.intellij.util.containers.MultiMap
import org.jetbrains.kotlin.descriptors.SimpleFunctionDescriptor
import org.jetbrains.kotlin.descriptors.VariableDescriptor
import org.jetbrains.kotlin.diagnostics.Errors
import org.jetbrains.kotlin.idea.KotlinLanguage
import org.jetbrains.kotlin.idea.analysis.analyzeInContext
import org.jetbrains.kotlin.idea.caches.resolve.analyze
import org.jetbrains.kotlin.idea.caches.resolve.getResolutionFacade
import org.jetbrains.kotlin.idea.caches.resolve.resolveToDescriptor
import org.jetbrains.kotlin.idea.codeInliner.CallableUsageReplacementStrategy
import org.jetbrains.kotlin.idea.codeInliner.CodeToInlineBuilder
import org.jetbrains.kotlin.idea.codeInsight.shorten.performDelayedRefactoringRequests
import org.jetbrains.kotlin.idea.core.ShortenReferences
import org.jetbrains.kotlin.idea.core.copied
import org.jetbrains.kotlin.idea.core.replaced
import org.jetbrains.kotlin.idea.refactoring.addTypeArgumentsIfNeeded
import org.jetbrains.kotlin.idea.refactoring.checkConflictsInteractively
import org.jetbrains.kotlin.idea.refactoring.getQualifiedTypeArgumentList
import org.jetbrains.kotlin.idea.references.KtSimpleNameReference
import org.jetbrains.kotlin.idea.references.mainReference
import org.jetbrains.kotlin.idea.resolve.ResolutionFacade
import org.jetbrains.kotlin.idea.util.IdeDescriptorRenderers
import org.jetbrains.kotlin.idea.util.application.executeWriteCommand
import org.jetbrains.kotlin.idea.util.getResolutionScope
import org.jetbrains.kotlin.psi.*
import org.jetbrains.kotlin.psi.psiUtil.*
import org.jetbrains.kotlin.resolve.BindingContext
import org.jetbrains.kotlin.resolve.lazy.BodyResolveMode
import org.jetbrains.kotlin.types.ErrorUtils
import org.jetbrains.kotlin.types.TypeUtils
import org.jetbrains.kotlin.types.expressions.OperatorConventions
import org.jetbrains.kotlin.utils.addIfNotNull
import org.jetbrains.kotlin.utils.addToStdlib.firstIsInstanceOrNull
import org.jetbrains.kotlin.utils.sure

class KotlinInlineValHandler : InlineActionHandler() {
    enum class InlineMode {
        ALL, PRIMARY, NONE
    }

    override fun isEnabledForLanguage(l: Language) = l == KotlinLanguage.INSTANCE

    override fun canInlineElement(element: PsiElement): Boolean {
        if (element !is KtProperty) return false
        return element.getter == null && element.receiverTypeReference == null
    }

    private fun doReplace(expression: KtExpression, replacement: KtExpression): List<KtExpression> {
        val parent = expression.parent

        if (parent is KtStringTemplateEntryWithExpression &&
            replacement is KtStringTemplateExpression &&
            // Do not mix raw and non-raw templates
            parent.parent.firstChild.text == replacement.firstChild.text) {
            val entriesToAdd = replacement.entries
            val templateExpression = parent.parent as KtStringTemplateExpression
            val inlinedExpressions = if (entriesToAdd.isNotEmpty()) {
                val firstAddedEntry = templateExpression.addRangeBefore(entriesToAdd.first(), entriesToAdd.last(), parent)
                val lastNewEntry = parent.prevSibling
                val nextElement = parent.nextSibling
                if (lastNewEntry is KtSimpleNameStringTemplateEntry &&
                    lastNewEntry.expression != null &&
                    !canPlaceAfterSimpleNameEntry(nextElement)) {
                    lastNewEntry.replace(KtPsiFactory(expression).createBlockStringTemplateEntry(lastNewEntry.expression!!))
                }
                firstAddedEntry.siblings()
                        .take(entriesToAdd.size)
                        .mapNotNull { (it as? KtStringTemplateEntryWithExpression)?.expression }
                        .toList()
            }
            else emptyList()

            parent.delete()
            return inlinedExpressions
        }

        return listOf(expression.replaced(replacement))
    }

    override fun inlineElement(project: Project, editor: Editor?, element: PsiElement) {
        val declaration = element as KtProperty
        val file = declaration.containingKtFile
        val name = declaration.name ?: return

        val assignments = hashSetOf<PsiElement>()
        val referenceExpressions = arrayListOf<KtExpression>()
        val foreignUsages = arrayListOf<PsiElement>()

        val searchHelper = PsiSearchHelper.SERVICE.getInstance(project)
        val scope = GlobalSearchScope.projectScope(project)
        val isCheapToSearch =
                searchHelper.isCheapEnoughToSearch(name, scope, null, null) != PsiSearchHelper.SearchCostResult.TOO_MANY_OCCURRENCES

        if (isCheapToSearch) {
            val references = ReferencesSearch.search(declaration)
            for (ref in references) {
                val refElement = ref.element ?: continue
                if (refElement !is KtElement) {
                    foreignUsages.add(refElement)
                    continue
                }
                referenceExpressions.addIfNotNull((refElement as? KtExpression)?.getQualifiedExpressionForSelectorOrThis())
            }

            if (referenceExpressions.isEmpty()) {
                val kind = if (declaration.isLocal) "Variable" else "Property"
                return showErrorHint(project, editor, "$kind '$name' is never used")
            }

            referenceExpressions.forEach { expression ->
                val parent = expression.parent

                val assignment = expression.getAssignmentByLHS()
                if (assignment != null) {
                    assignments.add(parent)
                }

                if (parent is KtUnaryExpression && OperatorConventions.INCREMENT_OPERATIONS.contains(parent.operationToken)) {
                    assignments.add(parent)
                }
            }
        }

        val initializerInDeclaration = declaration.initializer
        val initializer = if (initializerInDeclaration != null) {
            if (!assignments.isEmpty()) return reportAmbiguousAssignment(project, editor, name, assignments)
            initializerInDeclaration
        }
        else {
            (assignments.singleOrNull() as? KtBinaryExpression)?.right
            ?: return reportAmbiguousAssignment(project, editor, name, assignments)
        }

        val typeArgumentsForCall = getQualifiedTypeArgumentList(initializer)
        val parametersForFunctionLiteral = getParametersForFunctionLiteral(initializer)

        val referencesInOriginalFile = referenceExpressions.filter { it.containingFile == file }
        val isHighlighting = referencesInOriginalFile.isNotEmpty()
        highlightElements(project, editor, referencesInOriginalFile)

        if (referencesInOriginalFile.size != referenceExpressions.size) {
            preProcessInternalUsages(initializer, referenceExpressions)
        }

        val descriptor = element.resolveToDescriptor() as VariableDescriptor
        val expectedType = if (element.typeReference != null)
            descriptor.returnType ?: TypeUtils.NO_EXPECTED_TYPE
        else
            TypeUtils.NO_EXPECTED_TYPE

        val initializerCopy = initializer.copied()
        fun analyzeInitializerCopy(): BindingContext {
            return initializer.analyze()
        }

        fun performRefactoring() {
            val reference = editor?.let { TargetElementUtil.findReference(it, it.caretModel.offset) }
            val nameReference = when (reference) {
                is KtSimpleNameReference -> reference
                is PsiMultiReference -> reference.references.firstIsInstanceOrNull<KtSimpleNameReference>()
                else -> null
            }
            val replacementBuilder = CodeToInlineBuilder(descriptor, element.getResolutionFacade())
            val replacement = replacementBuilder.prepareCodeToInline(initializer, emptyList(), ::analyzeInitializerCopy)
            val replacementStrategy = CallableUsageReplacementStrategy(replacement)

            val dialog = KotlinInlineValDialog(declaration, nameReference, replacementStrategy, assignments)

            if (!ApplicationManager.getApplication().isUnitTestMode) {
                dialog.show()
                if (!dialog.isOK && isHighlighting) {
                    val statusBar = WindowManager.getInstance().getStatusBar(project)
                    statusBar?.info = RefactoringBundle.message("press.escape.to.remove.the.highlighting")
                }
            }
            else {
                dialog.doAction()
            }
/*
            val chosenExpressions = if (inlineMode == InlineMode.ALL) referenceExpressions else listOf(primaryExpression)

            project.executeWriteCommand(RefactoringBundle.message("inline.command", name)) {
                val inlinedExpressions = chosenExpressions
                        .flatMap { referenceExpression ->
                            if (assignments.contains(referenceExpression!!.parent)) return@flatMap emptyList<KtExpression>()

                            val importDirective = referenceExpression.getStrictParentOfType<KtImportDirective>()
                            if (importDirective != null) {
                                val reference = referenceExpression.getQualifiedElementSelector()?.mainReference
                                if (reference != null && reference.multiResolve(false).size <= 1) {
                                    importDirective.delete()
                                }

                                return@flatMap emptyList<KtExpression>()
                            }

                            doReplace(referenceExpression, initializer)
                        }
                        .mapNotNull { postProcessInternalReferences(it) }

                if (inlineMode == InlineMode.ALL) {
                    assignments.forEach { it.delete() }
                    declaration.delete()
                }

                if (inlinedExpressions.isNotEmpty()) {
                    if (typeArgumentsForCall != null) {
                        inlinedExpressions.forEach { addTypeArgumentsIfNeeded(it, typeArgumentsForCall) }
                    }

                    parametersForFunctionLiteral?.let { addFunctionLiteralParameterTypes(it, inlinedExpressions) }

                    if (isHighlighting) {
                        highlightElements(project, editor, inlinedExpressions)
                    }
                }
                performDelayedRefactoringRequests(project)
            }
            */
        }

        if (foreignUsages.isNotEmpty()) {
            val conflicts = MultiMap<PsiElement, String>().apply {
                putValue(null, "Property '$name' has non-Kotlin usages. They won't be processed by the Inline refactoring.")
                foreignUsages.forEach { putValue(it, it.text) }
            }
            project.checkConflictsInteractively(conflicts) { performRefactoring() }
        }
        else {
            performRefactoring()
        }
    }

    private fun reportAmbiguousAssignment(project: Project, editor: Editor?, name: String, assignments: Set<PsiElement>) {
        val key = if (assignments.isEmpty()) "variable.has.no.initializer" else "variable.has.no.dominating.definition"
        val message = RefactoringBundle.getCannotRefactorMessage(RefactoringBundle.message(key, name))
        showErrorHint(project, editor, message)
    }

    private fun showErrorHint(project: Project, editor: Editor?, message: String) {
        CommonRefactoringUtil.showErrorHint(project, editor, message, RefactoringBundle.message("inline.variable.title"), HelpID.INLINE_VARIABLE)
    }

    private fun getParametersForFunctionLiteral(initializer: KtExpression): String? {
        val functionLiteralExpression = initializer.unpackFunctionLiteral(true) ?: return null
        val context = initializer.analyze(BodyResolveMode.PARTIAL)
        val lambdaDescriptor = context.get(BindingContext.FUNCTION, functionLiteralExpression.functionLiteral)
        if (lambdaDescriptor == null || ErrorUtils.containsErrorType(lambdaDescriptor)) return null
        return lambdaDescriptor.valueParameters.joinToString {
            it.name.asString() + ": " + IdeDescriptorRenderers.SOURCE_CODE.renderType(it.type)
        }
    }

    private fun addFunctionLiteralParameterTypes(parameters: String, inlinedExpressions: List<KtExpression>) {
        val containingFile = inlinedExpressions.first().containingKtFile
        val resolutionFacade = containingFile.getResolutionFacade()

        val functionsToAddParameters = inlinedExpressions.mapNotNull {
            val lambdaExpr = it.unpackFunctionLiteral(true).sure { "can't find function literal expression for " + it.text }
            if (needToAddParameterTypes(lambdaExpr, resolutionFacade)) lambdaExpr else null
        }

        val psiFactory = KtPsiFactory(containingFile)
        for (lambdaExpr in functionsToAddParameters) {
            val lambda = lambdaExpr.functionLiteral

            val currentParameterList = lambda.valueParameterList
            val newParameterList = psiFactory.createParameterList("($parameters)")
            if (currentParameterList != null) {
                currentParameterList.replace(newParameterList)
            }
            else {
                // TODO: Ugly code, need refactoring
                val openBraceElement = lambda.lBrace

                val nextSibling = openBraceElement.nextSibling
                val whitespaceToAdd = if (nextSibling is PsiWhiteSpace && nextSibling.text.contains("\n"))
                    nextSibling.copy()
                else
                    null

                val whitespaceAndArrow = psiFactory.createWhitespaceAndArrow()
                lambda.addRangeAfter(whitespaceAndArrow.first, whitespaceAndArrow.second, openBraceElement)

                lambda.addAfter(newParameterList, openBraceElement)
                if (whitespaceToAdd != null) {
                    lambda.addAfter(whitespaceToAdd, openBraceElement)
                }
            }
            ShortenReferences.DEFAULT.process(lambdaExpr.valueParameters)
        }
    }

    private fun needToAddParameterTypes(
            lambdaExpression: KtLambdaExpression,
            resolutionFacade: ResolutionFacade
    ): Boolean {
        val functionLiteral = lambdaExpression.functionLiteral
        val context = resolutionFacade.analyze(lambdaExpression, BodyResolveMode.PARTIAL_WITH_DIAGNOSTICS)
        return context.diagnostics.any { diagnostic ->
            val factory = diagnostic.factory
            val element = diagnostic.psiElement
            val hasCantInferParameter = factory == Errors.CANNOT_INFER_PARAMETER_TYPE &&
                                        element.parent.parent == functionLiteral
            val hasUnresolvedItOrThis = factory == Errors.UNRESOLVED_REFERENCE &&
                                        element.text == "it" &&
                                        element.getStrictParentOfType<KtFunctionLiteral>() == functionLiteral
            hasCantInferParameter || hasUnresolvedItOrThis
        }
    }
}
