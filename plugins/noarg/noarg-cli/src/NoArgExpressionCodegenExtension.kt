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

package org.jetbrains.kotlin.noarg

import org.jetbrains.kotlin.codegen.ExpressionCodegen
import org.jetbrains.kotlin.codegen.FrameMap
import org.jetbrains.kotlin.codegen.ImplementationBodyCodegen
import org.jetbrains.kotlin.codegen.OwnerKind
import org.jetbrains.kotlin.codegen.context.ConstructorContext
import org.jetbrains.kotlin.codegen.extensions.ExpressionCodegenExtension
import org.jetbrains.kotlin.descriptors.*
import org.jetbrains.kotlin.descriptors.annotations.Annotations
import org.jetbrains.kotlin.descriptors.impl.ClassConstructorDescriptorImpl
import org.jetbrains.kotlin.psi.KtClass
import org.jetbrains.kotlin.resolve.descriptorUtil.getSuperClassOrAny
import org.jetbrains.kotlin.resolve.descriptorUtil.hasDefaultValue
import org.jetbrains.kotlin.resolve.jvm.annotations.findJvmOverloadsAnnotation
import org.jetbrains.kotlin.resolve.jvm.diagnostics.JvmDeclarationOrigin
import org.jetbrains.org.objectweb.asm.Opcodes
import org.jetbrains.org.objectweb.asm.Type

class NoArgExpressionCodegenExtension : ExpressionCodegenExtension {
    override fun generateClassSyntheticParts(codegen: ImplementationBodyCodegen) = with(codegen) {
        if (shouldGenerateNoArgConstructor()) {
            generateNoArgConstructor()
        }
    }

    private fun ImplementationBodyCodegen.generateNoArgConstructor() {
        val superClassInternalName = typeMapper.mapClass(descriptor.getSuperClassOrAny()).internalName
        val ownerContext = this.context

        val constructorDescriptor = createNoArgConstructorDescriptor(descriptor)

        v.newMethod(JvmDeclarationOrigin.NO_ORIGIN, Opcodes.ACC_PUBLIC, "<init>", "()V", null, null).apply {
            val methodContext = ConstructorContext(constructorDescriptor, OwnerKind.IMPLEMENTATION, ownerContext, null)
            val frameMap = FrameMap()
            val expressionCodegen = ExpressionCodegen(this, frameMap, Type.VOID_TYPE, methodContext, state, this@generateNoArgConstructor)

            visitCode()
            visitVarInsn(Opcodes.ALOAD, 0)
            visitMethodInsn(Opcodes.INVOKESPECIAL, superClassInternalName, "<init>", "()V", false)

            generateInitializers(expressionCodegen)

            visitInsn(Opcodes.RETURN)
            visitMaxs(-1, -1)
            visitEnd()
        }
    }

    private fun createNoArgConstructorDescriptor(containingClass: ClassDescriptor): ConstructorDescriptor {
        val descriptor = ClassConstructorDescriptorImpl.createSynthesized(
                containingClass, Annotations.EMPTY, false, SourceElement.NO_SOURCE)
        descriptor.initialize(emptyList(), Visibilities.PUBLIC)
        return descriptor
    }

    private fun KtClass.isNoArgClass() = this.getUserData(NO_ARG_CLASS_KEY) ?: false

    private fun ImplementationBodyCodegen.shouldGenerateNoArgConstructor(): Boolean {
        val origin = myClass as? KtClass ?: return false

        if (descriptor.kind != ClassKind.CLASS || !origin.isNoArgClass()) {
            return false
        }

        return descriptor.constructors.none { it.isZeroParameterConstructor() }
    }

    private fun ClassConstructorDescriptor.isZeroParameterConstructor(): Boolean {
        val parameters = this.valueParameters
        return parameters.isEmpty()
               || (parameters.all { it.hasDefaultValue() } && (isPrimary || findJvmOverloadsAnnotation() != null))
    }
}