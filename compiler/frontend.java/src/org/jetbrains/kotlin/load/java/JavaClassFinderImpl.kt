/*
 * Copyright 2010-2016 JetBrains s.r.o.
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

package org.jetbrains.kotlin.load.java

import org.jetbrains.kotlin.asJava.KtLightClassMarker
import org.jetbrains.kotlin.load.java.structure.JavaClass
import org.jetbrains.kotlin.load.java.structure.impl.JavaClassImpl
import org.jetbrains.kotlin.load.java.structure.impl.JavaPackageImpl
import org.jetbrains.kotlin.name.ClassId
import org.jetbrains.kotlin.name.FqName
import org.jetbrains.kotlin.resolve.BindingTrace
import org.jetbrains.kotlin.resolve.CodeAnalyzerInitializer
import org.jetbrains.kotlin.resolve.jvm.KotlinJavaPsiFacade
import org.jetbrains.kotlin.resolve.lazy.KotlinCodeAnalyzer

import javax.annotation.PostConstruct

class JavaClassFinderImpl : AbstractJavaClassFinder() {

    private lateinit var javaFacade: KotlinJavaPsiFacade

    @PostConstruct
    fun initialize(trace: BindingTrace, codeAnalyzer: KotlinCodeAnalyzer) {
        javaSearchScope = FilterOutKotlinSourceFilesScope(baseScope)
        javaFacade = KotlinJavaPsiFacade.getInstance(proj)
        CodeAnalyzerInitializer.getInstance(proj).initialize(trace, codeAnalyzer.moduleDescriptor, codeAnalyzer)
    }

    override fun findClass(classId: ClassId): JavaClass? {
        val psiClass = javaFacade.findClass(classId, javaSearchScope) ?: return null

        val javaClass = JavaClassImpl(psiClass)
        val fqName = classId.asSingleFqName()
        if (fqName != javaClass.fqName) {
            throw IllegalStateException("Requested $fqName, got ${javaClass.fqName}")
        }

        if (psiClass is KtLightClassMarker) {
            throw IllegalStateException("Kotlin light classes should not be found by JavaPsiFacade, resolving: $fqName")
        }

        return javaClass
    }

    override fun findPackage(fqName: FqName) = javaFacade.findPackage(fqName.asString(), javaSearchScope)?.let { JavaPackageImpl(it, javaSearchScope) }

    override fun knownClassNamesInPackage(packageFqName: FqName): Set<String>? = javaFacade.knownClassNamesInPackage(packageFqName)

}