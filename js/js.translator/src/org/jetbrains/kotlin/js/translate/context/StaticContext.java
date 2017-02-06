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

package org.jetbrains.kotlin.js.translate.context;

import com.google.common.collect.Lists;
import com.google.common.collect.Maps;
import com.intellij.openapi.util.Factory;
import com.intellij.openapi.util.text.StringUtil;
import com.intellij.util.containers.ContainerUtil;
import com.intellij.util.containers.hash.LinkedHashMap;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;
import org.jetbrains.kotlin.builtins.KotlinBuiltIns;
import org.jetbrains.kotlin.descriptors.*;
import org.jetbrains.kotlin.descriptors.impl.LocalVariableDescriptor;
import org.jetbrains.kotlin.js.backend.ast.*;
import org.jetbrains.kotlin.js.backend.ast.metadata.MetadataProperties;
import org.jetbrains.kotlin.js.backend.ast.metadata.SideEffectKind;
import org.jetbrains.kotlin.js.config.JsConfig;
import org.jetbrains.kotlin.js.naming.NameSuggestion;
import org.jetbrains.kotlin.js.naming.SuggestedName;
import org.jetbrains.kotlin.js.translate.context.generator.Generator;
import org.jetbrains.kotlin.js.translate.context.generator.Rule;
import org.jetbrains.kotlin.js.translate.declaration.ClassModelGenerator;
import org.jetbrains.kotlin.js.translate.intrinsic.Intrinsics;
import org.jetbrains.kotlin.js.translate.utils.AnnotationsUtils;
import org.jetbrains.kotlin.js.translate.utils.JsAstUtils;
import org.jetbrains.kotlin.js.translate.utils.UtilsKt;
import org.jetbrains.kotlin.name.FqName;
import org.jetbrains.kotlin.resolve.BindingContext;
import org.jetbrains.kotlin.resolve.BindingTrace;
import org.jetbrains.kotlin.resolve.DescriptorUtils;
import org.jetbrains.kotlin.resolve.calls.tasks.DynamicCallsKt;
import org.jetbrains.kotlin.resolve.descriptorUtil.DescriptorUtilsKt;
import org.jetbrains.kotlin.serialization.js.ModuleKind;
import org.jetbrains.kotlin.types.typeUtil.TypeUtilsKt;

import java.util.*;

import static org.jetbrains.kotlin.js.config.LibrarySourcesConfig.UNKNOWN_EXTERNAL_MODULE_NAME;
import static org.jetbrains.kotlin.js.translate.utils.AnnotationsUtils.isLibraryObject;
import static org.jetbrains.kotlin.js.translate.utils.AnnotationsUtils.isNativeObject;
import static org.jetbrains.kotlin.js.translate.utils.JsAstUtils.pureFqn;
import static org.jetbrains.kotlin.js.translate.utils.JsDescriptorUtils.getSuperclass;

/**
 * Aggregates all the static parts of the context.
 */
public final class StaticContext {

    public static StaticContext generateStaticContext(
            @NotNull BindingTrace bindingTrace,
            @NotNull JsConfig config,
            @NotNull ModuleDescriptor moduleDescriptor
    ) {
        JsProgram program = new JsProgram();
        Namer namer = Namer.newInstance(program.getRootScope());
        JsFunction rootFunction = JsAstUtils.createFunctionWithEmptyBody(program.getScope());
        JsProgramFragment fragment = new JsProgramFragment(rootFunction.getScope());
        return new StaticContext(program, fragment, bindingTrace, namer, program.getRootScope(), config, moduleDescriptor);
    }

    @NotNull
    private final JsProgram program;

    @NotNull
    private final JsProgramFragment fragment;

    @NotNull
    private final BindingTrace bindingTrace;
    @NotNull
    private final Namer namer;

    @NotNull
    private final Intrinsics intrinsics;

    @NotNull
    private final JsScope rootScope;

    @NotNull
    private final Generator<JsName> innerNames = new InnerNameGenerator();
    @NotNull
    private final Map<FqName, JsName> packageNames = Maps.newHashMap();
    @NotNull
    private final Generator<JsScope> scopes = new ScopeGenerator();
    @NotNull
    private final Generator<JsName> objectInstanceNames = new ObjectInstanceNameGenerator();

    @NotNull
    private final Map<JsScope, JsFunction> scopeToFunction = Maps.newHashMap();

    @NotNull
    private final Map<MemberDescriptor, List<DeclarationDescriptor>> classOrConstructorClosure = Maps.newHashMap();

    @NotNull
    private final Map<ClassDescriptor, List<DeferredCallSite>> deferredCallSites = new HashMap<ClassDescriptor, List<DeferredCallSite>>();

    @NotNull
    private final JsConfig config;

    @NotNull
    private final ModuleDescriptor currentModule;

    @NotNull
    private final NameSuggestion nameSuggestion = new NameSuggestion();

    @NotNull
    private final Map<DeclarationDescriptor, JsName> nameCache = new HashMap<DeclarationDescriptor, JsName>();

    @NotNull
    private final Map<PropertyDescriptor, JsName> backingFieldNameCache = new HashMap<PropertyDescriptor, JsName>();

    @NotNull
    private final Map<DeclarationDescriptor, JsExpression> fqnExpressionCache = new HashMap<DeclarationDescriptor, JsExpression>();

    private final Map<DeclarationDescriptor, JsFqName> jsFqnCache = new HashMap<DeclarationDescriptor, JsFqName>();

    @NotNull
    private final Map<JsImportedModuleKey, JsImportedModule> importedModules = new LinkedHashMap<JsImportedModuleKey, JsImportedModule>();

    @NotNull
    private final JsScope rootPackageScope;

    @NotNull
    private final DeclarationExporter exporter = new DeclarationExporter(this);

    @NotNull
    private final Map<FqName, JsScope> packageScopes = new HashMap<FqName, JsScope>();

    @NotNull
    private final ClassModelGenerator classModelGenerator;

    //TODO: too many parameters in constructor
    private StaticContext(
            @NotNull JsProgram program,
            @NotNull JsProgramFragment fragment,
            @NotNull BindingTrace bindingTrace,
            @NotNull Namer namer,
            @NotNull JsScope rootScope,
            @NotNull JsConfig config,
            @NotNull ModuleDescriptor moduleDescriptor
    ) {
        this.program = program;
        this.fragment = fragment;
        this.bindingTrace = bindingTrace;
        this.namer = namer;
        this.intrinsics = new Intrinsics(this);
        this.rootScope = rootScope;
        this.config = config;
        this.currentModule = moduleDescriptor;
        rootPackageScope = new JsObjectScope(rootScope, "<root package>");

        JsName kotlinName = rootScope.declareName(Namer.KOTLIN_NAME);
        JsImportedModule kotlinModule = new JsImportedModule(Namer.KOTLIN_LOWER_NAME, kotlinName, null);
        importedModules.put(kotlinModule.getKey(), kotlinModule);
        fragment.getImportedModules().add(kotlinModule);

        classModelGenerator = new ClassModelGenerator(this);
    }

    @NotNull
    public JsProgram getProgram() {
        return program;
    }

    @NotNull
    public JsProgramFragment getFragment() {
        return fragment;
    }

    @NotNull
    public BindingTrace getBindingTrace() {
        return bindingTrace;
    }

    @NotNull
    public BindingContext getBindingContext() {
        return bindingTrace.getBindingContext();
    }

    @NotNull
    public Intrinsics getIntrinsics() {
        return intrinsics;
    }

    @NotNull
    public Namer getNamer() {
        return namer;
    }

    @NotNull
    public JsScope getScopeForDescriptor(@NotNull DeclarationDescriptor descriptor) {
        if (descriptor instanceof ModuleDescriptor) {
            return rootScope;
        }
        JsScope scope = scopes.get(descriptor.getOriginal());
        assert scope != null : "Must have a scope for descriptor";
        return scope;
    }

    @NotNull
    public JsFunction getFunctionWithScope(@NotNull CallableDescriptor descriptor) {
        JsScope scope = getScopeForDescriptor(descriptor);
        JsFunction function = scopeToFunction.get(scope);
        assert scope.equals(function.getScope()) : "Inconsistency.";
        return function;
    }

    @NotNull
    public JsNameRef getQualifiedReference(@NotNull DeclarationDescriptor descriptor) {
        return (JsNameRef) getQualifiedExpression(descriptor);
    }

    @Nullable
    private JsFqName getFqName(@NotNull DeclarationDescriptor descriptor) {
        JsFqName fqn;
        if (!jsFqnCache.containsKey(descriptor)) {
            fqn = UtilsKt.fqNameForDeclaration(nameSuggestion, descriptor);
            jsFqnCache.put(descriptor, fqn);
        }
        else {
            fqn = jsFqnCache.get(descriptor);
        }
        return fqn;
    }

    @NotNull
    private JsExpression getQualifiedExpression(@NotNull DeclarationDescriptor descriptor) {
        JsExpression fqn = fqnExpressionCache.get(descriptor);
        if (fqn == null) {
            fqn = buildQualifiedExpression(descriptor);
            fqnExpressionCache.put(descriptor, fqn);
        }

        return fqn.deepCopy();
    }

    @NotNull
    private JsExpression buildQualifiedExpression(@NotNull DeclarationDescriptor descriptor) {
        if (descriptor instanceof ClassDescriptor) {
            ClassDescriptor classDescriptor = (ClassDescriptor) descriptor;
            if (KotlinBuiltIns.isAny(classDescriptor)) {
                return pureFqn("Object", null);
            }
            else if (TypeUtilsKt.isThrowable(classDescriptor.getDefaultType())) {
                return pureFqn("Error", null);
            }
        }

        SuggestedName suggested = nameSuggestion.suggest(descriptor);
        if (suggested == null) {
            ModuleDescriptor module = DescriptorUtils.getContainingModule(descriptor);
            JsExpression result = getModuleExpressionFor(module);
            return result != null ? result : pureFqn(Namer.getRootPackageName(), null);
        }

        if (config.getModuleKind() != ModuleKind.PLAIN) {
            String moduleName = AnnotationsUtils.getModuleName(suggested.getDescriptor());
            if (moduleName != null) {
                return JsAstUtils.pureFqn(getImportedModule(moduleName, suggested.getDescriptor()).getInternalName(), null);
            }
        }

        JsExpression expression;
        List<JsName> partNames = getActualNameFromSuggested(suggested);
        if (isLibraryObject(suggested.getDescriptor())) {
            expression = Namer.kotlinObject();
        }
        // Don't generate qualifier for top-level native declarations
        // Don't generate qualifier for local declarations
        else if (isNativeObject(suggested.getDescriptor()) && !isNativeObject(suggested.getScope()) ||
                 suggested.getDescriptor() instanceof CallableDescriptor && suggested.getScope() instanceof FunctionDescriptor) {
            expression = null;
        }
        else {
            expression = getQualifiedExpression(suggested.getScope());
        }

        if (isNativeObject(suggested.getDescriptor()) && DescriptorUtils.isTopLevelDeclaration(suggested.getDescriptor())) {
            String fileModuleName = AnnotationsUtils.getFileModuleName(getBindingContext(), suggested.getDescriptor());
            if (fileModuleName != null) {
                JsName moduleJsName = getImportedModule(fileModuleName, null).getInternalName();
                expression = pureFqn(moduleJsName, expression);
            }

            String qualifier = AnnotationsUtils.getFileQualifier(getBindingContext(), suggested.getDescriptor());
            if (qualifier != null) {
                for (String qualifierPart : StringUtil.split(qualifier, ".")) {
                    expression = pureFqn(qualifierPart, expression);
                }
            }
        }

        for (JsName partName : partNames) {
            expression = new JsNameRef(partName, expression);
            applySideEffects(expression, suggested.getDescriptor());
        }
        assert expression != null : "Since partNames is not empty, expression must be non-null";
        return expression;
    }

    @NotNull
    public JsNameRef getQualifiedReference(@NotNull FqName packageFqName) {
        JsName packageName = getNameForPackage(packageFqName);
        return pureFqn(packageName, packageFqName.isRoot() ? null : getQualifierForParentPackage(packageFqName.parent()));
    }

    @NotNull
    public JsName getNameForDescriptor(@NotNull DeclarationDescriptor descriptor) {
        if (descriptor instanceof ClassDescriptor && KotlinBuiltIns.isAny((ClassDescriptor) descriptor)) {
            JsName result = rootScope.declareName("Object");
            MetadataProperties.setDescriptor(result, descriptor);
            return result;
        }
        SuggestedName suggested = nameSuggestion.suggest(descriptor);
        if (suggested == null) {
            throw new IllegalArgumentException("Can't generate name for root declarations: " + descriptor);
        }
        return getActualNameFromSuggested(suggested).get(0);
    }

    @NotNull
    public JsName getNameForBackingField(@NotNull PropertyDescriptor property) {
        JsName name = backingFieldNameCache.get(property);

        if (name == null) {
            SuggestedName fqn = nameSuggestion.suggest(property);
            assert fqn != null : "Properties are non-root declarations: " + property;
            assert fqn.getNames().size() == 1 : "Private names must always consist of exactly one name";

            JsScope scope = getScopeForDescriptor(fqn.getScope());
            String baseName = NameSuggestion.getPrivateMangledName(fqn.getNames().get(0), property) + "_0";
            name = scope.declareFreshName(baseName);
            backingFieldNameCache.put(property, name);
        }

        return name;
    }

    @NotNull
    public JsName getInnerNameForDescriptor(@NotNull DeclarationDescriptor descriptor) {
        JsName name = innerNames.get(descriptor.getOriginal());
        assert name != null : "Must have inner name for descriptor";
        return name;
    }

    @NotNull
    public JsName getNameForObjectInstance(@NotNull ClassDescriptor descriptor) {
        JsName name = objectInstanceNames.get(descriptor.getOriginal());
        assert name != null : "Must have inner name for object instance";
        return name;
    }

    @NotNull
    private List<JsName> getActualNameFromSuggested(@NotNull SuggestedName suggested) {
        JsScope scope = getScopeForDescriptor(suggested.getScope());

        if (DynamicCallsKt.isDynamic(suggested.getDescriptor())) {
            scope = JsDynamicScope.INSTANCE;
        }
        else if (AnnotationsUtils.isPredefinedObject(suggested.getDescriptor()) &&
                 DescriptorUtils.isTopLevelDeclaration(suggested.getDescriptor())) {
            scope = rootScope;
        }

        List<JsName> names = new ArrayList<JsName>();
        if (suggested.getStable()) {
            for (String namePart : suggested.getNames()) {
                JsName name = scope.declareName(namePart);
                MetadataProperties.setDescriptor(name, suggested.getDescriptor());
                names.add(name);
            }
        }
        else {
            // TODO: consider using sealed class to represent FQNs
            assert suggested.getNames().size() == 1 : "Private names must always consist of exactly one name";
            JsName name = nameCache.get(suggested.getDescriptor());
            if (name == null) {
                String baseName = NameSuggestion.sanitizeName(suggested.getNames().get(0));
                if (suggested.getDescriptor() instanceof LocalVariableDescriptor ||
                    suggested.getDescriptor() instanceof ValueParameterDescriptor
                ) {
                    name = scope.declareTemporaryName(baseName);
                }
                else {
                    if (!DescriptorUtils.isDescriptorWithLocalVisibility(suggested.getDescriptor())) {
                        baseName += "_0";
                    }
                    name = scope.declareFreshName(baseName);
                }
            }
            nameCache.put(suggested.getDescriptor(), name);
            MetadataProperties.setDescriptor(name, suggested.getDescriptor());
            names.add(name);
        }

        return names;
    }

    @NotNull
    private JsName getNameForPackage(@NotNull final FqName packageFqName) {
        return ContainerUtil.getOrCreate(packageNames, packageFqName, new Factory<JsName>() {
            @Override
            public JsName create() {
                String name = Namer.generatePackageName(packageFqName);
                return rootPackageScope.declareName(name);
            }
        });
    }

    @NotNull
    private JsNameRef getQualifierForParentPackage(@NotNull FqName packageFqName) {
        JsNameRef result = null;
        JsNameRef qualifier = null;

        FqName fqName = packageFqName;

        while (true) {
            JsNameRef ref = pureFqn(getNameForPackage(fqName), null);

            if (qualifier == null) {
                result = ref;
            }
            else {
                qualifier.setQualifier(ref);
            }

            qualifier = ref;

            if (fqName.isRoot()) break;
            fqName = fqName.parent();
        }

        return result;
    }

    @NotNull
    public JsConfig getConfig() {
        return config;
    }

    @NotNull
    public JsName importDeclaration(@NotNull String suggestedName, @NotNull JsFqName fqName, @NotNull JsExpression declaration) {
        // Adding prefix is a workaround for a problem with scopes.
        // Consider we declare name `foo` in functions's local scope, then call top-level function `foo`
        // from another module. It's imported into global scope under name `foo`. If we could somehow
        // declare all names in global scope before running translator, we would have got `foo_1` for local variable,
        // since local scope inherited from global scope.
        // TODO: remove prefix when problem with scopes is solved

        JsName result = fragment.getScope().declareTemporaryName(suggestedName);
        MetadataProperties.setImported(result, true);
        fragment.getImports().put(fqName, declaration);
        return result;
    }

    @NotNull
    private JsName localOrImportedName(@NotNull DeclarationDescriptor descriptor, @NotNull String suggestedName) {
        ModuleDescriptor module = DescriptorUtilsKt.getModule(descriptor);
        JsName name;
        JsFqName fqName = getFqName(descriptor);
        if (module != currentModule) {
            assert fqName != null : "Can't import declaration without fqname: " + descriptor;
            name = importDeclaration(suggestedName, fqName, getQualifiedReference(descriptor));
        }
        else {
            name = fragment.getScope().declareTemporaryName(suggestedName);
        }
        if (fqName != null) {
            fragment.getNameBindings().add(new JsNameBinding(fqName, name));
        }
        MetadataProperties.setDescriptor(name, descriptor);
        return name;
    }

    private final class InnerNameGenerator extends Generator<JsName> {
        public InnerNameGenerator() {
            addRule(new Rule<JsName>() {
                @Nullable
                @Override
                public JsName apply(@NotNull DeclarationDescriptor descriptor) {
                    if (descriptor instanceof FunctionDescriptor) {
                        FunctionDescriptor initialDescriptor = ((FunctionDescriptor) descriptor).getInitialSignatureDescriptor();
                        if (initialDescriptor != null) {
                            return getInnerNameForDescriptor(initialDescriptor);
                        }
                    }
                    if (descriptor instanceof ModuleDescriptor) {
                        return getModuleInnerName(descriptor);
                    }
                    if (descriptor instanceof LocalVariableDescriptor || descriptor instanceof ParameterDescriptor) {
                        return getNameForDescriptor(descriptor);
                    }
                    if (descriptor instanceof ConstructorDescriptor) {
                        if (((ConstructorDescriptor) descriptor).isPrimary()) {
                            return getInnerNameForDescriptor(((ConstructorDescriptor) descriptor).getConstructedClass());
                        }
                    }
                    return localOrImportedName(descriptor, getSuggestedName(descriptor));
                }
            });
        }
    }

    private final class ObjectInstanceNameGenerator extends Generator<JsName> {
        public ObjectInstanceNameGenerator() {
            addRule(new Rule<JsName>() {
                @Nullable
                @Override
                public JsName apply(@NotNull DeclarationDescriptor descriptor) {
                    String suggested = getSuggestedName(descriptor) + Namer.OBJECT_INSTANCE_FUNCTION_SUFFIX;
                    return fragment.getScope().declareTemporaryName(suggested);
                }
            });
        }
    }

    @NotNull
    public static String getSuggestedName(@NotNull DeclarationDescriptor descriptor) {
        String suggestedName;
        if (descriptor instanceof PropertyGetterDescriptor) {
            PropertyGetterDescriptor getter = (PropertyGetterDescriptor) descriptor;
            suggestedName = "get_" + getSuggestedName(getter.getCorrespondingProperty());
        }
        else if (descriptor instanceof PropertySetterDescriptor) {
            PropertySetterDescriptor setter = (PropertySetterDescriptor) descriptor;
            suggestedName = "set_" + getSuggestedName(setter.getCorrespondingProperty());
        }
        else if (descriptor instanceof ConstructorDescriptor) {
            ConstructorDescriptor constructor = (ConstructorDescriptor) descriptor;
            suggestedName = getSuggestedName(constructor.getContainingDeclaration()) + "_init";
            descriptor = descriptor.getContainingDeclaration();
            assert descriptor != null : "ConstructorDescriptor should have containing declaration: " + constructor;
        }
        else {
            if (descriptor.getName().isSpecial()) {
                if (descriptor instanceof ClassDescriptor) {
                    if (DescriptorUtils.isAnonymousObject(descriptor)) {
                        suggestedName = "ObjectLiteral";
                    }
                    else {
                        suggestedName = "Anonymous";
                    }
                }
                else if (descriptor instanceof FunctionDescriptor) {
                    suggestedName = "lambda";
                }
                else {
                    suggestedName = "anonymous";
                }
            }
            else {
                suggestedName = NameSuggestion.sanitizeName(descriptor.getName().asString());
            }
        }

        if (!(descriptor instanceof PackageFragmentDescriptor) && !DescriptorUtils.isTopLevelDeclaration(descriptor)) {
            DeclarationDescriptor container = descriptor.getContainingDeclaration();
            assert container != null : "We just figured out that descriptor is not for a top-level declaration: " + descriptor;
            suggestedName = getSuggestedName(container) + "$" + NameSuggestion.sanitizeName(suggestedName);
        }

        return suggestedName;
    }

    private JsScope getScopeForPackage(FqName fqName) {
        JsScope scope = packageScopes.get(fqName);
        if (scope == null) {
            if (fqName.isRoot()) {
                scope = new JsRootScope(program);
            }
            else {
                JsScope parentScope = getScopeForPackage(fqName.parent());
                scope = parentScope.innerObjectScope(fqName.shortName().asString());
            }
            packageScopes.put(fqName, scope);
        }
        return scope;
    }

    private final class ScopeGenerator extends Generator<JsScope> {

        public ScopeGenerator() {
            Rule<JsScope> generateNewScopesForClassesWithNoAncestors = new Rule<JsScope>() {
                @Override
                public JsScope apply(@NotNull DeclarationDescriptor descriptor) {
                    if (!(descriptor instanceof ClassDescriptor)) {
                        return null;
                    }
                    if (getSuperclass((ClassDescriptor) descriptor) == null) {
                        JsFunction function = new JsFunction(new JsRootScope(program), new JsBlock(), descriptor.toString());
                        scopeToFunction.put(function.getScope(), function);
                        return function.getScope();
                    }
                    return null;
                }
            };
            Rule<JsScope> generateInnerScopesForDerivedClasses = new Rule<JsScope>() {
                @Override
                public JsScope apply(@NotNull DeclarationDescriptor descriptor) {
                    if (!(descriptor instanceof ClassDescriptor)) {
                        return null;
                    }
                    ClassDescriptor superclass = getSuperclass((ClassDescriptor) descriptor);
                    if (superclass == null) {
                        return null;
                    }
                    return getScopeForDescriptor(superclass).innerObjectScope("Scope for class " + descriptor.getName());
                }
            };
            Rule<JsScope> generateNewScopesForPackageDescriptors = new Rule<JsScope>() {
                @Override
                public JsScope apply(@NotNull DeclarationDescriptor descriptor) {
                    return fragment.getScope();
                }
            };
            //TODO: never get there
            Rule<JsScope> generateInnerScopesForMembers = new Rule<JsScope>() {
                @Override
                public JsScope apply(@NotNull DeclarationDescriptor descriptor) {
                    return fragment.getScope().innerObjectScope("Scope for member " + descriptor.getName());
                }
            };
            Rule<JsScope> createFunctionObjectsForCallableDescriptors = new Rule<JsScope>() {
                @Override
                public JsScope apply(@NotNull DeclarationDescriptor descriptor) {
                    if (!(descriptor instanceof CallableDescriptor)) {
                        return null;
                    }

                    JsFunction correspondingFunction = JsAstUtils.createFunctionWithEmptyBody(fragment.getScope());
                    assert (!scopeToFunction.containsKey(correspondingFunction.getScope())) : "Scope to function value overridden for " + descriptor;
                    scopeToFunction.put(correspondingFunction.getScope(), correspondingFunction);
                    return correspondingFunction.getScope();
                }
            };
            Rule<JsScope> scopeForPackage = new Rule<JsScope>() {
                @Nullable
                @Override
                public JsScope apply(@NotNull DeclarationDescriptor descriptor) {
                    if (!(descriptor instanceof PackageFragmentDescriptor)) return null;

                    PackageFragmentDescriptor packageDescriptor = (PackageFragmentDescriptor) descriptor;
                    return getScopeForPackage(packageDescriptor.getFqName());
                }
            };
            addRule(scopeForPackage);
            addRule(createFunctionObjectsForCallableDescriptors);
            addRule(generateNewScopesForClassesWithNoAncestors);
            addRule(generateInnerScopesForDerivedClasses);
            addRule(generateNewScopesForPackageDescriptors);
            addRule(generateInnerScopesForMembers);
        }
    }

    @Nullable
    private JsExpression getModuleExpressionFor(@NotNull DeclarationDescriptor descriptor) {
        JsName name = getModuleInnerName(descriptor);
        return name != null ? JsAstUtils.pureFqn(name, null) : null;
    }

    @Nullable
    private JsName getModuleInnerName(@NotNull DeclarationDescriptor descriptor) {
        ModuleDescriptor module = DescriptorUtils.getContainingModule(descriptor);
        if (currentModule == module) {
            return rootScope.declareName(Namer.getRootPackageName());
        }
        String moduleName;
        if (module == module.getBuiltIns().getBuiltInsModule()) {
            moduleName = Namer.KOTLIN_LOWER_NAME;
        }
        else {
            moduleName = module.getName().asString();
            moduleName = moduleName.substring(1, moduleName.length() - 1);
        }

        if (UNKNOWN_EXTERNAL_MODULE_NAME.equals(moduleName)) return null;

        return getImportedModule(moduleName, null).getInternalName();
    }

    @NotNull
    private JsImportedModule getImportedModule(@NotNull String baseName, @Nullable DeclarationDescriptor descriptor) {
        String plainName = descriptor != null && config.getModuleKind() == ModuleKind.UMD ? getPlainId(descriptor) : null;
        JsImportedModuleKey key = new JsImportedModuleKey(baseName, plainName);

        JsImportedModule module = importedModules.get(key);
        if (module == null) {
            JsName internalName = rootScope.declareTemporaryName(Namer.LOCAL_MODULE_PREFIX + Namer.suggestedModuleName(baseName));
            module = new JsImportedModule(baseName, internalName, plainName != null ? new JsFqName(plainName, null) : null);
            importedModules.put(key, module);
            fragment.getImportedModules().add(module);
        }
        return module;
    }

    @NotNull
    private String getPlainId(@NotNull DeclarationDescriptor declaration) {
        SuggestedName suggestedName = nameSuggestion.suggest(declaration);
        assert suggestedName != null : "Declaration should not be ModuleDescriptor, therefore suggestedName should be non-null";
        return suggestedName.getNames().get(0);
    }

    private static JsExpression applySideEffects(JsExpression expression, DeclarationDescriptor descriptor) {
        if (descriptor instanceof FunctionDescriptor ||
            descriptor instanceof PackageFragmentDescriptor ||
            descriptor instanceof ClassDescriptor
        ) {
            MetadataProperties.setSideEffects(expression, SideEffectKind.PURE);
        }
        return expression;
    }

    public void putClassOrConstructorClosure(@NotNull MemberDescriptor localClass, @NotNull List<DeclarationDescriptor> closure) {
        classOrConstructorClosure.put(localClass, Lists.newArrayList(closure));
    }

    @Nullable
    public List<DeclarationDescriptor> getClassOrConstructorClosure(@NotNull MemberDescriptor descriptor) {
        List<DeclarationDescriptor> result = classOrConstructorClosure.get(descriptor);
        return result != null ? Lists.newArrayList(result) : null;
    }

    @NotNull
    public Map<ClassDescriptor, List<DeferredCallSite>> getDeferredCallSites() {
        return deferredCallSites;
    }

    @NotNull
    public List<JsStatement> getTopLevelStatements() {
        return fragment.getInitializerBlock().getStatements();
    }

    @NotNull
    public List<JsStatement> getDeclarationStatements() {
        return fragment.getDeclarationBlock().getStatements();
    }

    public void addClass(@NotNull ClassDescriptor classDescriptor) {
        if (!AnnotationsUtils.isNativeObject(classDescriptor) && !AnnotationsUtils.isLibraryObject(classDescriptor)) {
            fragment.getClasses().put(getInnerNameForDescriptor(classDescriptor), classModelGenerator.generateClassModel(classDescriptor));
        }
    }

    public void export(@NotNull MemberDescriptor descriptor, boolean force) {
        exporter.export(descriptor, force);
    }

    @NotNull
    public NameSuggestion getNameSuggestion() {
        return nameSuggestion;
    }

    @NotNull
    public ModuleDescriptor getCurrentModule() {
        return currentModule;
    }

    public void addInlineCall(@NotNull CallableDescriptor descriptor) {
        String tag = Namer.getFunctionTag(descriptor);
        fragment.getInlineModuleMap().put(tag, getModuleExpressionFor(descriptor));
    }
}
