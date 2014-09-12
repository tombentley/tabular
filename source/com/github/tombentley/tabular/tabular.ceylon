import ceylon.language.meta {
    type,
    optionalAnnotation
}
import ceylon.language.meta.model {
    Type,
    FunctionModel,
    Generic,
    ClassOrInterface
}
import ceylon.language.meta.declaration {
    ValueDeclaration,
    TypeParameter
}

"The *fundemental* types that are also value types."
alias FundementalValueType => String|Character|Integer|Float|Byte;

"Whether the given instance is a `ceylon.language::Array`."
Boolean isArray(Anything instance) {
    // this is lame but because Array is invariant there's no 
    // type we can use to test for array-ness
    
    return instance is List<Anything> // shortcircuit
            && type(instance).declaration.qualifiedName == "ceylon.language::Array";
}

"Whether the given instance is *fundemental*. 
 An instance is fundemental if it cannot be decomposed 
 in terms of its attributes, that is, is of type
 
 * `String`, `Character`, `Integer`, `Float `or `Byte`, or
 * Array<`T`> for some `T`
 "
Boolean isFundementalType(Anything instance) {
    if (instance is FundementalValueType) {
        return true;
    } else if (isArray(instance)) {
        return true;
    } else {
        return false;
    }
}

"The ValueDeclaration for the `object` declaration if the given instance is 
 the instance of a top level anonymous class, otherwise null."
ValueDeclaration? getObjectValueDeclaration(Anything instance) {
    if (exists instance) {
        if (instance == true) {
            return `value true`;
        } else if (instance == false) {
            return `value false`;
        } else {
            return type(instance).declaration.objectValue;
        }
    } else {
        return `value null`;
    }
}
"Whether the given instance is an anonymous class instance (`object` declaration)."
Boolean isObjectDeclaration(Anything instance) {
    return getObjectValueDeclaration(instance) exists;
}

"Whether the given instance can be serialized. 
 An instance can be serialized if it:
 
 * is `Identifiable` and annotated `serializable` or
 * is an object declaration or
 * is an instance a [[fundemental type|isFundementalType]]
 * is an `ArraySequence`
 "
Boolean isSerializable(Anything thing) {
    if (optionalAnnotation(`SerializableAnnotation`, type(thing).declaration) exists) {
        return true;
    } else if (thing is Sequence<Anything>) {
        // it can be decomposed
        return true;
    } else if (thing is FundementalValueType) {
        // it's fundemental
        return true;
    } else if (isArray(thing)) {
        return true;
    } else if (isObjectDeclaration(thing)) {
        // we can store a reference to it in the meta table
        return true;
    } else {
        return false;
    }
}

"The type arguments of the given Generic instance, in declaration order."
// see ceylon.language#544
Type[] typeArguments(Generic g) {
    TypeParameter[] tps;
    if (is ClassOrInterface g) {
        tps = g.declaration.typeParameterDeclarations;
    } else if (is FunctionModel g) {
        tps = g.declaration.typeParameterDeclarations;
    } else {
        throw;
    }
    return { for (tp in tps) g.typeArguments[tp] else nothing }.sequence();
}
