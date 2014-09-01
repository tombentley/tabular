import ceylon.language.meta {
    modules
}
import ceylon.language.meta.model {
    Type,
    UnionType,
    IntersectionType,
    ClassOrInterface
}
import ceylon.language.meta.declaration {
    Module,
    Package,
    ClassOrInterfaceDeclaration,
    ClassDeclaration,
    InterfaceDeclaration,
    NestableDeclaration,
    ValueDeclaration,
    AliasDeclaration,
    FunctionOrValueDeclaration,
    FunctionDeclaration,
    SetterDeclaration
}


/*"
 input ::= type
 type ::= unionType
 unionType ::= intersectionType ('|' intersectionType)*
 intersectionTypr ::= fqType ('&' fqType)*
 fqType ::= packageName? '::' uqType
 packageName ::= lident ('.' lident)*
 uqType ::= classOrInterface ('.' uqType)*;
 classOrInterface ::= uident ('<' typeArgumentList '>')?
 typeArgumentList ::= type (',' type)*
 "
shared class DeclarationParser() {
}*/

interface Scoped<out Scope> {
    shared formal Scope scope;
}

class ModuleLookup() {
    shared PackageLookup? lookup(String name) {
        for (mod in modules.list) {
            if (mod.name == name) {
                return PackageLookup(mod);
            }
        }
        return null;
    }
}

class PackageLookup(shared actual Module scope) satisfies Scoped<Module> {
    shared NestableLookup? lookup(String name) {
        if (exists pkg = scope.findPackage(name)) {
            return NestableLookup(pkg);
        }
        return null;
    }
}

class NestableLookup(shared actual ClassOrInterfaceDeclaration|Package scope) satisfies Scoped<NestableDeclaration|Package> {
    shared NestableLookup|FunctionOrValueDeclaration? lookup(String name) {
        NestableDeclaration? member;
        if (is ClassOrInterfaceDeclaration scope) {
            member = scope.getDeclaredMemberDeclaration<NestableDeclaration>(name);
        } else if (is Package scope) {
            member = scope.getMember<NestableDeclaration>(name);
        } else {
            assert (false);
        }
        if (exists member) {
            if (is FunctionOrValueDeclaration member) {
                return member;
            } else if (is AliasDeclaration member) {
                if (is ClassOrInterface cori = member.extendedType) {
                    return NestableLookup(cori.declaration);
                } else {
                    // TODO extendedType could be a union or intersection?
                    throw;
                }
            } else if (is ClassOrInterfaceDeclaration member) {
                return NestableLookup(member);
            }
            // Will never be setter, right?
        }
        return null;
    }
}

shared interface Lookup<M,P,C,I,F,V> {
    shared formal M? lookupModule(String mod);
    shared formal P? lookupPackage(M mod, String name);
    shared C|I? lookupType(P|C|I container, String name) {
        assert (is C|I? cls = lookupMember(container, name));
        return cls;
    }
    shared C? lookupClass(P|C|I container, String name) {
        assert (is C? cls = lookupMember(container, name));
        return cls;
    }
    shared I? lookupInterface(P|C|I container, String name) {
        assert (is I? cls = lookupMember(container, name));
        return cls;
    }
    shared F|V? lookupFunctionOrValue(P|C|I container, String name) {
        assert (is F|V? cls = lookupMember(container, name));
        return cls;
    }
    shared F? lookupFunction(P|C|I container, String name) {
        assert (is F? cls = lookupMember(container, name));
        return cls;
    }
    shared V? lookupValue(P|C|I container, String name) {
        assert (is V? cls = lookupMember(container, name));
        return cls;
    }
    shared formal C|I|F|V? lookupMember(P|C|I container, String name);
}

class DeclarationLookup() satisfies Lookup<Module,Package,ClassDeclaration,InterfaceDeclaration,FunctionDeclaration,ValueDeclaration> {
    shared actual Module? lookupModule(String mod) {
        for (m in modules.list) {
            if (m.name == mod) {
                return m;
            }
        }
        return null;
    }
    shared actual Package? lookupPackage(Module mod, String name) {
        return mod.findPackage(name);
    }
    shared actual ClassDeclaration|InterfaceDeclaration|FunctionDeclaration|ValueDeclaration lookupMember(Package|ClassDeclaration|InterfaceDeclaration container, String name) {
        return nothing;
    }
}
/*
"
 input ::= type
 type ::= unionType
 unionType ::= intersectionType ('|' intersectionType)*
 intersectionTypr ::= fqType ('&' fqType)*
 fqType ::= packageName? '::' uqType
 packageName ::= lident ('.' lident)*
 uqType ::= classOrInterface ('.' uqType)*;
 classOrInterface ::= uident ('<' typeArgumentList '>')?
 typeArgumentList ::= type (',' type)*
 "
shared class TypeParser2<M,P,C,I,F,V>(Lookup<M,P,C,I,F,V> lookup) {
    
    shared Type parse(String input) {
        value tokenizer = Tokenizer(input);
        value result = unionType(tokenizer);
        if (tokenizer.current.type != tt.eoi) {
            throw Exception();
        }
        return result;
    }
    "unionType ::= intersectionType ('|' intersectionType)*"
    Type unionType(Tokenizer tokenizer) {
        Type type1 = intersectionType(tokenizer);
        if (tokenizer.current.type == tt.or) {
            tokenizer.consume();
            Type type2 = intersectionType(tokenizer);
            return makeUnion(type1, type2);
        } else {
            return type1;
        }
    }
    
    Type makeUnion(Type type1, Type type2) {
        variable List<Type> cases;
        if (is UnionType type1) {
            cases = type1.caseTypes;
        } else {
            cases = [type1];
        }
        if (is UnionType type2) {
            cases = cases.chain(type2.caseTypes).sequence();
        } else {
            cases = cases.follow(type2).sequence();
        }
        // XXX there's no way to do thise
        return nothing;
    }
    "intersectionTypr ::= fqType ('&' fqType)*"
    Type intersectionType(Tokenizer tokenizer) {
        Type type1 = fqType(tokenizer);
        if (tokenizer.current.type == tt.or) {
            tokenizer.consume();
            Type type2 = fqType(tokenizer);
            return makeIntersection(type1, type2);
        } else {
            return type1;
        }
    }
    Type makeIntersection(Type type1, Type type2) {
        variable List<Type> satisfied;
        if (is IntersectionType type1) {
            satisfied = type1.satisfiedTypes;
        } else {
            satisfied = [type1];
        }
        if (is IntersectionType type2) {
            satisfied = satisfied.chain(type2.satisfiedTypes).sequence();
        } else {
            satisfied = satisfied.follow(type2).sequence();
        }
        // XXX there's no way to do thise
        return nothing;
    }
    
    "fqType ::= packageName? '::' uqType"
    Type fqType(Tokenizer tokenizer) {
        P pck = packageName(tokenizer);
        if (tokenizer.current.type != tt.dcolon) {
            throw Exception();
        }
        tokenizer.consume();
        return uqType(pck, tokenizer);
    }
    "packageName ::= lident ('.' lident)*"
    P packageName(Tokenizer tokenizer) {
        if (tokenizer.current.type != tt.lident) {
            throw Exception("");
        }
        variable value pkgName = tokenizer.current.token;
        tokenizer.consume();
        variable M? mod = null;
        while (tokenizer.current.type == tt.dot) {
            tokenizer.consume();
            if (tokenizer.current.type != tt.lident) {
                break;
            }
            if (!mod exists) {
                mod = lookup.lookupModule(pkgName);
            }
            pkgName = pkgName + "." + tokenizer.current.token;
            tokenizer.consume();
        }
        if (exists m = mod) {
            P? pkg = lookup.lookupPackage(m, pkgName);
            if (exists pkg) {
                return pkg;
            }
            throw Exception("package not found: ``pkgName``");
        } else {
            throw Exception("module not found for package: ``pkgName``");
        }
    }
    "uqType ::= classOrInterface ('.' uqType)*"
    ClassOrInterface uqType(P|C|I pck, Tokenizer tokenizer) {
        variable C|I decl = classOrInterface(pck, tokenizer);
        while (tokenizer.current.type == tt.dot) {
            tokenizer.consume();
            decl = uqType(decl, tokenizer);
        }
        return decl;
    }
    "classOrInterface ::= uident ('<' typeArgumentList '>')?"
    C|I classOrInterface(P|C|I container, Tokenizer tokenizer) {
        if (tokenizer.current.type != tt.uident) {
            throw Exception();
        }
        String name = tokenizer.current.token;
        tokenizer.consume();
        Type[] typeArguments;
        if (tokenizer.current.type == tt.lt) {
            tokenizer.consume();
            typeArguments = typeArgumentList(tokenizer);
        } else {
            typeArguments = [];
        }
        ClassOrInterface result;
        if (is Package container) {
            ClassOrInterfaceDeclaration? decl = container.getClassOrInterface(name);
            if (exists decl) {
                result = decl.apply<Anything>(*typeArguments);
            } else {
                throw Exception("class or interface not found: ``name`` in ``container``");
            }
        } else if (is ClassOrInterface container) {
            // XXX This cannot find non-shared member types
            value member = container.getClassOrInterface<Nothing>(name, *typeArguments);
            if (is ClassOrInterface member) {
                result = member;
            } else {
                if (exists member) {
                    throw Exception("``container``.``name``: ``member``");
                } else {
                    throw Exception("``container``.``name``: null");
                }
            }
        } else {
            assert (false);
        }
        return result;
    }
    "typeArgumentList ::= type (',' type)*"
    Type[] typeArgumentList(Tokenizer tokenizer) {
        variable Type[] types = [unionType(tokenizer)];
        while (tokenizer.current.type == tt.comma) {
            tokenizer.consume();
            types = types.follow(unionType(tokenizer)).sequence();
        }
        if (tokenizer.current.type == tt.gt) {
            tokenizer.consume();
            return types;
        } else {
            throw Exception("");
        }
    }
}


/*
"
 input ::= model
 model ::= unionModel
 unionModel ::= intersectionModel ('|' intersectionModel)*
 intersectionModel ::= fqModel ('&' fqType)*
 fqModel ::= packageName? '::' member;
 fqType ::= packageName? '::' type;
 fqValue ::= packageName? '::' value;
 
 packageName ::= lident ('.' lident)*
 
 member ::= type | value;
 
 type ::= classOrInterface ('.' member)*;
 classOrInterface ::= uident ('<' typeArgumentList '>')?
 typeArgumentList ::= model (',' model)*
 
 value ::= functionOrValue ('.' member)*;
 functionOrValue ::=  lident ('<' typeArgumentList '>')?
 "
shared class ModelParser<M,P,C,I,F,V>(Lookup<M,P,C,I,F,V> lookup) {
    
    shared Type parse(String input) {
        value tokenizer = Tokenizer(input);
        value result = unionType(tokenizer);
        if (tokenizer.current.type != tt.eoi) {
            throw Exception();
        }
        return result;
    }
    "unionType ::= intersectionType ('|' intersectionType)*"
    Type unionType(Tokenizer tokenizer) {
        Type type1 = intersectionType(tokenizer);
        if (tokenizer.current.type == tt.or) {
            tokenizer.consume();
            Type type2 = intersectionType(tokenizer);
            return makeUnion(type1, type2);
        } else {
            return type1;
        }
    }
    
    Type makeUnion(Type type1, Type type2) {
        variable List<Type> cases;
        if (is UnionType type1) {
            cases = type1.caseTypes;
        } else {
            cases = [type1];
        }
        if (is UnionType type2) {
            cases = cases.chain(type2.caseTypes).sequence();
        } else {
            cases = cases.follow(type2).sequence();
        }
        // XXX there's no way to do thise
        return nothing;
    }
    "intersectionTypr ::= fqType ('&' fqType)*"
    Type intersectionType(Tokenizer tokenizer) {
        Type type1 = fqType(tokenizer);
        if (tokenizer.current.type == tt.or) {
            tokenizer.consume();
            Type type2 = fqType(tokenizer);
            return makeIntersection(type1, type2);
        } else {
            return type1;
        }
    }
    Type makeIntersection(Type type1, Type type2) {
        variable List<Type> satisfied;
        if (is IntersectionType type1) {
            satisfied = type1.satisfiedTypes;
        } else {
            satisfied = [type1];
        }
        if (is IntersectionType type2) {
            satisfied = satisfied.chain(type2.satisfiedTypes).sequence();
        } else {
            satisfied = satisfied.follow(type2).sequence();
        }
        // XXX there's no way to do thise
        return nothing;
    }
    
    "fqType ::= packageName? '::' uqType"
    Type fqType(Tokenizer tokenizer) {
        P pck = packageName(tokenizer);
        if (tokenizer.current.type != tt.dcolon) {
            throw Exception();
        }
        tokenizer.consume();
        return uqType(pck, tokenizer);
    }
    "packageName ::= lident ('.' lident)*"
    P packageName(Tokenizer tokenizer) {
        if (tokenizer.current.type != tt.lident) {
            throw Exception("");
        }
        variable value pkgName = tokenizer.current.token;
        tokenizer.consume();
        variable M? m = null;
        while (tokenizer.current.type == tt.dot) {
            tokenizer.consume();
            if (tokenizer.current.type != tt.lident) {
                break;
            }
            if (!m exists) {
                m = lookup.lookupModule(pkgName);
            }
            pkgName = pkgName + "." + tokenizer.current.token;
            tokenizer.consume();
        }
        if (exists mod = m) {
            P? pkg = lookup.lookupPackage(mod, pkgName);
            if (exists pkg) {
                return pkg;
            }
            throw Exception("package not found: ``pkgName``");
        }
        throw Exception("no module found which contains package: ``pkgName``");
    }
    "uqType ::= classOrInterface ('.' uqType)*"
    C|I uqType(P|C|I pck, Tokenizer tokenizer) {
        variable C|I decl = classOrInterface(pck, tokenizer);
        while (tokenizer.current.type == tt.dot) {
            tokenizer.consume();
            decl = uqType(decl, tokenizer);
        }
        return decl;
    }
    "classOrInterface ::= uident ('<' typeArgumentList '>')?"
    C|I classOrInterface(P|C|I container, Tokenizer tokenizer) {
        if (tokenizer.current.type != tt.uident) {
            throw Exception();
        }
        String name = tokenizer.current.token;
        tokenizer.consume();
        Type[] typeArguments;
        if (tokenizer.current.type == tt.lt) {
            tokenizer.consume();
            typeArguments = typeArgumentList(tokenizer);
        } else {
            typeArguments = [];
        }
        ClassOrInterface result;
        if (is Package container) {
            ClassOrInterfaceDeclaration? decl = container.getClassOrInterface(name);
            if (exists decl) {
                result = lookup.apply(decl, *typeArguments);
            } else {
                throw Exception("class or interface not found: ``name`` in ``container``");
            }
        } else if (is ClassOrInterface container) {
            // XXX This cannot find non-shared member types
            value member = container.getClassOrInterface<Nothing>(name, *typeArguments);
            if (is ClassOrInterface member) {
                result = member;
            } else {
                if (exists member) {
                    throw Exception("``container``.``name``: ``member``");
                } else {
                    throw Exception("``container``.``name``: null");
                }
            }
        } else {
            assert (false);
        }
        return result;
    }
    "typeArgumentList ::= type (',' type)*"
    Type[] typeArgumentList(Tokenizer tokenizer) {
        variable Type[] types = [unionType(tokenizer)];
        while (tokenizer.current.type == tt.comma) {
            tokenizer.consume();
            types = types.follow(unionType(tokenizer)).sequence();
        }
        if (tokenizer.current.type == tt.gt) {
            tokenizer.consume();
            return types;
        } else {
            throw Exception("");
        }
    }
}
*/
*/
