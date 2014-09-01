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
    ClassOrInterfaceDeclaration
}

object tt {
    shared Integer lident = 0;
    shared Integer uident = 1;
    shared Integer or = 2;
    shared Integer and = 3;
    shared Integer dcolon = 4;
    shared Integer dot = 5;
    shared Integer comma = 6;
    shared Integer lt = 7;
    shared Integer gt = 8;
    shared Integer eoi = 9;
}

class Token(shared Object type, shared String token, shared Integer index) {
    shared actual String string => "``token`` (``type``) at index ``index``";
}

class TypeTokenizer(shared String input) {
    variable value index = 0;
    Token at(Integer index) {
        if (exists char = input[index]) {
            switch (char)
            case ('&') {
                return Token(tt.and, char.string, index);
            }
            case ('|') {
                return Token(tt.or, char.string, index);
            }
            case ('.') {
                return Token(tt.dot, char.string, index);
            }
            case (',') {
                return Token(tt.comma, char.string, index);
            }
            case ('<') {
                return Token(tt.lt, char.string, index);
            }
            case ('>') {
                return Token(tt.gt, char.string, index);
            }
            case (':') {
                // check next is also :
                if (exists char2 = input[index + 1]) {
                    if (char2 == ':') {
                        return Token(tt.dcolon, input[index:2], index);
                    } else {
                        throw Exception("tokenization error, expected ::, not :``char2``");
                    }
                }
                throw Exception("unexpected end of input");
            }
            else {
                Integer tti;
                if (char.uppercase) {
                    tti = tt.uident;
                } else if (char.lowercase) {
                    tti = tt.lident;
                } else {
                    assert (false);
                }
                variable value index2 = index + 1;
                while (exists char2 = input[index2],
                    char2.letter || char2.digit || char2 == '_') {
                    index2++;
                }
                return Token(tti, input[index .. index2 - 1], index);
            }
        } else {
            return Token(tt.eoi, "", index);
        }
    }
    variable Token current_ = at(0);
    
    shared Token current {
        return current_;
    }
    
    shared void consume() {
        index += current_.token.size;
        current_ = at(index);
    }
}


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
shared class TypeParser(Module ignored) {
    
    shared Type parse(String input) {
        value tokenizer = TypeTokenizer(input);
        value result = unionType(tokenizer);
        if (tokenizer.current.type != tt.eoi) {
            throw Exception();
        }
        return result;
    }
    "unionType ::= intersectionType ('|' intersectionType)*"
    Type unionType(TypeTokenizer tokenizer) {
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
    Type intersectionType(TypeTokenizer tokenizer) {
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
    Type fqType(TypeTokenizer tokenizer) {
        Package pck = packageName(tokenizer);
        if (tokenizer.current.type != tt.dcolon) {
            throw Exception();
        }
        tokenizer.consume();
        return uqType(pck, tokenizer);
    }
    "packageName ::= lident ('.' lident)*"
    Package packageName(TypeTokenizer tokenizer) {
        if (tokenizer.current.type != tt.lident) {
            throw Exception("");
        }
        variable value pkgName = tokenizer.current.token;
        tokenizer.consume();
        variable Module? m = null;
        while (tokenizer.current.type == tt.dot) {
            tokenizer.consume();
            if (tokenizer.current.type != tt.lident) {
                break;
            }
            pkgName = pkgName + "." + tokenizer.current.token;
            if (!m exists) {
                for (mod in modules.list) {
                    if (mod.name == pkgName) {
                        m = mod;
                        break;
                    }
                }
            }
            tokenizer.consume();
        }
        if (exists mod = m) {
            Package? pkg = mod.findPackage(pkgName);
            if (exists pkg) {
                return pkg;
            }
            throw Exception("package not found: ``pkgName``");
        } else {
            throw Exception("module not found containing package: ``pkgName``");
        }
    }
    "uqType ::= classOrInterface ('.' uqType)*"
    ClassOrInterface uqType(Package|ClassOrInterface pck, TypeTokenizer tokenizer) {
        variable ClassOrInterface decl = classOrInterface(pck, tokenizer);
        while (tokenizer.current.type == tt.dot) {
            tokenizer.consume();
            decl = uqType(decl, tokenizer);
        }
        return decl;
    }
    "classOrInterface ::= uident ('<' typeArgumentList '>')?"
    ClassOrInterface classOrInterface(Package|ClassOrInterface container, TypeTokenizer tokenizer) {
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
                try {
                    result = decl.apply<Anything>(*typeArguments);
                } catch (Exception e) {
                    throw Exception("type application error: with ``decl`` on input: ``tokenizer.input``", e);
                }
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
    Type[] typeArgumentList(TypeTokenizer tokenizer) {
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

class Bugger() {}
interface Sod {}

shared class Fuck<Y>() {
    shared class You<X>() {}
}
interface You<Y> {
    shared interface Fuck<X> {}
}

void testTypeParser() {
    print(modules.list);
    variable value parser = TypeParser(`module ceylon.language`);
    print(parser.parse("ceylon.language::String"));
    print(parser.parse("ceylon.language::Integer"));
    print(parser.parse("ceylon.language::List<ceylon.language::String>"));
    print(parser.parse("ceylon.language::Map<ceylon.language::String,ceylon.language::List<ceylon.language::String>>"));
    
    // TODO need to resolve against the (transitive) imports of the module, not just the module itself
    // for example the parser below cannot see c.l. even though
    // com.github.tombentley.tabular (implicitly) imports it.
    parser = TypeParser(`module ceylon.language`);
    print(parser.parse("com.github.tombentley.tabular::Fuck<com.github.tombentley.tabular::Bugger>"));
    print(parser.parse("com.github.tombentley.tabular::Fuck<com.github.tombentley.tabular::Bugger>.You<com.github.tombentley.tabular::Sod>"));
    print(parser.parse("com.github.tombentley.tabular::You<com.github.tombentley.tabular::Bugger>"));
    print(parser.parse("com.github.tombentley.tabular::You<com.github.tombentley.tabular::Bugger>.Fuck<com.github.tombentley.tabular::Sod>"));
    print(parser.parse("com.github.tombentley.tabular::You<com.github.tombentley.tabular::Fuck<com.github.tombentley.tabular::Bugger>.You<com.github.tombentley.tabular::Sod>>.Fuck<com.github.tombentley.tabular::Bugger>"));
}
