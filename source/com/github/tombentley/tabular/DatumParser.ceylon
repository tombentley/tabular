import ceylon.language.meta {
    modules
}
import ceylon.language.meta.declaration {
    Package,
    Module,
    ClassDeclaration,
    ClassOrInterfaceDeclaration,
    FunctionDeclaration,
    ValueDeclaration,
    GenericDeclaration,
    NestableDeclaration
}
import ceylon.language.meta.model {
    Type,
    ClassOrInterface,
    UnionType,
    IntersectionType
}
import ceylon.collection {
    ArrayList,
    HashMap,
    StringBuilder
}

"A token produced by a lexer"
class Token(shared Object type, shared String token, shared Integer index) {
    shared actual String string => "``token`` (``type``) at index ``index``";
}

"enumerates the different token types"
abstract class DatumTokenType(shared actual String string)
        of dtAnd | dtOr | dtDot | dtComma | dtDColon | dtGt | dtLt | dtLSq | dtRSq | /*dtLParen | dtRParen |*/ dtDQuote | dtSQuote | dtPlus | dtMinus | dtHash | dtDollar | dtDigit | dtAlpha | dtEoi {}

object dtAnd extends DatumTokenType("&") {}
object dtOr extends DatumTokenType("|") {}
object dtDot extends DatumTokenType(".") {}
object dtComma extends DatumTokenType(",") {}
object dtDColon extends DatumTokenType("::") {}
object dtGt extends DatumTokenType(">") {}
object dtLt extends DatumTokenType("<") {}
object dtLSq extends DatumTokenType("[") {}
object dtRSq extends DatumTokenType("]") {}
//object dtLParen extends DatumTokenType("(") {}
//object dtRParen extends DatumTokenType(")") {}
object dtDQuote extends DatumTokenType("\"") {}
object dtSQuote extends DatumTokenType("'") {}
object dtPlus extends DatumTokenType("+") {}
object dtMinus extends DatumTokenType("-") {}
object dtHash extends DatumTokenType("#") {}
object dtDollar extends DatumTokenType("$") {}
object dtDigit extends DatumTokenType("digit") {}
object dtAlpha extends DatumTokenType("alpha") {}
object dtEoi extends DatumTokenType("<eoi>") {}


"The tokenizer used by [[DatumParser]]."
class DatumTokenizer(input) {
    "The input stream that we're tokenizing."
    shared String input;
    
    "Our index into the input."
    variable value ii = 0;
    Token at(Integer index) {
        if (exists char = input[ii]) {
            switch (char)
            case ('&') {
                return Token(dtAnd, char.string, ii);
            }
            case ('|') {
                return Token(dtOr, char.string, ii);
            }
            case ('.') {
                return Token(dtDot, char.string, ii);
            }
            case (',') {
                return Token(dtComma, char.string, ii);
            }
            case ('<') {
                return Token(dtLt, char.string, ii);
            }
            case ('>') {
                return Token(dtGt, char.string, ii);
            }
            case ('[') {
                return Token(dtLSq, char.string, ii);
            }
            case (']') {
                return Token(dtRSq, char.string, ii);
            }
            /*case ('(') {
                return Token(dtLParen, char.string, ii);
            }
            case (')') {
                return Token(dtRParen, char.string, ii);
            }*/
            case ('"') {
                return Token(dtDQuote, char.string, ii);
            }
            case ('\'') {
                return Token(dtSQuote, char.string, ii);
            }
            case ('+') {
                return Token(dtPlus, char.string, ii);
            }
            case ('-') {
                return Token(dtMinus, char.string, ii);
            }
            case ('#') {
                return Token(dtHash, char.string, ii);
            }
            case ('$') {
                return Token(dtDollar, char.string, ii);
            }
            case (':') {
                // check next is also :
                if (exists char2 = input[ii + 1]) {
                    if (char2 == ':') {
                        return Token(dtDColon, input[ii:2], ii);
                    } else {
                        throw Exception("tokenization error, expected ::, not :``char2`` at index ``ii``");
                    }
                }
                throw Exception("unexpected end of input");
            }
            else {
                if ('0' <= char <= '9') {
                    return Token(dtDigit, char.string, ii);
                } else if ('a' <= char <= 'z'
                            || 'A' <= char <= 'Z') {
                    return Token(dtAlpha, char.string, ii);
                } else {
                    throw Exception("unexpected character ``char`` at index ``ii``");
                }
            }
        } else {
            return Token(dtEoi, "", ii);
        }
    }
    variable Token current_ = at(0);
    
    "The current token."
    shared Token current {
        return current_;
    }
    
    "Consume the current token, moving on to the next token."
    shared void consume() {
        ii += current_.token.size;
        current_ = at(index);
    }
    
    "The index of the current token in the input."
    shared Integer index => ii;
}

"""
   A parser for "datums", the values store in a [[ValueTable]] as 
   emitted by [[ValueTableWriter]] and read by [[ValueTableReader]]. 
   The following grammar is parsed: 
 
       input ::= ::= value | meta
       value ::= string | character | number | byte | ref | array
       string ::= '\"' escapedCharacter* '\"'
       character ::= '\\'' escapedCharacter '\\''
       number ::= ('+'|'-') digits (('.') digits ('E' ('+'|'-') digits )?)?
       digits ::= ('0'-'9')*;
       byte ::= '#' hexDigit*
       
       array ::= '[' valueList? ']'
       valueList ::= value (',' value)*
 
       meta ::= package | declaration | model | application 
 
       package ::= ident ('.' ident)*;
       ref ::= ident
       declaration ::= ident '::' declarationMember
       declarationMember ::= ident ('.' ident)*
 
       model ::= typeApplication
       typeApplication ::= ident '<' typeArgumentList? '>'
       typeArgumentList ::= type (',' type)*
       type ::= intersectionType;
       intersectionType ::= unionType ('&' unionType)*
       unionType ::= model ('&' model)*
 """
class DatumParser(Map<Id,FundementalValueType|MetaValue> table) {
    // TODO Decide whether we throw exclusively AssertionError or some Exception from this parser
    
    shared FundementalValueType|MetaValue|Id[]|Id parse(String datum) {
        value tokenizer = DatumTokenizer(datum);
        return input(tokenizer);
    }
    FundementalValueType|MetaValue|Id[]|Id input(DatumTokenizer tokenizer) {
        value ct = tokenizer.current.type;
        switch (ct)
        case (dtDQuote) {
            return str(tokenizer);
        }
        case (dtSQuote) {
            return char(tokenizer);
        }
        case (dtPlus, dtMinus) {
            return number(tokenizer);
        }
        case (dtHash) {
            return byte(tokenizer);
        }
        case (dtLSq) {
            return array(tokenizer);
        }
        case (dtDigit, dtAlpha) {
            return meta(tokenizer);
        }
        else {
            throw Exception("unexpected token ``tokenizer.current``");
        }
    }
    
    "Unquotes the characters in the given string, which should not be be enclosed 
     in double quotes."
    String unquoteString(String string) {
        StringBuilder sb = StringBuilder();
        value iter = string.iterator();
        variable value ii = -1;
        while (true) {
            value char = iter.next();
            ii++;
            switch (char)
            case (is Finished) {
                break;
            }
            case ('\\') {
                if ('{' != iter.next()) {
                    throw Exception("expecting { following \\ ");
                }
                ii++;
                if ('#' != iter.next()) {
                    throw Exception("expecting # following \\{ ");
                }
                ii++;
                value start = ii + 1;
                while (true) {
                    if (is Character hexDigit = iter.next()) {
                        ii++;
                        if (hexDigit == '}') {
                            if (exists unquoted = unquoteCharacter(string, start, ii - start)) {
                                sb.appendCharacter(unquoted);
                                break;
                            } else {
                                throw Exception("invalid quoted character ``string[start:ii]``");
                            }
                        } else if (!('0' <= hexDigit <= '9' || 'a' <= hexDigit <= 'f')) {
                            throw Exception("expecting only hexadecimal digits following \\{#");
                        }
                    } else {
                        throw Exception("unterminated quoted character");
                    }
                }
            }
            case ('"', '\'', ',', '\n', '\r') {
                throw Exception("unquoted quotable character in quoted string: \"``string``\"");
            }
            else {
                assert (is Character char);
                sb.appendCharacter(char);
            }
        }
        return sb.string;
    }
    
    Character? unquoteCharacter(String hex, Integer start = 0, Integer end = hex.size) {
        Integer? codepoint = parseInteger(hex[start:end], 16);
        return codepoint?.character;
    }
    "string ::= '\\\"' escapedCharacter* '\\\"'"
    String str(DatumTokenizer tokenizer) {
        assert (tokenizer.current.type == dtDQuote);
        //tokenizer.consume();
        value start = tokenizer.index + 1;
        if (exists end = tokenizer.input[start...].firstOccurrence('\"')) {
            return end > start then unquoteString(tokenizer.input[start..end]) else "";
        } else {
            throw Exception("unterminated string: starting at ``start``");
        }
        // TODO the tokenizer state is now fucked
    }
    "character ::= '\\\\'' escapedCharacter '\\\\''"
    Character char(DatumTokenizer tokenizer) {
        assert (tokenizer.current.type == dtSQuote);
        //tokenizer.consume();
        value start = tokenizer.index + 1;
        if (exists end = tokenizer.input[start...].firstOccurrence('\'')) {
            value unquoted = unquoteString(tokenizer.input[start:end]);
            if (unquoted.size == 1,
                exists c = unquoted[0]) {
                return c;
            } else {
                throw Exception(unquoted.size == 0 then "empty quoted character" else "invalid quoted character: ``tokenizer.input[start:end]``");
            }
        } else {
            throw Exception("unterminated character: starting at ``start``");
        }
        // TODO the tokenizer state is now fucked
    }
    "number ::= ('+'|'-') digits (('.') digits ('E' ('+'|'-')? digits )?)?"
    Integer|Float number(DatumTokenizer tokenizer) {
        Integer start = tokenizer.index;
        Boolean plus;
        if (tokenizer.current.type == dtPlus) {
            plus = true;
        } else if (tokenizer.current.type == dtMinus) {
            plus = false;
        } else {
            assert (false);
        }
        tokenizer.consume();
        
        if (tokenizer.current.type != dtDigit) {
            if (tokenizer.current.token == "I") { // +Inf and -Inf
                tokenizer.consume();
                if (tokenizer.current.token != "n") {
                    throw Exception("unexpected token following `` plus then "+" else "-" ``I: ``tokenizer.current``");
                }
                tokenizer.consume();
                if (tokenizer.current.token != "f") {
                    throw Exception("unexpected token following `` plus then "+" else "-" ``In: ``tokenizer.current``");
                }
                tokenizer.consume();
                return plus then infinity else -infinity;
            } else if (tokenizer.current.token == "N") { // +NaN and -NaN
                tokenizer.consume();
                if (tokenizer.current.token != "a") {
                    throw Exception("unexpected token following `` plus then "+" else "-" ``N: ``tokenizer.current``");
                }
                tokenizer.consume();
                if (tokenizer.current.token != "N") {
                    throw Exception("unexpected token following `` plus then "+" else "-" ``Na: ``tokenizer.current``");
                }
                tokenizer.consume();
                return 0.0 / 0.0;
            } else {
                throw Exception("unexpected token following `` plus then "+" else "-" ``: ``tokenizer.current``");
            }
        }
        while (tokenizer.current.type == dtDigit) {
            tokenizer.consume();
        }
        
        if (tokenizer.current.type == dtDot) {
            tokenizer.consume();
            while (tokenizer.current.type == dtDigit) {
                tokenizer.consume();
            }
            if (tokenizer.current.type == dtAlpha
                        && tokenizer.current.token in "eE") {
                tokenizer.consume();
                if (tokenizer.current.type == dtPlus || tokenizer.current.type == dtMinus) {
                    tokenizer.consume();
                }
                if (tokenizer.current.type != dtDigit) {
                    throw Exception("expected digit in exponent but found ``tokenizer.current``");
                }
                while (tokenizer.current.type == dtDigit) {
                    tokenizer.consume();
                }
            }
            "invalid float"
            assert (exists float = parseFloat(tokenizer.input[start..tokenizer.index]));
            return float;
        } else {
            "invalid integer" // should be impossible
            assert (exists int = parseInteger(tokenizer.input[start..tokenizer.index]));
            return int;
        }
    }
    "byte ::= '#' hexDigit hexDigit?"
    Byte byte(DatumTokenizer tokenizer) {
        assert (tokenizer.current.type == dtHash);
        tokenizer.consume();
        Integer start = tokenizer.index;
        while (tokenizer.current.type == dtDigit
                    || (tokenizer.current.type == dtAlpha && tokenizer.current.token in "abcdefABCDEF")) {
            tokenizer.consume();
        }
        if (tokenizer.index != start + 1
                    && tokenizer.index != start + 2) {
            throw Exception("invalid byte literal: expected two or two hex digits");
        }
        "invalid byte" // should be impossible
        assert (exists int = parseInteger(tokenizer.input[start..tokenizer.index], 16));
        return int.byte;
    }
    
    Id identifier(DatumTokenizer tokenizer) {
        assert (tokenizer.current.type == dtAlpha
                    || tokenizer.current.type == dtDigit);
        value start = tokenizer.index;
        while (tokenizer.current.type == dtAlpha
                    || tokenizer.current.type == dtDigit) {
            tokenizer.consume();
        }
        return Id(tokenizer.input[start .. tokenizer.index - 1]);
    }
    
    MetaValue|Id meta(DatumTokenizer tokenizer) {
        Id ident = identifier(tokenizer);
        switch (tokenizer.current.type)
        case (dtEoi) {
            // plain ident, though actually ambiguous wrt a package name of one component
            return ident;
        }
        case (dtDot) {
            //package name
            return pkgOrMemberClass(ident, tokenizer);
        }
        case (dtDColon) {
            // declaration
            return member(ident, tokenizer);
        }
        case (dtLt) {
            //model
            return typeApplication(ident, tokenizer);
        }
        case (dtOr) {
            return union(ident, tokenizer);
        }
        case (dtAnd) {
            return intersection(ident, tokenizer);
        }
        else {
            throw Exception("unexpected token ``tokenizer.current``");
        }
    }
    
    // XXX Ids and Ceylon identifiers are not the same thing 
    // but these functions are conflating them
    String lident(DatumTokenizer tokenizer) => checkLident(identifier(tokenizer)).string;
    Id checkLident(Id ident) {
        if (!isLident(ident)) {
            throw Exception("illegal package name component: ``ident``");
        }
        return ident;
    }
    Boolean isLident(Id ident) {
        return (ident.string[0]?.lowercase else false);
    }
    
    Package|ClassOrInterfaceDeclaration|ValueDeclaration|NothingMeta pkgOrMemberClass(Id ident, DatumTokenizer tokenizer) {
        if (isLident(ident)) {
            return pkg(ident, tokenizer);
        } else {
            return member(ident, tokenizer);
        }
    }
    
    Package pkg(Id ident, DatumTokenizer tokenizer) {
        variable String pkgName = checkLident(ident).string;
        variable Module? mod = null;
        assert (tokenizer.current.type == dtDot);
        while (tokenizer.current.type == dtDot) {
            tokenizer.consume();
            pkgName += "." + lident(tokenizer);
            for (m in modules.list) {
                if (m.name == pkgName) {
                    mod = m;
                    break;
                }
            }
        }
        if (exists m = mod) {
            if (exists p = m.findPackage(pkgName)) {
                return p;
            } else {
                throw Exception("cannot find package ``pkgName`` in module ``m.name``");
            }
        } else {
            throw Exception("cannot find module for package ``pkgName``");
        }
    }
    
    ClassOrInterfaceDeclaration|ValueDeclaration|NothingMeta member(Id pident, DatumTokenizer tokenizer) {
        assert (tokenizer.current.type == dtDColon
                    || tokenizer.current.type == dtDot);
        tokenizer.consume();
        value pkg = table.get(pident);
        if (!is Package|ClassOrInterfaceDeclaration pkg) {
            throw Exception("container is neither package nor class nor interface: `` pkg else "null" ``");
        }
        assert (is Package|ClassOrInterfaceDeclaration pkg);
        variable Package|ClassOrInterfaceDeclaration container = pkg;
        variable NestableDeclaration? nestable = null;
        while (true) {
            String name = identifier(tokenizer).string;
            if (is Package p = container) {
                if ("Nothing" == name && "ceylon.language" == p.qualifiedName) {
                    return nothingMeta;
                }
                nestable = p.getMember<NestableDeclaration>(name);
            } else if (is ClassOrInterfaceDeclaration c = container) {
                nestable = c.getDeclaredMemberDeclaration<NestableDeclaration>(name);
            } else {
                assert (false);
            }
            "class not found"
            assert (exists n = nestable);
            if (is ClassOrInterfaceDeclaration n) {
                container = n;
            }
            if (tokenizer.current.type != dtDot) {
                break;
            } else {
                tokenizer.consume();
            }
        }
        assert (is ClassOrInterfaceDeclaration|ValueDeclaration n = nestable);
        return n;
    }
    
    Type union(Id ident, DatumTokenizer tokenizer) {
        assert (tokenizer.current.type == dtOr);
        tokenizer.consume();
        Type t1 = toType(table.get(ident));
        Id other = identifier(tokenizer);
        Type t2 = toType(table.get(other));
        variable Type result = t1.union(t2);
        while (tokenizer.current.type == dtOr) {
            tokenizer.consume();
            Type t3 = toType(table.get(identifier(tokenizer)));
            result = result.union(t3);
        }
        return result;
    }
    
    Type intersection(Id ident, DatumTokenizer tokenizer) {
        assert (tokenizer.current.type == dtAnd);
        tokenizer.consume();
        Id other = identifier(tokenizer);
        ///print(table.get(ident));
        Type t1 = toType(table.get(ident));
        Type t2 = toType(table.get(other));
        variable Type result = t1.intersection(t2);
        while (tokenizer.current.type == dtAnd) {
            tokenizer.consume();
            Id other3 = identifier(tokenizer);
            Type t3 = toType(table.get(other3));
            result = result.intersection(t3);
        }
        return result;
    }
    
    "typeApplication ::= ident typeArgumentList"
    ClassOrInterface<Anything> typeApplication(Id ident, DatumTokenizer tokenizer) {
        assert (tokenizer.current.type == dtLt);
        value callable = table.get(ident);
        value tas = typeArgumentList(tokenizer);
        if (is FunctionDeclaration callable) {
            assert (false);
            //return callable.apply<Anything,Nothing>(*tas);
        } else if (is ClassOrInterfaceDeclaration callable) {
            return callable.apply<Anything>(*tas);
        } else if (is GenericDeclaration callable) {
            throw Exception("unexpected kind of generic declaration ``callable``");
        } else {
            throw Exception("expected a generic declaration `` callable else "null" ``");
        }
    }
    "typeArgumentList ::= '<' ident (',' ident)* '>'"
    Type[] typeArgumentList(DatumTokenizer tokenizer) {
        assert (tokenizer.current.type == dtLt);
        value args = ArrayList<Type>();
        tokenizer.consume();
        args.add(toType(table.get(identifier(tokenizer))));
        while (tokenizer.current.type == dtComma) {
            tokenizer.consume();
            args.add(toType(table.get(identifier(tokenizer))));
        }
        return args.sequence();
    }
    
    Type toType(FundementalValueType|MetaValue? typeOrDeclaration) {
        Type t;
        if (is ClassOrInterfaceDeclaration typeOrDeclaration) {
            t = typeOrDeclaration.apply<Anything>();
        } else if (is Type typeOrDeclaration) {
            t = typeOrDeclaration;
        } else {
            assert (false);
        }
        return t;
    }
    
    Id[] array(DatumTokenizer tokenizer) {
        assert (tokenizer.current.type == dtLSq);
        tokenizer.consume();
        while (tokenizer.current.type != dtRSq) {
            // I know it's an Array. I'll need to know what it's an array of
            // then I can create the reference
            identifier(tokenizer);
        }
        return nothing;
    }
    
    /*"application ::= ident '(' argumentList? ')'"
    Anything application(String ident, DatumTokenizer tokenizer) {
        assert (tokenizer.current.type == dtLParen);
        value functional = table.get(ident);
        Anything[] arguments = argumentList(tokenizer);
        if (is FunctionDeclaration functional) {
            return functional.invoke([], *arguments);
        } else if (is ClassDeclaration functional) {
            return functional.instantiate([], *arguments);
        } else if (is Applicable functional) {
            return functional.apply(*arguments);
        } else {
            throw Exception("expected a function declaration, class declaration, or an applicable model: `` functional else "null" ``");
        }
    }
    "argumentList ::= '(' ident (',' ident)* ')'"
    Anything[] argumentList(DatumTokenizer tokenizer) {
        assert (tokenizer.current.type == dtLt);
        value args = ArrayList<Anything>();
        tokenizer.consume();
        args.add(table.get(identifier(tokenizer)));
        while (tokenizer.current.type == dtComma) {
            tokenizer.consume();
            args.add(table.get(identifier(tokenizer)));
        }
        return args.sequence();
    }*/
    /*
    Generic typeApply(GenericDeclaration g, DatumTokenizer tokenizer) {
        value tas = typeArguments(tokenizer);
        if (is FunctionDeclaration g) {
            return g.apply(*tas);
        } else if (is ClassOrInterfaceDeclaration g) {
            return g.apply(*tas);
        }
        throw Exception(g.string);
    }
    
    
     */
}


/*
shared interface Externalizable<Other> of Other
        given Other satisfies Externalizable<Other> {
    shared formal Factory<Other> factory();
}

Factory<Product>? externalize<Product>(Product p) {
    Factory<Anything>? f;
    if (is Package p) {
        f = PackageFactory(p.qualifiedName);
    } else if (is NestableDeclaration p) {
        assert (is Package pck = p.container);
        f = ToplevelDeclarationFactory<NestableDeclaration>(pck, p.name);
    } else if (is Value p) {
        f = ValueFactory(p);
    } else if (is Class p) {
        f = ClassFactory(p);
    } else if (is Externalizable<Product> p) {
        f = p.factory();
    } else {
        f = null;
    }
    assert (is Factory<Product>? f);
    return f;
}

shared class Example() satisfies Externalizable<Example> {
    shared actual Factory<Example> factory() {
        return ApplicableFactory(`Example`, []);
    }
}

shared interface Factory<out Product> {
    shared formal Product create();
}

shared serializable
class PackageFactory(String name) satisfies Factory<Package> {
    shared actual Package create() {
        return nothing;
    }
}
shared serializable
class ToplevelDeclarationFactory<Kind>(Package p, String name)
        satisfies Factory<Kind>
        given Kind satisfies NestableDeclaration {
    PackageFactory pf = PackageFactory(p.qualifiedName); //p.factory();
    shared actual Kind create() {
        assert (exists c = pf.create().getMember<Kind>(name));
        return c;
    }
}

shared serializable
class ValueFactory<CType>(Value<CType> c)
        satisfies Factory<Value<CType>> {
    ToplevelDeclarationFactory<ValueDeclaration> cdf = nothing; //c.factory()
    shared actual Value<CType> create() {
        return cdf.create().apply<CType>();
    }
}

shared interface TypeFactory<out Product>
        satisfies Factory<Product>
        given Product satisfies Type<Anything> {}

shared serializable
class TypeArgumentFactory(TypeFactory<Type<Anything>>[] t)
        satisfies Factory<Type<Anything>[]> {
    shared actual Type<Anything>[] create() => t*.create();
}

TypeArgumentFactory typeArgumentFactory(Generic g) {
    return TypeArgumentFactory(typeArguments(g));
}

shared serializable
class ClassFactory<CType,Arguments>(Class<CType,Arguments> c)
        satisfies TypeFactory<Class<CType,Arguments>>
        given Arguments satisfies Anything[] {
    ToplevelDeclarationFactory<ClassDeclaration> cdf = ToplevelDeclarationFactory(c.declaration.container, c.declatation.name); //c.factory()
    TypeArgumentFactory tpfs = typeArgumentFactory(c);
    shared actual Class<CType,Arguments> create() {
        return cdf.create().classApply<CType,Arguments>(*tpfs.create());
    }
}

shared serializable
class InterfaceFactory<CType>(Interface<CType> c)
        satisfies TypeFactory<Interface<CType>> {
    ToplevelDeclarationFactory<InterfaceDeclaration> cdf = nothing; //c.factory()
    TypeArgumentFactory tpfs = typeArgumentFactory(c);
    shared actual Interface<CType> create() {
        return cdf.create().interfaceApply<CType>(*tpfs.create());
    }
}

shared serializable
class ApplicableFactory<out Product>(Class<Product> c, Anything[] arguments)
        satisfies Factory<Product> {
    ClassFactory<Product,Anything[]> cf = nothing;
    shared actual Product create() {
        return cf.create().apply(*arguments);
    }
}
*/
