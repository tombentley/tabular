import ceylon.language.meta.declaration {
    Package,
    ClassDeclaration,
    InterfaceDeclaration,
    ClassOrInterfaceDeclaration,
    ValueDeclaration
}
import ceylon.language.meta.model {
    Type,
    Class,
    ClassModel
}

abstract class NothingMeta() of nothingMeta {}

object nothingMeta extends NothingMeta() {}

"Representation of a union type within a [[MetaTable]]"
class Union(shared Id[] cases) extends Object() {
    shared actual Boolean equals(Object other) {
        if (is Union other) {
            // FIXME we don't want separate entries for X&Y versus Y&X, so we need a canonical order
            return cases == other.cases;
        } else {
            return false;
        }
    }
    shared actual Integer hash => cases.hash;
}
"Representation of an intersection type within a [[MetaTable]]"
class Intersection(shared Id[] satisfyeds) extends Object() {
    shared actual Boolean equals(Object other) {
        if (is Intersection other) {
            // FIXME we don't want separate entries for X&Y versus Y&X, so we need a canonical order
            return satisfyeds == other.satisfyeds;
        } else {
            return false;
        }
    }
    shared actual Integer hash => satisfyeds.hash;
}
"Representation of a member access within a [[MetaTable]]"
class Member(shared Boolean toplevel, shared Id container, shared String memberName) extends Object() {
    shared actual Boolean equals(Object other) {
        if (is Member other) {
            return container == other.container && memberName == other.memberName;
        } else {
            return false;
        }
    }
    shared actual Integer hash => container.hash + memberName.hash;
}
"Representation of a type application within a [[MetaTable]]."
class TypeApplication(shared Id generic, shared [Id*] typeArguments) extends Object() {
    shared actual Boolean equals(Object other) {
        if (is TypeApplication other) {
            return generic == other.generic && typeArguments == other.typeArguments;
        } else {
            return false;
        }
    }
    shared actual Integer hash => generic.hash + typeArguments.hash;
}

alias MetaValue => Package|Member|TypeApplication|Union|Intersection|ClassOrInterfaceDeclaration|ValueDeclaration|Type|String|Id[]|NothingMeta;
