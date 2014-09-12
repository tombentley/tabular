shared interface LegalEntity {
    shared formal String name;
}

shared serializable
class Person(name, address)
        satisfies LegalEntity {
    shared actual variable String name;
    shared variable Address address;
    shared variable Person? spouse = null;
    
    shared actual default String string {
        variable value s = "``name`` who lives at ``address``";
        if (exists sp = spouse) {
            s = s + " and has spouse ``sp.name``";
        }
        return s;
    }
    shared actual default Boolean equals(Object other) {
        if (is Person other) {
            return name == other.name
                    && address == other.address;
        }
        return false;
    }
    shared actual default Integer hash => name.hash + address.hash;
}

shared serializable
class Address(lines) {
    shared String* lines;
    shared actual String string => "|".join(lines);
    shared actual Boolean equals(Object other) {
        if (is Address other) {
            return lines == other.lines;
        }
        return false;
    }
    shared actual Integer hash => lines.hash;
}

shared serializable
class EmployedPerson(String name, Address address, employer)
        extends Person(name, address) {
    shared Organization employer;
    shared variable Person? boss = null;
    shared actual default String string => "``super.string`` and is employed by ``employer``";
    shared actual Boolean equals(Object other) {
        if (is EmployedPerson other) {
            return super.equals(other)
                    && employer == other.employer;
        }
        return false;
    }
    shared actual Integer hash => super.hash + employer.hash + (boss?.hash else 0);
}


/*
shared serializable
class RetiredPerson(String name, Address address) extends Person(name, address) {
}

shared serializable
class SelfEmployedPerson(String name, Address address) extends Person(name, address) {
}

shared serializable
class Student(String name, Address address, placeOfStudy) extends Person(name, address) {
    shared University placeOfStudy;
}
*/
shared serializable
class Organization(name)
        satisfies LegalEntity {
    shared actual String name;
    shared actual String string => name;
    shared actual Boolean equals(Object other) {
        if (is Organization other) {
            return name == other.name;
        }
        return false;
    }
}

shared abstract serializable
class Contract<out X,out Y>(x, y)
        given X satisfies LegalEntity
        given Y satisfies LegalEntity {
    shared X x;
    shared Y y;
    shared actual default String string =>
            "contract between ``x`` and ``y``";
}

shared serializable
class EmploymentContract(Organization org, Person person)
        extends Contract<Organization,Person>(org, person) {
    shared actual Boolean equals(Object other) {
        if (is EmploymentContract other) {
            return this.x == other.x
                    && this.y == other.y;
        }
        return false;
    }
    shared actual Integer hash => x.hash ^ y.hash;
}
/*
shared serializable
class Company(String name) extends Organization(name) {
}

shared serializable
class University(String name) extends Organization(name) {
}
 */
