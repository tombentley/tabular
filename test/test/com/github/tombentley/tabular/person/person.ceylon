shared serializable
class Person(name, address) {
    shared variable String name;
    shared variable Address address;
    shared variable Person? spouse = null;
    shared actual default String string {
        variable value s = "``name`` who lives at ``address``";
        if (exists sp = spouse) {
            s = s + " and has spouse ``sp.name``";
        }
        return s;
    }
}

shared serializable
class Address(lines) {
    shared String lines;
    shared actual String string => lines;
}

shared serializable
class EmployedPerson(String name, Address address, employer)
        extends Person(name, address) {
    shared Organization employer;
    shared variable Person? boss = null;
    shared actual default String string => "``super.string`` and is employed by ``employer``";
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
class Organization(name) {
    shared String name;
    shared actual String string => name;
}
/*
shared serializable
class Company(String name) extends Organization(name) {
}

shared serializable
class University(String name) extends Organization(name) {
}
 */
