"Every instance will be identified by a unique `String`, 
 but let's use an alias for clarity."
//alias Id => String;
class Id(shared actual String string) {
    shared actual Boolean equals(Object other) {
        if (is Id other) {
            return this.string == other.string;
        } else {
            return false;
        }
    }
    shared actual Integer hash => string.hash;
}
