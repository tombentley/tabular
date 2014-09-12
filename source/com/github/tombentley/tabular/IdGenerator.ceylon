import ceylon.collection {
    HashSet,
    ArrayList
}

"Generates ids from the characters in the given alphabet.
 Yields all 1 character ids then all 2 character ids etc."
// We could just use Integers of course, but there's a 
// space saving to be had working in base 62 instead of base 10
class IdGenerator(String alphabet = "0123456789" +
            "ABCDEFGHIJKLMNOPQRSTUVWXYZ" +
            "abcdefghijklmnopqrstuvwxyz") {
    "The characters in the alphabet must not be repeated"
    assert (HashSet { elements = alphabet; }.size == alphabet.size);
    
    value digits = ArrayList<Character>();
    variable value index = alphabet.size;
    
    Character? increment(Character digit) {
        if (exists index = alphabet.firstOccurrence(digit),
            exists next = alphabet[index + 1]) {
            return next;
        }
        return null;
    }
    "Yields the next id."
    shared Id next() {
        if (exists digit = alphabet[++index]) {
            digits.set(0, digit);
        } else {
            index = 0;
            assert (exists zero = alphabet[index]);
            variable value ii = 0;
            for (digit in digits) {
                if (exists nd = increment(digit)) {
                    digits.set(ii, nd);
                    break;
                }
                digits.set(ii, zero);
                ii++;
            } else {
                digits.insert(0, zero);
            }
        }
        
        return Id("".join(digits.reversed));
    }
}
