// Bernardo Zomer, Carlo Mantovani and Lucas Cunha

// An array-based set of elements of type int.
class Set {
    var elements: array<int>

    constructor() {
        this.elements := new int[0];
    }

    // Ensures an element is in the set
    // and returns true if it was previously not present.
    method Add(e: int) returns (isNewElement: bool)
        modifies this.elements
        // Ensures the element will be in the set.
        ensures e in this.elements[..]
        ensures isNewElement ==>
            // Ensures the element was not present in the set if isNewElement is true.
            !(e in old(this.elements[..]))
            // Ensures the first n elements of the element array were not changed, 
            // where n is the length of the old array.
            && this.elements[0..old(this.elements.Length)] == old(this.elements[..]) 
            // Ensures the last index of the element array contains the element.
            && this.elements[this.elements.Length - 1] == e
        // Ensures the element array has not been changed 
        // if the element was already present in the set.
        ensures !isNewElement ==> this.elements == old(this.elements)

    // Ensures an element is not in the set
    // and returns true if it was previously present.
    method Remove(e: int) returns (wasInSet: bool)
        modifies this.elements 
        // Ensures the element will not be in the set.
        ensures !(e in this.elements[..])
        // Ensures the element was present in the set if wasInSet is true.
        ensures wasInSet ==> e in old(this.elements[..])
        // Ensures the element array has not been changed
        // if the element was not present in the set.
        ensures !wasInSet ==> this.elements == old(this.elements)

    // Returns whether the set contains an element or not.
    method Contains(e: int) returns (contains: bool)
        ensures contains ==> e in this.elements[..]
    {
        for i := 0 to this.elements.Length {
            if this.elements[i] == e {
                return true;
            }
        }

        return false;
    }

    // Returns the amount of elements in the set.
    method Size() returns (length: int)
        ensures length == this.elements.Length
    {
        return this.elements.Length;
    }

    // Returns whether the set is empty or not.
    method IsEmpty() returns (isEmpty: bool)
        ensures isEmpty ==> this.elements.Length == 0
    {
        return this.elements.Length == 0;
    }
}