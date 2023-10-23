// Bernardo Zomer, Carlo Mantovani and Lucas Cunha

// An array-based set of elements of type int.
class {:autocontracts true} Set {
    var elements: array<int>
    var size: int

    ghost var ghostElements: seq<int>
    ghost var ghostSize: int

    ghost predicate Valid() {
        this.ghostElements == this.elements[..]
        && this.ghostSize == this.size
        && this.size == this.elements.Length
    }

    constructor() 
        ensures this.ghostElements == []
        ensures this.ghostSize == 0
    {
        this.elements := new int[0];
        this.size := 0;
        this.ghostElements := [];
        this.ghostSize := 0;
    }

    // Ensures an element is in the set
    // and returns true if it was previously not present.
    method Add(e: int) returns (isNewElement: bool)
        // Ensures the element will be in the set.
        ensures e in this.elements[..]
        ensures isNewElement ==>
            // Ensures the element was not present in the set if isNewElement is true.
            !(old(Contains(e)))
            // Ensures the array is the same as before 
            // with the added element at the end.
            && this.ghostElements == old(this.ghostElements) + [e]
            && this.ghostSize == old(this.ghostSize + 1)
        // Ensures the element array has not been changed 
        // if the element was already present in the set.
        ensures !isNewElement ==> this.ghostElements == old(this.ghostElements)
        ensures Valid()
    {
        isNewElement := !Contains(e);

        if isNewElement {
            var newElements := new int[this.size + 1];
            forall i | 0 <= i < size { newElements[i] := this.elements[i]; }
            newElements[this.size] := e;
            this.elements := newElements;
            this.size := this.size + 1;
            this.ghostElements := this.elements[..];
            this.ghostSize := this.size;
        }
    }

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
    function Contains(e: int): bool
        ensures Valid()
    {
        e in this.elements[..]
    }

    // Returns the amount of elements in the set.
    function Size(): int
        ensures Valid()
    {
        this.size
    }

    // Returns whether the set is empty or not.
    function IsEmpty(): bool
        ensures Valid()
    {
        this.size == 0
    }
}