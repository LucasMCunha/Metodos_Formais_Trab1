// Bernardo Zomer, Carlo Mantovani and Lucas Cunha

method Main() {
    var set_ := new Set();
    var twoIsNewElement := set_.Add(2);
    assert twoIsNewElement;
    
    twoIsNewElement := set_.Add(2);
    var containsTwo := set_.Contains(2);
    var size := set_.Size();
    var isEmpty := set_.IsEmpty();
    assert !twoIsNewElement && containsTwo && size == 1 && !isEmpty;

    // TODO: Add assertions according to the following operations.
    var twoWasInSet := set_.Remove(2);
    twoWasInSet := set_.Remove(2);
    size := set_.Size();
    isEmpty := set_.IsEmpty();
}

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
        ensures Contains(e)
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
            forall i | 0 <= i < this.size { newElements[i] := this.elements[i]; }
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
        // Ensures the element was present in the set if wasInSet is true.
        ensures wasInSet ==> e in old(this.ghostElements)
        // Ensures the element array has not been changed
        // if the element was not present in the set.
        ensures !wasInSet ==> this.ghostElements == old(this.ghostElements)
        ensures Valid()
    {
        wasInSet := this.Contains(e);

        if wasInSet {
            var eAt := 0;

            for i := 0 to this.size { 
                if this.elements[i] == e { 
                    eAt := i;
                    break;
                } 
            }

            var newElementsSeq := this.elements[..eAt] + this.elements[eAt + 1..];
            var newElements := new int[this.size - 1];

            forall i | 0 <= i < this.size - 1 { 
                newElements[i] := newElementsSeq[i]; 
            }

            this.elements := newElements;
            this.size := this.size - 1;
            this.ghostElements := this.elements[..];
            this.ghostSize := this.size;
        }
    }

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