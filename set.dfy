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
        && (forall i,j :: 0<=i<j<size ==> elements[i] != elements[j])
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
        ensures e in this.ghostElements
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
            assert forall j :: 0<=j<size-1 ==> ghostElements[j] == old(ghostElements[j]) && old(ghostElements[j]) != elements[this.size-1];
            
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
            var aux := false;

            for i := 0 to this.size { 
                if this.elements[i] == e { 
                    eAt := i;
                    assert elements[eAt] == e;
                    aux := true;
                    break;
                } 
            }

            if aux == true{
            assert forall j :: 0<=j<size ==> ghostElements[j] == elements[j];
            assert ghostElements[eAt] == e;
            assert exists j :: 0<=j<size && ghostElements[j] == e;
            assert (forall i,j :: 0<=i<j<size ==> elements[i] != elements[j]);
            var newElementsSeq := this.elements[..eAt] + this.elements[eAt + 1..];
            assert forall j :: 0<=j<size-1 ==> newElementsSeq[j] != elements[eAt];
            var newElements := new int[this.size - 1];
                
            forall i | 0 <= i < this.size - 1 { 
                newElements[i] := newElementsSeq[i]; 
            }
            
            assert forall j :: 0<=j<size-1 ==> elements[eAt] != newElementsSeq[j];
            this.elements := newElements;
            assert forall j :: 0<=j<size-1 ==> elements[j] == newElementsSeq[j];
            this.size := this.size - 1;
            assert forall j :: 0<=j<size ==> elements[j] != e;
            this.ghostElements := this.elements[..];
            assert forall j :: 0<=j<size ==> ghostElements[j] != e;
            assert size > 1 ==> ghostElements != [];
            assert size > 1 ==> exists j :: (0<=j<size && (ghostElements[j] != e || ghostElements[j] == e));
            assert size == 1 ==> exists j :: (j==size-1 && (ghostElements[j] != e || ghostElements[j] == e));
        
            assert exists j :: 0<=j<size+1 && old(ghostElements[j]) == e;
            assert forall j :: (0<=j<size) ==> ghostElements[j] != e;
            // Se descobrir pq isso embaixo nao funciona, mata a charada.
            assert size > 1 ==> forall j :: (0<=j<size+1 && old(ghostElements[j]) == e) ==> (exists i :: i == j && old(ghostElements[i]) == old(ghostElements[j]));
            assert size > 1 ==> forall j :: (0<=j<size+1 && old(ghostElements[j]) == e) ==> (exists i :: 0<=i<size && ghostElements[i] != old(ghostElements[j]));
            assert size > 1 ==> forall j :: (0<=j<size+1) ==> (exists i :: 0<=i<size && ((ghostElements[i] != old(ghostElements[j]) ||  old(ghostElements[j]) == e)));
            this.ghostSize := this.size;
        }
    }
}

    method AddAll(toBeAdded: seq<int>)
    requires |toBeAdded| > 0
    requires forall i,j :: 0<=i<j<|toBeAdded| ==> toBeAdded[i] != toBeAdded[j]
    requires forall i,j :: 0<=i<j<elements.Length ==> elements[i] != elements[j]
    requires forall j :: 0<=j<|toBeAdded| ==> !(Contains(toBeAdded[j]))
    ensures Valid()
    ensures ghostElements == old(ghostElements) + toBeAdded
    ensures forall i | 0<=i<|toBeAdded| :: Contains(toBeAdded[i])
   
    {
        var newArray := new int[this.size + |toBeAdded|];
        assert newArray.Length == this.size + |toBeAdded|;
        var i := 0;
        var e_len := this.elements.Length;
        assert this.elements.Length == this.size;
        forall i | 0 <= i < this.size {
            newArray[i] := this.elements[i];

        }
        forall i | 0 <= i < |toBeAdded| {
            newArray[i + this.size] := toBeAdded[i];
        }
        this.elements := newArray;
        this.size := this.size + |toBeAdded|;
        this.ghostElements := this.elements[..];
        this.ghostSize := this.size;

    }


    // method AddAll(toBeAdded: array<int>)
    // requires toBeAdded.Length > 0
    // requires forall i,j :: 0<=i<j<toBeAdded.Length ==> toBeAdded[i] != toBeAdded[j]
    // requires forall i,j :: 0<=i<j<elements.Length ==> elements[i] != elements[j]
    // requires forall i,j :: 0<=i<j<size ==> elements[i] != elements[j]
    // ensures Valid()
    // {
        // var i := 0;
        // var k := 0;
        // var len := toBeAdded.Length;
        // while i < toBeAdded.Length {
        //     if !(Contains(toBeAdded[i])) {
        //         k := k + 1;
        //     }
        //     i := i + 1;
        // }
        // var newArray := new int[this.size + k];
        // assert newArray.Length == this.size + k;
        // i := 0;
        // var e_len := this.elements.Length;
        // assert this.elements.Length == this.size;
        // while i < this.size 
        //     invariant 0 <= i <= this.size
        //     invariant this.size <= newArray.Length
        //     invariant this.elements.Length == this.size
        //     invariant newArray.Length == this.size + k
        //     invariant forall i,j :: 0<=i<j<size ==> elements[i] != elements[j]
        //     {
        //     newArray[i] := this.elements[i];
        //     i := i + 1;
        // }
        // i := this.size;
        // var j := 0;
        // //assert forall m,n :: 0<=m<n<size ==> elements[m] != elements[n];
        // this.ghostSize := this.size;
        // assert size == ghostSize;
        // assert size == this.elements.Length;
        // assert 0 <= i <= this.size + k;

        // assert newArray.Length == this.size + k;
        // while j < toBeAdded.Length
        //     //invariant 0 <= i <= this.size + k
        //    //invariant 0 <= j <= toBeAdded.Length
        //    // invariant this.size <= newArray.Length
        //     invariant newArray.Length == this.size + k
        //     //invariant size == this.elements.Length
        //     invariant forall i,j :: 0<=i<j<size ==> elements[i] != elements[j]
        // {
    
        //         assert newArray.Length == this.size + k ;
        //     if !(Contains(toBeAdded[j])) {
        //         if i <= this.size + k {
        //             newArray[i] := toBeAdded[j];
        //             assert newArray.Length == this.size + k ;
        //             i := i + 1;
        //         }
               
        //     }
        //     assert newArray.Length == this.size + k ;

        //     j := j + 1;
        //     assert newArray.Length == this.size + k ;

        // }
        // assert newArray.Length == this.size + k ;
        // this.elements := newArray;
        // assert this.elements.Length == newArray.Length;

        // this.size := this.size + k;
        // this.ghostElements := this.elements[..];
        // this.ghostSize := this.size;

        // assert this.ghostElements == this.elements[..];

        // assert this.ghostSize == this.size;

        // assert this.size == this.elements.Length;

        // assert (forall i,j :: 0<=i<j<size ==> elements[i] != elements[j]);
        
    
   // }

// addAll (toBeAdded):
// var k := 0;
// For i | i < toBeAdded.length {
//  if !(Contains(toBeAdded[i]){
//   k := k + 1;
//   }
//  var newArray = int[size+k];
//  For i | i < size {
//   newArray[i] := elements[i];
// }
// For i | size <= i < k+size {
//   newArray[i] := toBeAdded[i-size];
// }
// elements := newArray


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