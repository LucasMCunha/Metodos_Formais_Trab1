class {:autocontracts true} Conjunto
{
    var elements: array<int>
    var size: int

    ghost var Content: seq<int>
    ghost var sizeGhost: int
    
    ghost predicate Valid()
    {
        sizeGhost == size && 
        elements.Length == size &&
        Content == elements[0..size]
    }

    constructor ()
        ensures Content == [] 
        ensures sizeGhost == 0
    {
        elements := new int[0];
        size := 0;
        Content := [];
        sizeGhost := 0;
    }

    function Contains(x: int): bool
        ensures Valid()
    {
        x in elements[0..size]
    }

    function SetSize(): int
        ensures Valid()
        ensures sizeGhost == size
    {
        size
    }

    function IsEmpty(): bool
        ensures Valid()
        ensures sizeGhost == size
    {
        size == 0
    }
    
    method Add(element: int) returns (contained: bool)
        ensures Valid()
        ensures contained ==> !(old(Contains(element)))
        ensures contained == !(old(Content) == Content)
        ensures (contained ==> Content == old(Content) + [element] && 
                       sizeGhost == old(sizeGhost) + 1)
        ensures (!contained ==> Content == old(Content) && 
                        sizeGhost == old(sizeGhost) && 
                        element in Content)
    {
        if (Contains(element)) 
        {
            contained := false;
        } 
        else 
        {
            var newArray := new int[size + 1];
            forall i | 0 <= i < size {
                newArray[i] := elements[i];
            }
            newArray[size] := element;
            elements := newArray;
            size := size + 1;
            contained := true;

            Content := elements[0..size];
            sizeGhost := size;
        }
    }

    method Remove(element: int) returns (contained:bool) //TO DO: Finish
    ensures Valid()
    ensures (Contains(element)) ==> size == old(size) - 1
        {
        contained := true;
        var i := 0;
        var k := 0;
        if Contains(element) == true{
            var newArray := new int[size-1];
            while i < size-1
                invariant forall j :: 0 <= j < i-1 ==> newArray[j] != element
                {
                    if elements[i] != element {
                        newArray[k] := elements [i];
                        k := k + 1;
                    }
                    i := i + 1;
                }
                elements := newArray;
                return true;
            }
            else{
                return false;
            }

    }

    method addAll(toBeAdded: array<int>) //TO DO: Finish
    ensures Valid()
    {
    var i := 0;
    while i < toBeAdded.Length
        invariant forall j :: 0 <= j < i ==> Contains(toBeAdded[j])
    {
        var aux := Add(toBeAdded[i]);
        i := i + 1;
    }
    }
}
method Main()
{
}
