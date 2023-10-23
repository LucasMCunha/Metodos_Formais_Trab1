class Set {
   ghost var elements: array<int>;


    constructor() {
        this.elements := new int[0];
    }

    method Add(element: int) returns (contained: bool) 
       requires true
       ensures (contained == true) ==> elements.Length == old(elements.Length) + 1 
       {
       var contained := true;
       var i := 0;
       var newArray := new int[elements.Length+1];
       while i < elements.Length
            invariant forall j :: 0 <= j < i ==> elements[j] == old(elements[j])
            {
                if element == elements[i]{
                    contained := false;
                }
                newArray[i] := elements[i];
                i := i + 1;
            }
        if contained == true
        {
        newArray[elements.Length] := element;
        elements := newArray;
        return contained;
        }
        else{
            return contained;
        }
    }

    method Remove(element: int) returns (contained: bool)  
        requires true
        ensures (contained == true) ==> elements.Length == old(elements.Length) - 1
        {
        var contained := true;
        var i := 0;
        var k := 0;
        var newArray := new int[elements.Length-1];
        if Contains(element) == true{
            while i < elements.Length
                invariant forall j :: 0 <= j < i-1 ==> newArray[j] != element
                {
                    if elements[i] != element {
                        newArray[k] := elements [i];
                        k := k + 1;
                    }
                    i := i + 1;
                }
                elements := newArray;
                return contained;
            }
            else{
                contained := false;
                return contained;
            }
        }


    method Contains(element: int) returns (contained: bool) 
        requires elements.Length != 0
        {
        var i := 0;
        contained := false;
        while i < elements.Length
            invariant forall j :: 0 <= j < i ==> elements[j] != element || elements [j] == element
            {
            if elements[i] == element {
                contained := true;
                return;
            }
            i := i + 1;
        }
        return contained;
    }

    method NumberOfElements()
    requires true
    {
        return elements.Length;
    }

method empty() returns (empty: bool) 
    requires true
    {
    empty := false;
    if elements == [] {
        empty := true;
        }
    return empty;
    }

method addAll(toBeAdded: array<int>)
    requires toBeAdded != []
    {
    var i := 0;
    while i < toBeAdded.Length
        invariant forall j :: 0 <= j < i ==> Contains(toBeAdded[j])
    {
        Add(toBeAdded[i]);
        i := i + 1;
    }
    }
}
//    method NumberOfElements()
//        requires elements.Length != 0
//        {
//         var i := 0;
//         var j := 0;
//         var count = 0;
//         var auxArray = new int[0];
//         while i < elements.Length
//            invariant true
//            {
//              while j < auxArray.Length  
//                invariant true
//                if auxArray[j] == elements[i]
//                {
//                    count = count + 0;
//                }
//                else
//                {
//                    auxArray := elements[i]
//                    count = count + 1;
//                }
//
//                
//            }
//            return count
//    }
                
