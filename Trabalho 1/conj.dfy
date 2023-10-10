class Conjunto {
   ghost var elements: array<int>;


    constructor() {
        elements := new int[0];
    }

    method Add(element: int) 
       requires !(Contains(element))
       ensures elements.Length == old(elements.Length) + 1
       {
       newArray = new int[elements.Length+1];
       while i < elements.Length
            invariant forall j :: 0 <= j < i ==> elements[j] == old(elements[j])
            {
                newArray[i] := elements[i];
                i = i + 1;
            }
        newArray[elements.Length+1] = element;
        elements = newArray;
    }

    method Remove(element: int) 
        requires (Contains(element))
        ensures elements.Length == old(elements.Length) - 1
        {
        var i := 0;
        var k := 0;
        newArray = new int[elements.Length-1]
        while i < elements.Length
            invariant forall j :: 0 <= j < i-1 ==> newArray[j] != element
            {
                if elements[i] != element {
                    newArray[k] := elements [i]
                    k = k + 1;
                }
                i := i + 1;
            }
        elements = newArray
        }


    method Contains(element: int) returns (contained: bool) 
        requires elements.Length != 0
        {
        var i := 0;
        contained := false;
        while i < elements.Length
            invariant j :: 0 <= j < i ==> elements[j] != element || elements [j] == element
            {
            if elements[i] == element {
                contained := true;
                return;
            }
            i := i + 1;
        }
        return contained
    }

    method NumberOfElements1()
    requires true
    {
        return elements.Length
    }

    method NumberOfElements()
        requires elements.Length != 0
        {
         var i := 0;
         var j := 0;
         var count = 0;
         var auxArray = new int[0];
         while i < elements.Length
            invariant true
            {
              while j < auxArray.Length  
                invariant true
                if auxArray[j] == elements[i]
                {
                    count = count + 0;
                }
                else
                {
                    auxArray := elements[i]
                    count = count + 1;
                }

                
            }
            return count
    }
}