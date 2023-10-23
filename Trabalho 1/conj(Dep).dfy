class {:autocontracts}  Conjunto
{
  //Implementação
  var elements: array<int>

  //Invariante de classe
  ghost predicate Valid()
  {
    elements.Length > -1
  }

  constructor ()
  {
    elements := new int[0];
  }

  method Replace(newArray:array<int>)
    requires newArray.Length >= 0
    ensures elements == newArray 
  {
    elements := newArray;
  }

method Add(element: int) returns (contained: bool) 
       requires true
       ensures (contained == true) ==> elements.Length == old(elements.Length) 
        {
        contained := true;
        var newArray := new int[elements.Length+1];
        var i := 0;
        while i < elements.Length
        invariant 0 <= i <= elements.Length
        invariant forall j :: 0 <= j < i ==> (elements[j] == 0 || elements[j] != 0)
        {
            if element == elements[i]{
                    contained := false;
                }
            if i < newArray.Length{
                newArray[i] := elements[i];
                }
            i := i + 1;
            }
        if contained == true && newArray.Length > elements.Length
        {
        newArray[elements.Length] := element;
        //Replace(newArray);
        return contained;
        }
        else
        {
            if(contained == false){
                return contained;
            }
        }
    }
}

method Main()
{
}

/*
    constructor() {
        this.elements := new int[0];
    }

    method Substitution(e: array<int>)
        modifies elements
        ensures elements == e
    {
        elements := e;
    }

method Add(element: int) returns (contained: bool) 
       requires true
       ensures (contained == true) ==> elements.Length == old(elements.Length) + 1 
        {
        contained := true;
        var newArray := new int[elements.Length+1];
        var i := 0;
        var h := elements.Length;
        while i < h
        invariant 0 <= i <= h
        invariant forall j :: 0 <= j < i ==> (elements[j] == 0 || elements[j] != 0)
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
        Substitution(newArray);
        return contained;
        }
        else{
            return contained;
        }
    }
}

method Main()
{
    
}
*/

/*
class Conjunto2 {
    ghost var elements: array<int>
    ghost var contained: bool

    constructor() {
        this.elements := new int[0];
    }


 var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant forall j :: 0 <= j < i ==> a[j] == 0
  {
    a[i] := 0;
    i := i + 1;
  }

}

    method Remove(element: int) returns (contained: bool)  
        requires true
        ensures (contained == true) ==> elements.Length == old(elements.Length) - 1
        {
        contained := true;
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

    method NumberOfElements() returns (number:int)
    requires true
    {
        return elements.Length;
    }

method empty() returns (empty: bool) 
    requires true
    {
    empty := false;
    if elements.Length == 0 {
        empty := true;
        }
    return empty;
    }

method addAll(toBeAdded: array<int>)
    requires toBeAdded.Length != 0
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
*/        