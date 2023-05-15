type T = int // para demonstração, mas poderia ser qualquer tipo

class {:autocontracts} Deque
{
    // Abstração
    ghost var elems: seq<T>;
    ghost const capacidade: nat; 

    // Implementação 
    const a: array<T>; // array circular, de a[inicio] (frente) até a[(inicio+tamanho-1) % a.Length] (final) 
    var inicio : nat; 
    var tamanho : nat;

    ghost predicate Valid()
    {
        0 <= tamanho <= a.Length
        && 0 <= inicio < a.Length 
        && capacidade == a.Length 
        && elems == if inicio + tamanho <= a.Length then a[inicio..inicio + tamanho]
                    else a[inicio..] + a[..tamanho - (a.Length - inicio)]  
    }
 
    constructor (capacidade: nat)
      requires capacidade > 0
      ensures elems == [] && this.capacidade == capacidade
    {
        a := new T[capacidade];
        inicio := 0;
        tamanho := 0;
        this.capacidade := capacidade;
        elems := []; 
    }

    //Predicado que pode ser utilizado como um método, gerando código executável
    predicate isEmpty()
      ensures isEmpty() <==> elems == []
    {
        tamanho == 0
    }
    
    //Predicado que pode ser utilizado como um método, gerando código executável
    predicate isFull()
      ensures isFull() <==> |elems| == capacidade
    {
        tamanho == a.Length
    }

    //Função que pode ser utilizada como um método, gerando código executável
    function front() : T
      requires !isEmpty()
      ensures front() == elems[0]
    {
        a[inicio]
    }

    //Função que pode ser utilizada como um método, gerando código executável
    function back() : T
      requires !isEmpty()
      ensures back() == elems[|elems| - 1]
    {
        a[(inicio + tamanho - 1) % a.Length] 
    }
    
    method push_back(x : T)
      requires !isFull()
      ensures elems == old(elems) + [x]
    {
        a[(inicio + tamanho) % a.Length] := x;
        tamanho := tamanho + 1;
        elems := elems + [x];
    }

    method pop_back()
      requires !isEmpty()
      ensures elems == old(elems[..|elems|-1])
    {
        tamanho := tamanho - 1;
        elems := elems[..|elems|-1];
    }

    method push_front(x : T)
      requires !isFull()
      ensures elems == [x] + old(elems) 
    {
        if inicio > 0
        {
            inicio := inicio - 1;
        }
        else
        {
            inicio := a.Length - 1;
        }
        a[inicio] := x;
        tamanho := tamanho + 1;
        elems := [x] + elems;
    }    

    method pop_front()
      requires !isEmpty()
      ensures elems == old(elems[1..]) 
    {
        if inicio + 1 < a.Length
        {
            inicio := inicio + 1;
        }
        else
        {
            inicio := 0;
        }
        tamanho := tamanho - 1;
        elems := elems[1..];
    } 

}

method Main()
{
    var q := new Deque(3);
    q.push_back(1);
    assert !q.isFull();
    q.push_back(2);
    q.push_back(3);
    assert q.capacidade == 3;
}
