// ---------------------------------------------------------------------------
// This file contains code needed to perform the node counts from Section 6.2
// ---------------------------------------------------------------------------


NodeCount:=function(N) 

    // ---------------------------------------------------------------------------------------------------
    // NodeCount: counts the number of (N,N)-isogeneous nodes using the formula from Castryk--Decru [CD21]
    //
    // INPUT: A positive integer N > 1
    // OUTPUT: The number of (N,N)-isogeneous nodes
    // ---------------------------------------------------------------------------------------------------

    if N eq 1 then
        return 1;
    end if;

    primes_dividing := [f[1] : f in Factorization(N)];
    M := &*[p : p in primes_dividing];
    nodes := &*[ (p+ 1)*(p^2 + 1) : p in primes_dividing];
    nodes *:= (N/M)^3;

    return nodes;
end function;


ExcessTermNodes:=function(N)

    // -----------------------------------------------------------------------------------------------
    // INPUT: An integer N
    // OUTPUT: Counts the number nodes overcounted (i.e., the excess term in Lemma 4, D_N - D_N')
    // -----------------------------------------------------------------------------------------------

    k := Max([k : k in [0..Floor(Log(2, N))] | (N mod 2^k) eq 0]);
    m := N div 2^k;
    
    if k eq 0 then 
        return 0;
    else
        return  &+[NodeCount(2^(k-i)*m) : i in [1..k]];
    end if;
end function;


NodesRevealed:=function(N)

    // -----------------------------------------------------------------------------------------------
    // INPUT: An integer N
    // OUTPUT: Counts the number nodes revealed by SPLITSEARCHER per step. That is D_N' of Lemma 4.
    // -----------------------------------------------------------------------------------------------

    return NodeCount(N) - ExcessTermNodes(N);
end function;


Lemma4calNCheck:=function(calN)

    // -----------------------------------------------------------------------------------------------
    // INPUT: A set of integers \geq 2
    // OUTPUT: A boolean true iff calN satisfies the hypothesis of Lemma 4.
    // -----------------------------------------------------------------------------------------------

    S := {N : N in calN}; assert #calN eq #S; calN := S;
    maxk := Ceiling(Log(2, Max(calN)));
    bool := not exists{N : N in calN | #(calN meet {N*2^k : k in [1..maxk]}) ge 1};
    return bool;
end function;


StepsToNodes:=function(steps, calN)

    // -----------------------------------------------------------------------------------------------
    // INPUT: An integer 'steps' and a set calN of N which satisfy the conditions of Lemma 4.
    // OUTPUT: A lower bound on the number of nodes revealed by SPLITSEARCHER after 'steps' steps
    //          given by Lemma 4.
    // -----------------------------------------------------------------------------------------------

    if #calN eq 0 then 
        return steps;
    end if;

    assert Lemma4calNCheck(calN); //check that calN satisfies the hypothesis
    
    if exists{N : N in calN | N in [2^i : i in [1..Ceiling(Log(2, N))]]} then //if calN has a power of 2 
        return steps*(&+[NodesRevealed(N) : N in calN]);
    else 
        return steps*(&+[NodesRevealed(N) : N in calN]) + steps;
    end if;
end function;