// ---------------------------------------------------------------------------------------
// This file contains code needed to do the precomputation necessary to run SplitSearcher
// ---------------------------------------------------------------------------------------

ig:=function(N)

    // -----------------------------------------------------------------------------------------------
    // INPUT: N \in {2,...,11}
    // OUTPUT: Sequence of polynomials II such that the normalised invariants are precisely 
    //         [II[1]/II[4], II[2]/II[4], II[3]/II[4]]
    // -----------------------------------------------------------------------------------------------

    _<r,s> := PolynomialRing(Integers(), 2);
    return eval Read("splitsearcher/normalisedinvs/" cat Sprint(N) cat ".m");
end function;


///////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////

ImagePoly:=function(N)
    
    // -----------------------------------------------------------------------------------------------
    // INPUT: N \in {2,...,11}
    // OUTPUT: Returns a single polynomial cutting out the image of Kumar's map \varphi_N
    // -----------------------------------------------------------------------------------------------

    _<i1,i2,i3> := PolynomialRing(Integers(), 3);
    return eval Read("splitsearcher/imageeqns/" cat Sprint(N) cat ".m");
end function;

///////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////

GetPrecompRes:=function(N)
        
    // -----------------------------------------------------------------------------------------------
    // INPUT: N \in {2,...,11}
    // OUTPUT: Returns the precomputed resultants corresponding to N
    // -----------------------------------------------------------------------------------------------

    _<r,s,i1,i2,i3> := PolynomialRing(Fp2, 5);
    f,g := eval Read("splitsearcher/precompres/" cat Sprint(N) cat ".m");
    return [f,g];
end function;

///////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////


CostOfStep:=function(p, constants)
    
    // -----------------------------------------------------------------------------------------------
    // INPUT: The underlying prime p and Tonelli--Shanks constants 
    // OUTPUT: Returns the cost of taking a step in \Gamma_2(2;p) via a Richelot isogeny using RIsog
    // -----------------------------------------------------------------------------------------------

    number_instances := 1; // Number of steps we want to average over
    steps_away := 30; // Number of steps we want to move away to begin with 
    instances := GetSupersingularWeierstrassPoints(number_instances,steps_away,Fp2);
    mulcount := 0;
    for weier_pts in instances do
        _, _, m := RIsog(weier_pts,constants,0);
        mulcount +:= m;
    end for;
    av_cost_step := mulcount/number_instances;
    Sprintf("The cost of a Richelot step for our %o bit prime (averaged \nover %o steps) is approximately %o F_p muls.\n", Ceiling(Log(2,p)), number_instances*steps_away, RealField(Floor(Log(10, av_cost_step)) + 3)!(av_cost_step));
    return av_cost_step;
end function; 


///////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////

SplitSearcherCost:=function(N)
        
    // -----------------------------------------------------------------------------------------------
    // INPUT: N \in {2,...,11}
    // OUTPUT: Returns the number of Fp multiplications to run SplitSearcher for N
    //         (assuming 1 Fp2 mult. = 3 Fp mults.)
    // -----------------------------------------------------------------------------------------------

    if N in [2..9] then 

        // For N = 2, ..., 9: we use the EVALUATE+GCD method.
        // Cost given by Proposition 4

        d1 := [1,2,6,6,7,10,16,12,24];
        d2 := [2,3,8,10,11,14,24,16,32];
        d3 := [1,2,6,6,7,10,16,12,24];
        m := [6,11,78,64,91,190,433,271,1005];
        M := [23,97,1136,2500,4118,24779,73454,69648,260178,669432];
        d_p := [6,16,35,92,114,264,340,540,606];
        n := N-1;
        return 3*(d1[n] + d2[n] + d3[n]) + 6*m[n] + 2*M[n] + 3/2*(d_p[n]+2)*(d_p[n]+3) - 27;

    elif N in [10,11] then 
        
        // For N= 10, 11: we use the RESULTANT+GCD method

        //Cost of Res(f,g): (Degree(g, 1)+Degree(f,1))^3 -- OVERESITMATE as we use in-built function //
        cost_resultants := [175616+262144, 262144+405224];

        //Cost of Polynomial Division: Div(p,q): Degree(p)*Degree(q) //
        cost_ply_div := [880*556 + 1080*798, 1240*640+1420*900];

        // Cost of Fast GCD //
        D := [606,1120];
        
        n:=N-9;
        return Ceiling(cost_resultants[n]+cost_ply_div[n]+3/2*(D[n]+2)*(D[n]+3) - 18);
    end if;
end function;

///////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////

SortListofListsbySecondEntry:=function(L)
        
    // -----------------------------------------------------------------------------------------------
    // INPUT: A list L of lists
    // OUTPUT: Sorts the list L of lists l_i by the second entries of l_i
    // -----------------------------------------------------------------------------------------------

    temp := [l[2][1] : l in L];
    temp_sorted := Sort(temp);
    L_sorted := [ [L[Index(temp, t)][1], [t]]  : t in temp_sorted];
    return L_sorted;
end function;

///////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////

ComputeNs:=function(av_cost_step, split_after_22_flag)
        
    // -----------------------------------------------------------------------------------------------
    // INPUT: The average cost of a step in \Gamma_2(2;p), av_cost_step
    // OUTPUT: The set of optimal N's to conduct the detection of (N,N)-splittings for
    // -----------------------------------------------------------------------------------------------

    nodes2 := 1; // nodes revealead by taking a step

    list_N := {};
    cost_N := [];
    node_N := [];
    
    Sprintf("| %-3o| %-22o |", "N", "Cost per node revealed");
    for N in [2..11] do
        if split_after_22_flag then
            cost := 14*SplitSearcherCost(N);
            Append(~cost_N, cost);
            nodes := NodesRevealed(2*N);
            Append(~node_N, nodes);
        else
            cost := SplitSearcherCost(N);
            Append(~cost_N, cost);
            nodes := NodesRevealed(N);
            Append(~node_N, nodes);
        end if;
        cost_per_node := cost/nodes;
        if cost_per_node le av_cost_step/nodes2 then 
            Include(~list_N, N);
        end if;
        Sprintf("| %-3o| %-22o |", N, RealField(Floor(Log(10, cost_per_node)) + 3)!(cost_per_node));
    end for;
    "Table: For p, the per-node cost of checking\n    for (N,N)-splittings is given as above.\n";

    N_subsets := Subsets(list_N);
    Exclude(~N_subsets, {});
    for S in N_subsets do 
        maxk := Ceiling(Log(2, Max(S)));
        if exists{N : N in S | #(S meet {N*2^k : k in [1..maxk]}) ge 1} then 
            Exclude(~N_subsets, S);
        end if;
    end for; 

    calN := [];
    optimal_cost := av_cost_step/nodes2;

    costs := [ [[], [av_cost_step/nodes2]] ];

    if split_after_22_flag then 
         _, c_Ig := IsogenousInvariantsFromWeierstrass([Random(Fp2) : i in [0..5]], 0);  // cost of computing alpha(C) for all neighbours 
    else
        _, c_Ig := InvariantsFromWeierstrassPoints([Random(Fp2) : i in [0..5]], 0);  // cost of computing alpha(C), we could also use 291 + 2log_2(p)
    end if; 

    for S in N_subsets do 
        assert #S ne 0;
        cost := av_cost_step + c_Ig + &+[cost_N[l-1] : l in S];

        if exists{N : N in S | N mod 2 eq 0} or split_after_22_flag then 
            nodes := &+[node_N[l-1] : l in S];
        else
            nodes := 1 + &+[node_N[l-1] : l in S]; 
        end if;
        cost_per_node := cost/nodes;
        Append(~costs, [[s : s in S], [cost_per_node]]);
    end for;

    // Sort the list of costs by the second entry (cost_per_node)
    costs_sorted := SortListofListsbySecondEntry(costs);
    
    Sprintf("| %-12o| %-22o |", "\\mathcal{N}", "Cost per node revealed");
    for i in [1..Min(5, #costs_sorted)] do
        Nset := [{N : N in t[1]} : t in costs_sorted[1..Min(5, #costs_sorted)]][i];
        cost_Nset := [RealField(4)!(t[2][1]) : t in costs_sorted[1..Min(5, #costs_sorted)]][i];
        Sprintf("| %-12o| %-22o |", Nset, RealField(Floor(Log(10, cost_Nset)) + 3)!(cost_Nset));
    end for;
    "Table: The 5 most efficient sets \\mathcal{N} \n    and their cost per node revealed.\n"; 

    calN := costs_sorted[1][1];
    calN := [Integers()!N : N in calN];
    return calN;
end function;

///////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////

MonomialsFromCoefficients:=function(plys)
        
    // -----------------------------------------------------------------------------------------------
    // INPUT: A list of polynomials plys
    // OUTPUT: A list of monomials in the polynomials of plys
    // -----------------------------------------------------------------------------------------------

    mons := {};
    cc := [];
    for ply in plys do
        cc1,_ := CoefficientsAndMonomials(ply);
        cc := cc cat cc1;
    end for;
    
    for c in cc do
        ms := Monomials(c);
        for m in ms do
            Include(~mons, m);
        end for;
    end for;
    return [m : m in mons];
end function;

///////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////

SplitSearcherPrecomp:=function(p, splitsearcher_flag, split_after_22_flag, constants)
        
    // -----------------------------------------------------------------------------------------------
    // SplitSearcherPrecomp: performs the precomputation for SplitSearcher using the functions above
    //
    // INPUT: Underlying prime p and the Tonelli--Shanks constants needed to take a (2,2)-step
    //
    // OUTPUT: 
    // (1) Set of Ns calN for which the detection will performed, 
    // (2) list of normalised invariants INVARIANTS given by Kumar's map for these N,
    // (3) list of pairs [\tilde{P}_{1,2}, \tilde{P}_{2,3}] RESULTANTS for these N < 10, 
    // (4) list of image equations (Section 4.4) IMAGES for these N < 5, 
    // (5) list of polynomials DIV_INFO (the polynomials Q_{i,j} of Proposition 3, reduced mod p) 
    //      to divide the resultants by when doing the RESULTANT+GCD method for N < 10, 
    // (6) list of monomials MONS_RES in RESULTANTS for these N < 10.
    // -----------------------------------------------------------------------------------------------

    INVARIANTS := AssociativeArray();
    RESULTANTS := AssociativeArray();
    IMAGES := AssociativeArray();
    DIV_INFO := AssociativeArray();
    MONS_RES := AssociativeArray();

    if splitsearcher_flag then 
        // COMPUTE THE COST OF A STEP IN THE (2,2)-GRAPH \Gamma_2(2;p): 
        av_cost_step := CostOfStep(p, constants);
        calN := ComputeNs(av_cost_step, split_after_22_flag);
        Sprintf("From the above we conclude the optimal set \\mathcal{N} is %o", {N : N in calN});

        for N in calN do
            INVARIANTS[N] := [<Evaluate(polys[1], [r,s]), Evaluate(polys[2], [r,s])> : polys in ig(N)];
            DIV_INFO[N] := eval Read("splitsearcher/divinfo/" cat Sprint(N) cat ".m");
            if N in [2..4] then 
                IMAGES[N] := Evaluate(ImagePoly(N), [i1,i2,i3]);
                RESULTANTS[N] := [Evaluate(poly, [rr,ss,i1,i2,i3]) : poly in GetPrecompRes(N)];
                MONS_RES[N] := MonomialsFromCoefficients(RESULTANTS[N]);
            elif N in [5..9] then 
                RESULTANTS[N] := [Evaluate(poly, [rr,ss,i1,i2,i3]) : poly in GetPrecompRes(N)];
                MONS_RES[N] := MonomialsFromCoefficients(RESULTANTS[N]);
            end if;
        end for;    
    else
        // THIS IS THE NON-SPLITSEARCHER VERSION, NEED THIS INFO ONLY FOR POST-COMPUTATION
        INVARIANTS[2] := [<Evaluate(polys[1], [r,s]), Evaluate(polys[2], [r,s])> : polys in ig(2)];
        RESULTANTS[2] := [Evaluate(poly, [rr,ss,i1,i2,i3]) : poly in GetPrecompRes(2)];
        MONS_RES[2] := MonomialsFromCoefficients(RESULTANTS[2]);
        calN:=[]; IMAGES := []; DIV_INFO:=[];
    end if;

    /*
    // To verify Table 2 //
    
    for N in calN do
        mons := {m : m in MONS_RES[N]};
        "N: " cat IntegerToString(N);
        "d1: " cat IntegerToString(Maximum({Degree(m, 1) : m in mons}));
        "d2: " cat IntegerToString(Maximum({Degree(m, 2) : m in mons}));
        "d3: " cat IntegerToString(Maximum({Degree(m, 3) : m in mons}));
        "m: " cat IntegerToString(#mons);
        "M: " cat IntegerToString(&+[#Monomials(c) : c in Coefficients(RESULTANTS[N][1]) cat Coefficients(RESULTANTS[N][1])]);
        d_P := Degree(RESULTANTS[N][1]) + Degree(RESULTANTS[N][2]);
        "d_P: " cat IntegerToString(d_P);
        "";
    end for;

    */

    // Stores all the monomials present in coefficients of precomputed resultants
    for N in [2..9] do 
        if N in calN then 
            ind := Index(calN,N);
            MONS_RES[N] := [ m : m in MONS_RES[N] | not m in &cat[MONS_RES[j] : j in calN[1..ind-1] ]]; // Removes repeated monomials
        end if;
    end for;

    return calN, INVARIANTS, RESULTANTS, IMAGES, DIV_INFO, MONS_RES;
end function;