declare verbose SplEnd, 2;

ALL_DISCS := [ 4, 5, 8, 9, 12, 13, 16, 17, 21, 24, 25, 28, 29, 33,
               36, 36, 37, 41, 44, 53, 56, 57, 60, 64, 65, 69, 73,
               76, 77, 81, 85, 89, 92, 93, 97, 100, 121 ];
ALL_DISCS := [D : D in ALL_DISCS | D lt 89];


function CostOfStep(p, Fp2, constants)
  // INPUT: The underlying prime p and Tonelli--Shanks constants 
  // OUTPUT: Returns the cost of taking a step in \Gamma_2(2;p) via a Richelot isogeny using RIsog
  
  number_instances := 1; // Number of steps we want to average over
  steps_away := 30; // Number of steps we want to move away to begin with 
  instances := GetSupersingularWeierstrassPoints(number_instances,steps_away,Fp2);
  mulcount := 0;
  for weier_pts in instances do
    _, _, m := RIsog(weier_pts,constants,0);
    mulcount +:= m;
  end for;
  av_cost_step := mulcount/number_instances;

  displ_av_cost := RealField(Floor(Log(10, av_cost_step)) + 3)!(av_cost_step);
  vprintf SplEnd, 2: "The cost of a Richelot step for our %o bit prime (averaged \nover %o steps) is approximately %o F_p muls.\n\n", Ceiling(Log(2,p)), number_instances*steps_away, displ_av_cost;
  return av_cost_step;
end function; 


function GetCostInvariants(D)
  // From Table 2 and 4 //
  P<i1,i2,i3> := PolynomialRing(Integers(), 3);
  P<rr,ss> := PolynomialRing(P, 2);
  res := GetPrecompRes(D);
  res := [Evaluate(f, [rr,ss,i1,i2,i3]) : f in res];
  mres := MonomialsFromCoefficients(res);
  mons := {m : m in mres};
  d1 := Maximum({Degree(m, 1) : m in mons});
  d2 := Maximum({Degree(m, 2) : m in mons});
  d3 := Maximum({Degree(m, 3) : m in mons});
  m := #mons;
  M := &+[#Monomials(c) : c in Coefficients(res[1]) cat Coefficients(res[1])];
  d_p := Degree(res[1]) + Degree(res[2]);
  return d1,d2,d3,m,M,d_p;
end function;

 
function EndSearcherCost(D)
  // INPUT: Discriminant D
  // OUTPUT: Returns the number of Fp multiplications to run EndSearcher for N
  //         (assuming 1 Fp2 mult. = 3 Fp mults.)

  if D lt 89 then
    // Use the EVALUATE+GCD method.
    // Cost given by Proposition 4

    d1,d2,d3,m,M,d_p := GetCostInvariants(D);
    return 3*(d1 + d2 + d3) + 6*m + 2*M + 3/2*(d_p + 2)*(d_p + 3) - 27;

  elif D in [100,121] then 
    // Use the RESULTANT+GCD method
    if D eq 100 then
      // Cost of Res(f,g): (Degree(g, 1)+Degree(f,1))^3 -- OVERESITMATE as we use in-built function //
      cost_resultants := 175616+262144;
      // Cost of Polynomial Division: Div(p,q): Degree(p)*Degree(q) //
      cost_ply_div := 880*556 + 1080*798;
      // Cost of Fast GCD //
      DD := 606;
    elif D eq 121 then
      cost_resultants := 262144 + 405224;
      cost_ply_div := 1240*640 + 1420*900;
      DD := 1120;
    end if;

    return Ceiling(cost_resultants + cost_ply_div + 3/2*(DD + 2)*(DD + 3) - 18);
  end if;
end function;


function SortListofListsbySecondEntry(L)
  // INPUT: A list L of lists
  // OUTPUT: Sorts the list L of lists l_i by the second entries of l_i

  temp := [l[2][1] : l in L];
  temp_sorted := Sort(temp);
  L_sorted := [ [L[Index(temp, t)][1], [t]]  : t in temp_sorted];
  return L_sorted;
end function;


function ComputeNs(av_cost_step, split_after_22_flag, Fp2)
  // INPUT: The average cost of a step in \Gamma_2(2;p), av_cost_step
  // OUTPUT: The set of optimal N's to conduct the detection of RM N

  nodes2 := 1; // nodes revealead by taking a step

  list_N := {};
  /* cost_N := []; */
  /* node_N := []; */
  cost_N := AssociativeArray();
  node_N := AssociativeArray();

  vprintf SplEnd, 2: "| %-3o| %-22o |\n", "D", "Cost per node revealed";
  
  // Ẉe choose to run for N in ALL_DISCS[1..11] for now, but when we have an accurate heuristic, we should instead 
  // compute the optimal set as a subset of ALL_DISCS
  for N in ALL_DISCS[1..11] do
    if split_after_22_flag then
      cost := 14*EndSearcherCost(N);
      cost_N[N] := cost;
      nodes := NodesRevealed(2*N);
      node_N[N] := nodes;
    else
    // WARNING: This heuristic is currently not accurate. Should be replaced when we have a better heuristic.
      cost := EndSearcherCost(N);
      cost_N[N] := cost;
      nodes := HeuristicNodesRevealed(N);
      node_N[N] := nodes;
    end if;
    cost_per_node := cost/nodes;
    if cost_per_node le av_cost_step/nodes2 then 
      Include(~list_N, N);
    end if;
    disp_cost_per_node := RealField(Floor(Log(10, cost_per_node)) + 3)!(cost_per_node);
    vprintf SplEnd, 2: "| %-3o| %-22o |\n", N, disp_cost_per_node;
  end for;
  vprint SplEnd, 2: "Table: For p, the per-node cost of checking\n    for RM D is given as above.\n\n";

  N_subsets := Subsets(list_N);
  Exclude(~N_subsets, {});
  for S in N_subsets do 
    maxk := Ceiling(Log(2, Max(S)));
    sqrs := {N : N in S | IsSquare(N)};
    sqrts := {};
    for D in sqrs do
      _, N := IsSquare(D);
      Include(~sqrts, N);
    end for;
    if exists{N : N in sqrts | #(sqrts meet {N*2^k : k in [1..maxk]}) ge 1} then 
      Exclude(~N_subsets, S);
    end if;
  end for; 

  calN := [];
  optimal_cost := av_cost_step/nodes2;

  costs := [ [[], [av_cost_step/nodes2]] ];

  if split_after_22_flag then
    // cost of computing alpha(C) for all neighbours 
    _, c_Ig := IsogenousInvariantsFromWeierstrass([Random(Fp2) : i in [0..5]], 0);  
  else
    // cost of computing alpha(C), we could also use 291 + 2log_2(p)
    _, c_Ig := InvariantsFromWeierstrassPoints([Random(Fp2) : i in [0..5]], 0);  
  end if; 

  for S in N_subsets do 
    assert #S ne 0;
    cost := av_cost_step + c_Ig + &+[cost_N[N] : N in S];

    if exists{N : N in S | N mod 2 eq 0} or split_after_22_flag then 
      nodes := &+[node_N[N] : N in S];
    else
      nodes := 1 + &+[node_N[N] : N in S]; 
    end if;
    cost_per_node := cost/nodes;
    Append(~costs, [[s : s in S], [cost_per_node]]);
  end for;

  // Sort the list of costs by the second entry (cost_per_node)
  costs_sorted := SortListofListsbySecondEntry(costs);

  vprintf SplEnd, 2: "| %-30o| %-22o |\n", "\\mathcal{D}", "Cost per node revealed";
  for i in [1..Min(5, #costs_sorted)] do
    Nset := [{N : N in t[1]} : t in costs_sorted[1..Min(5, #costs_sorted)]][i];
    cost_Nset := [RealField(4)!(t[2][1]) : t in costs_sorted[1..Min(5, #costs_sorted)]][i];
    disp_cost_Nset := RealField(Floor(Log(10, cost_Nset)) + 3)!(cost_Nset);
    vprintf SplEnd, 2: "| %-30o| %-22o |\n", Nset, disp_cost_Nset;
  end for;
  vprint SplEnd, 2: "Table: The 5 most efficient sets \\mathcal{D} \n  and their cost per node revealed.\n\n"; 

  calN := costs_sorted[1][1];
  calN := [Integers()!N : N in calN];
  return calN;
end function;


intrinsic EndSearcherPrecomp(
            p::RngIntElt,
            Fp2::FldFin,
            constants::SeqEnum :
            calD:=[],
            endsearcher_flag:=true,
            end_after_22_flag:=true
  )
          ->  SeqEnum, SeqEnum[Assoc]
{EndSearcherPrecomp: performs the precomputation for EndSearcher using the functions above
INPUT: Underlying prime p and the Tonelli--Shanks constants needed to take a (2,2)-step  
OUTPUT: 
(1) Set of Ns calN for which the detection will performed, 
(2) list of normalised invariants INVARIANTS given by Elkies--Kumar's map for these N,
(3) list of pairs [\tilde P_(1,2), \tilde P_(2,3)] RESULTANTS for these N < 94, 
(4) list of polynomials DIV_INFO (the polynomials Q_(i,j) of Proposition 3, reduced mod p) 
     to divide the resultants by when doing the RESULTANT+GCD method for N < 122, 
(5) list of monomials MONS_RES in RESULTANTS for these N < 94.
}
  PP<r,s> := PolynomialRing(Fp2, 2);
  _<i1,i2,i3> := PolynomialRing(Fp2, 3);
  _<rr,ss> := PolynomialRing(Parent(i1), 2);

  INVARIANTS := AssociativeArray();
  RESULTANTS := AssociativeArray();
  IMAGES := AssociativeArray();
  DIV_INFO := AssociativeArray();
  MONS_RES := AssociativeArray();

  if endsearcher_flag then 
    // COMPUTE THE COST OF A STEP IN THE (2,2)-GRAPH \Gamma_2(2;p): 
    av_cost_step := CostOfStep(p, Fp2, constants);

    if #calD eq 0 then
      calN := ComputeNs(av_cost_step, end_after_22_flag, Fp2);
    else
      calN := calD;
    end if;
      
    Sprintf("From the above we conclude the optimal set \\mathcal{N} is %o", {N : N in calN});

    for N in calN do
      INVARIANTS[N] := [<Evaluate(polys[1], [r,s]), Evaluate(polys[2], [r,s])> : polys in GetNormalisedIg(N)];
      DIV_INFO[N] := eval Read("endsearcher/divinfo/" cat Sprint(N) cat ".m");
      RESULTANTS[N] := [Evaluate(poly, [rr,ss,i1,i2,i3]) : poly in GetPrecompRes(N)];
      MONS_RES[N] := MonomialsFromCoefficients(RESULTANTS[N]);
    end for;    
  else
    // THIS IS THE NON-ENDSEARCHER VERSION, NEED THIS INFO ONLY FOR POST-COMPUTATION
    INVARIANTS[4] := [<Evaluate(polys[1], [r,s]), Evaluate(polys[2], [r,s])> : polys in GetNormalisedIg(4)];
    RESULTANTS[4] := [Evaluate(poly, [rr,ss,i1,i2,i3]) : poly in GetPrecompRes(4)];
    MONS_RES[4] := MonomialsFromCoefficients(RESULTANTS[4]);
    calN := []; IMAGES := AssociativeArray(); DIV_INFO := AssociativeArray();
  end if;


  // To verify Table 2 and 4 //
  
  // for N in calN do
  //   mons := {m : m in MONS_RES[N]};
  //   "N: " cat IntegerToString(N);
  //   d1 := Maximum({Degree(m, 1) : m in mons});
  //   d2 := Maximum({Degree(m, 2) : m in mons});
  //   d3 := Maximum({Degree(m, 3) : m in mons});
  //   "d1: " cat IntegerToString(d1);
  //   "d2: " cat IntegerToString(d2);
  //   "d3: " cat IntegerToString(d3);
  //   "m: " cat IntegerToString(#mons);
  //   MM := &cat[Monomials(c) : c in Coefficients(RESULTANTS[N][1]) cat Coefficients(RESULTANTS[N][2])]; 
  //   "M: " cat IntegerToString(#MM);
  //   d_P := Degree(RESULTANTS[N][1]) + Degree(RESULTANTS[N][2]);
  //   "d_P: " cat IntegerToString(d_P);
  //   upp_muls := 3*(d1 + d2 + d3) + 6*#mons + 2*#MM + 3/2*(d_P + 2)*(d_P + 3) - 27;
  //   "muls: " cat Sprint(upp_muls);
  //   "";
  // end for;

  
  // Stores all the monomials present in coefficients of precomputed resultants
  for N in calN do 
    ind := Index(calN,N);
    MONS_RES[N] := [ m : m in MONS_RES[N] | not m in &cat[MONS_RES[j] : j in calN[1..ind-1] ]]; // Removes repeated monomials
  end for;

  return calN, [INVARIANTS, RESULTANTS, IMAGES, DIV_INFO, MONS_RES];
end intrinsic;
