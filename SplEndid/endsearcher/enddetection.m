declare verbose SplEnd, 2;

function getfs(alphas, invs, mulcount) 
  // -----------------------------------------------------------------------------------------------
  // getfs: Outputs the f_i defined before Proposition 2
  //
  // INPUT: List of noramlised Igusa-Clebsh invariants alphas, list of normalised 
  //        invariants invs given by Elkies--Kumar's map, and the Fp multiplication count.
  // OUTPUT: The polynomials f1, f2, f3 and an updated Fp multiplication count
  // -----------------------------------------------------------------------------------------------
  Fp2 := Parent(alphas[1]);
  PP<r,s> := PolynomialRing(Fp2, 2);
  f1 := invs[1][1] - alphas[1]*invs[1][2];   mulcount +:= 3*#Monomials(invs[1][2]);
  f2 := invs[2][1] - alphas[2]*invs[2][2];   mulcount +:= 3*#Monomials(invs[2][2]);
  f3 := invs[3][1] - alphas[3]*invs[3][2];   mulcount +:= 3*#Monomials(invs[3][2]);
  return f1,f2,f3, mulcount;
end function;


function ComputePossibler(invs, alphas, my_s)
  _<x> := PolynomialRing(Parent(my_s));
  ply := Evaluate(invs[1][1] - alphas[1]*invs[1][2], [x,my_s]);
  if ply ne 0 then
    possible_r := [my_r[1] : my_r in Roots(ply)];
    return possible_r;
  else
    ply := Evaluate(invs[2][1] - alphas[2]*invs[2][2], [x,my_s]);
    possible_r := [my_r[1] : my_r in Roots(ply)];
    return possible_r;
  end if;    
end function;


function HasEnd_Eval_Res_GCD(alphas, invs, div_info, mulcount);
  // -----------------------------------------------------------------------------------------------
  // HasEnd_Eval_Res_GCD: Performs the RESULTANT+GCD method to determine whether the Jacobian has 
  //                       RM D and returns the pair [r,s] if so.
  //
  // INPUT: List of noramlised Igusa-Clebsh invariants alphas, list of normalised 
  //        invariants invs given by Elkies--Kumar's map, list of polynomials div_info to divide the resultants 
  //        by, and Fp multiplication count
  // OUTPUT: Boolean saying whether Jacobian has RM D, [r,s] if split and [] otherwise, and 
  //         the updated Fp multiplication count
  // -----------------------------------------------------------------------------------------------
  Fp2 := Parent(alphas[1]);
  
  f,g,h, mulcount := getfs(alphas, invs, mulcount);

  // Upper Bound on muls from determinant via LU decomp
  r12 := Resultant(f, g, 1); mulcount +:= (Degree(g, 1)+Degree(f,1))^3; 
  r23 := Resultant(g, h, 1); mulcount +:= (Degree(g, 1)+Degree(h,1))^3;
  
  // Divide resultants by polynomials, as discussed in Lemma 3
  _<x> := PolynomialRing(Fp2);
  r12, mulcount := PolyDiv(Evaluate(r12, [0,x]), Evaluate(div_info[1], [0,x]), mulcount); 
  r23, mulcount := PolyDiv(Evaluate(r23, [0,x]), Evaluate(div_info[2], [0,x]), mulcount);

  bool, ply_gcd, mulcount := FastPolyGCD(r12, r23, mulcount);
  if not bool then    
    return bool, [], mulcount;
  else
    ///////////////////////////////////////////////////////////////
    ////// THIS IS NOW A POSTCOMPUTATION WE DON'T COUNT MULS //////
    ///////////////////////////////////////////////////////////////
    my_s:=Roots(Evaluate(ply_gcd, x))[1][1];
    possible_r := ComputePossibler(invs, alphas, my_s);
    assert exists(my_r){my_r : my_r in  possible_r | Evaluate(invs[2][1]/invs[2][2], [my_r, my_s]) eq alphas[2]};
    return bool, [my_r, my_s], mulcount; 
  end if;
end function;


function HasEnd_Eval_GCD(alphas, invs, resultants, mon_res, eval_mons, mulcount)
  
  // -----------------------------------------------------------------------------------------------
  // HasEnd_Eval_GCD: Performs the EVALUATE+GCD method to determine whether the Jacobian has RM D
  //                   and returns the pair [r,s] if so.
  //                   Corresponds to a generalised Algorithm 3 with the post-computation to get 
  //                   [r,s] included
  //
  // INPUT: List of normalised Igusa-Clebsh invariants alphas, list of normalised invariants invs 
  //        given by Elkies--Kumar's map, list of precomputed resultants, list of monomials in
  //        resultants mon_res, list of monomials eval_mons that have alread been evaluated at alphas,
  //        and Fp multiplication count
  // OUTPUT: Boolean saying whether Jacobian has RM S, [r,s] if split and [] otherwise,
  //         evaluated monomials, and the updated Fp multiplication count
  // -----------------------------------------------------------------------------------------------
  Fp2 := Parent(alphas[1]);
  
  r12, r23 := Explode(resultants);
  if #mon_res ne 0 then
    // This gets evaluated monomials appearing in the coeffs
    eval_mons, mulcount := EvalMons(mon_res, alphas, eval_mons, mulcount);
  end if;

  // Now construct the ~R_{ij}(C)
  c12, m12 := CoefficientsAndMonomials(r12);
  ev_c12 := [];
  for c in c12 do
    ev_c, mulcount := EvalCoeffs(c,alphas,eval_mons,mulcount);
    Append(~ev_c12,ev_c);
  end for;
  r12 := &+[ev_c12[i]*m12[i] : i in [1..#m12]]; // Reconstruct the polynomial, takes no multiplications

  c23, m23 := CoefficientsAndMonomials(r23);
  ev_c23 := [];
  for c in c23 do
    ev_c, mulcount := EvalCoeffs(c,alphas,eval_mons,mulcount);
    Append(~ev_c23,ev_c);
  end for;
  r23 := &+[ev_c23[i]*m23[i] : i in [1..#m23]]; // Reconstruct the polynomial, takes no multiplications

  // Coerce into the correct ring
  _<x> := PolynomialRing(Fp2);
  r12 := Evaluate(r12, [0,x]);
  r23 := Evaluate(r23, [0,x]);

  // Compute the GCD
  bool, ply_gcd, mulcount := FastPolyGCD(r12, r23, mulcount);

  if not bool then
    return bool, [], eval_mons, mulcount;
  else
    ///////////////////////////////////////////////////////////////
    ////// THIS IS NOW A POSTCOMPUTATION WE DON'T COUNT MULS //////
    ///////////////////////////////////////////////////////////////
    my_s := Roots(Evaluate(ply_gcd,x))[1][1];
    possible_r := ComputePossibler(invs, alphas, my_s);
    assert exists(my_r){my_r : my_r in  possible_r | Evaluate(invs[2][1]/invs[2][2], [my_r, my_s]) eq alphas[2]};
    return bool, [my_r, my_s], [], mulcount;
  end if;
end function;

function SANITYCHECK(alphas, D, rs)
  // SANITYCHECK: Check to ensure that we have indeed found an RM for D
  //
  // INPUT: Normalised (using normalisation in Lemma 2) Igusa--Clebsch invariants alphas, D for which we 
  //        detect the RM and the corresponding (r,s) we compute.
  // OUTPUT: A boolean saying whether the check passes

  ek_invs := GetIg(D);
  our_ek_invs := [Evaluate(ek_inv, rs) : ek_inv in ek_invs];
  I2,I4,I6,I10 := Explode(our_ek_invs);
  return alphas eq [I4/I2^2, I2*I4/I6, I4*I6/I10];
end function;


function HasEndMethod(alphas, invs, resultants, image, div_info, mon_res, eval_mons, mulcount : method:= "eval")
  // HasEnd:  Determines whether the Jacobian has RM D and returns the pair [r,s] if so.
  //         By default we use the EVALUATE+GCD method, but this can be changed.
  // INPUT: Normalised (using normalisation in Lemma 2) Igusa--Clebsch invariants alphas, 
  //        invariants given by Elkies--Kumar's map for some D, precomputed resultants for this D (if using
  //        method = eval), polynomials to divide resultants by (Lemma 3), div_info, for this D (if using method = res),
  //        list of monomials mon_res in the precomputed resultants for this D (if using method = eval), 
  //        and Fp multiplication count
  // OUTPUT: Boolean saying whether Jacobian has RM D, [r,s] if so and [] otherwise, evaluated 
  //         monomials (if method = eval), and the updated Fp multiplication count

  if method eq "res" then
    return HasEnd_Eval_Res_GCD(alphas, invs, div_info, mulcount);
    
  elif method eq "eval" then
    return HasEnd_Eval_GCD(alphas, invs, resultants, mon_res, eval_mons, mulcount);

  end if;
end function;

//////////////////////////////////////////////////////////////////////////////////////////
/////////////////////////////DETECTION FOR SET OF OPTIMAL Ns//////////////////////////////
//////////////////////////////////////////////////////////////////////////////////////////

intrinsic HasEnd(
            alphas::SeqEnum,
            calD::SeqEnum,
            INFO::SeqEnum[Assoc],
            mulcount::RngIntElt
  ) -> BoolElt, RngIntElt, SeqEnum, RngIntElt
{Peforms EndSearcher for a set D's using methods discussed in Section 7
This can be done using three methods:
  - RESULTANT+GCD: computing resultants and then gcd (method = "res")
  - EVALUATE+GCD: evaluating precomputed resultants and then compute gcd (method = "eval")

INPUT: Normalised (using normalisation in Lemma 2) Igusa--Clebsch invariants alphas, invariants 
  given by Eklies--Kumar's map INVARIANTS for these D, precomputed resultants RESULTANTS for 
  these D < 94, polynomials to divide resultants by (Lemma 3) DIV_INFO,
  list of monomials MONS_RES in the precomputed resultants for these D < 94, and Fp multiplication
  count

OUTPUT: Boolean, given by flag, saying whether the Jacobian has RM for some D in calD,
  if so then the D such that Jacobian has RM D and -1 otherwise, and if so the
  corresponding [r,s] and [] otherwise, and the updated Fp multiplication count
}
  INVARIANTS, RESULTANTS, IMAGES, DIV_INFO, MONS_RES := Explode(INFO);
  
  eval_mons:=AssociativeArray();

  require not exists{alpha : alpha in alphas | alpha eq 0}: "Error, one of your alphas is zero?";
  
  for D in calD do
    flag := false;
    invs := INVARIANTS[D];
    
    if D in [97, 100, 121] then 
      // For N = 97, 10^2,11^2 we use the RESULTANT+GCD method
      div_info := DIV_INFO[D];
      flag, rs, mulcount := HasEndMethod(alphas, invs, [], [], div_info, [], eval_mons, mulcount : method:="res");
    else
      // For other N, we use the EVALUATE+GCD method
      resultants := RESULTANTS[D];
      mon_res := MONS_RES[D];
      MUL := mulcount;
      flag, rs, eval_mons, mulcount := HasEndMethod(alphas, invs, resultants, [], [], mon_res, eval_mons, mulcount : method:= "eval");
    end if;

    if flag then
      sanity := SANITYCHECK(alphas, D, rs);
      require sanity: Sprintf("Error, sanity check failed when D=%o", D);

      vprintf SplEnd, 1: "We found an RM where D=%o\n", D;
      vprint SplEnd, 2:  "SANITY CHECK: We solved for (r,s) and after substituting";
      vprintf SplEnd, 2: "  back in it is %o that the invariants are the same.\n", sanity;

      return flag, D, rs, mulcount;
    end if;
  end for;

  return flag, -1, [], mulcount;
end intrinsic;


// intrinsic HasEnd(as::SeqEnum, N::RngIntElt) -> BoolElt, SeqEnum, RngIntElt
// {
// Allows to perform the detection for a specific D
  
// INPUT: Weierstrass Points, as, of the curve, and the N that you want to perform the detection for

// OUTPUT: Boolean, given by flag, saying whether the Jacobian is (N,N)-split for this N, if split the 
//   corresponding [r,s] and [] otherwise, and the Fp multiplication count for performing this detection
// }
//   mulcount := 0;
//   // Compute the Igusa--Clebsch invariants form the Weierstrass points
//   alphas,mulcount := InvariantsFromWeierstrassPoints(as,mulcount);

//   // Compute info needed to perform the splitting
//   invs, resultants, image, div_info, mon_res := GetInfo(N);
//   eval_mons:=AssociativeArray();

//   if N in [100, 121] then 
//     // For N = 10,11 we use the RESULTANT+GCD method
//     time flag, rs, mulcount := HasEndMethod(alphas, invs, [], [], div_info, [], eval_mons, mulcount : method:= "res");
//   else
//     // For other N, we use the EVALUATE+GCD method
//     flag, rs, eval_mons, mulcount := HasEndMethod(alphas, invs, resultants, [], [], mon_res, eval_mons, mulcount : method:= "eval");
//   end if;

//   if flag then
//     sanity := SANITYCHECK(alphas, N, rs);
//     assert sanity;
//     vprintf SplEnd, 1: "We found a splitting where N=%o", N;
//     vprintf SplEnd, 2: "SANITY CHECK: It is %o that the invariants are the same.\n", sanity;
//     return flag, rs, mulcount;
//   end if;
//   return flag, [], mulcount;
// end intrinsic;
