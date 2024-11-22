// ----------------------------------------------------------------------
// This file contains code needed to run splitting detection for some N
// ----------------------------------------------------------------------



///////////////////////////////////////////////////////////////////////////////////////////
//////////////////Functions needed to perform the detection////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////////


function PolyDiv(p,q, mulcount)
    pp<x> := Parent(p);
    if q eq 0 then 
        return "Division by zero";
    end if;
    l := 0;
    r:=p;
    while r ne 0 and Degree(q) le Degree(r) do
        t := LeadingCoefficient(r)/LeadingCoefficient(q);
        m := x^(Degree(r)-Degree(q));
        l +:= t*m; 
        r -:= t*m*q; mulcount +:= Degree(q);
    end while;
    return l, mulcount;
end function;

///////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////

function GenPowers(x,n, mulcount)

    // -----------------------------------------------------------------------------------------------
    // GenPowers: compute powers of an element in \FF_{p^2}
    //
    // INPUT: Element x \in \FF_{p^2}, a positive integer n, and the number of \FF_p multiplications
    //        done so far
    // OUTPUT: List of powers of x up to n, [x, x^2, ..., x^n] and updated number of \FF_p muls.
    // -----------------------------------------------------------------------------------------------

    if n eq 1 then 
        return [1,x], mulcount;
    end if;
    xpowers := [x,x^2]; mulcount +:= 3;
    if n eq 2 then 
        xpowers := Reverse(Append(Reverse(xpowers),1));
        return xpowers, mulcount;
    end if;
    
    if n mod 2 eq 1 then
        for e in [2..(n-1)/2] do
            Append(~xpowers, xpowers[e]*xpowers[e-1]); mulcount +:= 3;
            Append(~xpowers, xpowers[e]^2); mulcount +:= 3;
        end for;
        Append(~xpowers, xpowers[Floor((n+1)/2)]*xpowers[Floor((n-1)/2)]); mulcount +:= 3;
    else
        for e in [2..n/2] do
            Append(~xpowers, xpowers[e]*xpowers[e-1]); mulcount +:= 3;
            Append(~xpowers, xpowers[e]^2); mulcount +:= 3;
        end for;
    end if;
    xpowers := Reverse(Append(Reverse(xpowers),1));
    return xpowers, mulcount;
end function;

///////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////

function FastEvaluate(f, pt, mulcount : ms := [])

    // -----------------------------------------------------------------------------------------------
    // FastEvaluate: Evaluates a multivariate function at a point
    //
    // INPUT: A multivariate function f(x_1, ..., x_n), a point pt = [a_1, ..., a_n] and the number 
    //        of \FF_p multiplications done so far
    // OUTPUT: f evaluated at pt, namely f(a_1, ..., a_n), and updated number of \FF_p muls.
    // -----------------------------------------------------------------------------------------------

    pp := Parent(f);
    r := Rank(pp);
    ms := Monomials(f); // Obtain all monomials in f
    degs := [[Degree(m, pp.i) : i in [1..r]] : m in ms]; // List of lists giving the deg of each variable in the monomials
    
    // For each i, obtain a list of powers [a_i, a_i^2, ..., a_i^(d_i)], where d_i is the minimum needed for a_i to evaluate the monomials
    ListPowers:=[];
    for i in [1..r] do 
        p, mulcount := GenPowers(pt[i], Degree(f, pp.i), mulcount);
        Append(~ListPowers, p);
    end for;

    // Evaluate each monomial at pt = [a_1, ..., a_n]
    ms_eval := [ &*[ListPowers[i][d[i]+1] : i in [1..r]] : d in degs ]; mulcount +:= 3*r*#ms; 
    f_eval := &+[MonomialCoefficient(f,ms[i])*ms_eval[i] : i in [1..#ms_eval]]; mulcount +:= 3*#ms_eval;
    return f_eval, mulcount;
end function;

///////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////

function FastPolyGCD(g,h, mulcount)

    // -----------------------------------------------------------------------------------------------
    // FastPolyGCD: computes the gcd of two polynomials with no inversions. 
    //
    // INPUT: Polynomials g, h and the number of \FF_p multiplications done so far
    // OUTPUT: The greatest common divisor gcd(g,h), and updated number of \FF_p muls. 
    // -----------------------------------------------------------------------------------------------

    _<x> := Parent(g);
    r:=Coefficients(g); s:=Coefficients(h);

    if #r lt #s then 
        temp := r; r := s; s := temp;
    end if;

    lcr := r[#r]; lcs := s[#s];
    r:=[lcs*x : x in r]; s:=[lcr*x : x in s];               mulcount +:= 3*(#r+#s);

    while #r gt 2 and r ne s do
        degDiff := #r-#s;
        for i in [1..#s] do                         
            r[i+degDiff] := r[i+degDiff]-s[i];             
        end for;
        while r[#r] eq 0 do
            r := r[1..#r-1];
        end while;
        lcr := r[#r]; lcs := s[#s];
        r := [lcs*x : x in r]; s:= [lcr*x : x in s];        mulcount +:= 3*(#r+#s);
        if #r lt #s then 
            temp := r; r := s; s := temp;
        end if;
    end while;

    if (#r eq 2) and (r ne s) then
        return false, r[1],  mulcount;
    else 
        ply_gcd := &+[x^(i-1)*r[i] : i in [1..#r]];     
        return true, ply_gcd, mulcount;
    end if;
end function;

///////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////

function EvalMons(mons, pt, eval_mons, mulcount)

    // -----------------------------------------------------------------------------------------------
    // EvalMon: evaluates a list of monomials at a point 
    //
    // INPUT: List of monomials mons, a point pt = [a_1, ..., a_n], an associative array eval_mons 
    // containing monomials already evaluated at pt, the number of \FF_p multiplications done so far
    // OUTPUT: Updated array eval_mons containing the monomials in mons evaluated at pt, and updated 
    // number of \FF_p muls. 
    // -----------------------------------------------------------------------------------------------

    pp := Parent(mons[1]);
    r := Rank(pp);

    // For each i, compute powers a_i, a_i^2, ..., a_i^(d_i) where d_i is the minimum needed for a_i to evaluate the monomials in mons
    max_degs := [Maximum([Degree(m, pp.i)  : m in mons]) : i in [1..r]];
    powers:=[];
    for i in [1..r] do
        p, mulcount := GenPowers(pt[i], max_degs[i], mulcount);
        Append(~powers, p);
    end for;

    // Evaluate the monomials in mons at pt = [a_1, ..., a_n]
    for m in mons do
        degs := [Degree(m, pp.i) : i in [1..r]];
        ev_m := &*[powers[i][degs[i]+1] : i in [1..r]]; mulcount +:= 3*(r-1);
        eval_mons[degs]:= ev_m;
    end for;
    return eval_mons, mulcount;
end function;

///////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////


function EvalCoeffs(coeff, pt, eval_mons, mulcount)

    // -----------------------------------------------------------------------------------------------
    // EvalCoeffs: evaluates coefficient at a point
    //
    // INPUT: Coefficient coeff, a point pt = [a_1, ..., a_n], an associative array eval_mons 
    // containing monomials already evaluated at pt, the number of \FF_p multiplications done so far.
    // The coefficient coeff is composed of monomials that are evaluated at pt in eval_mons
    // OUTPUT: Coefficient evaluate at a point ev_coeff and updated number of \FF_p muls. 
    // -----------------------------------------------------------------------------------------------

    cc,mm := CoefficientsAndMonomials(coeff);
    pp := Parent(mm[1]);

    ev_coeff := 0;
    for i in [1..#cc] do
        d := [Degree(mm[i], pp.k) : k in [1..3]];
        ev_coeff +:= cc[i]*eval_mons[d];                mulcount +:= 2; // F_p * F_{p^2}
    end for;

    return ev_coeff, mulcount;
end function;

///////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////

function getfs(alphas, invs, mulcount)
    
    // -----------------------------------------------------------------------------------------------
    // getfs: Outputs the f_i defined before Proposition 2
    //
    // INPUT: List of noramlised Igusa-Clebsh invariants alphas, list of normalised 
    //        invariants invs given by Kumar's map, and the Fp multiplication count.
    // OUTPUT: The polynomials f1, f2, f3 and an updated Fp multiplication count
    // -----------------------------------------------------------------------------------------------

    PP<r,s> := PolynomialRing(Fp2, 2);
    f1 := invs[1][1] - alphas[1]*invs[1][2];   mulcount +:= 3*#Monomials(invs[1][2]);
    f2 := invs[2][1] - alphas[2]*invs[2][2];   mulcount +:= 3*#Monomials(invs[2][2]);
    f3 := invs[3][1] - alphas[3]*invs[3][2];   mulcount +:= 3*#Monomials(invs[3][2]);
    return f1,f2,f3, mulcount;
end function;

///////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////

function IsSplit_Eval_Res_GCD(alphas, invs, div_info, mulcount);
     
    // -----------------------------------------------------------------------------------------------
    // IsSplit_Eval_Res_GCD: Performs the RESULTANT+GCD method to determine whether the Jacobian is 
    //                       (N,N)-split and returns the pair [r,s] if so.
    //
    // INPUT: List of noramlised Igusa-Clebsh invariants alphas, Integer N, list of normalised 
    //        invariants invs given by Kumar's map, list of polynomials div_info to divide the resultants 
    //        by, and Fp multiplication count
    // OUTPUT: Boolean saying whether Jacobian is (N,N)-split, [r,s] if split and [] otherwise, and 
    //         the updated Fp multiplication count
    // -----------------------------------------------------------------------------------------------

    f,g,h, mulcount := getfs(alphas, invs, mulcount);


    r12 := Resultant(f, g, 1); mulcount +:= (Degree(g, 1)+Degree(f,1))^3; // Upper Bound: Determinant via LU decomp
    r23 := Resultant(g, h, 1); mulcount +:= (Degree(g, 1)+Degree(h,1))^3; // Upper Bound: Determinant via LU decomp
    
    // Divide resultants by polynomials, as discussed in Lemma 3
    _<x> := PolynomialRing(Fp2);
    r12, mulcount := PolyDiv(Evaluate(r12, [0,x]), Evaluate(div_info[1], [0,x]), mulcount); 
    r23, mulcount := PolyDiv(Evaluate(r23, [0,x]), Evaluate(div_info[2], [0,x]), mulcount);

    bool, ply_gcd, mulcount := FastPolyGCD(r12, r23, mulcount);
    if not bool then    
        return bool, [], mulcount;
    else
        ////// THIS IS NOW A POSTCOMPUTATION WE DON'T COUNT MULS //////
        my_s:=Roots(Evaluate(ply_gcd, x))[1][1];
        possible_r := [my_r[1] : my_r in Roots(Evaluate(invs[1][1] - alphas[1]*invs[1][2], [x,my_s]))];
        assert exists(my_r){my_r : my_r in  possible_r | Evaluate(invs[2][1]/invs[2][2], [my_r, my_s]) eq alphas[2]};
        return bool, [my_r, my_s], mulcount; 
    end if;
end function;

///////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////


function IsSplit_Eval_GCD(alphas, invs, resultants, mon_res, eval_mons, mulcount)
    
    // -----------------------------------------------------------------------------------------------
    // IsSplit_Eval_GCD: Performs the EVALUATE+GCD method to determine whether the Jacobian is 
    //                   (N,N)-split and returns the pair [r,s] if so.
    //                   Corresponds to Algorithm 3 with the post-computation to get [r,s] included
    //
    // INPUT: List of normalised Igusa-Clebsh invariants alphas, Integer N <10, list of normalised 
    //        invariants invs given by Kumar's map, list of precomputed resultants, list of monomials in 
    //        resultants mon_res, list of monomials eval_mons that have alread been evaluated at alphas, 
    //        and Fp multiplication count
    // OUTPUT: Boolean saying whether Jacobian is (N,N)-split, [r,s] if split and [] otherwise, 
    //         evaluated monomials, and the updated Fp multiplication count
    // -----------------------------------------------------------------------------------------------

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
        ////// THIS IS NOW A POSTCOMPUTATION WE DON'T COUNT MULS //////
        my_s := Roots(Evaluate(ply_gcd,x))[1][1];
        possible_r := [my_r[1] : my_r in Roots(Evaluate(invs[1][1] - alphas[1]*invs[1][2], [x,my_s]))];
        assert exists(my_r){my_r : my_r in  possible_r | Evaluate(invs[2][1]/invs[2][2], [my_r, my_s]) eq alphas[2]};
        return bool, [my_r, my_s], [], mulcount; 
    end if;
end function;

///////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////

function IsSplit_Image(alphas, invs, image, div_info, mulcount)
        
    // -----------------------------------------------------------------------------------------------
    // IsSplit_Image: Performs the IMAGE method to determine whether the Jacobian is 
    //                (N,N)-split and returns the pair [r,s] if so. 
    //
    // INPUT: List of normalised Igusa-Clebsh invariants alphas, Integer N < 5, image of Kumar's
    //        maps \varphi_N, and Fp multiplication count. We also load in the list of normalised 
    //        invariants invs given by Kumar's map and the list of polynomials div_info to divide 
    //        the resultants by to run IsSplit_Eval_Res_GCD if true (to obtain the r,s).
    // OUTPUT: Boolean saying whether Jacobian is (N,N)-split, [r,s] if split and [] otherwise, and 
    //         the updated Fp multiplication count
    // -----------------------------------------------------------------------------------------------
   
    ev := Evaluate(image, alphas); 
    //upper bound as we don't implement Evaluate in this case    
    mulcount +:= 8*#Monomials(image) + 3*(Degree(image, 1) + Degree(image, 2) + Degree(image, 3)); 

    if ev eq 0 then
        // If true we run Split_Eval_Res_GCD to obtain the r,s. We consider this a post-computation so don't
        // count multiplcations of this step
        _, rs, _, _ := IsSplit_Eval_Res_GCD(alphas, invs, div_info, 0);
        return true, rs, mulcount;
    else
        return false, [], mulcount;
    end if;
end function;

///////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////

function SANITYCHECK(alphas, N, rs)
        
    // ------------------------------------------------------------------------------------------------------
    // SANITYCHECK: Check to ensure that we have indeed found a splitting at N
    //
    // INPUT: NNormalised (using normalisation in Lemma 2) Igusa--Clebsch invariants alphas, N for which we 
    //        detect the splitting and the corresponding (r,s) we compute.
    // OUTPUT: A boolean saying whether the check passes
    // ------------------------------------------------------------------------------------------------------

    // Takes input a computed (r,s) pair. Uses this and Kumar's equations for
    // L_N to compute the invariants and checks they're equal to ours.
    _<r,s> := PolynomialRing(Fp2, 2);
    kumar_invs := eval Read("splitsearcher/kumarinvs/" cat Sprint(N) cat ".m");
    our_kumar_invs := [Evaluate(k_inv, rs) : k_inv in kumar_invs];
    I2,I4,I6,I10 := Explode(our_kumar_invs);
    return alphas eq [I4/I2^2, I2*I4/I6, I4*I6/I10];
end function;

///////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////

function IsSplitMethod(alphas, invs, resultants, image, div_info, mon_res, eval_mons, mulcount : method:= "eval")
        
    // -----------------------------------------------------------------------------------------------------
    // IsSplit:  Determines whether the Jacobian is (N,N)-split and returns the pair [r,s] if so.
    //           By default we use the EVALUATE+GCD method, but this can be changed.
    // INPUT: Normalised (using normalisation in Lemma 2) Igusa--Clebsch invariants alphas, 
    //        invariants given by Kumar's map for some N, precomputed resultants for this N (if using
    //        method = eval), image of Kumar's map for this N (if using method = image), polynomials to 
    //        divide resultants by (Lemma 3), div_info, for this N (if using method = res),
    //        list of monomials mon_res in the precomputed resultants for this N (if using method = eval), 
    //        and Fp multiplication count
    // OUTPUT: Boolean saying whether Jacobian is (N,N)-split, [r,s] if split and [] otherwise, evaluated 
    //         monomials (if method = eval), and the updated Fp multiplication count
    // ----------------------------------------------------------------------------------------------------

    if method eq "res" then
        return IsSplit_Eval_Res_GCD(alphas, invs, div_info, mulcount);
    
    elif method eq "eval" then
        return IsSplit_Eval_GCD(alphas, invs, resultants, mon_res, eval_mons, mulcount);

    elif method eq "image" then
        return IsSplit_Image(alphas, invs, image, div_info, mulcount);
    end if;
end function;

//////////////////////////////////////////////////////////////////////////////////////////
/////////////////////////////DETECTION FOR SET OF OPTIMAL Ns//////////////////////////////
//////////////////////////////////////////////////////////////////////////////////////////

function IsSplit(alphas, calN, INVARIANTS, RESULTANTS, IMAGES, DIV_INFO, MONS_RES, mulcount : just_checking:=true)
        
    // ---------------------------------------------------------------------------------------------------------
    // SplitSearcher: Peforms SplitSearcher for the set of optimal N's using methods discussed in Section 5-6
    // 
    // This can be done using three methods:
    //      - RESULTANT+GCD: computing resultants and then gcd (method = "res")
    //      - EVALUATE+GCD: evaluating precomputed resultants and then compute gcd (method = "eval")
    //      - IMAGE: evaluate images (method = "image")
    //
    // INPUT: Normalised (using normalisation in Lemma 2) Igusa--Clebsch invariants alphas, invariants given by Kumar's map
    //        INVARIANTS for these N, precomputed resultants RESULTANTS for these N <10, images of 
    //        Kumar's map IMAGES for these N < 5, polynomials to divide resultants by (Lemma 3) DIV_INFO,
    //        list of monomials MONS_RES in the precomputed resultants for these N < 10, and Fp multiplication
    //        count
    // OUTPUT: Boolean, given by flag, saying whether the Jacobian is (N,N)-split for some N in calN,
    //         if split then the N such that Jacobian is (N,N)-split and -1 otherwise, if split the 
    //         corresponding [r,s] and [] otherwise, and the updated Fp multiplication count 
    // --------------------------------------------------------------------------------------------------------


    eval_mons:=AssociativeArray();

    for N in calN do
    
        flag := false;
        invs := INVARIANTS[N];
        // image := IMAGES[N]; //Uncomment if using the IMAGE method
        
        if N in [10, 11] then 
            // For N = 10,11 we use the RESULTANT+GCD method
            
            // check none of alpha are zero
            if exists{alpha : alpha in alphas | alpha eq 0} then 
                "You should never get here, one of your alphas is zero.";
                assert false;
            end if;

            div_info := DIV_INFO[N];
            flag, rs, mulcount := IsSplitMethod(alphas, invs, [], [], div_info, [], eval_mons, mulcount : method:= "res");
        else
            // For other N, we use the EVALUATE+GCD method

            // check none of alpha are zero
            if exists{alpha : alpha in alphas | alpha eq 0} then 
                "You should never get here, one of your alphas is zero.";
                assert false;
            end if;

            resultants := RESULTANTS[N];
            mon_res := MONS_RES[N];
            MUL := mulcount;
            flag, rs, eval_mons, mulcount := IsSplitMethod(alphas, invs, resultants, [], [], mon_res, eval_mons, mulcount : method:= "eval");
        end if;

        if flag then
            sanity := SANITYCHECK(alphas, N, rs);
            assert sanity;

            if just_checking then 
                Sprintf("    We found a splitting where N=%o (with SplitSearcher)", N);
            end if;
            
            Sprintf("    SANITY CHECK: We solved for (r,s) and after substituting \n        back in it is %o that the invariants are the same.\n", sanity);

            return flag, N, rs, mulcount;
        end if;
    end for;

    return flag, -1, [], mulcount;
end function;


 
/*

///////////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////DETECTION FOR ONE N/////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////////


// We do not use this for our applications but will be useful if you are 
// wishing to run detection for only one N


load "precomp.m";
//load "../invs.m"; // Uncomment if you are running this by itself to obtain the 
                     // InvariantsFromWeierstrassPoints function

function GetInfo(N)

    invs := [<Evaluate(polys[1], [r,s]), Evaluate(polys[2], [r,s])> : polys in ig(N)];
    div_info := eval Read("splitsearcher/divinfo/" cat Sprint(N) cat ".m");
    if N in [2..4] then 
        image := Evaluate(ImagePoly(N), [i1,i2,i3]);
        resultants := [Evaluate(poly, [rr,ss,i1,i2,i3]) : poly in GetPrecompRes(N)];
        mon_res := MonomialsFromCoefficients(resultants);
    elif N in [5..9] then 
        resultants := [Evaluate(poly, [rr,ss,i1,i2,i3]) : poly in GetPrecompRes(N)];
        mon_res := MonomialsFromCoefficients(resultants);
    end if;

    return invs, resultants, image, div_info, mon_res;
end function;


///////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////


function IsSplitForN(as, N)
        
    // -------------------------------------------------------------------------------------------------------------
    // IsSplitForN: Allows to perform the detection for a specific N
    // 
    // This can be done using three methods:
    //      - RESULTANT+GCD: computing resultants and then gcd (method = "res")
    //      - EVALUATE+GCD: evaluating precomputed resultants and then compute gcd (method = "eval")
    //      - IMAGE: evaluate images (method = "image")
    //
    // INPUT: Weierstrass Points, as, of the curve, and the N that you want to perform the detection for
    // OUTPUT: Boolean, given by flag, saying whether the Jacobian is (N,N)-split for this N, if split the 
    //         corresponding [r,s] and [] otherwise, and the Fp multiplication count for performing this detection
    // ------------------------------------------------------------------------------------------------------------

    mulcount := 0;
    // Compute the Igusa--Clebsch invariants form the Weierstrass points
    alphas,mulcount := InvariantsFromWeierstrassPoints(as,mulcount);


    // Compute info needed to perform the splitting
    invs, resultants, image, div_info, mon_res := GetInfo(N);
    eval_mons:=AssociativeArray();

    if N in [10, 11] then 
            // For N = 10,11 we use the RESULTANT+GCD method
            time flag, rs, mulcount := IsSplitMethod(alphas, invs, [], [], div_info, [], eval_mons, mulcount : method:= "res");
        else
            // For other N, we use the EVALUATE+GCD method
            flag, rs, eval_mons, mulcount := IsSplitMethod(alphas, invs, resultants, [], [], mon_res, eval_mons, mulcount : method:= "eval");
        end if;

        if flag then
            sanity := SANITYCHECK(alphas, N, rs);
            assert sanity;
            Sprintf("We found a splitting where N=%o", N);
            Sprintf("SANITY CHECK: It is %o that the invariants are the same.\n", sanity);
            return flag, rs, mulcount;
        end if;
    return flag, [], mulcount;
end function;

*/