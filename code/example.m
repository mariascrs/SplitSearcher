// -------------------------------------------------------------------------------------------------
// This file contains code needed to run the attack on the general isogeny problem in two dimension
// By changing splitsearcher_flag, you can run the attack with and without the splitting detection
// -------------------------------------------------------------------------------------------------

clear;

"--------------------------------------------------------------
LOADING FILES
--------------------------------------------------------------\n";

load "instantiate/Fp2functions.m";
load "instantiate/instances.m";

///////////////////////////////////////////////////////////////
///////// BELOW IS THE ONLY INPUT THAT NEEDS CHANGING /////////
///////////////////////////////////////////////////////////////

// INPUT PRIME HERE
// Example
p:= 2^17 - 1;

////////////////////////////////
//DON'T CHANGE, MAKING THE FIELD
Fp,Fp2,constants := GetTonelliShanksConstants(p);
Fp2<i> := Fp2;
////////////////////////////////

// INPUT WEIERSTRASS POINTS OF CURVE HERE
// Example
weier_pts := [
    15760*i + 54470,
    42859*i + 90353,
    58953*i + 3159,
    105880*i + 50861,
    120185*i + 19231,
    125491*i + 102080
];

// NAME YOUR OUTPUT FILE
file := "example_solution.txt";


///////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////
// Set up some stuff

splitsearcher_flag:=true; // Flag decides whether or not splitsearcher is run
split_after_22_flag:=true; // Flag decides whether or not we run improvement 5 in section 7

PP<r,s> := PolynomialRing(Fp2, 2);
_<i1,i2,i3> := PolynomialRing(Fp2, 3);
_<rr,ss> := PolynomialRing(Parent(i1), 2);

load "richelotstep/richelot.m";
load "splitsearcher/invs.m";
load "splitsearcher/splitafter22/invsfromquads.m";
load "splitsearcher/splitdetection.m";
load "splitsearcher/splitsearcher.m";
load "splitsearcher/graphcounts.m";
load "splitsearcher/precomp.m";
load "splitsearcher/ecsfromrs.m";

///////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////

"\n--------------------------------------------------------------
SPLITSEARCHER PRECOMPUTATION
--------------------------------------------------------------\n";

calN, INVARIANTS, RESULTANTS, IMAGES, DIV_INFO, MONS_RES:=SplitSearcherPrecomp(p, splitsearcher_flag, split_after_22_flag, constants);


///////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////

// RUN THE ATTACK WITH DETECTION OF SPLITTINGS //
"\n\n--------------------------------------------------------------
RUNNING SPLITSEARCHER IN THE (2,2)-GRAPH
--------------------------------------------------------------\n";
    
t0:=Cputime();

starting_points,solution,N,rs,steps,mulcount:=SplitSearcher(weier_pts, constants, splitsearcher_flag, split_after_22_flag, calN, INVARIANTS, RESULTANTS, IMAGES, DIV_INFO, MONS_RES); 
t1:=Cputime(t0);

// Find the j-invariants of the elliptic curves in the product E_1 x E_2 which the starting Jacobian is 
// isogenous to 
j1,j2:=Genus1Curves(rs[1],rs[2],N);

Sprintf("    The j-invariants of the elliptic curves in the product is\n        (%o, %o).", j1, j2);

Write(file, Sprintf("Total number of steps = %o\n", steps));
Write(file, Sprintf("Total number of F_p multiplications = %o\n", mulcount));
Write(file, Sprintf("Total time taken = %o seconds\n", t1));
Write(file, Sprintf("The j-invariants of the elliptic product is\n(%o, %o)\n\n", j1, j2));

readable_soln := [PermutationFromIndex(k) : k in solution];
readable_soln := Sprintf("%o and a (%o,%o)-isogeny", readable_soln, N, N);
Write(file, Sprintf("The path to a splitting is:\n%o", readable_soln));