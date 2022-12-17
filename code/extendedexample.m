// -------------------------------------------------------------------------------------------------
// This file contains code needed to run the attack on the general isogeny problem in two dimension
// By changing splitsearcher_flag, you can run the attack with and without the splitting detection
// By changing split_after_22_flag, you can run the attack using improvement 5 listed in Section 7
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

p:=2^17 - 1; // THIS SHOULD BE 5 or 7 mod 8 (as we generate examples using a specific starting curve)
number_instances:=50;
splitsearcher_flag:=true; // Flag decides whether or not splitsearcher is run
split_after_22_flag:=false; // Flag decides whether or not we run improvement 5 in section 7

file:="p" cat IntegerToString(Ceiling(Log(2,p))) cat ".txt";

///////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////
Write(file, Sprintf("The prime we are working with is %o bits.\n", Ceiling(Log(2,p))));

Fp,Fp2,constants := GetTonelliShanksConstants(p);
instances := GetSupersingularWeierstrassPoints(number_instances,50,Fp2);
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

///////////////////////////
// Print what's going on 
if split_after_22_flag then 
    spl_after_22_str := ""; 
else 
    spl_after_22_str := "not "; 
end if;
str := Sprintf("We are %ousing improvement 5 in Section 7.", spl_after_22_str);
str; Write(file, str);
str := Sprintf("The set \\mathcal{N} is %o\n", {N : N in calN});
str; Write(file, str);
//////////////////////////

total_steps:=0;
total_muls:=0;
total_time:=0;


for weier_pts in instances do 
    
    Sprintf("THIS INSTANCE=%o", Index(instances,weier_pts));

    t0:=Cputime();

    starting_points,solution,N,rs,steps,mulcount:=SplitSearcher(weier_pts, constants, splitsearcher_flag, split_after_22_flag, calN, INVARIANTS, RESULTANTS, IMAGES, DIV_INFO, MONS_RES); 
    t1:=Cputime(t0);

    // Find the j-invariants of the elliptic curves in the product E_1 x E_2 which the starting Jacobian is 
    // isogenous to 
    j1,j2:=Genus1Curves(rs[1],rs[2],N);

    Sprintf("    The j-invariants of the elliptic curves in the product is\n    (%o, %o).\n", j1, j2);

    total_steps+:=steps;
    total_muls+:=mulcount;
    total_time+:=t1;

end for;

number_instances_splitsearcher:=number_instances;
av_steps_splitsearcher:=Ceiling(total_steps/number_instances);
av_muls_splitsearcher:=Ceiling(total_muls/number_instances);
av_time_splitsearcher:= total_time/number_instances;

calN_splitsearcher := calN;

///////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////

// FOR COMPARISON WE DO THE USUAL ATTACK WITHOUT DETECTION OF SPLITTINGS //

"\n--------------------------------------------------------------
RUNNING COSTELLO--SMITH IN THE (2,2)-GRAPH
--------------------------------------------------------------\n";
splitsearcher_flag:=false; // Flag decides whether or not splitsearcher is run
split_after_22_flag:=false; // Flag decides whether or not we run improvement 5 in section 7

calN, INVARIANTS, RESULTANTS, IMAGES, DIV_INFO, MONS_RES:=SplitSearcherPrecomp(p, splitsearcher_flag, split_after_22_flag, constants);


total_steps:=0;
total_muls:=0;
total_time:=0;

for weier_pts in instances do 
    
    Sprintf("THIS INSTANCE=%o", Index(instances,weier_pts));

    t0:=Cputime();
    
    starting_points,solution,N,rs,steps,mulcount:=SplitSearcher(weier_pts, constants, splitsearcher_flag, split_after_22_flag, calN, INVARIANTS, RESULTANTS, IMAGES, DIV_INFO, MONS_RES); 
    
    // Find the j-invariants of the elliptic curves in the product E_1 x E_2 which the starting Jacobian is 
    // isogenous to 
    j1,j2:=Genus1Curves(rs[1],rs[2],2);

    Sprintf("    The j-invariants of the elliptic curves in the product is\n    (%o, %o).\n", j1, j2);

    t1:=Cputime(t0);

    total_steps+:=steps;
    total_muls+:=mulcount;
    total_time+:=t1;

end for;

av_steps:=Ceiling(total_steps/number_instances);
av_muls:=Ceiling(total_muls/number_instances);
av_time:= total_time/number_instances;

///////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////

// DISPLAY A TABLE //
info_str := 
"\n--------------------------------------------------------------
A COMPARISON OF SPLITSEARCHER VERSUS COSTELLO--SMITH
--------------------------------------------------------------\n";

info_str;
Write(file, info_str);

table_str := 
Sprintf("| %-30o| %-20o | %-20o |\n", "", "Costello--Smith", "SplitSearcher") cat 
Sprintf("| %-30o| %-20o | %-20o |\n", "Number of instances solved", number_instances, number_instances_splitsearcher) cat
Sprintf("| %-30o| %-20o | %-20o |\n", "Avg number of steps", av_steps, av_steps_splitsearcher) cat
Sprintf("| %-30o| %-20o | %-20o |\n", "Avg number of nodes checked", av_steps, StepsToNodes(av_steps_splitsearcher, calN)) cat 
Sprintf("| %-30o| %-20o | %-20o |\n", "Avg number of F_p muls", av_muls, av_muls_splitsearcher) cat
Sprintf("| %-30o| %-20o | %-20o |\n", "Avg time", Sprint(av_time) cat " seconds", Sprint(av_time_splitsearcher) cat " seconds") cat
Sprintf("\nTable: Performance of the Costello--Smith algorithm running in the\n    (2,2)-graph, versus the same algorithm augmented with \n    SplitSearcher (over the same instances). In this case our prime\n    was %o bits and the set used by SplitSearcher was %o \n    (we were using 5 in Section 7). Note the number of nodes checked\n    is an upper bound for SplitSearcher.\n", Ceiling(Log(2,p)), {N : N in calN_splitsearcher}, spl_after_22_str);

table_str;

Write(file, table_str);