// ------------------------------------------------------------------------------------------------------
// This file contains code to run an example of SplEndid and compare it to the Costello--Smith algorithm
// ------------------------------------------------------------------------------------------------------

// BEFORE RUNNING:
//    Change the 'CURR_DIR' variable in endsearcher/getinfo.m to be the correct directory this file 
//     is in.

clear;

"LOADING FILES";
"=============\n";
AttachSpec("spec");
SetVerbose("SplEnd", 1);

///////////////////////////////////////////////////////////////
///////// BELOW IS THE ONLY INPUT THAT NEEDS CHANGING /////////
///////////////////////////////////////////////////////////////

p := 2^17 - 1; // THIS SHOULD BE 5 or 7 mod 8 (as we generate examples using a specific starting curve)
number_instances := 1;
endsearcher_flag := true; // Flag decides whether or not splitsearcher is run
end_after_22_flag := false; // Flag decides whether or not we run improvement 5 in section 7

file:="p" cat IntegerToString(Ceiling(Log(2,p))) cat ".txt";

///////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////
Write(file, Sprintf("The prime we are working with is %o bits.\n", Ceiling(Log(2,p))));

Fp,Fp2,constants := GetTonelliShanksConstants(p);
instances := GetSupersingularWeierstrassPoints(number_instances,50,Fp2);

///////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////

print "\n\nENDSEARCHER PRECOMPUTATION";
print "==========================\n";

calN, INFO := EndSearcherPrecomp(
                  p,
                  Fp2,
                  constants :
                  endsearcher_flag:=endsearcher_flag,
                  end_after_22_flag:=end_after_22_flag
                );

///////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////

// RUN THE ATTACK WITH DETECTION OF ENDTINGS //

print "\n\nRUNNING ENDSEARCHER IN THE (2,2)-GRAPH";
print "======================================\n";

///////////////////////////
// Print what's going on 
if end_after_22_flag then 
    spl_after_22_str := ""; 
else 
    spl_after_22_str := "not"; 
end if;
str := Sprintf("We are %o using improvement 5 in Section 7.", spl_after_22_str);
str; Write(file, str);
str := Sprintf("The set \\mathcal{N} is %o\n", {N : N in calN});
str; Write(file, str);
//////////////////////////

total_steps:=0;
total_muls:=0;
total_time:=0;


for weier_pts in instances do   
  Sprintf("THIS INSTANCE=%o", Index(instances,weier_pts));
  print "---------------";

  t0:=Cputime();
  solution,D,rs,steps,mulcount := EndSearcher(
                                      weier_pts,
                                      constants,
                                      calN,
                                      INFO :
                                      endsearcher_flag:=endsearcher_flag,
                                      end_after_22_flag:=end_after_22_flag
                                    ); 
  t1:=Cputime(t0);

  if IsSquare(D) then
    _, N := IsSquare(D);
    j1,j2:=Genus1Curves(rs[1],rs[2],N);
    Sprintf("The j-invariants of the elliptic curves in the product is\n    (%o, %o).\n", j1, j2);
  end if;
  
  total_steps+:=steps;
  total_muls+:=mulcount;
  total_time+:=t1;
end for;

number_instances_endsearcher:=number_instances;
av_steps_endsearcher:=Ceiling(total_steps/number_instances);
av_muls_endsearcher:=Ceiling(total_muls/number_instances);
av_time_endsearcher:= total_time/number_instances;

calN_endsearcher := calN;

///////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////

// FOR COMPARISON WE DO THE USUAL ATTACK WITHOUT DETECTION OF ENDTINGS //


print "\n\nRUNNING COSTELLO--SMITH IN THE (2,2)-GRAPH";
print "==========================================\n";
endsearcher_flag:=false; // Flag decides whether or not endsearcher is run
end_after_22_flag:=false; // Flag decides whether or not we run improvement 5 in section 7

calN, INFO := EndSearcherPrecomp(
                  p,
                  Fp2,
                  constants :
                  endsearcher_flag:=endsearcher_flag,
                  end_after_22_flag:=end_after_22_flag
                );

total_steps:=0;
total_muls:=0;
total_time:=0;

for weier_pts in instances do 
  Sprintf("THIS INSTANCE=%o", Index(instances,weier_pts));
  print "---------------";
  
  t0:=Cputime();
  solution,N,rs,steps,mulcount := EndSearcher(
                                      weier_pts,
                                      constants,
                                      calN,
                                      INFO :
                                      endsearcher_flag:=endsearcher_flag,
                                      end_after_22_flag:=end_after_22_flag
                                    );     
  // Find the j-invariants of the elliptic curves in the product E_1 x E_2 which the starting Jacobian is 
  // isogenous to 
  j1,j2:=Genus1Curves(rs[1],rs[2],2);

  Sprintf("The j-invariants of the elliptic curves in the product is\n  (%o, %o).\n", j1, j2);

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
print "\n\nA COMPARISON OF ENDSEARCHER VERSUS COSTELLO--SMITH";
print "==================================================\n";

table_str := Sprintf(
                 "| %-30o| %-20o | %-20o |\n",
                 "",
                 "Costello--Smith",
                 "EndSearcher"
               );
table_str cat:= Sprintf(
                    "| %-30o| %-20o | %-20o |\n",
                    "Number of instances solved",
                    number_instances,
                    number_instances_endsearcher
                  );
table_str cat:= Sprintf(
                    "| %-30o| %-20o | %-20o |\n",
                    "Avg number of steps",
                    av_steps,
                    av_steps_endsearcher
                  );
/* table_str cat:= Sprintf( */
/*                     "| %-30o| %-20o | %-20o |\n", */
/*                     "Avg number of nodes checked", */
/*                     av_steps, */
/*                     StepsToNodes(av_steps_endsearcher, calN) */
/*                   ); */
table_str cat:= Sprintf(
                    "| %-30o| %-20o | %-20o |\n",
                    "Avg number of F_p muls",
                    av_muls,
                    av_muls_endsearcher
                  );
table_str cat:= Sprintf(
                    "| %-30o| %-20o | %-20o |\n",
                    "Avg time",
                    Sprint(av_time) cat " seconds",
                    Sprint(av_time_endsearcher) cat " seconds");
table_str cat:= "\nTable: Performance of the Costello--Smith algorithm running in the\n";
table_str cat:= "  (2,2)-graph, versus the same algorithm augmented with\n";
table_str cat:= "  EndSearcher (over the same instances). In this case our prime\n";
table_str cat:= Sprintf(
                     "  was %o bits and the set used by EndSearcher was %o \n",
                     Ceiling(Log(2,p)),
                     {N : N in calN_endsearcher}
                  );
table_str cat:= Sprintf(
                    "  (we were %o using 5 in Section 7). Note the number of nodes checked\n",
                    spl_after_22_str
                  );
table_str cat:= "  is an upper bound for EndSearcher.\n";

print table_str;

Write(file, table_str);
