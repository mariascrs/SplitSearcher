// ----------------------------------------------------------------------------------
// This file contains code needed to obtain instances on which to run SplitSearcher
// ----------------------------------------------------------------------------------


SplitSearcher:=function(start_pt,constants,splitsearcher_flag,split_after_22_flag,calN,INVARIANTS, RESULTANTS, IMAGES, DIV_INFO, MONS_RES)

    steps:=0;
    found:=false;
    mulcount:=0;

    // to tell us if there was a case where one of the IC invariants vanished
    alpha_zero:=false;

    H:=StartingSeed(start_pt);

    while not found do
        as := start_pt;
        H,next_steps:=Hash(H);
        i:=0;
        N := -1;

        while i lt #next_steps and not found do
            i+:=1;

            if splitsearcher_flag then 
                //Compute alphas from Weierstrass points 
                alphas,mulcount := InvariantsFromWeierstrassPoints(as,mulcount);
                //Run SuperSolver on the node you're on, unless we're in the excluded case when alpha_i = 0 for some i
                if not exists{alpha : alpha in alphas | alpha eq 0} then 
                    // If we do improvement 5 then we do SplitSeacher on (2,2)-isogenous neighbours after one step
                    if split_after_22_flag and steps gt 0 then 
                        isog_alphas,mulcount := IsogenousInvariantsFromWeierstrass(as,mulcount);
                        k := 0;
                        repeat
                            k +:= 1; 
                            found, N, rs, mulcount := IsSplit(isog_alphas[k], calN, INVARIANTS,RESULTANTS,IMAGES,DIV_INFO,MONS_RES,mulcount);
                            if found then 
                                neighbour := k-1;
                            end if;
                        until k eq 14 or found eq true;
                    else
                        // Otherwise we do SplitSeacher on current node as described in paper 
                        found, N, rs, mulcount := IsSplit(alphas, calN, INVARIANTS,RESULTANTS,IMAGES,DIV_INFO,MONS_RES,mulcount);
                    end if;

                elif not alpha_zero then
                    alpha_zero:=true;
                    Sprintf("Worthy of Further investigation:\n    alpha=%o after the path \n    %o.", &cat Split(Sprint(alphas), " "), &cat Split(Sprint(next_steps[1..i]), " "));
                end if;
            end if;

            if not found then
                // Take a step in the (2,2)-isogeny graph
                as_new,found,mulcount:=Step(as, next_steps[i], constants, mulcount);

                if found then
                    Sprintf("    We found a splitting where N=%o (with a (2,2)-step)\n", 2);
                    // Post-computation to find the r,s correspoding to this (2,2)-splitting
                    alphas,_ := InvariantsFromWeierstrassPoints(as,0);  //post-comp
                    _,_,rs,_ := IsSplit(alphas,[2],INVARIANTS,RESULTANTS,IMAGES,DIV_INFO,MONS_RES,0 : just_checking:=false);
                end if;
                as := as_new;
                steps+:=1;
            end if;

        end while;
    end while;
    
    if splitsearcher_flag and N ne -1 then 
        if split_after_22_flag then 
            solution := next_steps[1..i] cat [neighbour];
            return start_pt,solution,N,rs,steps+2,mulcount;
        else 
            solution := next_steps[1..i];
            return start_pt,solution,N,rs,steps+1,mulcount;
        end if;
    else 
        solution := next_steps[1..i];
        return start_pt,solution,N,rs,steps,mulcount;
    end if;

end function;
