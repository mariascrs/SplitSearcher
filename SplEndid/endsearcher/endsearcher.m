declare verbose SplEnd, 2;

intrinsic EndSearcher(
  as::SeqEnum,
  constants::SeqEnum,
  calN::SeqEnum,
  INFO:: SeqEnum[Assoc] :
  endsearcher_flag:=true,
  end_after_22_flag:=false
  ) -> SeqEnum, RngIntElt, SeqEnum, RngIntElt, RngIntElt
{
The endsearcher algorithm
}
  steps:=0;
  found:=false;
  mulcount:=0;

  // to tell us if there was a case where one of the IC invariants vanished
  alpha_zero:=false;

  H:=StartingSeed(as);

  while not found do

    H,next_steps:=Hash(H);
    i:=0;
    N := -1;

    while i lt #next_steps and not found do
      i+:=1;

      if endsearcher_flag then 
        //Compute alphas from Weierstrass points 
        alphas,mulcount := InvariantsFromWeierstrassPoints(as,mulcount);
        //Run SplEndidSearcher on the node you're on, unless we're in the excluded case when alpha_i = 0 for some i
        if not exists{alpha : alpha in alphas | alpha eq 0} then 
          // If we do improvement 5 then we do SplEndidSeacher on (2,2)-isogenous neighbours after one step
          if end_after_22_flag and steps gt 0 then 
            isog_alphas,mulcount := IsogenousInvariantsFromWeierstrass(as,mulcount);
            k := 0;
            repeat
              k +:= 1; 
              found, N, rs, mulcount := HasEnd(isog_alphas[k], calN, INFO, mulcount);
              if found then 
                neighbour := k-1;
              end if;
            until k eq 14 or found eq true;
          else
            // Otherwise we do EndSeacher on current node as described in paper 
            found, N, rs, mulcount := HasEnd(alphas, calN, INFO, mulcount);
          end if;

        elif not alpha_zero then
          alpha_zero:=true;
          Sprintf("Worthy of Further investigation:\n  alpha=%o after the path \n  %o.", &cat Split(Sprint(alphas), " "), &cat Split(Sprint(next_steps[1..i]), " "));
        end if;
      end if;

      if not found then
        // Take a step in the (2,2)-isogeny graph
        as_new,found,mulcount:=Step(as, next_steps[i], constants, mulcount);

        if found then
          // Post-computation to find the r,s corresponding to this (2,2)-splitting
          alphas,_ := InvariantsFromWeierstrassPoints(as,0);  //post-comp
          _,_,rs,_ := HasEnd(alphas, [4], INFO, 0);
        end if;
        as := as_new;
        steps+:=1;
      end if;

    end while;
  end while;
  
  if endsearcher_flag and N ne -1 then 
    if end_after_22_flag then 
      solution := next_steps[1..i] cat [neighbour];
      return solution,N,rs,steps+2,mulcount;
    else 
      solution := next_steps[1..i];
      return solution,N,rs,steps+1,mulcount;
    end if;
  else 
    solution := next_steps[1..i];
    return solution,N,rs,steps,mulcount;
  end if;

end intrinsic;
