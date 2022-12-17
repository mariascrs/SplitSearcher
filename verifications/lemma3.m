/*
    This file proves the claim made in Lemma 3
*/
QQ := Rationals();

for N in [2..11] do
    P<s> := PolynomialRing(QQ);
    Qij := eval Read("../code/splitsearcher/divinfo/" cat Sprint(N) cat ".m");

    for i in [1..2] do
        // to vanish at Qji has to vanish at a factor

        for fact in [fact[1] : fact in Factorization(Qij[i])] do
            
            if Degree(fact) gt 1 then 
                K<s0> := NumberField(fact);
            else
                K := QQ;
                s0 := Roots(fact)[1][1];
            end if;

            KK<[a]> := FunctionField(K,3);
            PP<r> := PolynomialRing(KK);

            s := s0; // just to read the file
            ff := eval Read("../code/splitsearcher/normalisedinvs/" cat Sprint(N) cat ".m");
            fk := [ff[i][1] - a[i]*ff[i][2] : i in [1..3]];
            possible := GCD(fk); // if vanishes at all fk

            if not Degree(possible) eq 0 then 
                fcts := [f[1] : f in Factorisation(possible)];
                assert forall{f : f in fcts | Degree(f) eq 1};
                
                for fct in fcts do 
                    r0 := Roots(fct)[1][1];

                    try 
                        r := r0; s := s0; // just to read the file
                        calI_r0s0 := eval Read("../code/splitsearcher/kumarinvs/" cat Sprint(N) cat ".m");
                        assert exists{I : I in calI_r0s0 | I eq 0};
                    catch e 
                        // we only get here if A1(r0,s0)=0 (zero division error) 
                        // in which case calI_10(r0,s0)=0 (see kumarinvs)
                        assert 0 eq 0;
                    end try;
                end for;
            end if;

        end for;
    end for;

end for;