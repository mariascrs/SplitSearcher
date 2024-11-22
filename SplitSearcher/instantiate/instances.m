// ----------------------------------------------------------------------------------
// This file contains code needed to generate instances on which to run the attack
// ----------------------------------------------------------------------------------


///////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////

GetSupersingularWeierstrassPoints:=function(number_instances,steps_away,Fp2)

    _<x>:=PolynomialRing(Fp2);
    C:=HyperellipticCurve(x^5+x);
    J:=Jacobian(C);

    instances:=[];

    for thisinstance:=1 to number_instances do

        for steps:=1 to steps_away do
            repeat
                isos:=RichelotIsogenousSurfaces(C);
                CC:=isos[Random(1,#isos)];
            until Type(CC) ne SetCart;
            C:=CC;
        end for;
        
        f:=Roots(HyperellipticPolynomials(C));
        weierpts:=[a[1]: a in f];
            
        Append(~instances,weierpts);
    end for;

    return instances;

end function;

///////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////