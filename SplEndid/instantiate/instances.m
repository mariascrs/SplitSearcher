// ----------------------------------------------------------------------------------
// This file contains code needed to generate random instances on which to run the attack
// ----------------------------------------------------------------------------------

intrinsic GetSupersingularWeierstrassPoints(number_instances::RngIntElt, steps_away::RngIntElt, Fp2::FldFin) -> SeqEnum
{Generates a number of pseudo-random lists of Weierstrass points of superspecial Jacobians

Inputs
------
number_instances::RngIntElt
  The number of instances you want
steps_away::RngIntElt
  The number of steps to take away from the starting curve
Fp2
  Finite field

Outputs
-------
SeqEnum
  Lists of Weierstass points of superspecial genus 2 Jacobians
}
  p := Characteristic(Fp2);
  require p ge 5: "You need to choose bigger p";
  _<x> := PolynomialRing(Fp2);

  if Integers(8)!p in [7] then
    C := HyperellipticCurve(x^5-x);
  elif Integers(6)!p eq 5 then
    C := HyperellipticCurve(x*(x-1)*(x+1)*(x-2)*(x-1/2));
  else
    require false: "Sorry we don't have a choice of starting curve for p";
  end if;
  
  J := Jacobian(C);

  instances := [];

  for thisinstance:=1 to number_instances do

    for steps:=1 to steps_away do
      repeat
        isos := RichelotIsogenousSurfaces(C);
        CC := isos[Random(1,#isos)];
      until Type(CC) ne SetCart; //make sure you're not stepping to a product
      C := CC;
    end for;
    
    f := Roots(HyperellipticPolynomials(C));
    weierpts := [a[1]: a in f];
    
    Append(~instances,weierpts);
  end for;

  return instances;
end intrinsic;
