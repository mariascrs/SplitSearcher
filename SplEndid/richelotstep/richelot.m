// ----------------------------------------------------------------------------------
// This file contains code needed to take a pseudorandom walk using Richelot Isogenies
// ----------------------------------------------------------------------------------

intrinsic StartingSeed(as::SeqEnum) -> MonStgElt
{Hash function used to defined the walk in the graph (see description in Section 3.2)

Input
-----
as::SeqEnum
  Sequence of Weierstrass points

Output
------
MonStgElt
  The hash
}
  pts := [];

  for i:=1 to #as do
    this := ElementToSequence(as[i]);
    this := [Integers()!z: z in this];
    for j:=1 to #this do
      Append(~pts,this[j]);
    end for;    
  end for;
  
  seed := "";
  for j:=1 to #pts do
    seed := seed cat IntegerToString(pts[j]);
  end for;

  return seed;
end intrinsic;


intrinsic Hash(a::MonStgElt) -> MonStgElt, SeqEnum
{Hash function used to defined the walk in the graph (see description in Section 3.2)

Input
-----
a::MonStgElt
  The string given as the output of StartingSeed

Output
------
MonStgElt
  The hash of a through SHA1
SeqEnum
  List of list of bits from the hex hash
}
  bits := [];
  
  for i:=1 to 3 do
    a := SHA1(a);
    for j:=1 to #a do
      case a[j]:

        when "0": next_bits := [0,0,0,0];
        when "1": next_bits := [0,0,0,1];
        when "2": next_bits := [0,0,1,0];
        when "3": next_bits := [0,0,1,1];
        when "4": next_bits := [0,1,0,0];
        when "5": next_bits := [0,1,0,1];
        when "6": next_bits := [0,1,1,0];
        when "7": next_bits := [0,1,1,1];
        when "8": next_bits := [1,0,0,0];
        when "9": next_bits := [1,0,0,1];
        when "A": next_bits := [1,0,1,0];
        when "B": next_bits := [1,0,1,1];
        when "C": next_bits := [1,1,0,0];
        when "D": next_bits := [1,1,0,1];
        when "E": next_bits := [1,1,1,0];
        when "F": next_bits := [1,1,1,1];
      end case;

      Append(~bits,next_bits[1]);
      Append(~bits,next_bits[2]);
      Append(~bits,next_bits[3]);
      Append(~bits,next_bits[4]);
      
    end for;
  end for;

  return a, IntegerToSequence(SequenceToInteger(bits,2),8);
end intrinsic;


intrinsic PermuteKernel(as::SeqEnum, ind::RngIntElt) -> SeqEnum
{Permutes the Weierstrass points to define the kernel of a good extension (see description in Section 3.2)

Inputs
------
as::SeqEnum
  Weierstrass points
ind::RngIntElt
  Integer between 0 and 7

Outputs
-------
SeqEnum
  Reordered sequence of Weierstrass poitns
}
  case ind:
    when 0: as := [as[1],as[3],as[2],as[5],as[4],as[6]]; 
    when 1: as := [as[1],as[3],as[2],as[6],as[4],as[5]]; 
    when 2: as := [as[1],as[4],as[2],as[5],as[3],as[6]]; 
    when 3: as := [as[1],as[4],as[2],as[6],as[3],as[5]]; 
    when 4: as := [as[1],as[5],as[2],as[3],as[4],as[6]]; 
    when 5: as := [as[1],as[5],as[2],as[4],as[3],as[6]]; 
    when 6: as := [as[1],as[6],as[2],as[4],as[3],as[5]]; 
    when 7: as := [as[1],as[6],as[2],as[3],as[4],as[5]]; 
  end case;

  return as;
end intrinsic;

///////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////

intrinsic RIsog(as::SeqEnum, constants::SeqEnum, mulcount::RngIntElt) -> SeqEnum, BoolElt, RngIntElt
{Computes a Richelot Isogeny from a curve with Weierstrass points (see Algorithm 2)

Input
-----
as::SeqEnum
  Weierstrass points as a list of roots of f(x)
constants::SeqEnum 
  Tonelli--Shanks constants
mulcount::RngIntElt
  current Fp multiplication count

Output
------
SeqEnum
  Weierstrass points of image curve atils
BoolElt
  A boolean 'split' that is true if the image of this isogeny is a 
  product of elliptic curves
RngIntElt
  An updated Fp multiplication count.

Notes
-----
Should take 63*M + 3*InvSqrt <= 129 + 12*Log(p) mults because recall
  InvSqrt = 22*M + 2*expon
and 
  expon <= 2Log(p)
}
	lambdas := [as[j]*as[j+1]: j in [1,3,5]];                         mulcount+:=9;
	thetas := [];
	atils := [];

	for j:=0 to 2 do
		rho0 := as[(2*(j+1))   mod 6 + 1] - as[(2*(j+2))   mod 6 + 1]; 
		rho1 := as[(2*(j+1)+1) mod 6 + 1] - as[(2*(j+2)+1) mod 6 + 1];
		rho2 := as[(2*(j+1))   mod 6 + 1] - as[(2*(j+2)+1) mod 6 + 1];
		rho3 := as[(2*(j+1)+1) mod 6 + 1] - as[(2*(j+2))   mod 6 + 1];
		Append(~thetas,rho0+rho1);
    
		nu := lambdas[(j+1) mod 3 + 1] - lambdas[(j+2) mod 3 + 1];
		delta := rho0*rho1*rho2*rho3;                                   mulcount+:=9;
    if delta in BaseField(Parent(as[1])) then
      mu,kappa,mulcount := InvBaseSqrt(thetas[j+1],delta,constants,mulcount); 
    else 
		  mu,kappa,mulcount := InvSqrt(thetas[j+1],delta,constants,mulcount); 
    end if;
		Append(~atils,(nu+kappa)*mu);                                   mulcount+:=3;
		Append(~atils,(nu-kappa)*mu);                                   mulcount+:=3;
	end for;	

	chi := -&+[lambdas[j+1]*thetas[j+1]: j in [0..2]];                mulcount+:=9;

	return atils, (chi eq 0), mulcount;
end intrinsic;


intrinsic Step(as::SeqEnum, bits::RngIntElt, constants::SeqEnum, mulcount::RngIntElt) -> SeqEnum, BoolElt, RngIntElt
{Used to take a step in the (2,2)-isogeny graph (see description in Section 3.2)

Input
-----
as::SeqEnum
  Weierstrass points as a list of roots of f(x)
bits::RngIntElt
  Bits desribing the permutation
constants::SeqEnum 
  Tonelli--Shanks constants
mulcount::RngIntElt
  current Fp multiplication count

Output
------
SeqEnum
  Weierstrass points of image curve atils
BoolElt
  A boolean 'split' that is true if the image of this isogeny is a 
  product of elliptic curves
RngIntElt
  An updated Fp multiplication count.
}
  // Permuting between the 8 "good" kernels
  as := PermuteKernel(as, bits);
  // Call Takashima's (simplified) Richelot isogeny
  as,found,mulcount := RIsog(as,constants,mulcount);

  return as,found,mulcount;
end intrinsic;


intrinsic PermutationFromIndex(ind::RngIntElt) -> SeqEnum
{Give a Weierstrass points permutation from an integer

Input
-----
ind::RngIntElt
  An index ind in (0,...,14)
Output
------
SeqEnum
  The corresponding permutation of the Weierstrass points from the previous node that 
  gives current node
}
  case ind:
    when 0: perm := [1,3,2,5,4,6]; 
    when 1: perm := [1,3,2,6,4,5]; 
    when 2: perm := [1,4,2,5,3,6]; 
    when 3: perm := [1,4,2,6,3,5]; 
    when 4: perm := [1,5,2,3,4,6]; 
    when 5: perm := [1,5,2,4,3,6];  
    when 6: perm := [1,6,2,4,3,5];  
    when 7: perm := [1,6,2,3,4,5];
    when 8: perm := [1,2,3,5,4,6]; 
    when 9: perm := [1,2,3,6,4,5];
    when 10: perm := [1,3,2,4,5,6];
    when 11: perm := [1,4,2,3,5,6];
    when 12: perm := [1,5,2,6,3,4];
    when 13: perm := [1,6,2,5,3,4];
    when 14: perm := [1,2,3,4,5,6];
  end case;

  return perm;
end intrinsic;
