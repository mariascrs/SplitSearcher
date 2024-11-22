intrinsic MonomialsFromCoefficients(plys::SeqEnum) -> SeqEnum
{ 
INPUT: A list of polynomials plys
OUTPUT: A list of monomials in the polynomials of plys
}
  mons := {};
  cc := [];
  for ply in plys do
    cc1,_ := CoefficientsAndMonomials(ply);
    cc := cc cat cc1;
  end for;
  
  for c in cc do
    ms := Monomials(c);
    for m in ms do
      Include(~mons, m);
    end for;
  end for;
  return [m : m in mons];
end intrinsic;


intrinsic PolyDiv(p::RngUPolElt , q::RngUPolElt , mulcount::RngIntElt) -> RngUPolElt, RngIntElt
{
}
  require q ne 0: "Division by zero";

  pp<x> := Parent(p);
  l := 0;
  r:=p;
  while r ne 0 and Degree(q) le Degree(r) do
    t := LeadingCoefficient(r)/LeadingCoefficient(q);
    m := x^(Degree(r)-Degree(q));
    l +:= t*m; 
    r -:= t*m*q; mulcount +:= Degree(q);
  end while;
  
  return l, mulcount;
end intrinsic;


intrinsic GenPowers(x::FldFinElt, n::RngIntElt, mulcount::RngIntElt) -> SeqEnum, RngIntElt
{
GenPowers: compute powers of an element in \FF_(p^2)

INPUT: Element x \in \FF_(p^2), a positive integer n, and the number of \FF_p multiplications
       done so far
OUTPUT: List of powers of x up to n, [x, x^2, ..., x^n] and updated number of \FF_p muls.
}

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
end intrinsic;


intrinsic FastEvaluate(f::RngMPolElt, pt::SeqEnum, mulcount::RngIntElt : ms := []) -> FldFinElt, RngIntElt
{
FastEvaluate: Evaluates a multivariate function at a point

INPUT: A multivariate function f(x_1, ..., x_n), a point pt = [a_1, ..., a_n] and the number 
       of \FF_p multiplications done so far
OUTPUT: f evaluated at pt, namely f(a_1, ..., a_n), and updated number of \FF_p muls.
}

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
end intrinsic;


intrinsic FastPolyGCD(g::RngUPolElt, h::RngUPolElt, mulcount::RngIntElt) -> BoolElt, RngUPolElt, RngIntElt
{
FastPolyGCD: computes the gcd of two polynomials with no inversions. 

INPUT: Polynomials g, h and the number of \FF_p multiplications done so far
OUTPUT: The greatest common divisor gcd(g,h), and updated number of \FF_p muls. 
}

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
end intrinsic;


intrinsic EvalMons(mons::SeqEnum, pt::SeqEnum, eval_mons::Assoc, mulcount::RngIntElt) -> Assoc, RngIntElt
{Evaluates a list of monomials at a point 

INPUT: List of monomials mons, a point pt = [a_1, ..., a_n], an associative array eval_mons 
containing monomials already evaluated at pt, the number of \FF_p multiplications done so far
OUTPUT: Updated array eval_mons containing the monomials in mons evaluated at pt, and updated 
number of \FF_p muls. 
}

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
end intrinsic;


intrinsic EvalCoeffs(coeff::RngMPolElt, pt::SeqEnum, eval_mons::Assoc, mulcount::RngIntElt) -> FldFinElt, RngIntElt
{
EvalCoeffs: evaluates coefficient at a point

INPUT: Coefficient coeff, a point pt = [a_1, ..., a_n], an associative array eval_mons 
containing monomials already evaluated at pt, the number of \FF_p multiplications done so far.
The coefficient coeff is composed of monomials that are evaluated at pt in eval_mons
OUTPUT: Coefficient evaluate at a point ev_coeff and updated number of \FF_p muls. 
}

  cc,mm := CoefficientsAndMonomials(coeff);
  pp := Parent(mm[1]);

  ev_coeff := 0;
  for i in [1..#cc] do
    d := [Degree(mm[i], pp.k) : k in [1..3]];
    ev_coeff +:= cc[i]*eval_mons[d];                mulcount +:= 2; //F_p * F_{p^2}
  end for;

  return ev_coeff, mulcount;
end intrinsic;
