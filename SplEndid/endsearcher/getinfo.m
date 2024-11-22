CURR_DIR := "/TODO/SplEndid/endsearcher/";

intrinsic GetIg(N::RngIntElt) -> SeqEnum
{
INPUT: Fundamental discriminants or squares N \in 4,...,121
OUTPUT: Sequence of polynomials II such that the (weighted) IC invariants
}
  _<r,s> := PolynomialRing(Rationals(), 2);
  return eval Read(CURR_DIR cat "ekinvs/" cat Sprint(N) cat ".m");
end intrinsic;


intrinsic GetNormalisedIg(N::RngIntElt) -> SeqEnum
{
INPUT: Funadamental discriminants or squares N \in 4,...,121
OUTPUT: Sequence of polynomials II such that the normalised invariants are precisely 
  [II[1]/II[4], II[2]/II[4], II[3]/II[4]]
}
  _<r,s> := PolynomialRing(Integers(), 2);
  return eval Read(CURR_DIR cat "normalisedinvs/" cat Sprint(N) cat ".m");
end intrinsic;


intrinsic GetPrecompRes(N::RngIntElt) -> SeqEnum
{
INPUT: Fundamental discriminants or squares N \in 2,...,11
OUTPUT: Returns the precomputed resultants corresponding to N
}
  _<r,s,i1,i2,i3> := PolynomialRing(Integers(), 5);
  f,g := eval Read(CURR_DIR cat "precompres/" cat Sprint(N) cat ".m");
  return [f,g];
end intrinsic;
