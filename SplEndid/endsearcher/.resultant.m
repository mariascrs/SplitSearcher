//DD := [5, 8, 12, 13, 17, 21, 24, 28, 29, 33, 37, 40, 41, 44, 53, 56, 57, 60, 65, 69, 73, 76, 77, 85, 88, 89, 92, 93, 97];

DD := [97];

procedure SwapRoles(D)
  P<r,s> := PolynomialRing(Rationals(), 2);
  ff := eval Read("normalisedinvs/" cat Sprint(D) cat ".m");
  gg := [<Evaluate(f[1], [s,r]), Evaluate(f[2], [s,r])> : f in ff];
  PrintFile("normalisedinvs/" cat Sprint(D) cat ".m", gg : Overwrite:=true);

  II := eval Read("ekinvs/" cat Sprint(D) cat ".m");
  JJ := [Evaluate(i, [s,r]) : i in II];
  PrintFile("ekinvs/" cat Sprint(D) cat ".m", gg : Overwrite:=true);
end procedure;

function CleanUp(f)
  cc := Coefficients(f);
  cc := [Numerator(c) : c in cc];
  D := GCD(cc);
  f := f / D;
  cc := Coefficients(f);
  cc := [Numerator(c) : c in cc];
  cc := &cat [Coefficients(c) : c in cc];
  cc := [Numerator(c) : c in cc];
  f := f / GCD(cc);
  return f;
end function;



for D in DD do
KK<i1,i2,i3> := FunctionField(Rationals(), 3);
P<r,s> := PolynomialRing(KK, 2);

ff := eval Read("normalisedinvs/" cat Sprint(D) cat ".m");

ff := [
  ff[1][1] - i1*ff[1][2],
  ff[2][1] - i2*ff[2][2],
  ff[3][1] - i3*ff[3][2]
];
ff := [Numerator(f) : f in ff];

r1 := Resultant(ff[1], ff[2], 1);
print "here";
r2 := Resultant(ff[2], ff[3], 1);
print "here";
/* s1 := Resultant(ff[1], ff[2], 2); */
/* s2 := Resultant(ff[2], ff[3], 2); */

rr1 := Factorisation(Numerator(r1));
rr2 := Factorisation(Numerator(r2));
rr1 := rr1[1..#rr1-1];
rr2 := rr2[1..#rr2-1];

rr1; rr2;

d1 := &*([1] cat [a[1]^a[2] : a in rr1]);
d2 := &*[a[1]^a[2] : a in rr2];
dd := Coefficients(Numerator(d1)); dd := [Denominator(Rationals()!a) : a in dd]; dd := LCM(dd);
d1 := dd*d1;
dd := Coefficients(Numerator(d2)); dd := [Denominator(a) : a in dd]; dd := LCM(dd);
d2 := dd*d2;


DIVINFO := [
  d1, d2
];

r1 := CleanUp(r1) div DIVINFO[1];
r2 := CleanUp(r2) div DIVINFO[2];

str1 := "f := " cat Sprint(r1) cat ";\n";
str2 := "g := " cat Sprint(r2) cat ";\n";
ret := str1 cat str2 cat "return f, g;";
PrintFile("precompres/" cat Sprint(D) cat ".m", ret : Overwrite:=true);
PrintFile("divinfo/" cat Sprint(D) cat ".m", DIVINFO : Overwrite:=true);
end for;
