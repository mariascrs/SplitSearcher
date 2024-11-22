DD := [5, 8, 12, 13, 17, 21, 24, 28, 29, 33, 37, 40, 41, 44, 53, 56, 57, 60, 65, 69, 73, 76, 77, 85, 88, 89, 92, 93, 97];
P<r,s> := FunctionField(Rationals(), 2);

for D in DD do 
ff := eval Read("normalisedinvs/" cat Sprint(D) cat ".m");
cd := [LCM(Denominator(f[1]), Denominator(f[2])) : f in ff];
gg := [<ff[i][1]*cd[i], ff[i][2]*cd[i]> : i in [1..#ff]];
nn := [GCD(Numerator(g[1]), Numerator(g[2])) : g in gg];
gg := [<gg[i][1] / nn[i], gg[i][2] / nn[i]> : i in [1..#ff]];
cd := [Coefficients(Numerator(f[1])) cat Coefficients(Numerator(f[2])) : f in gg];
cd := [LCM([Denominator(c) : c in cc]) : cc in cd];
gg := [<gg[i][1]*cd[i], gg[i][2]*cd[i]> : i in [1..#ff]];

cd := [Coefficients(Numerator(f[1])) cat Coefficients(Numerator(f[2])) : f in gg];
cd := [GCD([Numerator(c) : c in cc]) : cc in cd];
gg := [<gg[i][1] / cd[i], gg[i][2] / cd[i]> : i in [1..#ff]];

PrintFile("normalisedinvs/" cat Sprint(D) cat ".m", gg : Overwrite:=true);
end for;


//
