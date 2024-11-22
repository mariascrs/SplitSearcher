intrinsic InvariantsFromWeierstrassPoints(as::SeqEnum, mulcount::RngIntElt) -> SeqEnum, RngIntElt
{Compute normalised IC invariants

Input
-----
as::SeqEnum 
  Defines a genus 2 curve C (these are its Weierstrass points)
mulcount::RngIntElt

Output
------
SeqEnum
  The Igusa--Clebsch invariants alpha as normalised in Lemma 2
RngIntElt
  Updated mulcount
}
  a1,a2,a3,a4,a5,a6:=Explode(as);

  a12:=(a1-a2)^2;             mulcount+:=3;
  a13:=(a1-a3)^2;             mulcount+:=3;
  a14:=(a1-a4)^2;             mulcount+:=3;
  a15:=(a1-a5)^2;             mulcount+:=3;
  a16:=(a1-a6)^2;             mulcount+:=3;
  a23:=(a2-a3)^2;             mulcount+:=3;
  a24:=(a2-a4)^2;             mulcount+:=3;
  a25:=(a2-a5)^2;             mulcount+:=3;
  a26:=(a2-a6)^2;             mulcount+:=3;
  a34:=(a3-a4)^2;             mulcount+:=3;
  a35:=(a3-a5)^2;             mulcount+:=3;
  a36:=(a3-a6)^2;             mulcount+:=3;
  a45:=(a4-a5)^2;             mulcount+:=3;
  a46:=(a4-a6)^2;             mulcount+:=3;
  a56:=(a5-a6)^2;             mulcount+:=3; //45

  T00:=a35*a46;               mulcount+:=3;
  T01:=a36*a45;               mulcount+:=3;
  T02:=a13*a25;               mulcount+:=3;
  T03:=a26*a45;               mulcount+:=3;
  T04:=a14*a25;               mulcount+:=3;
  T05:=a14*a26;               mulcount+:=3;
  T06:=a12*a34;               mulcount+:=3;
  T07:=a14*a23*a56;           mulcount+:=6;
  T08:=a16*a23;               mulcount+:=3;
  T09:=a16*a25;               mulcount+:=3;
  T10:=a13*a24*a56;           mulcount+:=6;
  T11:=a15*a24;               mulcount+:=3;
  T12:=a15*a26*a34;           mulcount+:=6;           
  T13:=a16*a35;               mulcount+:=3;
  T14:=a15*a23;               mulcount+:=3;
  T15:=a34*a56;               mulcount+:=3;
  T16:=a12*a56;               mulcount+:=3; //45+57

  S00:=T08*T11*T15;           mulcount+:=6;
  S01:=T11*a13*a26*T00;       mulcount+:=9;
  S02:=T08*T04*T00;           mulcount+:=6;
  S03:=T05*T14*T01;           mulcount+:=6;
  S04:=T02*a16*a24*T01;       mulcount+:=9;
  S05:=T06*a15*a25*a36*a46;   mulcount+:=12;
  S06:=T16*a13*a23*a45*a46;   mulcount+:=12;
  S08:=T06*T13*T03;           mulcount+:=6;
  S09:=T02*T05*T15;           mulcount+:=6;
  S07:=a14*a35*a36*a24;       mulcount+:=9; //45+57+81

  T00:=a12*T00;               mulcount+:=3;
  T01:=a12*T01;               mulcount+:=3;
  T02:=a46*T02;               mulcount+:=3;
  T03:=a13*T03;               mulcount+:=3;
  T04:=a36*T04;               mulcount+:=3;
  T05:=a35*T05;               mulcount+:=3;
  T06:=a56*T06;               mulcount+:=3;
  T08:=a45*T08;               mulcount+:=3;
  I10:=S06*S07*T12*T09;       mulcount+:=9;
  T09:=a34*T09;               mulcount+:=3;
  T11:=a36*T11;               mulcount+:=3;
  S07:=T16*S07;               mulcount+:=3;
  T13:=a24*T13;               mulcount+:=3;
  T14:=a46*T14;               mulcount+:=3; //45+57+81+48

  I4:= S00+S01+S02+S03+S04+S05+S06+S07+S08+S09;

  I6:= S00*(T00+T01+T02+T03+T04+T05)
       +S01*(T01+T04+T06+T07+T08+T09)
       +S02*(T01+T03+T06+T10+T11+T12)
       +S03*(T00+T02+T06+T10+T13+T09)
       +S04*(T00+T05+T06+T07+T12+T14)
       +S05*(T03+T05+T07+T08+T10+T13)
       +S06*(T04+T05+T09+T11+T12+T13)
       +S07*(T02+T03+T08+T09+T12+T14)
       +S08*(T10+T02+T04+T07+T11+T14) 
       +S09*(T00+T01+T08+T11+T13+T14);               mulcount+:=30;  //45+57+81+48+30

  I2:=T00+T01+T02+T03+T04+T05+T06+T07+T08+T09+T10+T11+T12+T13+T14;

  T00:=I2^2;                                        mulcount+:=3; 
  T01:=I2*T00;                                      mulcount+:=3;
  T02:=T00*T01;                                     mulcount+:=3;
  T03:=T02*I6;                                      mulcount+:=3;
  inv:=T03*I10;                                     mulcount+:=3; 
  inv,mulcount:=InvFp2(inv,mulcount);
  T04:=I10*inv;                                     mulcount+:=3;
  T05:=T03*inv;                                     mulcount+:=3;
  T06:=T02*T04;                                     mulcount+:=3;
  T07:=T04*I6;                                      mulcount+:=3;
  T08:=T07*T01;                                     mulcount+:=3;
  T06:=T06*I4;                                      mulcount+:=3;
  T05:=T05*I6;                                      mulcount+:=3;

  T06:=I2*T06;                                      mulcount+:=3;
  T05:=I4*T05;                                      mulcount+:=3; //45+57+81+48+30+30+InvFp2
  T09:=I4*T08;                                      mulcount+:=3; //291+InvFp2

  alphas:=[T09,T06,T05];                     

  /*
    // TO CHECK THE CODE
    ii:=[
        I4/I2^2,
        I2*I4/I6,
        I4*I6/I10
    ];
    assert ii eq vec1;
 */

  return alphas, mulcount;
end intrinsic;
