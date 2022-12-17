// ---------------------------------------------------------------------------------------------
// This file contains code needed for operations in Fp2 (e.g., taking square roots, inversions)
// ---------------------------------------------------------------------------------------------


///////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////

GetTonelliShanksConstants:=function(p)
    
    // -----------------------------------------------------------------------------------------------
    // Gets the Tonelli--Shanks Constants needed for computing square roots in Fp2
    // -----------------------------------------------------------------------------------------------


    Fp:=GF(p);

    c0 := -1; // tries c0 = -1,-2,... for quadratic extension
    while IsSquare(Fp!c0) do
        c0-:=1;
    end while;
    Fp2<i> := ExtensionField<Fp,x|x^2-c0>;

    c0:=Fp!c0;  // smallest QNR in GF(p)
    c1:=Fp!1/2; // constant for division by 2  
    c2:=1;      //Tonelli-Shanks "e" in Scott's paper
    while (p-1) mod 2^(c2+1) eq 0 do
        c2+:=1;
    end while;

    c3:=c0^((p-1) div (2^c2)); // "z" in Scott's paper
    c4:=Fp!((p-1-2^c2) div (2^(c2+1))); // y=x^c4 in Michael Scott's paper
    c6:=2^c2-1;
    c7:=c2+1;
    c8:=1/c0; //#1/c0 in Michael Scott's paper
    c5:=c0^(Integers()!(c4));
    constants:=[c0,c1,c2,c3,c4,c5,c6,c7,c8];

    return Fp,Fp2,constants;

end function;

///////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////



Expon:=function(a,n,mulcount)

    // -----------------------------------------------------------------------------------------------
    // Expon: Given a in Fp2 and integer n computes a^n and updates number of Fp multiplications
    // -----------------------------------------------------------------------------------------------
    if n ne 0 then
        bits:=IntegerToSequence(n,2);
        x:=a;
        for i:=#bits-1 to 1 by -1 do
            x:=x^2;                                                     mulcount+:=1;
            if bits[i] eq 1 then
                x*:=a;                                                  mulcount+:=1;
            end if;
        end for;
        return x,mulcount;
    else
        return 1,mulcount;
    end if;

end function;

///////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////

TonelliShanksUpdate:=function(x,y,constants,mulcount)

    // -----------------------------------------------------------------------------------------------
    // Expon: Updates the Tonelli--Shanks constants
    // -----------------------------------------------------------------------------------------------


    a0:=Integers()!constants[1];
    a1:= constants[2];
    a2:= constants[3];
    a3:= constants[4];
    
    s0:=y;
    s1:=x;

    for j := 2 to a0 do
        s0:=s0^2;                        mulcount+:=1;
        s1:=s1^2;                        mulcount+:=1;
    end for;

    s0:=s0^2;                            mulcount+:=1;
    s0*:=s1;                             mulcount+:=1;

    if s0 ne 1 then
        x*:=a2;                          mulcount+:=1;
        y*:=a3;                          mulcount+:=1;
    end if;

    s1:=x*y;                             mulcount+:=1;
    s2:=s1*y;                            mulcount+:=1;

    for k:= a0 to 2 by -1 do
        s3:=s2;
        for i:=3 to k do
            s3*:=s3;                     mulcount+:=1;
        end for;
        if s3 ne 1 then
            s1*:=a1;                     mulcount+:=1;
        end if;
        a1*:=a1;                         mulcount+:=1;
        if s3 ne 1 then
            s2*:=a1;                     mulcount+:=1;
        end if;
    end for;
    
    return s1,s0,mulcount;

end function;

///////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////

InvSqrt:=function(u,v,constants,mulcount)

    // -----------------------------------------------------------------------------------------------
    // InvSqrt: merged inversion-and-square root computation (see Section 3.1) using Tonelli--Shanks
    //          constants and updates the number of Fp multiplications
    // -----------------------------------------------------------------------------------------------


    c0,c1,c2,c3,c4,c5,c6,c7,c8:=Explode(constants); //may remove later
    
    c4:=Integers()!c4;
    c6:=Integers()!c6;
    c7:=Integers()!c7;

    u0:=ElementToSequence(u)[1];
    u1:=ElementToSequence(u)[2];
    v0:=ElementToSequence(v)[1];
    v1:=ElementToSequence(v)[2];

    U:=u0^2;                                                        mulcount+:=1;
    U+:=u1^2;                                                       mulcount+:=1;

    t0:=v0; 
    t1:=v1;

    t2:=t0^2;                                                       mulcount+:=1;
    t3:=t1^2;                                                       mulcount+:=1;
    t3:=c0*t3;                                                      mulcount+:=1;
    t2:=t2-t3;                                                      

    X:=U^2;                                                         mulcount+:=1;
    X*:=t2;                                                         mulcount+:=1;

    Y,mulcount:=Expon(X,c4,mulcount);  

    Xinv:=Y^2;                                                      mulcount+:=1;
    Xinv:=Xinv^2;                                                   mulcount+:=1;
    Xinv:=Xinv*X;                                                   mulcount+:=1;
    Xinv,mulcount:=Expon(Xinv,c6,mulcount);  
    Uinv,mulcount:=Expon(X,c6-1,mulcount);

    Uinv:=U*t2;                                                     mulcount+:=1;
    Uinv:=Uinv*Xinv;                                                mulcount+:=1;
    u0:=u0*Uinv;                                                    mulcount+:=1;
    u1:=-u1*Uinv;                                                   mulcount+:=1;
    rtX,_,mulcount:=TonelliShanksUpdate(X,Y,[c2,c3,c0,c5],mulcount);

    t2:=rtX*Uinv;                                                   mulcount+:=1;
    t3:=t0+t2;
    t3:=t3*c1;                                                      mulcount+:=1;
    t0,mulcount:=Expon(t3,c4,mulcount);
    t2:=t0;

    for i:=1 to c7 do
        t2:=t2^2;                                                   mulcount+:=1;
    end for;

    t2:=t2*c1;                                                      mulcount+:=1;
    t2:=t2*t1;                                                      mulcount+:=1;
    t1,mulcount:=Expon(t3,c6,mulcount);                 
    t2:=t2*t1;                                                      mulcount+:=1;
    t3,t0,mulcount:=TonelliShanksUpdate(t3,t0,[c2,c3,c0,c5],mulcount);
    t2:=t2*t3;                                                      mulcount+:=1;

    if t0 eq 1 then
        t0:=t3;
        t3:=t2;
    else 
        t0:=t2;
        t3:=t3*c8;                                                  mulcount+:=1;
    end if;

    return SequenceToElement([u0,u1],Parent(v)),SequenceToElement([t0,t3],Parent(v)),mulcount;

end function;

///////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////

InvBaseSqrt:=function(u,v,constants,mulcount)

    // -----------------------------------------------------------------------------------------------
    // InvBaseSqrt: special case of InvSqrt where v is in the base field GF(p)
    // -----------------------------------------------------------------------------------------------

    c0,c1,c2,c3,c4,c5,c6,c7,c8:=Explode(constants); //may remove later
    
    c4:=Integers()!c4;
    c6:=Integers()!c6;
    c7:=Integers()!c7;

    u0:=ElementToSequence(u)[1];
    u1:=ElementToSequence(u)[2];
    v:=Parent(u0)!v;

    U:=u0^2;                                                        mulcount+:=1;
    U+:=u1^2;                                                       mulcount+:=1;                                         

    X:=U^2;                                                         mulcount+:=1;
    X*:=v;                                                          mulcount+:=1;

    Y,mulcount:=Expon(X,c4,mulcount);  

    Y4:=Y^2;                                                        mulcount+:=1;
    Y4:=Y4^2;                                                       mulcount+:=1;
    XY4:=X*Y4;                                                      mulcount+:=1;

    Xinv,mulcount:=Expon(XY4,c6,mulcount);  
    Uinv,mulcount:=Expon(X,c6-1,mulcount);
    Xinv:=Uinv*Xinv;                                                mulcount+:=1;
    Uinv:=U*v;                                                      mulcount+:=1;
    Uinv:=Uinv*Xinv;                                                mulcount+:=1;

    s:=X*Y;                                                         mulcount+:=1;
    t:=s*Y;                                                         mulcount+:=1;

    s,t,mulcount:=TonelliShanksUpdate(s,t,[c2,c3,c0,c5],mulcount);
    
    s2:=s^2;                                                        mulcount+:=1;
    rtv:=Uinv*s;                                                    mulcount+:=1;

    if s2 eq X then
        rtv:=SequenceToElement([rtv,0],Parent(u));
    else
        rtv:=SequenceToElement([0,rtv],Parent(u));
    end if;

    U0:=u0*Uinv;                                                    mulcount+:=1;
    U1:=-u1*Uinv;                                                   mulcount+:=1;
    uinv:=SequenceToElement([U0,U1],Parent(u)); 

    return uinv,rtv,mulcount;

end function;

///////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////

InvFp2:=function(D,mulcount)


    // -----------------------------------------------------------------------------------------------
    // InvFp2: Computes inverse of D over Fp2 and updates the number of Fp multiplcations
    // -----------------------------------------------------------------------------------------------

    
    D0:=ElementToSequence(D)[1];
    D1:=ElementToSequence(D)[2];

    t0:=D0^2; mulcount+:=1;
    t1:=D1^2; mulcount+:=1;
    t0:=t0+t1;

    t0,mulcount:=Expon(t0,Characteristic(Parent(D))-2,mulcount);
    
    D0:=D0*t0; mulcount+:=1;
    D1:=D1*t0; mulcount+:=1;
    D1:=-D1;

    return SequenceToElement([D0,D1],Parent(D)), mulcount;

end function;

///////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////

BatchMontgomeryInversion:=function(L)

    // -----------------------------------------------------------------------------------------------
    // INPUT: A list L = [L[1],...,L[n]]
    // OUTPUT:  L' = [1/L[1],...,1/L[n]] using 3*(n-1) multiplications (in Fp2) and 1 inversion
    // -----------------------------------------------------------------------------------------------

    mulcount:=0;
    M:=[L[1]];
    for i:=2 to #L do
        Append(~M,L[i]*M[i-1]); mulcount+:=3;
    end for;

    inv,mulcount:=InvFp2(M[#M],mulcount);

    N:=[inv];
    for i:=1 to #L-1 do
        Append(~N,L[#L+1-i]*N[i]); mulcount+:=3;
    end for;
    N:=Reverse(N);
    LL:=[N[1]];
    for i:=2 to #L do
        Append(~LL,M[i-1]*N[i]); mulcount+:=3;
    end for;

    return LL,mulcount;

end function;

///////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////