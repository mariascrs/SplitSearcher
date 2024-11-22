// ----------------------------------------------------------------------------------
// This file contains code performing various operations on Weierstrass points
// ----------------------------------------------------------------------------------


QuadraticsFromWeierstrass:=function(as,mulcount)
    // -----------------------------------------------------------------------------------------------
    // INPUT: Weierstrass points of a genus 2 curve C and the multiplication count
    // OUTPUT: All quadratic splittings of the Weierstrass sextic and an updated multiplication count 
    // -----------------------------------------------------------------------------------------------

    a1,a2,a3,a4,a5,a6:=Explode(as);
    quadratics:=[];

    P12:=a1*a2;             mulcount+:=3;
    P13:=a1*a3;             mulcount+:=3; 
    P14:=a1*a4;             mulcount+:=3; 
    P15:=a1*a5;             mulcount+:=3; 
    P16:=a1*a6;             mulcount+:=3;
    P23:=a2*a3;             mulcount+:=3; 
    P24:=a2*a4;             mulcount+:=3; 
    P25:=a2*a5;             mulcount+:=3; 
    P26:=a2*a6;             mulcount+:=3;
    P34:=a3*a4;             mulcount+:=3; 
    P35:=a3*a5;             mulcount+:=3; 
    P36:=a3*a6;             mulcount+:=3;
    P45:=a4*a5;             mulcount+:=3; 
    P46:=a4*a6;             mulcount+:=3;
    P56:=a5*a6;             mulcount+:=3;

    T123:=P12*a3;           mulcount+:=3; 
    T124:=P12*a4;           mulcount+:=3; 
    T125:=P12*a5;           mulcount+:=3; 
    T126:=P12*a6;           mulcount+:=3;
    T134:=P13*a4;           mulcount+:=3; 
    T135:=P13*a5;           mulcount+:=3; 
    T136:=P13*a6;           mulcount+:=3;
    T145:=P14*a5;           mulcount+:=3; 
    T146:=P14*a6;           mulcount+:=3;
    T156:=P15*a6;           mulcount+:=3; 
    T234:=P23*a4;           mulcount+:=3; 
    T235:=P23*a5;           mulcount+:=3; 
    T236:=P23*a6;           mulcount+:=3; 
    T245:=P24*a5;           mulcount+:=3; 
    T246:=P24*a6;           mulcount+:=3;
    T256:=P25*a6;           mulcount+:=3;
    T345:=P34*a5;           mulcount+:=3;
    T346:=P34*a6;           mulcount+:=3;
    T356:=P35*a6;           mulcount+:=3;
    T456:=P45*a6;           mulcount+:=3;    
    
    ///////////////////
    //GOOD EXTENSIONS//
    ///////////////////

    //(1,3)(2,5)(4,6)//
    H12 := a2-a4+a5-a6; H22 := -a1-a3+a4+a6; H32 := a1-a2+a3-a5;
    H11 := -P25+P46; H21 := P13-P46; //H31 := -P13+P25
    H11:=H11+H11; H21:=H21+H21; H31:=-H11-H21;
    H10 := T245+T256-T246-T456;
    H20 := T146+T346-T134-T136;
    H30 := T123+T135-T125-T235;
    Include(~quadratics,[H12,H11,H10,H22,H21,H20,H32,H31,H30]);

    //(1,3)(2,6)(4,5)//
    H12 := a2-a4-a5+a6;
    H22 := -a1-a3+a4+a5;
    H32 := a1-a2+a3-a6;
    H11 := -P26+P45; H21 := P13-P45; //H31 := -P13+P26
    H11:=H11+H11; H21:=H21+H21; H31:=-H11-H21;
    H10 := T246+T256-T245-T456;
    H20 := T145+T345-T134-T135;
    H30 := T123+T136-T126-T236;
    Include(~quadratics,[H12,H11,H10,H22,H21,H20,H32,H31,H30]);

    //(1,4)(2,5)(3,6)//
    H12 := a2-a3+a5-a6;
    H22 := -a1+a3-a4+a6;
    H32 := a1-a2+a4-a5;
    H11 := -P25+P36; H21 := P14-P36; //H31 := -P14+P25
    H11:=H11+H11; H21:=H21+H21; H31:=-H11-H21;
    H10 := T235-T236+T256-T356;
    H20 := -T134+T136-T146+T346;
    H30 := T124-T125+T145-T245;
    Include(~quadratics,[H12,H11,H10,H22,H21,H20,H32,H31,H30]);

    //(1,4)(2,6)(3,5)//
    H12 := a2-a3-a5+a6; 
    H22 := -a1+a3-a4+a5; 
    H32 := a1-a2+a4-a6;
    H11 := -P26+P35; H21 := P14-P35; //H31 := -P14+P26
    H11:=H11+H11; H21:=H21+H21; H31:=-H11-H21;
    H10 := -T235+T236+T256-T356;
    H20 := -T134+T135-T145+T345;
    H30 := T124-T126+T146-T246;
    Include(~quadratics,[H12,H11,H10,H22,H21,H20,H32,H31,H30]);

    //(1,5)(2,3)(4,6)
    H12 := a2+a3-a4-a6; 
    H22 := -a1+a4-a5+a6; 
    H32 := a1-a2-a3+a5;
    H11 := -P23+P46; H21 := P15-P46; //H31 := -P15+P23;
    H11:=H11+H11; H21:=H21+H21; H31:=-H11-H21;
    H10 := T234+T236-T246-T346;
    H20 := -T145+T146-T156+T456;
    H30 := -T123+T125+T135-T235;
    Include(~quadratics,[H12,H11,H10,H22,H21,H20,H32,H31,H30]);

    //(1,5)(2,4)(3,6)
    H12 := a2-a3+a4-a6;
    H22 := -a1+a3-a5+a6;
    H32 := a1-a2-a4+a5;
    H11 := -P24+P36; H21 := P15-P36; H31 := -P15+P24;
    H11:=H11+H11; H21:=H21+H21; H31:=-H11-H21;
    H10 := T234-T236+T246-T346;
    H20 := -T135+T136-T156+T356;
    H30 := -T124+T125+T145-T245;
    Include(~quadratics,[H12,H11,H10,H22,H21,H20,H32,H31,H30]);

    //(1,6)(2,4)(3,5)//
    H12 := a2-a3+a4-a5;
    H22 := -a1+a3+a5-a6;
    H32 := a1-a2-a4+a6;
    H11 := -P24+P35; H21 := P16-P35; H31 := -P16+P24;
    H11:=H11+H11; H21:=H21+H21; H31:=-H11-H21;
    H10 := T234-T235+T245-T345;
    H20 := T135-T136-T156+T356;
    H30 := -T124+T126+T146-T246;
    Include(~quadratics,[H12,H11,H10,H22,H21,H20,H32,H31,H30]);

    //(1,6)(2,3)(4,5)// 
    H12 := a2+a3-a4-a5;
    H22 := -a1+a4+a5-a6;
    H32 := a1-a2-a3+a6;
    H11 := -P23+P45; H21 := P16-P45; H31 := -P16+P23;
    H11:=H11+H11; H21:=H21+H21; H31:=-H11-H21;
    H10 := T234+T235-T245-T345;
    H20 := T145-T146-T156+T456;
    H30 := -T123+T126+T136-T236;
    Include(~quadratics,[H12,H11,H10,H22,H21,H20,H32,H31,H30]);

    //////////////////
    //BAD EXTENSIONS//
    //////////////////

    //(1,2)(3,5)(4,6)
    H12 := a3-a4+a5-a6;  H22 := -a1-a2+a4+a6; H32 := a1+a2-a3-a5;
    H11 := P46-P35; H21 := P12-P46; //H31 := -P12+P35;
    H11:=H11+H11; H21:=H21+H21; H31:=-H11-H21;
    H10 := T345+T356-T346-T456;
    H20 := T146+T246-T124-T126;
    H30 := T123+T125-T135-T235;
    Include(~quadratics,[H12,H11,H10,H22,H21,H20,H32,H31,H30]);

    //(1,2)(3,6)(4,5)
    H12 := a3-a4-a5+a6; H22 := -a1-a2+a4+a5; H32 := a1+a2-a3-a6;
    H11 := -P36+P45; H21 := P12-P45; //H31 := -P12+P36;
    H11:=H11+H11; H21:=H21+H21; H31:=-H11-H21;
    H10 := T346+T356-T345-T456;
    H20 := T145+T245-T124-T125;
    H30 := T123+T126-T136-T236;
    Include(~quadratics,[H12,H11,H10,H22,H21,H20,H32,H31,H30]);

    //(1,3)(2,4)(5,6)
    H12 := a2+a4-a5-a6;  H22 := -a1-a3+a5+a6; H32 := a1-a2+a3-a4;
    H11 := -P24+P56; H21 := P13-P56; //H31 := -P13+P24;
    H11:=H11+H11; H21:=H21+H21; H31:=-H11-H21;
    H10 := T245+T246-T256-T456;
    H20 := T156+T356-T135-T136;
    H30 := T123+T134-T124-T234;
    Include(~quadratics,[H12,H11,H10,H22,H21,H20,H32,H31,H30]);

    //(1,4)(2,3)(5,6)
    H12 := a2+a3-a5-a6;
    H22 := -a1-a4+a5+a6;
    H32 := a1-a2-a3+a4;
    H11 := -P23+P56; H21 := P14-P56; // H31 := -P14+P23;
    H11:=H11+H11; H21:=H21+H21; H31:=-H11-H21;
    H10 := T235+T236-T256-T356;
    H20 := -T145-T146+T156+T456;
    H30 := -T123+T124+T134-T234;
    Include(~quadratics,[H12,H11,H10,H22,H21,H20,H32,H31,H30]);
    
    //(1,5)(2,6)(3,4)    
    H12 := a2-a3-a4+a6;
    H22 := -a1+a3+a4-a5;
    H32 := a1-a2+a5-a6;
    H11 := -P26+P34; H21 := P15-P34; H31 := -P15+P26;
    H11:=H11+H11; H21:=H21+H21; H31:=-H11-H21;
    H10 := -T234+T236+T246-T346;
    H20 := T134-T135-T145+T345;
    H30 := T125-T126+T156-T256;
    Include(~quadratics,[H12,H11,H10,H22,H21,H20,H32,H31,H30]);
    
    //(1,6)(2,5)(3,4)  
    H12 := a2-a3-a4+a5;
    H22 := -a1+a3+a4-a6;
    H32 := a1-a2-a5+a6;
    H11 := -P25+P34; H21 := P16-P34; H31 := -P16+P25;
    H11:=H11+H11; H21:=H21+H21; H31:=-H11-H21;
    H10 := -T234+T235+T245-T345;
    H20 := T134-T136-T146+T346;
    H30 := -T125+T126+T156-T256;
    Include(~quadratics,[H12,H11,H10,H22,H21,H20,H32,H31,H30]);

    /////////////////
    //////DUAL///////
    /////////////////

    // (1,2)(3,4)(5,6)
    // H12 := a3+a4-a5-a6; H22 := -a1-a2+a5+a6; H32 := a1+a2-a3-a4;
    // H11 := P56-P34; H21 := P12-P56; //H31 := -P12+P34;
    // H11:=H11+H11; H21:=H21+H21; H31:=-H11-H21;
    // H10 := T345+T346-T356-T456;
    // H20 := T156+T256-T125-T126;
    // H30 := T123+T124-T134-T234;
    // Include(~quadratics,[H12,H11,H10,H22,H21,H20,H32,H31,H30]);

    return quadratics,mulcount;

end function;   

///////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////

InvariantsFromQuadratics:=function(quadratics,mulcount)


    // -----------------------------------------------------------------------------------------------------
    // INPUT: A quadratic splitting of a Weierstrass sextic and multiplication count
    // OUTPUT: The Igusa--Clebsch invariants of the (2,2)-isogenous Jacobian corresponding to the splitting
    // -----------------------------------------------------------------------------------------------------

    a2,a1,a0,b2,b1,b0,c2,c1,c0:=Explode(quadratics);

    A:=b0*c2;              mulcount+:=3;
    B:=b2*c0;              mulcount+:=3;
    C:=b1*c2;              mulcount+:=3;
    D:=b2*c1;              mulcount+:=3;
    E:=b0*c1;              mulcount+:=3;
    F:=b1*c0;              mulcount+:=3;
    G:=b0*c0;              mulcount+:=3;
    H:=b1*c1;              mulcount+:=3;
    I:=b2*c2;              mulcount+:=3;
    S0:=C-D;               //A
    S1:=E-F;               //A
    S2:=A-B;               //A
    S2:=S2^2;              mulcount+:=3;
    S1:=S1*S0;             mulcount+:=3;
    I10:=S2-S1;            //A
    E:=E+F;                //A
    A:=A+H;                //A
    A:=A+B;                //A
    C:=C+D;                //A
    f0 := a0*G;            mulcount+:=3;
    f1:=a0*E;              mulcount+:=3;
    S0:=a1*G;              mulcount+:=3;
    f1:=f1+S0;             //A
    f2 := a0*A;            mulcount+:=3;
    S0:=a1*E;              mulcount+:=3;
    f2:=f2+S0;             //A
    S0:=a2*G;              mulcount+:=3;
    f2:=f2+S0;             //A
    f3:=a0*C;              mulcount+:=3;
    S0:=a1*A;              mulcount+:=3;
    f3:=f3+S0;             //A
    S0:=a2*E;              mulcount+:=3;
    f3:=f3+S0;             //A
    f4:=a0*I;              mulcount+:=3;
    S0:=a1*C;              mulcount+:=3;
    f4:=f4+S0;             //A
    S0:=a2*A;              mulcount+:=3;
    f4:=f4+S0;             //A
    f5:=a1*I;              mulcount+:=3;
    S0:=a2*C;              mulcount+:=3;
    f5 :=f5+S0;            //A
    f6 := a2*I;            mulcount+:=3;
    A:=a0*c2;              mulcount+:=3;
    B:=a2*c0;              mulcount+:=3;
    C:=a1*c2;              mulcount+:=3;
    D:=a2*c1;              mulcount+:=3;
    E:=a0*c1;              mulcount+:=3;
    F:=a1*c0;              mulcount+:=3;
    S0:=C-D;               //A
    S1:=E-F;               //A
    S2:=A-B;               //A
    S2:=S2^2;              mulcount+:=3;
    S1:=S1*S0;             mulcount+:=3;
    S2:=S2-S1;             //A
    I10:=I10*S2;           mulcount+:=3;
    A:=a0*b2;              mulcount+:=3;
    B:=a2*b0;              mulcount+:=3;
    C:=a1*b2;              mulcount+:=3;
    D:=a2*b1;              mulcount+:=3;
    E:=a0*b1;              mulcount+:=3;
    F:=a1*b0;              mulcount+:=3;
    S0:=C-D;               //A
    S1:=E-F;               //A
    S2:=A-B;               //A
    S2:=S2^2;              mulcount+:=3;
    S1:=S1*S0;             mulcount+:=3;
    S2:=S2-S1;;            //A
    I10:=I10*S2;           mulcount+:=3;
    I10:=I10^2;            mulcount+:=3;
    S0:=a0*a2;             mulcount+:=3;
    S0:=4*S0;              //2A
    S1:=a1^2;              mulcount+:=3;
    S0:=S0-S1;;            //A
    I10:=I10*S0;           mulcount+:=3;
    S0:=b0*b2;             mulcount+:=3;
    S0:=4*S0;              //2A
    S1:=b1^2;              mulcount+:=3;
    S0:=S0-S1;;            //A
    I10:=I10*S0;           mulcount+:=3;
    S0:=c0*c2;             mulcount+:=3;
    S0:=4*S0;              //2A
    S1:=c1^2;              mulcount+:=3;
    S0:=S0-S1;;            //A
    I10:=I10*S0;           mulcount+:=3;
    F0:=f0*f6;             mulcount+:=3;
    F1:=f1*f5;             mulcount+:=3; 
    F2:=f2*f4;             mulcount+:=3; 
    F3:=f3^2;              mulcount+:=3;
    F4:=F2*F3;             mulcount+:=3;
    S1:=F1^2;              mulcount+:=3; 
    S2:=F2^2;              mulcount+:=3;
    S3:=F3^2;              mulcount+:=3;
    J0:=f1*f4;             mulcount+:=3;
    J1:=f2*f5;             mulcount+:=3; 
    J2:=f0*f5;             mulcount+:=3; 
    J3:=f1*f6;             mulcount+:=3;
    H0:=J0*f4;             mulcount+:=3; 
    H1:=J1*f2;             mulcount+:=3; 
    H2:=J2*f4;             mulcount+:=3; 
    H3:=J3*f2;             mulcount+:=3;
    G0:=J2*J1;             mulcount+:=3;
    G1:=J0*J3;             mulcount+:=3;
    G0:=G0+G1;             //A 
    G1:=H2+H3;             //A
    G1:=f3*G1;             mulcount+:=3; 
    K0:=f0*f4;             mulcount+:=3;
    K1:=f2*f6;             mulcount+:=3;
    K2:=f4^2;              mulcount+:=3;
    K0:=K0*K2;             mulcount+:=3;
    G2:=f2^2;              mulcount+:=3;
    G2:=G2*K1;             mulcount+:=3;
    G2:=G2+K0;             //A
    G3:=H0+H1;             //A
    G3:=f3*G3;             mulcount+:=3;
    F15:=15*F0;            //5A
    F33:=3*F3;             //2A
    F99:=3*F33;            //2A
    G0:=5*G0;              //3A
    F51:=5*F1;             //3A
    G1:=3*G1;              //2A
    I2:=F15+F2;            //A
    I2:=I2+I2;             //A
    I2:=F51-I2;            //A
    I2:=4*I2;              //2A
    I2:=I2+F33;            //A
    I24:=4*I2;             //2A
    O1:=4*F51;             //2A
    O1:=O1-F2;             //A
    O1:=O1-F99;            //A
    F150:=F15+F0;          //A
    I4:=G0-G1;             //A
    I4:=I4+G2;             //A
    I4:=5*I4;              //3A
    I4:=I4-G2;             //A
    I4:=I4-G3;             //A
    I4:=3*I4;              //2A
    I4:=I4+S2;             //A
    F24:=4*F2;             //2A
    I6:=H2^2;              mulcount+:=3;                   
    H3:=H3^2;              mulcount+:=3;
    I6:=I6+H3;             //A
    I6:=I6+I6;             //A
    H2:=J2^2;              mulcount+:=3;
    H2:=f5*H2;             mulcount+:=3;
    H3:=J3^2;              mulcount+:=3;
    H3:=f1*H3;             mulcount+:=3;
    H2:=H2+H3;             //A
    H2:=f3*H2;             mulcount+:=3;
    H2:=5*H2;              //3A
    H2:=H2-I6;             //A              
    H2:=25*H2;             //6A
    H0:=H0^2;              mulcount+:=3;
    H1:=H1^2;              mulcount+:=3;
    H0:=H0+H1;             //A
    H0:=H0+H0;             //A
    H2:=H2-H0;             //A
    H2:=9*H2;              //4A
    I6:=F4-S2;             //A
    S2:=S2+S2;             //A
    I6:=I6-S2;             //A
    I6:=F24*I6;            mulcount+:=3;
    I6:=H2+I6;             //A
    O2:=F15-F2;            //A
    H0:=O2-F24;            //A
    H0:=3*H0;              //2A  
    H0:=H0+F51;            //A                 
    H0:=H0-O1;             //A
    H0:=9*H0;              //4A
    H0:=F0*H0;             mulcount+:=3;     
    I4:=I4+H0;             //A         
    H0:=F1*O1;             mulcount+:=3;
    I4:= I4-H0;            //A
    H0:=F24+F24;           //A
    H0:=H0+H0;             //A
    H0:=F99+H0;            //A
    H1:=F51+F24;           //A
    H1:=5*H1;              //3A
    H1:=F99-H1;            //A
    H1:=H1+H1;             //A
    H1:=H1-F51;            //A
    H1:=H1-I2;             //A
    H2:=H1+H1;             //A
    H2:=H2-I2;             //A
    H2:=H2+H2;             //A
    H1:=H1+H2;             //A
    H1:=H1+H1;             //A
    H1:=H1-O2;             //A
    H1:=H1+H1;             //A
    H1:=H1+F33;            //A
    H1:=H1-F51;            //A
    H2:=F0+F0;             //A
    H2:=H2+F150;           //A
    H1:=H1*H2;             mulcount+:=3;
    H3:=F24+H0;            //A
    H3:=H3+H0;             //A
    H3:=H3+H0;             //A
    H3:=3*H3;              //2A
    H3:=H3+H0;             //A      
    H3:=10*H3;             //4A
    H3:=H3+H0;             //A
    H3:=F1*H3;             mulcount+:=3;
    H4:=F4+F4;             //A
    H3:=H3+H4;             //A
    H3:=H3+F4;             //A
    H2:=S2-H4;             //A
    H5:=10*S1;             //4A
    H2:=H5-H2;             //A
    H2:=H2+H2;             //A
    H2:=H2+F4;             //A
    H2:=H2-S3;             //A
    H2:=H2+S1;             //A
    H5:=4*H2;              //2A
    H2:=H5-H2;             //A
    H2:=H5+H2;             //A
    H5:=H5-H3;             //A
    H3:=F4+S3;             //A
    H3:=4*H3;              //2A
    H3:=H3-S1;             //A
    H2:=H2-H3;             //A
    H2:=7*H2;              //4A
    H2:=H2+H5;             //A
    H2:=H1+H2;             //A
    F0:=F0*H2;             mulcount+:=3;
    I6:=I6-F0;             //A
    S1:=4*S1;              //2A
    H4:=H4-S3;             //A
    H4:=H4+F4;             //A
    H4:=H4+S1;             //A
    H4:=5*H4;              //3A
    F3:=F33-F3;            //A
    F3:=F3+F99;            //A
    F3:=F3+F24;            //A
    F3:=F3*F1;             mulcount+:=3;
    F3:=H4-F3;             //A
    F3:=F3-S2;             //A
    F3:=F3+S3;             //A
    F3:=F3+F3;             //A
    F3:=F3-S3;             //A
    F3:=4*F3;              //2A
    F3:=F3+S2;             //A
    F3:=F3-F4;             //A
    F3:=F1*F3;             mulcount+:=3;
    I6:=I6-F3;             //A
    H1:=30*F15;            //6A
    H1:=I24-H1;            //A
    H1:=2*H1;              //A
    H1:=H1+F99;            //A
    H1:=G0*H1;             mulcount+:=3;
    I6:=I6+H1;             //A
    H1:=19*F1;             //6A
    H1:=F24-H1;            //A
    H1:=6*H1;              //3A             
    H1:=F15+H1;            //A
    H1:=H1-F1;             //A
    H1:=H1+F2;             //A
    H1:=H1-F99;            //A
    H1:=H1+H1;             //A
    H1:=H1-F33;            //A
    H1:=H1-I24;            //A
    H1:=G1*H1;             mulcount+:=3;
    I6:=I6+H1;             //A
    H1:=F150+F1;           //A
    H1:=H1+H1;             //A
    H1:=H1+F1;             //A
    H1:=18*H1;             //5A
    H1:=H1+I2;             //A
    H1:=H1+I24;            //A
    H1:=H1+H1;             //A
    H1:=H1*G2;             mulcount+:=3;
    I6:=I6+H1;             //A
    H1:=F51-F24;           //A
    H1:=H1-F24;            //A
    H1:=3*H1;              //2A
    H1:=H1+F24;            //A
    H1:=H1+F150;           //A
    H1:=3*H1;              //2A
    H2:=O2+F1;             //A
    H2:=H2+F99;            //A
    H2:=H2+H2;             //A
    H2:=I24-H2;            //A
    H2:=H2-I2;             //A
    H2:=H2-F33;            //A
    H2:=H2-H1;             //A
    H2:=G3*H2;             mulcount+:=3;
    I6:=I6+H2;             //A

    I2:=2*I2;   I4:=4*I4; I6:=2*I6;  I10:=-I10; 

    invs:=[I2,I4,I6,I10];

    return invs,mulcount;

end function;

//////////////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////////////

IsogenousInvariantsFromWeierstrass:=function(as, mulcount)

    // -----------------------------------------------------------------------------------------------------
    // INPUT: Weierstrass points of a genus 2 curve C and a multiplication count
    // OUTPUT: The Igusa--Clebsch invariants of all the (2,2)-isogenous Jacobians from Jac(C)
    // -----------------------------------------------------------------------------------------------------

    isog_alphas:=[];
    quadratics,mulcount:=QuadraticsFromWeierstrass(as,mulcount);

    for q in quadratics do
        numers:=[];
        denoms:=[];
        invs,mulcount:=InvariantsFromQuadratics(q,mulcount);
        Append(~numers,invs[2]);   
        Append(~numers,invs[1]*invs[2]);      mulcount+:=3; 
        Append(~numers,invs[2]*invs[3]);      mulcount+:=3;   
        Append(~denoms,invs[1]^2);            mulcount+:=3;    
        Append(~denoms,invs[3]);   
        Append(~denoms,invs[4]);

        inv_denoms:=BatchMontgomeryInversion(denoms);
        alphas:=[numers[i]*inv_denoms[i]: i in [1..#numers]];   mulcount+:=3*#numers;
        Append(~isog_alphas, alphas);
    end for;

    return isog_alphas,mulcount;

end function;

//////////////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////////////