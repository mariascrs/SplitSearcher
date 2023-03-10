A1 := -s^10*(s+2)^2*(s-r)^5*(s+r)^2*(s+r+2)*(s^2+2*s-r^2)^2*(s^2+r*s+2*s-r^2)^2
    *(2*s^2+2*s-r^2);
A := (5*s^12+30*s^11-49*r^2*s^10-52*r*s^10+6*s^10-30*r^3*s^9-320*r^2*s^9-180*r*s^9
    -180*s^9+87*r^4*s^8+4*r^3*s^8-560*r^2*s^8+24*r*s^8-225*s^8+90*r^5*s^7
    +648*r^4*s^7+252*r^3*s^7-300*r^2*s^7+360*r*s^7-19*r^6*s^6+380*r^5*s^6
    +1600*r^4*s^6+64*r^3*s^6-156*r^2*s^6-60*r^7*s^5-282*r^6*s^5+580*r^5*s^5
    +1948*r^4*s^5-360*r^3*s^5-25*r^8*s^4-336*r^7*s^4-1048*r^6*s^4
    +264*r^5*s^4+1322*r^4*s^4-80*r^8*s^3-668*r^7*s^3-1596*r^6*s^3
    -232*r^5*s^3-6*r^8*s^2-368*r^7*s^2-956*r^6*s^2+112*r^8*s+232*r^7*s-r^8)
/48;
B1 :=  s^10*(s+2)^2*(s-r)^5*(s+r)^2*(s+r+2)
*(5*s^16+10*r*s^15+60*s^15+3*r^2*s^14+134*r*s^14+358*s^14-18*r^3*s^13
        +46*r^2*s^13+948*r*s^13+1474*s^13-79*r^4*s^12-338*r^3*s^12
        +237*r^2*s^12+4228*r*s^12+4512*s^12-48*r^5*s^11-844*r^4*s^11
        -2746*r^3*s^11+14*r^2*s^11+11944*r*s^11+9872*s^11+197*r^6*s^10
        +46*r^5*s^10-3665*r^4*s^10-11888*r^3*s^10-3736*r^2*s^10
        +20976*r*s^10+14496*s^10+180*r^7*s^9+1856*r^6*s^9+2842*r^5*s^9
        -7310*r^4*s^9-29032*r^3*s^9-13400*r^2*s^9+22048*r*s^9+13344*s^9
        -238*r^8*s^8+586*r^7*s^8+6573*r^6*s^8+13456*r^5*s^8-3948*r^4*s^8
        -39840*r^3*s^8-20944*r^2*s^8+12672*r*s^8+6912*s^8-228*r^9*s^7
        -1930*r^8*s^7-1344*r^7*s^7+10040*r^6*s^7+27224*r^5*s^7
        +8368*r^4*s^7-28544*r^3*s^7-15680*r^2*s^7+3072*r*s^7+1536*s^7
        +173*r^10*s^6-662*r^9*s^6-5180*r^8*s^6-8056*r^7*s^6+4008*r^6*s^6
        +25744*r^5*s^6+13632*r^4*s^6-8320*r^3*s^6-4608*r^2*s^6
        +144*r^11*s^5+1120*r^10*s^5+484*r^9*s^5-5046*r^8*s^5-11752*r^7*s^5
        -4920*r^6*s^5+9312*r^5*s^5+5792*r^4*s^5-81*r^12*s^4+262*r^11*s^4
        +1991*r^10*s^4+2764*r^9*s^4-204*r^8*s^4-5600*r^7*s^4-3920*r^6*s^4
        -46*r^13*s^3-358*r^12*s^3-254*r^11*s^3+834*r^10*s^3+2000*r^9*s^3
        +1520*r^8*s^3+23*r^14*s^2-22*r^13*s^2-309*r^12*s^2-456*r^11*s^2
        -328*r^10*s^2+6*r^15*s+50*r^14*s+70*r^13*s+34*r^12*s-3*r^16-6*r^15
        -r^14) /12;
B := -(70*s^18+630*s^17-219*r^2*s^16-12*r*s^16+2556*s^16-252*r^3*s^15-2382*r^2*s^15
        +828*r*s^15+6966*s^15-381*r^4*s^14-3972*r^3*s^14-15399*r^2*s^14
        +3996*r*s^14+14310*s^14+630*r^5*s^13-966*r^4*s^13-22890*r^3*s^13
        -63288*r^2*s^13+540*r*s^13+18468*s^13+2444*r^6*s^12+14220*r^5*s^12
        +26577*r^4*s^12-47764*r^3*s^12-140580*r^2*s^12-18792*r*s^12
        +10206*s^12+378*r^7*s^11+18318*r^6*s^11+84234*r^5*s^11
        +175986*r^4*s^11+4068*r^3*s^11-143532*r^2*s^11-21384*r*s^11
        -3153*r^8*s^10-11424*r^7*s^10+17226*r^6*s^10+177984*r^5*s^10
        +410202*r^4*s^10+118224*r^3*s^10-46980*r^2*s^10-1764*r^9*s^9
        -27546*r^8*s^9-94554*r^7*s^9-159854*r^6*s^9+52392*r^5*s^9
        +384768*r^4*s^9+93528*r^3*s^9+1041*r^10*s^8-5412*r^9*s^8
        -68421*r^8*s^8-223284*r^7*s^8-467400*r^6*s^8-228576*r^5*s^8
        +104850*r^4*s^8+1008*r^11*s^7+10842*r^10*s^7+17214*r^9*s^7
        -696*r^8*s^7-113016*r^7*s^7-416448*r^6*s^7-176400*r^5*s^7
        +196*r^12*s^6+6588*r^11*s^6+34203*r^10*s^6+69228*r^9*s^6
        +177138*r^8*s^6+180672*r^7*s^6-87352*r^6*s^6+1092*r^12*s^5
        +15096*r^11*s^5+34998*r^10*s^5+30300*r^9*s^5+147468*r^8*s^5
        +150384*r^7*s^5+3210*r^12*s^4+19680*r^11*s^4+2076*r^10*s^4
        -71256*r^9*s^4-4878*r^8*s^4+5728*r^12*s^3+25524*r^11*s^3
        +9612*r^10*s^3-45224*r^9*s^3+3966*r^12*s^2+19536*r^11*s^2
        +24156*r^10*s^2-528*r^12*s-1032*r^11*s-2*r^12)/1728;
B2 := 1/1024;
return([-24*B1/A1, -12*A, 96*(A/A1)*B1-36*B, -4*A1*B2]);