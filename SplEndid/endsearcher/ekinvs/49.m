A1 := -(r*s-1)^2/16;
A := -(144*r^4*s^6+912*r^4*s^5-96*r^3*s^5-24*r^2*s^5+2320*r^4*s^4-856*r^3*s^4
            -88*r^2*s^4+16*r*s^4+s^4+2720*r^4*s^3-1872*r^3*s^3+128*r^2*s^3
            +20*r*s^3+1400*r^4*s^2-1336*r^3*s^2+198*r^2*s^2+232*r^4*s
            -220*r^3*s+r^4)/48;
B1 := (12*r^6*s^6+24*r^6*s^5-48*r^5*s^5+12*r^4*s^5+12*r^6*s^4-84*r^5*s^4+92*r^4*s^4
        -28*r^3*s^4+r^2*s^4-36*r^5*s^3+116*r^4*s^3-90*r^3*s^3+44*r^2*s^3
        -2*r*s^3+37*r^4*s^2-76*r^3*s^2+84*r^2*s^2-40*r*s^2+s^2-14*r^3*s
        +32*r^2*s-50*r*s+12*s+r^2-12*r+12)/192;
B := -(12960*r^6*s^8-2592*r^5*s^8+432*r^4*s^8+72000*r^6*s^7-35280*r^5*s^7
            +6552*r^4*s^7-432*r^3*s^7+36*r^2*s^7+166888*r^6*s^6
            -122208*r^5*s^6+28368*r^4*s^6-3956*r^3*s^6+36*r^2*s^6-24*r*s^6
            -s^6+209352*r^6*s^5-195360*r^5*s^5+48348*r^4*s^5-5952*r^3*s^5
            +432*r^2*s^5-30*r*s^5+153360*r^6*s^4-170892*r^5*s^4
            +41568*r^4*s^4-228*r^3*s^4+417*r^2*s^4+64480*r^6*s^3
            -84720*r^5*s^3+22956*r^4*s^3+2180*r^3*s^3+13140*r^6*s^2
            -20196*r^5*s^2+7473*r^4*s^2+516*r^6*s-534*r^5*s-r^6)/864;
B2 := 16*r^5*s^7*(s+1)^4*(r*s+r-1);

return([-24*B1/A1, -12*A, 96*(A/A1)*B1-36*B, -4*A1*B2]);