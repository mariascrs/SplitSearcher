A1 :=  -4*(r-s-1)^2*(s*r+r-s)^2*(s^2*r+s*r-r-s^2+1)^2*(r^2-s^2*r-s*r-r+s^2)^2
    *(s*r^2+2*r^2-s^2*r-3*s*r-2*r+s^2+s)^2;

A :=   -s^2*(r-1)^2
*(s^6*r^10+12*s^5*r^10+38*s^4*r^10+44*s^3*r^10+193*s^2*r^10+32*s*r^10
            +256*r^10-4*s^7*r^9-42*s^6*r^9-172*s^5*r^9-488*s^4*r^9
            -920*s^3*r^9-1342*s^2*r^9-2472*s*r^9-1856*r^9+6*s^8*r^8
            +60*s^7*r^8+269*s^6*r^8+928*s^5*r^8+2350*s^4*r^8+5512*s^3*r^8
            +11875*s^2*r^8+13640*s*r^8+5312*r^8-4*s^9*r^7-48*s^8*r^7
            -212*s^7*r^7-536*s^6*r^7-1824*s^5*r^7-8108*s^4*r^7-25132*s^3*r^7
            -40712*s^2*r^7-30264*s*r^7-7808*r^7+s^10*r^6+24*s^9*r^6
            +130*s^8*r^6-80*s^7*r^6-1791*s^6*r^6-1492*s^5*r^6+15476*s^4*r^6
            +49616*s^3*r^6+61213*s^2*r^6+33216*s*r^6+6272*r^6-6*s^10*r^5
            -68*s^9*r^5+32*s^8*r^5+2992*s^7*r^5+13154*s^6*r^5+20600*s^5*r^5
            +580*s^4*r^5-35216*s^3*r^5-40670*s^2*r^5-17832*s*r^5-2624*r^5
            +15*s^10*r^4+120*s^9*r^4-650*s^8*r^4-8428*s^7*r^4-29847*s^6*r^4
            -48880*s^5*r^4-37378*s^4*r^4-7604*s^3*r^4+5877*s^2*r^4
            +3256*s*r^4+448*r^4-20*s^10*r^3-140*s^9*r^3+1024*s^8*r^3
            +10108*s^7*r^3+31908*s^6*r^3+50856*s^5*r^3+45088*s^4*r^3
            +22312*s^3*r^3+5784*s^2*r^3+648*s*r^3+15*s^10*r^2+104*s^9*r^2
            -602*s^8*r^2-5560*s^7*r^2-16206*s^6*r^2-24288*s^5*r^2
            -20658*s^4*r^2-9920*s^3*r^2-2437*s^2*r^2-224*s*r^2-6*s^10*r
            -44*s^9*r+80*s^8*r+1068*s^7*r+3020*s^6*r+4204*s^5*r+3216*s^4*r
            +1300*s^3*r+218*s^2*r+s^10+8*s^9+28*s^8+56*s^7+70*s^6+56*s^5
            +28*s^4+8*s^3+s^2)/48;

B1 := (r-s-1)^2*(s^12*r^18+2*s^11*r^18-35*s^10*r^18-210*s^9*r^18-492*s^8*r^18
                -510*s^7*r^18-23*s^6*r^18+626*s^5*r^18+1033*s^4*r^18
                +940*s^3*r^18+380*s^2*r^18+16*s*r^18+12*r^18-2*s^14*r^17
                -22*s^13*r^17-80*s^12*r^17+96*s^11*r^17+1700*s^10*r^17
                +5794*s^9*r^17+9086*s^8*r^17+4236*s^7*r^17-9058*s^6*r^17
                -19924*s^5*r^17-20206*s^4*r^17-12348*s^3*r^17
                -3832*s^2*r^17-296*s*r^17-120*r^17+s^16*r^16+24*s^15*r^16
                +216*s^14*r^16+902*s^13*r^16+1250*s^12*r^16-4852*s^11*r^16
                -27667*s^10*r^16-58418*s^9*r^16-47834*s^8*r^16
                +43012*s^7*r^16+159765*s^6*r^16+200880*s^5*r^16
                +148717*s^4*r^16+69628*s^3*r^16+18280*s^2*r^16+1992*s*r^16
                +540*r^16-4*s^17*r^15-82*s^16*r^15-728*s^15*r^15
                -3448*s^14*r^15-7844*s^13*r^15+2258*s^12*r^15
                +67914*s^11*r^15+193648*s^10*r^15+222614*s^9*r^15
                -92726*s^8*r^15-700320*s^7*r^15-1124326*s^6*r^15
                -1022176*s^5*r^15-597236*s^4*r^15-229888*s^3*r^15
                -54456*s^2*r^15-7248*s*r^15-1440*r^15+6*s^18*r^14
                +122*s^17*r^14+1128*s^16*r^14+5896*s^15*r^14
                +16874*s^14*r^14+12120*s^13*r^14-92769*s^12*r^14
                -365462*s^11*r^14-535754*s^10*r^14+129412*s^9*r^14
                +1981831*s^8*r^14+3950420*s^7*r^14+4395649*s^6*r^14
                +3148432*s^5*r^14+1519424*s^4*r^14+503420*s^3*r^14
                +112084*s^2*r^14+16512*s*r^14+2520*r^14-4*s^19*r^13
                -84*s^18*r^13-792*s^17*r^13-4258*s^16*r^13-12800*s^15*r^13
                -8948*s^14*r^13+95040*s^13*r^13+414938*s^12*r^13
                +663406*s^11*r^13-400838*s^10*r^13-4136918*s^9*r^13
                -9490114*s^8*r^13-12585590*s^7*r^13-10914908*s^6*r^13
                -6433390*s^5*r^13-2640556*s^4*r^13-777712*s^3*r^13
                -166256*s^2*r^13-25200*s*r^13-3024*r^13+s^20*r^12
                +22*s^19*r^12+103*s^18*r^12-504*s^17*r^12-8046*s^16*r^12
                -45418*s^15*r^12-159073*s^14*r^12-359938*s^13*r^12
                -290229*s^12*r^12+1454930*s^11*r^12+7111109*s^10*r^12
                +16767298*s^9*r^12+25295088*s^8*r^12+25960536*s^7*r^12
                +18451249*s^6*r^12+9166890*s^5*r^12+3260698*s^4*r^12
                +873212*s^3*r^12+180208*s^2*r^12+26544*s*r^12+2520*r^12
                +148*s^19*r^11+2854*s^18*r^11+23424*s^17*r^11
                +108172*s^16*r^11+299682*s^15*r^11+438920*s^14*r^11
                -165230*s^13*r^11-3019622*s^12*r^11-10332664*s^11*r^11
                -23157546*s^10*r^11-37448556*s^9*r^11-43921798*s^8*r^11
                -36949416*s^7*r^11-22044658*s^6*r^11-9334712*s^5*r^11
                -2908324*s^4*r^11-718972*s^3*r^11-142256*s^2*r^11
                -19392*s*r^11-1440*r^11-54*s^20*r^10-1684*s^19*r^10
                -18802*s^18*r^10-108810*s^17*r^10-361695*s^16*r^10
                -627404*s^15*r^10+49891*s^14*r^10+3570994*s^13*r^10
                +11906563*s^12*r^10+25768286*s^11*r^10+42627286*s^10*r^10
                +54705088*s^9*r^10+52979878*s^8*r^10+37476650*s^7*r^10
                +18913773*s^6*r^10+6823090*s^5*r^10+1868922*s^4*r^10
                +430808*s^3*r^10+80356*s^2*r^10+9648*s*r^10+540*r^10
                +320*s^20*r^9+6840*s^19*r^9+58166*s^18*r^9+260080*s^17*r^9
                +620826*s^16*r^9+405988*s^15*r^9-2396174*s^14*r^9
                -10017688*s^13*r^9-22779084*s^12*r^9-38367692*s^11*r^9
                -51816246*s^10*r^9-55741726*s^9*r^9-45758988*s^8*r^9
                -27398654*s^7*r^9-11609850*s^6*r^9-3519398*s^5*r^9
                -846384*s^4*r^9-183560*s^3*r^9-31384*s^2*r^9-3112*s*r^9
                -120*r^9-945*s^20*r^8-15942*s^19*r^8-108669*s^18*r^8
                -374880*s^17*r^8-548117*s^16*r^8+749288*s^15*r^8
                +5745716*s^14*r^8+15290828*s^13*r^8+27327788*s^12*r^8
                +38280130*s^11*r^8+44100904*s^10*r^8+40770516*s^9*r^8
                +28550214*s^8*r^8+14314144*s^7*r^8+4956614*s^6*r^8
                +1221200*s^5*r^8+257808*s^4*r^8+53432*s^3*r^8+7976*s^2*r^8
                +584*s*r^8+12*r^8+1728*s^20*r^7+23976*s^19*r^7
                +131772*s^18*r^7+330156*s^17*r^7+79542*s^16*r^7
                -2068700*s^15*r^7-7374460*s^14*r^7-14973966*s^13*r^7
                -22221554*s^12*r^7-26811720*s^11*r^7-26953764*s^10*r^7
                -21546118*s^9*r^7-12713968*s^8*r^7-5160540*s^7*r^7
                -1371218*s^6*r^7-254786*s^5*r^7-48652*s^4*r^7
                -10004*s^3*r^7-1176*s^2*r^7-48*s*r^7-2100*s^20*r^6
                -24216*s^19*r^6-104790*s^18*r^6-154538*s^17*r^6
                +380354*s^16*r^6+2396048*s^15*r^6+6019848*s^14*r^6
                +9948350*s^13*r^6+12655773*s^12*r^6+13440614*s^11*r^6
                +11869561*s^10*r^6+8099714*s^9*r^6+3884521*s^8*r^6
                +1182064*s^7*r^6+202992*s^6*r^6+22132*s^5*r^6+5037*s^4*r^6
                +1104*s^3*r^6+76*s^2*r^6+1728*s^20*r^5+16428*s^19*r^5
                +52152*s^18*r^5+1624*s^17*r^5-474254*s^16*r^5
                -1670240*s^15*r^5-3288644*s^14*r^5-4579422*s^13*r^5
                -5105174*s^12*r^5-4814526*s^11*r^5-3688948*s^10*r^5
                -2070844*s^9*r^5-746134*s^8*r^5-137084*s^7*r^5
                -3128*s^6*r^5+1416*s^5*r^5-306*s^4*r^5-60*s^3*r^5
                -945*s^20*r^4-7190*s^19*r^4-13347*s^18*r^4+45288*s^17*r^4
                +293516*s^16*r^4+752166*s^15*r^4+1217455*s^14*r^4
                +1462456*s^13*r^4+1445112*s^12*r^4+1197506*s^11*r^4
                +766565*s^10*r^4+328038*s^9*r^4+72265*s^8*r^4-484*s^7*r^4
                -3140*s^6*r^4-274*s^5*r^4+25*s^4*r^4+320*s^20*r^3
                +1796*s^19*r^3-322*s^18*r^3-28488*s^17*r^3-108320*s^16*r^3
                -220478*s^15*r^3-302148*s^14*r^3-317160*s^13*r^3
                -275266*s^12*r^3-192706*s^11*r^3-95608*s^10*r^3
                -26134*s^9*r^3-474*s^8*r^3+1624*s^7*r^3+266*s^6*r^3
                -6*s^5*r^3-54*s^20*r^2-148*s^19*r^2+1250*s^18*r^2
                +8538*s^17*r^2+24069*s^16*r^2+40868*s^15*r^2
                +48235*s^14*r^2+43744*s^13*r^2+31846*s^12*r^2
                +17384*s^11*r^2+5738*s^10*r^2+422*s^9*r^2-365*s^8*r^2
                -88*s^7*r^2+s^6*r^2-32*s^19*r-314*s^18*r-1296*s^17*r
                -3002*s^16*r-4404*s^15*r-4424*s^14*r-3244*s^13*r
                -1776*s^12*r-652*s^11*r-94*s^10*r+28*s^9*r+10*s^8*r+s^20
                +6*s^19+25*s^18+80*s^17+166*s^16+212*s^15+166*s^14+80*s^13
                +25*s^12+6*s^11+s^10)/3 ;

B :=  s^2*(r-1)^4
*(s^10*r^14+18*s^9*r^14+111*s^8*r^14+300*s^7*r^14-177*s^6*r^14
            -2478*s^5*r^14-3839*s^4*r^14+3792*s^3*r^14-5280*s^2*r^14
            -6272*s*r^14-1728*r^14-6*s^11*r^13-98*s^10*r^13-624*s^9*r^13
            -1464*s^8*r^13+1902*s^7*r^13+18366*s^6*r^13+26532*s^5*r^13
            -16676*s^4*r^13-9948*s^3*r^13+54432*s^2*r^13+52000*s*r^13
            +10368*r^13+15*s^12*r^12+228*s^11*r^12+1486*s^10*r^12
            +3738*s^9*r^12-5679*s^8*r^12-49344*s^7*r^12-48408*s^6*r^12
            +145350*s^5*r^12+277210*s^4*r^12+20916*s^3*r^12-250344*s^2*r^12
            -164864*s*r^12-25920*r^12-20*s^13*r^11-300*s^12*r^11
            -1992*s^11*r^11-6002*s^10*r^11+930*s^9*r^11+32850*s^8*r^11
            -89868*s^7*r^11-745998*s^6*r^11-1519338*s^5*r^11
            -1180438*s^4*r^11+63216*s^3*r^11+577872*s^2*r^11+258720*s*r^11
            +34560*r^11+15*s^14*r^10+250*s^13*r^10+1731*s^12*r^10
            +6576*s^11*r^10+13972*s^10*r^10+54810*s^9*r^10+420411*s^8*r^10
            +1748340*s^7*r^10+3733002*s^6*r^10+4096302*s^5*r^10
            +1746995*s^4*r^10-541116*s^3*r^10-724152*s^2*r^10-201600*s*r^10
            -25920*r^10-6*s^15*r^9-138*s^14*r^9-1100*s^13*r^9-5688*s^12*r^9
            -24228*s^11*r^9-103478*s^10*r^9-481266*s^9*r^9-1728696*s^8*r^9
            -3819780*s^7*r^9-4624038*s^6*r^9-2138778*s^5*r^9+1138388*s^4*r^9
            +1651332*s^3*r^9+546624*s^2*r^9+47712*s*r^9+10368*r^9+s^16*r^8
            +48*s^15*r^8+540*s^14*r^8+3958*s^13*r^8+25164*s^12*r^8
            +107292*s^11*r^8+276760*s^10*r^8+373374*s^9*r^8-285393*s^8*r^8
            -2988228*s^7*r^8-7722468*s^6*r^8-10625970*s^5*r^8
            -8071513*s^4*r^8-3039072*s^3*r^8-354072*s^2*r^8+35840*s*r^8
            -1728*r^8-8*s^16*r^7-180*s^15*r^7-1782*s^14*r^7-16538*s^13*r^7
            -100482*s^12*r^7-279948*s^11*r^7+71098*s^10*r^7+3149958*s^9*r^7
            +11614830*s^8*r^7+23874996*s^7*r^7+31304718*s^6*r^7
            +26292966*s^5*r^7+13357694*s^4*r^7+3539628*s^3*r^7
            +288144*s^2*r^7-26656*s*r^7+28*s^16*r^6+420*s^15*r^6
            +5256*s^14*r^6+52510*s^13*r^6+264915*s^12*r^6+480144*s^11*r^6
            -1229195*s^10*r^6-9214224*s^9*r^6-25263900*s^8*r^6
            -41037432*s^7*r^6-42810066*s^6*r^6-28656486*s^5*r^6
            -11666965*s^4*r^6-2521572*s^3*r^6-191592*s^2*r^6+5120*s*r^6
            -56*s^16*r^5-672*s^15*r^5-10746*s^14*r^5-103530*s^13*r^5
            -457596*s^12*r^5-717258*s^11*r^5+1654472*s^10*r^5
            +10654482*s^9*r^5+25113960*s^8*r^5+34743164*s^7*r^5
            +30571434*s^6*r^5+17106594*s^5*r^5+5770592*s^4*r^5
            +1026672*s^3*r^5+67392*s^2*r^5+70*s^16*r^4+756*s^15*r^4
            +13698*s^14*r^4+124470*s^13*r^4+517278*s^12*r^4+913512*s^11*r^4
            -426058*s^10*r^4-5462820*s^9*r^4-12301233*s^8*r^4
            -15195844*s^7*r^4-11596590*s^6*r^4-5489502*s^5*r^4
            -1515205*s^4*r^4-207636*s^3*r^4-9024*s^2*r^4-56*s^16*r^3
            -588*s^15*r^3-10530*s^14*r^3-89898*s^13*r^3-367494*s^12*r^3
            -773988*s^11*r^3-672688*s^10*r^3+552108*s^9*r^3+2216952*s^8*r^3
            +2788676*s^7*r^3+1933938*s^6*r^3+773790*s^5*r^3+163238*s^4*r^3
            +13260*s^3*r^3+28*s^16*r^2+300*s^15*r^2+4617*s^14*r^2
            +36448*s^13*r^2+148962*s^12*r^2+357312*s^11*r^2+535566*s^10*r^2
            +506856*s^9*r^2+287916*s^8*r^2+79972*s^7*r^2-351*s^6*r^2
            -3624*s^5*r^2+1054*s^4*r^2+528*s^3*r^2-8*s^16*r-90*s^15*r
            -996*s^14*r-6770*s^13*r-27000*s^12*r-68436*s^11*r-116760*s^10*r
            -138132*s^9*r-114120*s^8*r-64850*s^7*r-24228*s^6*r-5370*s^5*r
            -536*s^4*r+s^16+12*s^15+66*s^14+220*s^13+495*s^12+792*s^11
            +924*s^10+792*s^9+495*s^8+220*s^7+66*s^6+12*s^5+s^4)/864 ;

B2 := s^4*(r-1)^6*r^7*(r-s-1)*(r^2-s^2*r-2*s*r-r+s^2+s)/4;

return [-24*B1/A1, -12*A, 96*(A/A1)*B1-36*B, -4*A1*B2];