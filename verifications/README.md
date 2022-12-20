This directory contains code needed to verify the claims made in the paper. 

The only file in this directory is 

- `lemma3.m`: verifies the claim in Lemma 3.

The only sub-directory is `humberts` which contains the equations *F<sub>N</sub>(I<sub>2</sub>, I<sub>4</sub>, I<sub>6</sub>, I<sub>10</sub>)* from Section 4.4. These may be found in papers of Shaska together with Magaard, Volklein, Wijesiri, Wolf, and Woodland when [*N=2*](https://doi.org/10.1007/978-3-642-18487-1_42), [*N = 3*](https://doi-org.ezp.lib.cam.ac.uk/10.1007/3-540-45455-1_17), [*N = 4*](http://www.ams.org/mathscinet-getitem?mr=2470579) ([arXiv](https://doi.org/10.48550/arXiv.1301.4596)), and [*N = 5*](https://doi.org/10.1515/FORUM.2009.027). When *N = 2, 3, 4* these can also be found at http://www.cecm.sfu.ca/~nbruin/splitigusa/, which is attached to the paper [*The arithmetic of genus 2 curves with (4,4)-split Jacobians*](https://doi.org/10.4153/CJM-2011-039-3) by Nils Bruin and Kevin Doerksen. 

To load (for example) the equation for *F<sub>5</sub>* one can run
```
> ZZ := Integers();
> P<I2,I4,I6,I10> := PolynomialRing(ZZ, [1,2,3,5]);
> F_5 := eval Read("humberts/5.m");
```
