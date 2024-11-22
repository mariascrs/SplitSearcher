This directory contains files required to run the algorithms in Sections 5 and 6. 

The files are
- `graphcounts.m`: the main function in this file is `NodesRevealed`, which counts the nodes revealed by `SplitSearcher` per step for a given N.

- `invs.m`: this file contains the function `InvariantsFromWeierstrassPoints`, which given the Weierstrass points of a genus 2 curve, will compute its Igusa--Clebsch invariants alpha as normalised in Lemma 2. 

- `precomp.m`: the functions in this file perform the precomputation needed to run `SplitSeacher` optimally. The main function is `SplitSearcherPrecomp`.

- `splitdetection.m`: this file contains all the functions need run `IsSplit`, as described in Algorithm 3. In addition there are methods which use resultants and the polynomials *F<sub>N</sub>* from Section 4.4. At the bottom of this file, we also include code for those wishing to run detection for only one *N* (we do not use this for our application).

- `splitseacher.m`: this file runs `SplitSeacher` as described in Algorithm 4. 

- `ecsfromrs.m`: this file contains the function `Genus1Curves` called in post-computation to compute the *j*-invariants of the elliptic curves that form the (*N*,*N*)-isogenous product, from the *r*, *s*, *N* output by `SplitSearcher` when a splitting is found.


The subdirectories are
- `divinfo`

- `imageeqns`

- `kumarinvs`

- `normalisedinvs`

- `precompres`

- `splitafter22`

Each of these contains a `README.md`.


N.B. In the files stored in subdirectories we often replace &alpha;<sub>1</sub>, &alpha;<sub>2</sub>, &alpha;<sub>3</sub> from Section 5.1 with `i1, i2, i3` in the name of storage (some of these files are rather large).