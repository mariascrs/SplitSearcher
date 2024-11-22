This directory contains files required to run the algorithms in Section 7. 

The files are:
- `ecsfrommrs.m`: this file contains the function `Genus1Curves` called in post-computation to compute the *j*-invariants of the elliptic curves that form the (*N*,*N*)-isogenous product, from the *r*, *s*, *N* output by `SplitSearcher` when a splitting is found.

- `enddetection.m`: this file contains all the functions need run `HasEnd`, a generalisation of Algorithm 3. In addition there are methods which use resultants and the polynomials *F<sub>N</sub>* from Section 4.4. At the bottom of this file, we also include code for those wishing to run detection for only one *D* (we do not use this for our application).

- `endsearcher.m`: this file runs `SplEndid`, a generalisation of `SplitSeacher` from Algorithm 4, as desribed in Section 7. 

- `getinfo.m`: this file contains code needed to extract the correct information from `ekinvs/`, `normalisedinvs/`, and `precompres/` for each D. Note that in this file, the variable CURR_DIR must be changed so that the code runs.

- `graphcounts.m`: the main function in this file is `NodesRevealed`, which counts the nodes revealed by `SplEndid` per step for a given D when D = N^2 (i.e., this is equivalent to the nodes revealed when running SplitSeacher for N). We also implement a function `HeuristicNodesRevealed`, which uses a (currently inaccurate) heuristic to compute the nodes revealed when D is not a square. This could eventually be used to compute the optimal set of D's to run `SplEndid` on once the heuristic is more accurate. 

- `helpers.m`: this file contains helper functions (for multivariate polynomial arithmetic) needed to run `SplEndid`. For example, we implement the function `FastPolyGCD`, which computes the gcd of two polynomials with no inversions.

- `precomp.m`: the functions in this file perform the precomputation needed to run `SplitSeacher` optimally. The main function is `SplitSearcherPrecomp`.

The subdirectories are
- `divinfo`

- `ekinvs`

- `normalisedinvs`

- `precompres`

Each of these contains a `README.md`.

N.B. In the files stored in subdirectories we often replace &alpha;<sub>1</sub>, &alpha;<sub>2</sub>, &alpha;<sub>3</sub> from Section 5.1 with `i1, i2, i3` in the name of storage (some of these files are rather large).