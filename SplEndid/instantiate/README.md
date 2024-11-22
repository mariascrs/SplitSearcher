This directory contains four files:

- `Fp2functions.m` contains code needed for operations in **F**<sub>p<sup>2</sup></sub> using Tonelli--Shanks (e.g., taking square roots, inversions)

- `instances.m` generates contains the function `GetSupersingularWeierstrassPoints` which allows us to generate pseudo-random superspecial genus 2 Jacobians over **F**<sub>p<sup>2</sup></sub> (NB: the prime must be *5* or *7* mod *8* since we walk pseudo-randomly from the starting curve *y<sup>2</sup> = x<sup>5</sup>+x*). 

- `invs.m` contains the function `InvariantsFromWeierstrassPoints`, which given the Weierstrass points of a genus 2 curve, will compute its Igusa--Clebsch invariants alpha as normalised in Lemma 2.  

- `invsfromquads.m` contains the function `QuadraticsFromWeierstrass` that returns all quadratic splittings of Weierstrass points.