This directory contains code needed to run the algorithms in the paper. Note that to run the code, you should be in this directory. 

The only files in this directory are 
- `example.m`: takes as input a prime and the Weierstrass points of an example we wish to find a splitting for. It will run `SplitSearcher` for this example in its most optimised form. 

- `extendedexample.m`: this gives a more extended example which will generate a number of examples and proceed to solve them using both `SplitSeacher` and the Costello--Smith algorithm. As output, we also provide a comparison between these two algorithms. Note that larger primes will not terminate.  

The directories are arranged as follows:
- In the directory `instantiate` we have two files. The first, `Fp2functions.m`, contains functions for efficient arithmetic in **F**<sub>p<sup>2</sup></sub>. The second, `instances.m`, sets up a number of instances (as input into `runner.m`) of the general isogeny problem in dimension 2.

- The directory `richelot` contains files which implement the optimised step in the (2,2)-graph (see Section 3).

- The directory `splitsearcher` contains files implementing the algorithms detailed in Sections 5 and 6.  