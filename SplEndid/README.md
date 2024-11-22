This directory contains code needed to run the algorithms in Section 7 of the extended version of the paper. Note that to run the code, you should be in this directory and change the variable `CURR_DIR` in `endsearcher/getinfo.m` as appropriate.

The only files in this directory are 
- `example.m`: takes as input a prime and the Weierstrass points of an example we wish to find an RM for. It will run `SplEndid` for this example in its most optimised form. It will also compare the results obtained from `SplEndid` to those obtained by running the optimised implementation of the Costello--Smith algorithm. 

The directories are arranged as follows:
- In the directory `instantiate` we have two files. The first, `Fp2functions.m`, contains functions for efficient arithmetic in **F**<sub>p<sup>2</sup></sub>. The second, `instances.m`, sets up a number of instances (as input into `runner.m`) of the general isogeny problem in dimension 2.

- The directory `richelot` contains files which implement the optimised step in the (2,2)-graph (see Section 3).

- The directory `endsearcher` contains files implementing the algorithms detailed in Sections 7.