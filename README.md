# On a classification of planar functions in characteristics three

This repository contains the code used for the classification and expansion searches carried out in [1](#1).

# Software dependencies

To run this code, you will need the [MAGMA](http://magma.maths.usyd.edu.au/magma/) computational algebra system.
Running the detached searches was only tested on Linux and MacOS. It requires the [`screen` utility](https://linux.die.net/man/1/screen).

# Content of the repository

The main project directory contains the following relevant files for some of the tasks needed for the manuscript.

* `function_splits.m`: find splits for every representative, if they exist.
* `compute_invariants.m`: populate the table of invariants for all functions representatives.
* `compute_orbits.m`: find the orbits. Note that not restricting the dimension and range will result in a very long computation, likely to not finish. Edit the header of the file to restrict the search.
* `classification.m`: This will run a classification of the known families for a particular n (by default n=8), including trying to split isotopy classes into strong isotopy classes, and computing intersections of the families.
* `class_n_10_*.m`: These are tailored files for parts of the classification in dimension 10 that were too expensive to carry out as we did for the other dimensions.

## Detached run for expansion search and representatives search

The two scripts `launch_searches.sh` and `launch_representatives.sh` allow to specify sets of parameters for a number of searches,
and then launch them in detached screens to carry out the searches in parallel.

The execution is logged in the `logs` sub-directory. 

### Detailed report v.s. memory efficiency

There are two main versions of the parallel searches. `*.tpl` and `*_mem.tpl`. 

* `*_rep.tpl`: It can require a high amount of RAM, but it will report all the planar functions generated, their invariants, and their equivalence class. This is particularly useful for finding alternative representatives of known families, or for low dimension.
* `*_mem.tpl`: It requires a very small amount of RAM, but the results will be much less structured, and it will only report the first representative found, and only for novel inequivalent planar functions.

The detailed report will be saved in three subdirectories:
* `expansions`: for the raw data on all planar functions generated.
* `equivalence_test`: for the planar functions divided into buckets using invariants.
* `inequivalent`: for the planar functions divided into equivalence classes, including novel inequivalent planar functions.

## `lib` directory

This directory contains the main logic of the code. Notable files are:

* `representatives.m`, with the classification of the known families,
* `invariantTable.m`, with the data regarding the invariants in an easy to digest form,
* `familiesPlanar.m`, with the methods to generate members of all known families,
* `dupeq.m`, with the linear equivalence test, as implemented in [nskal/dupeq](https://github.com/nskal/dupeq/tree/main),
* `semifields_*.m`, with the algorithms for computing the semifields and their nuclei.

## References
<a id="1">[1]</a>
S. Andreoli, L. Budaghyan, R.S. Coulter, A. Haukenes, N. Kaleyski, E. Piccione. "On a classification of planar functions in characteristic three". arXiv [2407.03170](https://arxiv.org/abs/2407.03170)
