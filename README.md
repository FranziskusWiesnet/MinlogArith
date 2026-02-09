# Arithmetic in Minlog

This repository provides an overview of number theory in Minlog.
In the folder *minlog* there is a snapshot of Minlog in which all number-theoretic implementations run. The relevant files can be found in examples/arith.
The relevant files are *gcd_nat.scm*, *gcd_pos.scm*, *prime_nat.scm*, *prime_pos.scm*, *fta_nat.scm*, *fta_pos.scm*, *factor_nat.scm*, and *factor_pos.scm*.
In addition, the two library files *nat.scm* and *pos.scm* in the *lib* folder are also required.
In the *test-files* folder, you can find the extracted Haskell files *gcd_pos.hs*, *fta_pos.hs*, and *factor_pos.hs*, as well as documentation of individual tests for the corresponding files, each with the suffix "_test" in the filename.
*factor_pos_added.hs* is a slightly modified version of factor_pos.hs in which the fast square-root function *fastSqrt* was replaced by the standard square-root function *posSqrt*.

## Installation of Minlog
Instructions for installing Minlog are provided on the Minlog website: https://www.mathematik.uni-muenchen.de/~logik/minlog/
The latest version of Minlog can also be found there. The Minlog snapshot in the folder *minlog* of this repository should only be regarded as a backup in case the files mentioned above do not work in a newer version of Minlog.
However, since such updates usually have a reason, we recommend checking the latest Minlog version first even in that case. Usually it is sufficient to insert the files described above into the corresponding folders.

To run this Minlog-shapshot, the same programs are required as for the regular Minlog version, as explained under "Prerequisites" on the Minlog website: Git, a Scheme interpreter, Emacs, and pdfLaTeX.
The only difference is that, instead of cloning the Minlog repository, you clone the present repository using Git commands.
The rest of the installation remains unchanged, and the folder "minlog" of this repository then serves as the Minlog directory.

## Files in the test-files folder
### Haskell files
The files *gcd_pos.hs*, *fta_pos.hs*, and *factor_pos.hs* each contain the extracted terms from the Minlog files *gcd_pos.scm*, *fta_pos.scm*, and *factor_pos.scm*, respectively.
- *gcd_pos.hs* contains the Euclidean algorithm *euclid*, Stein’s algorithm *stein*, the extended Euclidean algorithm *extEuclid*, and the extended Stein algorithm *extStein*.
- *fta_pos.scm* contains the prime factorisation function (*toPrimes*),; the generation of a permutation from two prime factorisations of the same number (*genPms*); and the decomposition of a product $uv = xy$ into numbers $a, b, c, d$ with $ab = u$, $cd = v$, $ac = x$, and $bd = y$ (*prodSplit*)
- *factor_pos.hs* contains the two rounded square-root functions *posSqrt* and *fastSqrt*, as well as Fermat's factorisation algorithm *fermat*.
In the file *factor_pos_added.hs*, the function *fermatPosSqrt* was added for testing purposes by replacing *fastSqrt* with *posSqrt* in Fermat’s factorisation algorithm. This is the only .hs-file that was not produced exclusively by Minlog.
### Test documentation
The files with the suffix "_test.txt" each document runtime tests of the corresponding .hs-file. The tests were run in GHCi, using the command *:set +s* to display timing and memory statistics. Experiments were run on a computer with an Intel Core Ultra 5 125H (Meteor Lake-H) CPU (up to 4.5 GHz), 16 GB DDR5 RAM, running Linux.
### SymPy file
In the Python file *poly_approx.py*, an approximating polynomial was fitted visualised in a plot to some of the measurement results using SymPy.
The source code is provided solely for the sake of transparency. Comparable approximations and visualisations can be produced with most other computer algebra systems.
