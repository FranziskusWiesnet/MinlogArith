
This repository provides an overview of number theory in Minlog.
In the folder *minlog* there is a snapshot of Minlog in which all number-theoretic implementations run. The relevant files can be found in examples/arith.
The relevant files are *gcd_nat.scm*, *gcd_pos.scm*, *prime_nat.scm*, *prime_pos.scm*, *fta_nat.scm*, *fta_pos.scm*, *factor_nat.scm*, and *factor_pos.scm*.
In addition, the two library files *nat.scm* and *pos.scm* in the *lib* folder are also required.
In the *test-files* folder, you can find the extracted Haskell files *gcd_pos.hs*, *fta_pos.hs*, and *factor_pos.hs*, as well as documentation of individual tests for the corresponding files, each with the suffix "_test" in the filename.
*factor_pos_added.hs* is a slightly modified version of factor_pos.hs in which the fast square-root function *fastSqrt* was replaced by the standard square-root function *posSqrt*.
