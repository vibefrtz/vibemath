# Numerical validation

`check_numerics.py` sieves to `10^8` (numpy; a few seconds, ~100 MB) and checks

1. the first terms of OEIS A052034;
2. every numerical claim of §6.5 of the paper — `mu_S`, `kappa_S`, `log_3(10^8)`,
   the secondary term, the mean and variance of `omega(S(p))` over the
   eight-digit primes, the Gaussian-weighted comparison, and the drift of
   `sum 1/p - log(log_2 X + kappa_S)` on `[10^4, 10^8]`;
3. **the axiom `mmr` itself**, for `g = S`, `b = 10`, `d_S = 1`: the main term
   summed over all `k` against `pi(x)`, and the largest pointwise discrepancy
   against the error term the axiom permits.

`output.txt` records the expected output.

Item 3 is the important one. It cannot prove the axiom, but a transcription
error in the normalisation or in the exponent would show up immediately as a
main term that does not sum to `pi(x)`.
