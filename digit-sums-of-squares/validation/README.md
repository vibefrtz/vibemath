# Numerical validation

`check_numerics.py` reproduces every number quoted in §5.4 of the paper:

* the count `629304` of primes `p ≤ 10⁸` whose number of zero decimal digits
  is prime, the reciprocal sum `0.051`, and the drifting differences
  `−0.99` (at `10⁷`) and `−1.02` (at `10⁸`) against `log₃x`;
* the three shell proportions `0.11336 / 0.08126 / 0.05294` against the
  binomial model values `0.11305 / 0.08101 / 0.05220` — see the note in the
  script and in `VERIFICATION.md` §5.6: the quoted model values are those of
  `Bin(m−2, 1/10)`, not of the `(7, 1/10)` stated in the manuscript's prose;
* the full base-3 table for `m = 10, …, 16`, including the forced
  `F(p) = 2` rows `696 / 9118 / 51468` on the odd shells.

It also spot-checks the carry-free identities of Lemma 7.2 and Remark 7.3
against direct digit-sum computation in several bases, and counts the `P₂`'s
in the short intervals `(z − z^{0.455}, z]` as a sanity check on the
transcription of the `hhbr` axiom.

Run (about two minutes; needs `numpy`):

```sh
uv run --with numpy python check_numerics.py
```

`output.txt` is the committed output of a run; it ends `ALL CHECKS PASSED`.
