# Numerical validation

`check_numerics.py` reproduces every number quoted in §5.5 of the paper:

* the count `629304` of primes `p ≤ 10⁸` whose number of zero decimal digits
  is prime, the reciprocal sum `0.051`, and the drifting differences
  `−0.99` (at `10⁷`) and `−1.02` (at `10⁸`) against `log₃x`;
* the three shell proportions `0.11336 / 0.08126 / 0.05294` against the
  binomial model values `0.11305 / 0.08101 / 0.05220` of the
  `Bin(m−2, 1/10)` model the paper states (an earlier draft's `(7, 1/10)`
  parenthetical was a slip, corrected in the revision);
* the full base-3 table for `m = 10, …, 16`, including the forced
  `F(p) = 2` rows `696 / 9118 / 51468` on the odd shells.

It also spot-checks the carry-free identities of Lemma 7.2 and Remark 7.3
against direct digit-sum computation in several bases, counts the `P₂`'s
in the short intervals `(z − z^{0.455}, z]` as a sanity check on the
transcription of the `hhbr` axiom, and verifies the binary-endpoint
arithmetic of Remark 2.3 in exact rationals, the lattice density
`ρ_{s₁₀,□}` (quadratic residues mod 9, normalisation, `κ = 1`), the `κ_m`
product formula of Theorem 5.12 against direct counts over many moduli, the
finite-height portrait of the square local limit theorem (the mod-9 lattice
of `s₁₀(n²)` up to `2·10⁶`, with the Gaussian peak as an illustration), and
the exact reciprocal identity `S₀ = S − S(·/10)/10` of §8 in exact rational
arithmetic.

New in this revision, each mirroring a Lean statement:

* the **multiplicativity** of `N(c,·)` across coprime moduli and the **mean
  formula (61)** as exact rational identities, over `d ≤ 30` and several `A`
  (`DSS/KappaM.lean`);
* the **finite Fourier identity (37)**, `∑_j η_j e(−jk/d) = ρ_{g,□}(k)`, in
  complex arithmetic at `d = 9` (`DSS/RhoFourier.lean`);
* **Lemma 4.3** — the Gaussian mass on a residue class — checked *against
  the explicit error bound the Lean proof supplies*,
  `(4/M)·exp(−2π²s/M²)`, at four `(s, M, c, y)`; and the theta bound
  `|∑ₙ e^{−α(n+β)²} − √(π/α)| ≤ √(π/α)·2t/(1−t)` behind it
  (`DSS/GaussSum.lean`);
* the **`ρ/σ` scaling identity** in the proof of Theorem 2.1, i.e. that the
  main term of eq. (14) at `k = hℓ` for `h·g̃` is the main term of eq. (5) at
  `ℓ` for `g̃` (`DSS/SquareGeneral.lean`);
* the **degree-one affine identity** `s₁₀(u·10^k − c) = Ak + C` of
  Proposition 7.8(i) and the Dirichlet count behind the infinitude half of
  Theorem 7.5 (`DSS/Blocking.lean`);
* the **output discrepancy of Theorem 1.2** at finite height: the sum
  `∑_{m ≤ Q_η(L)} max_a |Δ_{s₁₀,□}(x;m,a)|` against `x·L^{−1/2+ε}`, with an
  illustration at three heights showing the relative discrepancy decreasing
  at roughly the predicted `L^{−1/2}` rate (`DSS/OutputLevel.lean`).

60 checks in all.

Run (a few seconds; needs `numpy`):

```sh
uv run --with numpy python check_numerics.py
```

`output.txt` is the committed output of a run; it ends `ALL CHECKS PASSED`.
