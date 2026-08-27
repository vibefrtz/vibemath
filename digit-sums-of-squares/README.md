# DSS — a Lean verification of *Prime values of digital functions and prescribed digit sums of squares*

This folder accompanies the paper *Prime values of digital functions and
prescribed digit sums of squares*
([`paper_anonymous.pdf`](paper_anonymous.pdf), source in
[`paper_anonymous.tex`](paper_anonymous.tex)), the sequel to
[*Prime values of digital functions along the primes*](../prime-values-digital-functions/).
It contains a Lean 4 formalisation in which

* **the entire squares half of the paper — Theorem 1.10, its corollaries, and
  every lemma feeding them — is machine-checked with no axioms at all** beyond
  Lean's three built-in ones.  In particular the theorem of Bose and Chowla on
  dense Sidon sets, which the paper quotes from the literature, is *proved*
  inside Lean (in the field with `p²` elements, via
  [`DSS/BoseChowla.lean`](lean/DSS/BoseChowla.lean)) rather than assumed;
* the almost-prime theorem along the primes (**Corollary 1.3**: `g(p)` is a
  `P₂` for `≫ π(x)/log log x` primes when `μ_g > 0` and `d_g = 1`) is proved
  from exactly **two** results quoted from the literature — the local limit
  theorem of Martin–Mauduit–Rivat and the short-interval almost-prime theorem
  of Halberstam–Heath-Brown–Richert — declared as axioms in the single file
  [`DSS/Cited.lean`](lean/DSS/Cited.lean) and audited against their sources in
  [`SOURCE_AUDIT.md`](SOURCE_AUDIT.md);
* every proof is `sorry`-free, the axiom discipline is **enforced at build
  time** by [`DSS/Guard.lean`](lean/DSS/Guard.lean), and
  [`axiom_audit.txt`](lean/axiom_audit.txt) records the `#print axioms` output
  for all 48 audited results.

## The headlines

**Theorem 1.10, zero axioms.**  Every sufficiently large admissible `q` is the
base-`b` digit sum of at least `2^(√q/(36b))` squares with root coprime to `b`
and at most `3q` digits:

```lean
theorem sq_digit_sum_count {b : ℕ} (hb : 3 ≤ b) {q u : ℕ}
    (hq : 2304 * b ^ 4 ≤ q) (hadm : u ^ 2 ≡ q [MOD b - 1]) :
    2 ^ (Nat.sqrt q / (36 * b)) ≤ (sqSols b q).card

theorem sq_digit_sum_count_two {q : ℕ} (hq : 36864 ≤ q) :
    2 ^ (Nat.sqrt q / 72) ≤ (sqSols 2 q).card
```

where `sqSols b q` is the set of `n` with `(n, b) = 1`, `s_b(n²) = q` and
`n² ≤ b^{3q}`.  Both depend on **no axiom** (`propext`, `Classical.choice`,
`Quot.sound` only): Bertrand's postulate and Dirichlet's theorem come from
Mathlib, and Bose–Chowla is proved here.

**Infinitely many squares with prime digit sum, zero axioms** (Remark 7.3 +
Dirichlet):

```lean
theorem infinite_coprime_sq_prime_digit_sum (b : ℕ) (hb : 2 ≤ b) :
    {n : ℕ | Nat.Coprime n b ∧ Nat.Prime (sb b (n ^ 2))}.Infinite
```

**Corollary 1.3**, from `mmr` and `hhbr` and nothing else — with the concrete
instances that the sum of squared decimal digits of `p` (the function of
OEIS A052034), and the binary digit sum of `p`, are almost primes `P₂` for
`≫ π(x)/log log x` primes `p ≤ x`:

```lean
theorem p2_count {b : ℕ} (g : Weight b) (hg : g.Coprime₁) (hdg : g.dg = 1)
    (hmu : 0 < g.mu) :
    ∃ c : ℝ, 0 < c ∧ ∃ x₀ : ℝ, 3 ≤ x₀ ∧ ∀ x : ℝ, x₀ ≤ x →
      c * (picount x : ℝ) / Real.log (Real.log x) ≤ ((p2Primes g x).card : ℝ)

theorem p2_count_S : …        -- S(p) is a P₂ for ≫ π(x)/log log x primes
theorem p2_count_binary : …   -- s_2(p) is a P₂ for ≫ π(x)/log log x primes
```

## Layout

| File | Contents | Axioms |
|---|---|---|
| [`DSS/Digits.lean`](lean/DSS/Digits.lean) | the digit sum `s_b`; block additivity, the complement rule (24), the carry-free representation lemma | none |
| [`DSS/Sidon.lean`](lean/DSS/Sidon.lean) | Sidon sets; closure under translation/dilation; `T ∪ {0}`; the coefficients of `(∑ b^r)²` | none |
| [`DSS/CarryFree.lean`](lean/DSS/CarryFree.lean) | `a_T`; uniqueness of power sums; **Lemma 7.2** for `b ≥ 3` | none |
| [`DSS/CarryFreeTwo.lean`](lean/DSS/CarryFreeTwo.lean) | **Lemma 7.2** for `b = 2` (the parity bookkeeping) | none |
| [`DSS/BoseChowla.lean`](lean/DSS/BoseChowla.lean) | **Bose–Chowla, proved** in `GF(p²)`; + Bertrand: a Sidon set of any size `m` below `4m²` | none |
| [`DSS/Singleton.lean`](lean/DSS/Singleton.lean) | `s_b((2b^k−1)²) = k(b−1)+1`; infinitude of squares with prime digit sum | none |
| [`DSS/Squares.lean`](lean/DSS/Squares.lean) | **Theorem 1.10**, both cases | none |
| [`DSS/PrimeCount.lean`](lean/DSS/PrimeCount.lean) | **Corollary 1.11** in bases 2 and 3, via Bertrand | none |
| [`DSS/FWeight.lean`](lean/DSS/FWeight.lean) | weights that see the length: the split (14), `Z_b`, the parameters of Cor. 1.7, **Example 5.5's forcing**, the base-4 example | none |
| [`DSS/Weight.lean`](lean/DSS/Weight.lean), [`Counting.lean`](lean/DSS/Counting.lean), [`Examples.lean`](lean/DSS/Examples.lean) | the framework inherited from the predecessor repository (Lemma 2.2, `d_g`, the counting functions, `S`) | none |
| [`DSS/Cited.lean`](lean/DSS/Cited.lean) | **the axiom base**: `mmr` and `hhbr`, with source quotations | — |
| [`DSS/P2.lean`](lean/DSS/P2.lean) | **Corollary 1.3** and its instances | `mmr`, `hhbr` |
| [`DSS/Sanity.lean`](lean/DSS/Sanity.lean) | compile-time `#guard`s: the identities computing on concrete numbers | none |
| [`DSS/Guard.lean`](lean/DSS/Guard.lean) | `#assert_axioms`: the axiom discipline as a build invariant | — |

## Reproducing the check

```sh
cd lean
lake exe cache get
lake build                      # "Build completed successfully", no warnings
lake env lean AxiomAudit.lean   # compare with axiom_audit.txt
cd ../validation
uv run --with numpy python check_numerics.py   # reproduces §5.4; ~2 minutes
```

Toolchain: Lean 4 `v4.33.0`, Mathlib tag `v4.33.0` (pinned in
`lean-toolchain` and `lake-manifest.json`).

## What is *not* verified

The verification report [`VERIFICATION.md`](VERIFICATION.md) gives the full
paper ↔ Lean correspondence and an honest inventory of what is not
machine-checked: the analytic theory of §§3–6 and §8 (the level of
distribution, the mean-zero asymptotics, the shellwise Mertens formulas, the
joint Erdős–Kac theorem, the transfer principle and the Fourier criterion),
Corollary 1.2 (whose weighted-sieve input we chose not to axiomatise), and
Corollary 1.11 for bases `b ≥ 4`.  The two axioms themselves are assumptions;
`SOURCE_AUDIT.md` records how they were checked against their sources.
