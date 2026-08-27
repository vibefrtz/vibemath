# Verification report

This repository contains a machine-checked Lean 4 verification of part of the
paper

> *Prime values of digital functions and prescribed digit sums of squares*

namely: **the entire squares half** (§7.1 with Theorem 1.10, Corollary 1.11 in
bases 2 and 3, and Remark 7.3), verified **unconditionally** — with no axioms
beyond Lean's three built-in ones — including a full Lean proof of the
Bose–Chowla theorem that the paper quotes; the elementary content of §5
(the split (14), the parameters of Corollary 1.7, Example 5.5's parity
forcing) and of §2; and **Corollary 1.3** (the `P₂` theorem along the primes),
proved from exactly two axioms transcribing the two results the paper's proof
quotes.  The Lean kernel therefore certifies, unconditionally,

> every sufficiently large admissible `q` is the base-`b` digit sum of at
> least `2^(√q/(36b))` squares with root coprime to `b` and at most `3q`
> digits — and, for every `b`, infinitely many squares coprime to `b` have
> prime digit sum,

and, as an implication,

> (Martin–Mauduit–Rivat Théorème 1, as transcribed in `Cited.lean`) ∧
> (Halberstam–Heath-Brown–Richert short-interval `P₂` theorem, as transcribed
> there) ⟹ (Corollary 1.3; in particular the sum of the squared decimal
> digits of `p`, and the binary digit sum of `p`, are `P₂`'s for
> `≫ π(x)/log log x` primes `p ≤ x`).

* **Toolchain**: Lean 4 `v4.33.0`, Mathlib tag `v4.33.0`.
* **Size**: ≈4 000 lines of Lean across 18 modules.
* **`sorry` count**: 0.  **Build warnings**: 0.
* **Axioms declared**: 2, both in `DSS/Cited.lean`, both audited in
  [`SOURCE_AUDIT.md`](SOURCE_AUDIT.md).
* **Audited results**: 48, of which exactly 3 (Corollary 1.3 and its two
  instances) depend on the axioms; the other 45 — including Theorem 1.10 —
  depend on none.
* **Axiom discipline**: enforced at build time by `DSS/Guard.lean`
  (`#assert_axioms`), not merely documented.
* **Mathlib surface**: `DSS/Imports.lean`; `import Mathlib` and
  `import Mathlib.Tactic` are deliberately avoided.  The named Mathlib inputs
  to the unconditional half are Bertrand's postulate
  (`Nat.exists_prime_lt_and_le_two_mul`), Dirichlet's theorem on primes in
  arithmetic progressions (`Nat.forall_exists_prime_gt_and_modEq`), and the
  finite-field library (`GaloisField`, cyclicity of the unit group).

## 1. The axiom base (`DSS/Cited.lean`)

| Axiom | Source quoted by the paper | Used for |
|---|---|---|
| `mmr` | Martin–Mauduit–Rivat, J. Inst. Math. Jussieu **18** (2019), Théorème 1, at `β = 0` | Corollary 1.3 |
| `hhbr` | Halberstam–Heath-Brown–Richert, *Almost-primes in short intervals*, Durham 1979 proceedings (1981), 69–101, at the admissible exponent `θ = 0.455` | Corollary 1.3 |

`mmr` is **identical, word for word, to the axiom of the predecessor
repository** (`prime-values-digital-functions`), where it was compared with
Théorème 1 of the source clause by clause and validated numerically; that
audit carries over verbatim and is reproduced in `SOURCE_AUDIT.md` §1.
`hhbr` is new here; `SOURCE_AUDIT.md` §2 records its transcription and the
accessibility caveat for the Durham proceedings volume.

Encoding notes for `hhbr`:

* A `P₂` is encoded as `IsP2 n := 2 ≤ n ∧ n.primeFactorsList.length ≤ 2`,
  i.e. `Ω(n) ≤ 2` with multiplicity, matching the paper's definition of `P_r`.
* The interval count is the cardinality of an explicit finite set
  `p2InInterval z` of integers `n` with `z − z^{0.455} < n ≤ z`.
* The quantifier order is the source's: absolute constants `c, z₀` first,
  then uniformity in `z ≥ z₀`.  The exponent is fixed at `0.455`, the value
  the source proves (their Theorem 2 at `R = 2`); the paper needs only *some*
  `θ < 1/2`, so this is the weakest faithful transcription.
* The threshold normalisation `3 ≤ z₀` only weakens the axiom.

`validation/check_numerics.py` counts the `P₂`'s in `(z − z^{0.455}, z]` at
`z = 10⁶, 10⁷, 5·10⁷` (141, 375, 721 — about four times `z^{0.455}/log z`),
which is the evidence that the transcription is not vacuous.

## 2. Paper ↔ Lean correspondence

### Definitions

| Paper | Lean | File |
|---|---|---|
| `s_b(n)` | `sb b n` | `Digits.lean` |
| Sidon set | `IsSidon` | `Sidon.lean` |
| `a_T = 1 + ∑_{r∈T} b^r`, eq. (22) | `aT b T` | `CarryFree.lean` |
| admissible `q` (`q ≡ □ mod b−1`) | `u ^ 2 ≡ q [MOD b - 1]` | `Squares.lean` |
| the solutions of Thm 1.10 | `sqSols b q` | `Squares.lean` |
| `ℓ_b(n)`; `F_w`, eq. (13) | `lb b n`; `Fw b w n` | `FWeight.lean` |
| `g_w(a) = w_a − w₀` | `gw b w hb` | `FWeight.lean` |
| `Z_b(n)` | `Zb b n` | `FWeight.lean` |
| the zero-count weight of Cor. 1.7 | `zeroWeight b hb` | `FWeight.lean` |
| Example 5.5's weight `(0,1,−4)` in base 3 | `exWeight3` | `FWeight.lean` |
| the base-4 example `(0,1,2,−3)` | `exWeight4` | `FWeight.lean` |
| the digit sum as a weight | `sbWeight b hb` | `FWeight.lean` |
| `P_2` | `IsP2` | `Cited.lean` |
| `#{p ≤ x : g(p) ∈ P₂}` | `(p2Primes g x).card` | `P2.lean` |
| strongly `b`-additive `g`; `μ_g, σ_g², d_g`; `π(x)`, `π_k(x)`, `#{p ≤ x : g(p)=k}`; `S` | `Weight b`; `Weight.mu/sigSq/dg`; `picount`, `piCong`, `countEq`; `S` | inherited: `Weight.lean`, `Counting.lean`, `Examples.lean` |

### The paper's own results

| Paper | Lean | Axioms |
|---|---|---|
| eq. (23): digit sums add along blocks | `sb_add_pow_mul` | none |
| eq. (24): the complement rule | `sb_pow_sub` | none |
| carries do not occur below `b` | `sb_sum_pow`, `sb_sum_over` | none |
| **Lemma 7.1** (via Bose–Chowla + Bertrand) | `bose_chowla`, `exists_sidon_of_card`, `transform_props` | none |
| **Lemma 7.2**, case `b ≥ 3` | `sb_aT_sq`, `sb_aT_sq_sub_one`, `sb_two_aT_sub_one`, `sb_shifted_sq` | none |
| **Lemma 7.2**, case `b = 2` | `aT_sq_eq_sum_expSet`, `card_expSet`, `sb_shifted_sq_two` | none |
| distinct `T` give distinct roots | `sum_pow_injective`, `aT_injective` | none |
| `(a_T b^k − 1, b) = 1` | `coprime_shifted` | none |
| **Theorem 1.10**, `b ≥ 3` | `sq_digit_sum_count` | none |
| **Theorem 1.10**, `b = 2` | `sq_digit_sum_count_two` | none |
| **Corollary 1.11**, bases 2 and 3 | `sq_prime_digit_sum_count_two`, `_three` | none |
| **Remark 7.3**: `s_b((2b^k−1)²) = k(b−1)+1` | `sb_singleton` | none |
| Remark 7.3 + Dirichlet: infinitude | `infinite_coprime_sq_prime_digit_sum` | none |
| eq. (14): the split `F_w = w₀ℓ_b + g_w` | `Fw_eq_split`, `Zb_eq_Fw` | none |
| Cor. 1.7's parameters: `μ = −(b−1)/b`, `σ² = (b−1)/b²`, `d = 1`, exact shell centre | `zeroWeight_mu`, `zeroWeight_sigSq`, `zeroWeight_dg`, `zeroWeight_shell_centre` | none |
| **Example 5.5**: odd shells force `F(p) = 2` | `base3_odd_shell_forcing` | none |
| the base-4 example: `d_g = 3`, `μ_g = 0`, (3) holds | `exWeight4_dg`, `exWeight4_mu`, `exWeight4_coprime₁` | none |
| `d = 1`, `μ = 1/2` for the binary digit sum | `sbWeight_two_dg`, `sbWeight_two_mu` | none |
| **Corollary 1.3** | `p2_count` | `mmr`, `hhbr` |
| Corollary 1.3 for `S` and for `s_2` | `p2_count_S`, `p2_count_binary` | `mmr`, `hhbr` |
| the binomial lower bound `C(m,t) ≥ 2^{m/3}` | `two_pow_le_choose`, `two_pow_le_choose_of_le` | none |
| Lemma 2.2 and the `d_g` theory (inherited) | `Weight.sigSq_pos`, `Weight.coprime_w_one_dg`, `Weight.dg_dvd_eval_sub`, … | none |

## 3. Encoding conventions, and why they matter

* **Theorem 1.10 is fully explicit.**  Where the paper has unspecified
  constants `c_b, C_b` and "sufficiently large", the Lean statement has
  `2^(√q/(36b))` representations, the digit bound `n² ≤ b^{3q}`, and the
  threshold `q ≥ 2304·b⁴` (`36864` for `b = 2`).  These are *effective* but
  not optimal; any reader can weaken them to the paper's form.  Admissibility
  is the hypothesis `u² ≡ q (mod b−1)`, literally the paper's condition; for
  `b = 2` it is vacuous and the Lean statement drops it, as does the paper.
* **`Nat` subtraction never hides an argument.**  All digit-sum identities
  with subtractions are stated additively (`sb_pow_sub` reads
  `s_b(b^k − c) + s_b(c−1) = k(b−1)`), so no truncated subtraction can make a
  statement vacuously true.
* **Corollary 1.3's normalisation.**  The paper states the count against
  `π(x)/log₂x`; the Lean statement uses `π(x)/log log x` with an unspecified
  constant `c > 0`, which is the same assertion (the two normalisations
  differ by the bounded factor `log log b`).  `π(x)` is the exact prime count
  `picount x`, not an asymptotic expression, so — as in the predecessor —
  **no prime number theorem enters anywhere**: with `d_g = 1` the factor
  `π(x)` is common to the main and error terms of `mmr` and cancels.
* **`g(p) ∈ P₂` at mean zero would be ill-typed**; here `μ_g > 0` and the
  value is rendered `∃ n : ℕ, IsP2 n ∧ g.eval p = (n : ℤ)`, never through
  `natAbs`.
* **The window book-keeping is deterministic.**  The proof of `p2_count`
  introduces every threshold explicitly (`exists_rpow_threshold`) rather than
  through filters, so `x₀` is in principle extractable from the proof term.

## 4. Where the formal proof differs from the paper's (same theorem)

1. **Bose–Chowla is proved, not quoted.**  The paper's Lemma 7.1 cites Bose
   and Chowla (1962/63) for a Sidon set of size `≥ ½√N` in `[1, N]`.  The
   formalisation instead *proves* the underlying construction: for `p` prime,
   the discrete logarithms of `θ + a`, `a ∈ F_p`, `θ` a generator of
   `F_{p²}^×`, form a Sidon set of `p` integers below `p²`
   (`bose_chowla`), and Bertrand's postulate (Mathlib) turns this into a
   Sidon set of any prescribed size `m` inside `[0, 4m²)`
   (`exists_sidon_of_card`).  The interval normalisation of Lemma 7.1
   (translate into the top half, double) is `transform_props`, exactly as in
   the paper.
2. **The `t`-selection is by an explicit residue window.**  The paper picks
   `t ≡ t₀ (mod b−1)` in `[m/3, 2m/3]`; the formal proof takes the least such
   `t ≥ ⌊m/3⌋` (`exists_residue_in_window`) and checks `t ≤ m`,
   `min(t, m−t) ≥ ⌊m/3⌋` — which is all the binomial bound needs.
3. **Corollary 1.11 is formalised for `b = 2, 3` only.**  The paper's proof
   takes a prime `q ≡ 1 (mod b−1)` in a dyadic window, i.e. the prime number
   theorem for progressions.  In bases 2 and 3 admissibility is free
   (mod 1, resp. every odd prime mod 2) and Bertrand suffices; for `b ≥ 4`
   the statement is not formalised (see §5).
4. **The `P₂` targets are collected on an explicit arithmetic progression of
   interval endpoints** `z_i = y + Δ(i+1)`, `Δ = (2y)^{0.455}`, rather than
   by the paper's iteration `z ↦ z − z^θ`; the intervals
   `(z_i − z_i^θ, z_i]` are pairwise disjoint because the spacing `Δ`
   dominates `z_i^θ`, and each carries `hhbr`'s quota.  This changes only
   constants.
5. **The Gaussian window is `H = √L` rather than `σ_g√L`**, so the pointwise
   lower bound at the half-window is `exp(−1/(8σ_g²))` times the peak
   (`gaussian_lower`); again only constants move.

## 5. What is *not* machine-checked (honest inventory)

1. **The two axioms.**  `mmr` and `hhbr` are assumptions; everything that
   uses them is conditional on them.  See `SOURCE_AUDIT.md` for how each was
   checked against its source, and for the caveat that the HHbR proceedings
   volume was not independently accessible at audit time.
2. **Theorem 1.1 and Corollary 1.2** (the level of distribution and the `P₃`
   theorem).  Corollary 1.2's engine, Richert's weighted sieve, is exactly
   the kind of heavy quoted machinery whose transcription would dominate the
   audit; we chose not to axiomatise it.  Theorem 1.1 needs Poisson
   summation and multiplicative bookkeeping that we did not undertake.
3. **Theorems 1.4, 1.5** (mean zero), **1.6, 5.1, 5.4** (the shellwise
   Mertens theory beyond the elementary identities verified here), **1.8,
   1.9** (the joint Erdős–Kac theorem), **§6.2** (the mean-value transfers),
   **§7.2** (the sparse polynomial sequences) and **§8** (the abstract
   transfer and the Fourier criterion).  These are the analytic majority of
   the along-the-primes half; each needs either the prime number theorem
   (with error), Mertens' theorems, or saddle-point analysis, none of which
   is in Mathlib.
4. **Corollary 1.11 for `b ≥ 4`**, as explained in §4.3.
5. **The general `κ_m` identity** of Theorem 5.4 (the CRT product formula);
   only its instance for Example 5.5 (`d = 2`, where it degenerates to the
   parity forcing) is formalised.
6. **The paper's numerical remarks (§5.4)** are checked by the script in
   `validation/`, not by the Lean kernel.  Every quoted number is reproduced
   exactly (the count `629304`, the reciprocal sums, the three shell
   proportions, and the seven-row base-3 table).  One finding: the paper's
   *model values* `0.11305 / 0.08101 / 0.05220` are those of the binomial
   `Bin(m−2, 1/10)` — leading **and last** digit zero-free, the right model
   for primes — while the manuscript's sentence says "(7, 1/10)", which
   would predict `0.14714`.  The manuscript's numbers are correct; the
   parenthetical should read `(6, 1/10)` (with the corresponding change of
   wording).  This is recorded here as an erratum to §5.4 found by the
   validation.

## 6. Sanity checks

`DSS/Sanity.lean` contains `#guard` checks evaluated at compile time: the
digit sums `s_10(19²) = 10`, `s_10(1101²) = 9`, the complement rule at
concrete values, the singleton identity in bases 2, 3, 10, the carry-free
square of `a_{{2,3}} = 1101` and its shifted form, the binary case on
`T = {2, 6}`, pair counts against `C(t,2)`, admissibility of `s_10(n²)` mod 9
for `n < 30`, the zero counter on concrete numbers, `d = 2` and `d = 3` for
the two examples, `d = 9` for the decimal digit sum (why Corollary 1.3 does
not directly apply to it) and `d = 1` for the binary one, and `IsP2` on
`1, 4, 6, 7, 8, 30`.

## 7. Reproducing the check

```sh
cd lean
lake exe cache get
lake build                      # no errors, no warnings; Guard.lean enforces the axiom discipline
lake env lean AxiomAudit.lean   # compare with axiom_audit.txt
cd ../validation
uv run --with numpy python check_numerics.py   # ≈2 minutes; ends "ALL CHECKS PASSED"
```
