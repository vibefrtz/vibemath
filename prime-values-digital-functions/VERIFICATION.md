# Verification report

This repository contains a machine-checked Lean 4 verification of part of the
paper

> *Prime values of digital functions along the primes*

namely the first two phases of a six-phase plan: the elementary core
of the paper, proved unconditionally, and Theorem 1.1 in the case `d_g = 1`
together with Corollaries 1.4 and 1.5, proved from a single axiom transcribing
the local limit theorem of Martin, Mauduit and Rivat. The Lean kernel therefore
certifies the implication

> (the Martin–Mauduit–Rivat local limit theorem, as transcribed in `Cited.lean`)
> ⟹ (Theorem 1.1 for `d_g = 1`, and in particular that OEIS A052034 is infinite),

and, with no hypothesis at all, Lemma 2.2 and the results of §6.1, §6.2 and §6.3.

The axiom has been **checked line-by-line against the source** (Martin, Mauduit,
Rivat, *Propriétés locales des chiffres des nombres premiers*, J. Inst. Math.
Jussieu **18** (2019), 189–224, Théorème 1): every hypothesis, every constant
and the quantifier order match, and no change to the axiom was required. The
comparison, the three independent cross-checks on the main-term constant, and
the residual caveats are in [`SOURCE_AUDIT.md`](SOURCE_AUDIT.md). A reader who
wants unconditional confidence should read that file and the twenty documented
lines of `Cited.lean`; everything else is checked by the Lean kernel.

* **Toolchain**: Lean 4 `v4.33.0`, Mathlib tag `v4.33.0`.
* **Size**: ≈1 500 lines of Lean across 11 modules.
* **Axiom provenance**: audited against the source; see `SOURCE_AUDIT.md`.
* **`sorry` count**: 0. **Build warnings**: 0.
* **Axioms declared**: 1, all in `DigSq/Cited.lean`.
* **Audited results**: 40, of which exactly 8 depend on the axiom.
* **Axiom discipline**: enforced at build time by `DigSq/Guard.lean`, not merely
  documented.
* **Mathlib surface**: `DigSq/Imports.lean` imports about a quarter of Mathlib;
  `import Mathlib` and `import Mathlib.Tactic` are deliberately avoided.

## 1. The axiom base (`DigSq/Cited.lean`)

| Axiom | Source quoted by the paper | Used for |
|---|---|---|
| `mmr` | Martin–Mauduit–Rivat, J. Inst. Math. Jussieu 18 (2019), Théorème 1, at `β = 0` | the paper's Theorem 2.1 → Theorem 1.1 |

The source statement is reproduced verbatim at the head of `DigSq/Cited.lean`
and compared clause by clause in [`SOURCE_AUDIT.md`](SOURCE_AUDIT.md). The
specialisation `β = 0` — the only difference between the axiom and Théorème 1 —
is a weakening, and is exactly what the accompanying paper quotes as its
Theorem 2.1. `SOURCE_AUDIT.md` §4 records how little of the axiom the
development actually consumes: one instance, at `ε = 1/4`, `d_g = 1`, and the
peak `x = b^{k/μ_g}`.

### Encoding conventions, and why they matter

* **Quantifier order.** The source reads *"fix `ε ∈ (0,1/2)`; uniformly for
  `x > 2` and `k ∈ ℤ`"*, so the implied constant depends on `b`, `g` and `ε` and
  on nothing else. The axiom is therefore `∀ ε, ∃ C, ∀ x, ∀ k`. Writing
  `∀ x, ∃ C` would make it vacuous; writing `∃ C, ∀ ε` would make it strictly
  stronger than the quoted theorem. This is the crux of the whole development
  and the first thing a reader should check.
* **Real cut-offs.** The counting functions take `x : ℝ`, matching the source.
  This is also what the proof needs: the range `x_k = b^{k/μ_g}` of §3 is
  irrational, and integer cut-offs would force an avoidable floor-error analysis.
* **`k : ℤ`.** Values of `g` may be negative when `μ_g = 0`, so "`g(p)` is
  prime" is rendered as `∃ q : ℕ, q.Prime ∧ g.eval p = (q : ℤ)`, not as a
  statement about `natAbs`.
* **Hypotheses.** The source's `g ∈ ℱ₊` is `Weight b` together with
  `Weight.Coprime₁`: the structure carries `2 ≤ b` and `g(0) = 0`, `Weight.eval`
  is the strongly `b`-additive extension, and `Coprime₁` is the `pgcd`
  condition. The source imposes nothing further, and neither does the axiom.
  The positivity `σ_g > 0`, implicit in the statement since it divides by
  `√(2π σ_g² log_b x)`, is *proved* (`Weight.sigSq_pos`, Lemma 2.2), not
  assumed — which is why `DigSq/Weight.lean` sits above `DigSq/Cited.lean` in
  the import order.
* **`π_k(x)`** is `#{p ≤ x : g(1)·p ≡ k (mod d_g)}`, encoded with `Int.emod`
  rather than `Int.ModEq` so that the predicate is decidable without appeal to
  classical choice. That encoding is meaningful because `d_g ≥ 1`, which is
  proved (`Weight.dg_pos`).

### Numerical validation of the axiom

`validation/` contains a sieve to `10^8` checking the transcription against
reality for `g = S`, `b = 10`. Summing the main term over all `k` reproduces
`π(x)` to within 0.46%, 0.24% and 0.13% at `x = 10^6, 10^7, 10^8` — which
confirms the normalisation `d_g π_k(x)/√(2π σ_g² log_b x)` is transcribed
correctly — and the largest pointwise discrepancy sits a factor of about 70
inside the error term the axiom allows. This does not prove the axiom, but it is
the evidence a reader needs that it was not mis-transcribed into something false
or vacuous. The same script verifies every numerical claim of the paper's §6.5.

### The axiom discipline as a build invariant

`DigSq/Guard.lean` defines a `#assert_axioms` command and applies it to every
result named in this report. Compilation fails unless the axiom closure of each
result is contained in the set declared for it. So the two claims

* every Phase 1 result depends on nothing but `propext`, `Classical.choice` and
  `Quot.sound`, and
* every Phase 2 result depends on those together with `DigSq.mmr` and nothing
  else

are checked by the compiler on every build, rather than being assertions in a
README that a reader has to verify by hand. Narrowing any declared set to
exclude an axiom that is genuinely used produces `AXIOM GUARD FAILED` and stops
the build; this was tested.

### Checks on the encoding of the counting functions

Three results exist purely so that a reader can convince themselves the counting
functions in `Counting.lean` mean what Theorem 2.1 says they mean:

* `sum_countEq`: summing `countEq g x k` over the values `g` actually takes on
  the primes `≤ x` recovers `π(x)` exactly. So `countEq` counts each prime once.
* `countEq_le_piCong`: every prime with `g(p) = k` satisfies the congruence
  `g(1)·p ≡ k (mod d_g)`, so `#{p ≤ x : g(p) = k} ≤ π_k(x)`. The two counts of
  Theorem 2.1 are the pair the source intends, not two unrelated quantities.
* `Weight.dg_dvd_eval_sub`: the congruence `g(n) ≡ g(1)·n (mod d_g)` displayed in
  §2 of the paper, which is what makes the previous item true.

All three are unconditional.

## 2. Paper ↔ Lean correspondence

### Definitions

| Paper | Lean | File |
|---|---|---|
| strongly `b`-additive `g`, values `g(0)=0,…,g(b-1)` | `Weight b` | `Weight.lean` |
| `g(n) = ∑_j g(ε_j(n))` | `Weight.eval` | `Weight.lean` |
| strong `b`-additivity | `Weight.eval_add_mul`, `Weight.eval_ofDigits` | `Weight.lean` |
| `μ_g`, `σ_g²` | `Weight.mu`, `Weight.sigSq` | `Weight.lean` |
| `d_g`, eq. (4) | `Weight.dg` | `Weight.lean` |
| hypothesis (3) `gcd(g(1),…,g(b-1)) = 1` | `Weight.Coprime₁` | `Weight.lean` |
| `g(a) = a^r`; `∑_j ε_j(n)^r` | `powWeight`, `powDigitSum` | `Examples.lean` |
| `S(n)` (sum of squared decimal digits) | `S` | `Examples.lean` |
| the digit-`c` counter of Cor. 1.5 | `digitCount`, `digitOccurrences` | `Examples.lean` |
| `π(x)` | `picount` | `Counting.lean` |
| `#{p ≤ x : g(p) = k}` | `countEq` | `Counting.lean` |
| `π_k(x)` | `piCong` | `Counting.lean` |
| the main term of (5) | `mmrMain` | `Cited.lean` |
| the eight-cycle of §6.3 | `happyCycle` | `Happy.lean` |

### The paper's own results

| Paper | Lean | Axioms |
|---|---|---|
| `d_g ∣ b - 1`; `d_g ∣ g(a) - a g(1)` | `Weight.dg_dvd_sub_one`, `Weight.dg_dvd_sub` | none |
| **Lemma 2.2** (`σ_g > 0`) | `Weight.sigSq_pos` | none |
| **Lemma 2.2** (`gcd(g(1), d_g) = 1`) | `Weight.coprime_w_one_dg` | none |
| §6.1: `d_S = 1`; and `μ_S = 57/2` (Conjecture 1.7) | `dg_wS`, `mu_wS` | none |
| §6.1: `d_g = 1` for `a ↦ a^r`, `r` even, base ten | `dg_powWeight_ten_even` | none |
| §6.1: `d_g = 1` for the digit-`c` counter, `c ≥ 2` | `dg_digitCount` | none |
| power weights and digit counters satisfy (3), `μ_g > 0` | `powWeight_coprime₁`, `powWeight_mu_pos`, `digitCount_coprime₁`, `digitCount_mu_pos` | none |
| the analytic content of the proof of Thm 1.1(i) | `sqrt_lt_rpow_three_quarters` | none |
| §2: the congruence `g(n) ≡ g(1)·n (mod d_g)` | `Weight.dg_dvd_eval_sub` | none |
| **§6.2** `S(n)=3 ⇒ 3 ∣ n` | `three_dvd_of_S_eq_three` | none |
| **§6.2** `S(n)=1 ⇒ n = 10^j` | `eq_pow_ten_of_S_eq_one` | none |
| **§6.2** `1`, `3` omitted on primes | `S_ne_one_of_prime`, `S_ne_three_of_prime` | none |
| **§6.3** `S(n) < n` for `n ≥ 244` | `S_lt_self` | none |
| **§6.3** the happy-number theorem | `reaches_one_or_cycle` | none |
| **§6.3** no prime has all its `S`-iterates prime | `exists_iterate_not_prime` | none |
| **Theorem 1.1(i)** for `d_g = 1` | `exists_prime_eval_eq_of_dg_one` | `mmr` |
| the infinitude argument (distinct `k` give distinct `p`) | `infinite_of_exists_prime_eval_eq` | none |
| **Theorem 1.1** for `d_g = 1` | `infinite_prime_eval_prime_of_dg_one` | `mmr` |
| **Corollary 1.4**, base ten, `r` even | `infinite_prime_powDigitSum_prime` | `mmr` |
| **Corollary 1.5**, digit `2 ≤ c < b` | `infinite_prime_digitOccurrences_prime` | `mmr` |
| §6.1: every large integer is `S(p)` | `exists_prime_S_eq` | `mmr` |
| **A052034 is infinite** | `A052034_infinite`, and `A052034_infinite_inlined` / `A052034_exists_gt` with `S` written out | `mmr` |

## 3. Where the formal proof differs from the paper's (same theorem)

The paper's proof of Theorem 1.1(i) invokes the prime number theorem for
arithmetic progressions (eq. (6)) to evaluate `π_k(x)`, and then compares the
main term `≍ x_k (log x_k)^{-3/2}` with the error term. The formal proof does
neither, in the case `d_g = 1`:

* when `d_g = 1` the congruence is vacuous, so `π_k(x) = π(x)` holds *exactly*
  (`piCong_of_dg_eq_one`), with no appeal to any distribution result;
* the factor `π(x)` is then common to the main term and to the error term of the
  axiom and cancels, so no estimate for `π(x)` is needed either — only
  `π(x) > 0`, which follows from `2 ≤ x` because `2` is prime.

The residue is the inequality `C√(2πσ_g²)·√L < (log b)^{3/4}·L^{3/4}` for large
`L`, which is `sqrt_lt_rpow_three_quarters`. This is why the headline theorem's
axiom closure contains `mmr` and nothing else. The paper's route is the correct
one for general `d_g`; the specialisation is what makes the `d_g = 1` case — which
covers `S`, every `a ↦ a^r` with `r` even in base ten, and every digit counter
with `c ≥ 2` — so cheap.

A second, smaller difference: §6.3's happy-number theorem is proved here by
showing `S(n) < n` for `n ≥ 244` (from `S(n) ≤ 81·(number of digits)` against
`n ≥ 10^{d-1}`, with `81d < 10^{d-1}` for `d ≥ 4`) and then checking the finitely
many `n ≤ 243` by kernel evaluation. The paper asserts the classification
without proof, as standard.

## 4. What is *not* machine-checked (honest inventory)

1. **The axiom itself.** `mmr` has not been *derived* — it is an assumption, and
   everything in Phase 2 is conditional on it. It has now been compared
   line-by-line with Théorème 1 of the source and matches
   ([`SOURCE_AUDIT.md`](SOURCE_AUDIT.md)), but two caveats remain: the
   comparison is against the authors' preprint rather than the paywalled
   published text, and the source PDF was read by a model rather than by a human
   eye. The three cross-checks in `SOURCE_AUDIT.md` §5 make a surviving error
   unlikely; a human should nevertheless read Théorème 1 once against
   `Cited.lean` before the repository is cited anywhere that matters.
2. **Theorem 1.1 for `d_g > 1`.** Not formalised. It needs the prime number
   theorem for arithmetic progressions, which is not in Mathlib and would have
   to be a second axiom. Corollary 1.4 for *odd* `r` (where `d_g = 3` in base
   ten) and Corollary 1.5 for `c = 1` are therefore absent.
3. **Theorem 1.1(ii)** (the case `μ_g = 0`). Not formalised.
4. **Theorems 1.2, 1.3, 1.8, 1.9, 1.11 and Lemmas 4.1, 5.1.** Not formalised;
   these are phases 3–6 of the plan. Theorem 1.3 is the dominant remaining cost.
5. **§6.1 in general.** The formula `d_g = ∏_{ℓ ∣ b-1, ℓ-1 ∣ r-1} ℓ` is proved
   only in the cases used (`r` even in base ten, where it gives `1`); the general
   statement, and the `d_g = 3` case for odd `r`, are not formalised. The
   Lagrange-interpolation correspondence `g ↔ P` of §1 is not formalised.
6. **The paper's numerical remarks (§6.5)** are checked by the scripts in
   `validation/`, not by the Lean kernel.

## 5. Sanity checks

`DigSq/Sanity.lean` contains `#guard` checks evaluated at compile time: values of
`S` on small numbers, the first fourteen terms of OEIS A052034, the eight-cycle
`4, 16, 37, 58, 89, 145, 42, 20`, the digit differences `a² - a` whose gcd with
`9` gives `d_S = 1`, the example `s(19) = s(28)` with `S(19) ≠ S(28)` of §6.3,
the `binom(a,2)` values of §1, and the primes below 200 in which the digit `1`
occurs a prime number of times.

## 6. Reproducing the check

```sh
cd lean
lake exe cache get
lake build                      # "Build completed successfully", no warnings
lake env lean AxiomAudit.lean   # compare with axiom_audit.txt
python3 validation/check_numerics.py
```
