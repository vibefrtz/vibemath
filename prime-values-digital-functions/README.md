# DigSq — a Lean verification of *Prime values of digital functions along the primes*

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.22093372.svg)](https://doi.org/10.5281/zenodo.22093372)

This repository accompanies the paper *Prime values of digital functions along
the primes* ([`paper_anonymous.pdf`](paper_anonymous.pdf), source in
[`paper_anonymous.tex`](paper_anonymous.tex)). It contains a
Lean 4 formalisation of the first two phases of a six-phase plan, in which

* the **one** result quoted from the literature that these phases need — the
  local limit theorem of Martin, Mauduit and Rivat — is declared as an axiom, in
  the single file [`DigSq/Cited.lean`](lean/DigSq/Cited.lean), transcribed from
  Théorème 1 of the source and checked against it clause by clause in
  [`SOURCE_AUDIT.md`](SOURCE_AUDIT.md);
* **every argument the paper itself makes** in reaching Theorem 1.1 and
  Corollaries 1.4 and 1.5 is proved in Lean from that axiom, with **no `sorry`**;
* and a majority of the development — Lemma 2.2, the theory of `d_g`, §6.1, §6.2
  and §6.3 — is proved **unconditionally**, with no axioms at all beyond Lean's
  three built-in ones.

## The headline

```lean
/-- There are infinitely many primes `p` such that the sum of the squares of the
decimal digits of `p` is again prime.  (OEIS A052034.) -/
theorem A052034_infinite : {p : ℕ | Nat.Prime p ∧ Nat.Prime (S p)}.Infinite
```

The same theorem is also stated with our definition of `S` written out, so that
nothing but Mathlib's own `Nat.digits`, `Nat.Prime` and `Set.Infinite` appears
and a reader auditing the claim need not read any definition of ours:

```lean
theorem A052034_infinite_inlined :
    {p : ℕ | Nat.Prime p ∧
      Nat.Prime (((Nat.digits 10 p).map (fun d => d ^ 2)).sum)}.Infinite

theorem A052034_exists_gt (N : ℕ) :
    ∃ p : ℕ, N < p ∧ Nat.Prime p ∧
      Nat.Prime (((Nat.digits 10 p).map (fun d => d ^ 2)).sum)
```

The sequence begins `11, 23, 41, 61, 83, 101, 113, 131, 137, 173, 179, 191, …`
and was recorded by De Geest in 1999 as [OEIS A052034](https://oeis.org/A052034),
where the citations are to the recreational literature. We have not located
anywhere a proof, or an assertion, that the sequence is infinite.

**`A052034_infinite` depends on exactly one axiom beyond Lean's own**, as
[`axiom_audit.txt`](lean/axiom_audit.txt) records. This is not an accident of
packaging. For `g = S` one has `d_S = 1`, so the congruence condition in the
local limit theorem is vacuous and `π_k(x) = π(x)` *exactly*; and at the peak
`k = μ_g log_b x` the factor `π(x)` is common to the main term and to the error
term, and cancels outright. What is left is the elementary comparison of `√L`
with `L^{3/4}` in [`DigSq/Analytic.lean`](lean/DigSq/Analytic.lean). No prime number
theorem, no Chebyshev bound, no Brun–Titchmarsh, no Siegel–Walfisz.

## Headline statements

| Lean name | Statement | Axioms |
|---|---|---|
| `A052034_infinite` | infinitely many primes `p` with `S(p)` prime | `mmr` |
| `A052034_infinite_inlined`, `A052034_exists_gt` | the same, with `S` written out and without `Set.Infinite` | `mmr` |
| `infinite_prime_powDigitSum_prime` | **Corollary 1.4** in base ten for even `r` | `mmr` |
| `infinite_prime_digitOccurrences_prime` | **Corollary 1.5** for a digit `2 ≤ c < b`, any base | `mmr` |
| `exists_prime_S_eq` | every sufficiently large integer is `S(p)` for a prime `p` (§6.1) | `mmr` |
| `exists_prime_eval_eq_of_dg_one` | **Theorem 1.1(i)** for `d_g = 1`, general `b` and `g` | `mmr` |
| `infinite_prime_eval_prime_of_dg_one` | **Theorem 1.1** for `d_g = 1` | `mmr` |
| `Weight.sigSq_pos`, `Weight.coprime_w_one_dg` | **Lemma 2.2** | none |
| `dg_wS`, `dg_powWeight_ten_even`, `dg_digitCount` | **§6.1**: `d_S = 1`, and `d_g = 1` for even powers in base ten and for digit counters | none |
| `mu_wS` | `μ_S = 57/2`, the constant in Conjecture 1.7 | none |
| `three_dvd_of_S_eq_three`, `eq_pow_ten_of_S_eq_one` | **§6.2** | none |
| `S_ne_one_of_prime`, `S_ne_three_of_prime` | §6.2: `1` and `3` are prime values `S` omits on the primes | none |
| `reaches_one_or_cycle` | **§6.3**, the happy-number theorem: every `S`-orbit reaches `1` or the cycle `4,16,37,58,89,145,42,20` | none |
| `exists_iterate_not_prime` | §6.3: no prime has all of its `S`-iterates prime | none |
| `sqrt_lt_rpow_three_quarters` | the analytic core of Theorem 1.1(i) | none |
| `piCong_of_dg_eq_one` | `π_k(x) = π(x)` when `d_g = 1` — why no PNT is needed | none |
| `Weight.dg_pos` | `d_g ≥ 1`, so the `Int.emod` encoding of the congruence is meaningful | none |
| `Weight.dg_dvd_eval_sub` | the congruence `g(n) ≡ g(1)·n (mod d_g)` of §2 | none |
| `sum_countEq` | the primes `≤ x` are partitioned by the value of `g`: `∑_k countEq = π(x)` | none |
| `countEq_le_piCong` | `#{p ≤ x : g(p) = k} ≤ π_k(x)`, tying the two counts of Theorem 2.1 together | none |

## Checking it yourself

Requires [`elan`](https://github.com/leanprover/elan); the pinned toolchain
(`lean-toolchain`: Lean 4 `v4.33.0`) and Mathlib version (`lake-manifest.json`)
are fetched automatically.

```sh
cd lean
lake exe cache get              # fetch the Mathlib binary cache (recommended)
lake build                      # expect "Build completed successfully"
lake env lean AxiomAudit.lean   # prints the axiom closure of every result
cd ..
python3 validation/check_numerics.py
```

* **`sorry` count**: 0. **Warnings**: 0. **Axioms declared**: 1.
* **The axiom discipline is a build invariant, not a promise.**
  [`DigSq/Guard.lean`](lean/DigSq/Guard.lean) asserts the permitted axiom closure of
  every result with a `#assert_axioms` command, so `lake build` *fails* if an
  unconditional result ever acquires `DigSq.mmr`, or if a conditional one
  acquires a second axiom. The guard is not decorative: narrowing any permitted
  set to exclude an axiom that is genuinely used produces
  `AXIOM GUARD FAILED` and stops the build.
* `lean/AxiomAudit.lean` additionally prints the axiom closure of 40 results; the
  expected output is [`axiom_audit.txt`](lean/axiom_audit.txt). Exactly eight of the
  40 mention `mmr`.
* `lean/DigSq/Sanity.lean` contains compile-time `#guard` checks of the computable
  definitions on concrete numbers, including the first fourteen terms of
  A052034 and the eight-cycle of §6.3.
* `validation/` sieves to `10^8` to check the paper's numerical claims **and the
  transcription of the axiom itself** — see [`SOURCE_AUDIT.md`](SOURCE_AUDIT.md) §5.

## Scope

This is the first two phases of a six-phase plan. What is *not* here: Theorem 1.1
for `d_g > 1` and clause (ii), Theorem 1.2, Lemma 4.1, Lemma 5.1, and Theorems 1.3, 1.8, 1.9 and 1.11. See [`VERIFICATION.md`](VERIFICATION.md) §4 for the
honest inventory.

## Layout

```
lean/
  DigSq/
    Imports.lean    the single place Mathlib is imported (about a quarter of it)
    Weight.lean     digit weights, g(n), μ_g, σ_g², d_g; Lemma 2.2
    Examples.lean   power weights, digit counters, S; μ_S = 57/2, d_S = 1, §6.1
    Counting.lean   π(x), #{p ≤ x : g(p) = k}, π_k(x), at real cut-offs
    Analytic.lean   the inequality B√L < A·L^{3/4}
    Cited.lean      THE AXIOM BASE (the only file with axioms)
    Main.lean       Theorem 1.1 for d_g = 1; Corollaries 1.4, 1.5; A052034_infinite
    Sharp.lean      §6.2: "sufficiently large" cannot be dropped
    Happy.lean      §6.3: the happy-number theorem
    Guard.lean      build-time #assert_axioms on every result's axiom closure
    Sanity.lean     executable #guard checks
  AxiomAudit.lean   #print axioms driver
  axiom_audit.txt   its expected output
VERIFICATION.md     the detailed verification report
SOURCE_AUDIT.md     the axiom compared clause by clause with Théorème 1
validation/         numerical validation of the axiom and of the paper's §6.5
paper_anonymous.pdf the manuscript, with paper_anonymous.tex
```

## Citing this work

This paper and its formalisation are archived on Zenodo with the permanent
identifier

```
doi:10.5281/zenodo.22093372
```

which is also recorded in the *Use of automated tools* section of the
manuscript.
