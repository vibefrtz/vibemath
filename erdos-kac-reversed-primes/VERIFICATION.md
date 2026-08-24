# Verification report

This repository contains a machine-checked, **conditional** Lean 4
verification of the paper

> *An Erdős–Kac law for palindromes and for reversed primes*

"Conditional" means: the results that the paper quotes from the literature
are declared as **axioms** (all of them in one file, `lean/EKRev/Cited.lean`,
and nowhere else), and **every argument the paper itself makes is proved in
Lean from those axioms**. The Lean kernel therefore certifies the
implication

> (quoted literature results, as transcribed in `Cited.lean`)
> ⟹ (the paper's theorems).

The axioms were transcribed from the statements as quoted in the paper,
and were subsequently compared against the original sources where automated
access allowed (see the cross-check table in §1: two of the four
paper-specific axioms verified against the originals, one corroborated
through a secondary quotation, one — Col's theorem — not independently
accessible). A reader who wants unconditional confidence should compare the
eight axioms in `lean/EKRev/Cited.lean` (≈100 lines, heavily documented) with
the cited literature; everything else is checked by the Lean kernel.

* **Toolchain**: Lean 4 `v4.33.0`, Mathlib tag `v4.33.0`.
* **Size**: ≈7 800 lines of Lean across 17 modules.
* **`sorry` count**: 0.
* **Axiom audit**: `lean/AxiomAudit.lean` prints, for each main theorem, the
  full axiom closure of its proof. The output (reproduced in
  `lean/axiom_audit.txt`) shows that every theorem depends only on Lean's three
  built-in axioms (`propext`, `Classical.choice`, `Quot.sound`) and on the
  declared axioms of `Cited.lean` — and, notably, that the axiom
  dependencies of each theorem match the paper's citation structure
  exactly (e.g. the palindrome ω-law uses exactly Col + GS + Mertens +
  the method of moments; the Ω-law additionally uses Banks–Shparlinski;
  the reversed-prime laws use DRS + PNT, with Brun–Titchmarsh entering
  only through hypothesis (iii)).

## 1. The axiom base (`lean/EKRev/Cited.lean`)

| Axiom | Source quoted by the paper | Used for |
|---|---|---|
| `gs_prop3` | Granville–Soundararajan, *Sieving and the Erdős–Kac theorem*, Prop. 3, specialised to `h ≡ 1` (the only case the paper uses) | Proposition 2.2 → the moment computation |
| `col_thm2` | S. Col, *Palindromes dans les progressions arithmétiques*, Thm. 2 | Theorem 3.1 → hypothesis (ii) for palindromes |
| `bsh_thm7` | Banks–Shparlinski, *Prime divisors of palindromes*, Thm. 7 | Theorem 3.2 → hypothesis (iii) for palindromes |
| `drs_thm13` | Dartyge–Rivat–Swaenepoel, *Prime numbers with an almost prime reverse*, Thm. 1.3 | Theorem 4.4 → hypotheses (ii), (iii) for reversed primes |
| `brun_titchmarsh` | Montgomery–Vaughan, *The large sieve*, Thm. 2 (interval form) | Lemma 4.2(ii) |
| `pnt` | prime number theorem, `π(x) log x / x → 1` | Lemma 4.2 (first part) |
| `mertens_regular` | Mertens' second theorem, in the paper's regularity form (1.10) | `S` = all primes is regular of density 1 |
| `method_of_moments` | Billingsley, *Probability and measure*, Thm. 30.2 + determinacy of the normal law by its moments, for empirical distributions of finite families | end of the proof of Prop. 2.1 |

Encoding conventions (documented per-axiom in the file):

* Sums of suprema (`∑_q sup_z max_a |…|` in Col and DRS) are encoded by an
  existentially quantified bound function `Bnd : ℕ → ℝ` dominating each
  discrepancy, whose sum over the admissible moduli obeys the quoted
  estimate. This is equivalent to the sum-of-sup form and is exactly the
  shape in which those sums are consumed.
* Residue classes mod `d` are encoded via `% d` (the paper's class
  `a = d` is the class `0`).
* Real-indexed counting functions are evaluated at integer cut-offs.
* `k ≤ σ^{2/3}` is encoded as `k³ ≤ σ²`.
* In `IsRegular` (eq. (1.10)) the `O(1)` is an explicit constant `C`
  valid for all `y ≥ 3`.


### Cross-check of the axioms against the sources

The four paper-specific axioms were compared, where automated access
allowed, against the *original* publications (not only the manuscript's
quotations); performed 2026-08-23.

| Axiom | Status | Notes |
|---|---|---|
| `gs_prop3` | **checked against the original** ([arXiv:math/0606039](https://arxiv.org/abs/math/0606039), Prop. 3) | Statement matches after the documented specialisations: `h ≡ 1` (so `r_d = A_d − x/d`); the multiset `𝒜 = {a_1,…,a_x}` taken as a finite set (the only case used — `𝒯_λ`, `𝒜_{λ,i}` consist of distinct integers); the two `O(·)` bounds carry one absolute constant `K` (the original is uniform in all parameters); `k ≤ σ^{2/3}` encoded as `k³ ≤ σ²`; `D_k(𝒫)` = squarefree products of at most `k` primes of `𝒫` = `piProds`. `μ_𝒫`, `σ_𝒫²`, `C_k`, and both displayed estimates (even: `C_k x σ^k (1+O(k³/σ²)) + O(μ^k Σ_{D_k}\|r_d\|)`; odd: `≪ C_k x σ^k k^{3/2}/σ + μ^k Σ_{D_k}\|r_d\|`) agree verbatim. |
| `drs_thm13` | **checked against the original** ([arXiv:2506.21642](https://arxiv.org/abs/2506.21642), Thm. 1.3) | Identical structure: `∑_{d ≤ b^{ξλ}, (d,b(b²−1))=1} sup_{t∈[b^{λ−1},b^λ]} sup_{1≤a≤d} \|π̄_λ(t,a,d) − π_λ(t)/d\| ≪ b^{λ−c√λ}`, with `ξ ∈ (0,ξ₀(b))`, `c = c(b,ξ) > 0`, `λ ≥ λ₀(b,ξ)`, and `R_λ(n) = Σ_j ε_j(n) b^{λ−1−j}` exactly as in `rev`. Deviations, all conservative: the real `sup` over `t` is consumed at integer cut-offs only (the counting functions jump only there); residues `1 ≤ a ≤ d` are encoded as all `a : ℕ` via `% d` (same set of classes); `≪` becomes an explicit constant `C`. |
| `bsh_thm7` | **corroborated (original not machine-accessible)** | The publisher copies (Springer/Akadémiai) and the University of Missouri repository copy ([MOspace 10355/10815](https://hdl.handle.net/10355/10815)) reject automated retrieval, so Thm. 7 could not be read in the original. Independent corroboration: a later paper by other authors ([arXiv:2311.15002](https://arxiv.org/abs/2311.15002), Lemma 4) quotes the Banks–Shparlinski divisibility bound in the equivalent form `#Π(N; 0, q) ≪_g g^{N/2} q^{−1/2}`, which since `#P_N ≍ g^{N/2}` is exactly the axiom's `#{n ∈ 𝒯_ν : d ∣ n} ≪_b #𝒯_ν d^{−1/2}` in the divisibility case (the only case axiomatised). That paper's Remark 5 flags a boundary subtlety (`q ≥ g^N`) in the *non-zero-residue* variant of a related Banks–Shparlinski lemma; it does not affect the divisibility case, and for `d > b^ν` the axiom is vacuously true (`𝒯_ν ⊆ [1, b^ν)` contains no multiple of `d`). A human check against Period. Math. Hungar. 51 (2005), 1–10, Thm. 7 is still recommended. |
| `col_thm2` | **not independently checked** | Acta Arith. 137 (2009) is paywalled and the open copies (HAL [hal-00143708](https://hal.science/hal-00143708), the author's thesis [tel-00339809](https://theses.hal.science/tel-00339809)) are behind anti-bot protection; no arXiv version exists. The axiom therefore rests on the manuscript's quotation (its Theorem 3.1) alone, including the coprimality condition `(q, b³−b) = 1` and the `#𝒯(x)(log x)^{−A}` saving. This is the one substantive axiom a human referee should verify against the source (DOI `10.4064/aa137-1-1`). |

The four standard axioms (`brun_titchmarsh`, `pnt`, `mertens_regular`,
`method_of_moments`) are textbook results and were not source-checked; each
is a *weakening* of the canonical statement: Brun–Titchmarsh is used with
modulus `1` and an unspecified constant (Montgomery–Vaughan give `2y/log y`
for `y > 1`); `pnt` is the classical asymptotic; `mertens_regular` follows
from Mertens' `Σ_{p≤y} 1/p = log log y + M + O(1/log y)` with any constant
absorbing `M` and the error for `y ≥ 3`; and `method_of_moments` is
Billingsley Thm. 30.2 plus moment-determinacy of the Gaussian, specialised
to empirical distributions of finite families (the empirical d.f. is the
d.f. of a uniformly sampled variable; weak convergence gives pointwise
d.f. convergence since `Φ` is continuous everywhere).

## 2. Paper ↔ Lean correspondence

### Definitions (§1.2, §3, §4)

| Paper | Lean | File |
|---|---|---|
| digits `ε_j(n)` | `digit b n j` | `Digits.lean` |
| reversal `R_λ(n)` (eq. (1.5)) | `rev b lam n` | `Digits.lean` |
| `𝒯_λ` (λ-digit palindromes) | `palSet b lam` | `PalCount.lean` |
| `𝒯(z)`, `𝒯(z,a,q)` | `palBelow b z`, `palBelowMod b z a q` | `PalCount.lean` |
| `𝒫_λ`, `𝒫_{λ,i}`, `π_λ`, `π_{λ,i}` | `PLam b lam`, `PLamI b lam i`, their `.card` | `PrimeBlocks.lean` |
| `𝒜_λ`, `𝒜_{λ,i}` (eq. (1.6)) | `ALam b lam`, `ALamI b lam i` | `PrimeBlocks.lean` |
| `π_λ(z)`, `π̄_λ(z,a,d)` (§4.2) | `picLam b lam z`, `revCount b lam z d a` | `PrimeBlocks.lean` |
| `ω, Ω, ω_S, Ω_S` | `smallOmega`, `bigOmega`, `omegaS S`, `bigOmegaS S` | `OmegaS.lean` |
| `L = log log b^λ` | `LL b lam` | `Defs.lean` |
| `C_k` (eq. (1.4)) | `Ck k`; Gaussian moments `normalMoment k` | `Defs.lean` |
| `r_d(λ)` (eq. (1.8)) | `rem (B lam) d` | `Defs.lean` |
| `𝒟(ℰ)` (eq. (1.9)) | `noFactorIn E d` | `Defs.lean` |
| regular set of density δ (eq. (1.10)) | `IsRegular S δ` | `Defs.lean` |
| `Φ` (eq. (1.2)) | `Phi`; `Φ = ∫ gauss / √(2π)` | `Phi.lean` |
| `ℰ_b` (eq. (3.4)) | `Eb b := (b³-b).primeFactors` | `PalHyp.lean` |
| truncation `y` (eq. (2.2)) | `ytr b ξ K lam = b^(ξλ/K)` | `CritSetup.lean` |
| `𝒬` (eq. (2.2)) | `Qtr b ξ K S E lam` | `CritSetup.lean` |

### The paper's own results

| Paper | Lean theorem(s) | File |
|---|---|---|
| Lemma 4.1 (congruences of `R_λ`; also (3.8)/(3.9) of DRS as re-proved by the paper) | `rev_modEq_pow_mul`, `rev_gcd_sq_sub_one`, `rev_coprime_sq_sub_one`, `rev_modEq_of_dvd_base` | `Digits.lean` |
| `#𝒯_λ = (b-1)b^{⌈λ/2⌉-1}` (§1.2) and eq. (3.1) | `palSet_card`, `palBelow_card_le` | `PalCount.lean` |
| eq. (4.2) (trivial bound via injectivity of `R_λ`) | `card_dvd_rev_le` | `PrimeBlocks.lean` |
| `Ω-ω = ∑_{m≥2} #{ℓ : ℓ^m ∣ ·}` (proof of Lemma 3.3(iii)) | `bigOmega_eq_add_sum_powers`, `sum_excess_eq` | `OmegaS.lean`, `PalHyp.lean` |
| Lemma 2.3(i) | `setup_mu_sigma` | `CritSetup.lean` |
| Lemma 2.3(ii) | `setup_large_primes` | `CritSetup.lean` |
| Lemma 2.3(iii) | `setup_remainder` | `CritSetup.lean` |
| Prop. 2.1, moment estimate (2.4) at each fixed order | `Wc_moment_limit`, `criterion_moments` | `CritMoments.lean` |
| Prop. 2.1, conclusion (2.5) for `ω_S` | `criterion_EK_omega`, `criterion_EK_omega_uniform` | `Criterion.lean` |
| Prop. 2.1, conclusion for `Ω_S` (the sandwich) | `criterion_EK_Omega`, `criterion_EK_Omega_uniform` | `Criterion.lean` |
| Pólya's uniformity argument ("uniformly in t") | `tendsto_uniform_of_mono` | `Criterion.lean` |
| Lemma 3.3(ii) (for **all** admissible moduli) | `pal_col_package`, `palCritHyps` | `PalHyp.lean` |
| Lemma 3.3(iii) | `palOmegaHyp` | `PalOmega.lean` |
| Lemma 4.2, first part (`π_{λ,i} ≍ b^λ/λ`) | `pilam_lower`, `pilam_upper` | `RevHyp.lean` |
| Lemma 4.2(ii) (`ℓ ∣ b`, leading-block argument) | `rev_modEq_top_block`, `card_blocks_le`, `count_block_le` | `RevOmega.lean` |
| Lemma 4.4 (hypothesis (ii) for `𝒜_{λ,i}`) | `rev_rem_le`, `rev_drs_package`, `revCritHyps` | `RevHyp.lean` |
| Lemma 4.5 (hypothesis (iii) for `𝒜_{λ,i}`) | `revOmegaHyp` | `RevOmega.lean` |
| **Theorem 1.1** (palindromes, ω and Ω) | `pal_EK_omega`, `pal_EK_Omega` (+ `_uniform`) | `Main.lean` |
| **Theorem 1.2** localised | `rev_EK_omega_loc`, `rev_EK_Omega_loc`, `rev_EK_omegaS_loc(_uniform)`, `rev_EK_OmegaS_loc(_uniform)` | `Main.lean` |
| **Theorem 1.2** unlocalised (convex combination over the leading digit) | `rev_EK_omega`, `rev_EK_Omega` (+ `_uniform`) | `Main.lean` |
| **Theorem 1.5**, each fixed moment order | `pal_moments`, `rev_moments_loc` | `Main.lean` |
| **Corollary 1.3** (normal order) | `normal_order_of_uniform` + `pal_normal_order_omega/Omega`, `rev_normal_order_omega/Omega` | `Main.lean` |
| **Corollary 1.6** (general regular `S`) | all `*_omegaS*`/`*_OmegaS*` theorems | `Main.lean` |

### Statement conventions in `Main.lean`

* "Uniformly in `t`" is rendered as
  `∀ ε > 0, ∀ᶠ λ, ∀ t, |F_λ(t) − Φ(t)| ≤ ε`, i.e.
  `sup_t |F_λ − Φ| → 0`; the pointwise statements are also provided.
* The empirical distribution of `f(R_λ(p))` over `𝒜_{λ,i}` is stated over
  the primes themselves: counts of `p ∈ 𝒫_{λ,i}` with
  `f(R_λ(p)) ≤ L + t√L`, normalised by `π_{λ,i}` — exactly the display in
  Theorem 1.2. (Internally the criterion is applied to the family
  `AFam b i`, which is `𝒜_{λ,i}` patched to `{1}` at the finitely many λ
  where it is empty — the paper's footnote; the two agree eventually and
  all statements are asymptotic.)
* In Theorem 1.1/1.2 the normalisation is `L = log log b^λ` (`LL b lam`),
  as in the paper's eq. (1.3).

## 3. What is *not* machine-checked (honest inventory)

1. **The axioms themselves.** By design. Their transcriptions follow the
   paper's quotations. A partial cross-check against the original sources
   was subsequently performed (see §1): `gs_prop3` and `drs_thm13` match
   their originals; `bsh_thm7` is corroborated through an independent
   secondary quotation; `col_thm2` could not be independently accessed and
   rests on the manuscript's transcription.
2. **The uniformity in `k` of Theorem 1.5** (`k ≤ ½L^{1/3}` with the
   explicit error `O(k^{3/2}L^{-1/2})`). What is machine-checked is the
   moment convergence at **every fixed order `k`**
   (`pal_moments`, `rev_moments_loc`, `criterion_moments`), which is
   exactly what the proofs of Theorems 1.1 and 1.2 use — as the paper
   itself notes ("Theorems 1.1 and 1.2 use only the case of fixed k").
   The uniform range would additionally require tracking the `O(log 2k)`
   dependence through Lemma 2.3 and the Lyapunov interpolation step with
   explicit constants; this refinement was not formalised.
3. **The Chebotarev instantiation in Corollary 1.6.** The corollary is
   formalised for an **arbitrary regular set `S`** (`IsRegular S δ`),
   which is its mathematical content. The step "for a finite Galois
   extension, `S_𝒞` is regular of density `#𝒞/[K:ℚ]`" (Chebotarev with
   the Lagarias–Odlyzko error term plus partial summation, quoted from
   the literature in the proof of Corollary 1.6) is not formalised and is
   not among the axioms: to apply the Lean theorems to a Frobenius set
   one must supply the `IsRegular` instance.
4. **Numerical remarks and asides** (admissible values of `β(b)`,
   Example 4.3, §5 Remarks) — expository, not formalised.

## 4. Where the formal proof deviates from the paper (same theorems)

Two deliberate design changes, both *strengthening-free* simplifications
made possible by working at fixed moment order; they change the proof, not
the statements:

1. **Truncation `K = 2k+1` and Cauchy–Schwarz instead of Lyapunov.**
   For the `k`-th moment the paper truncates at `y = b^{ξλ/(k+1)}` and
   controls the binomial cross-terms `avg|W|^j` (`j < k`) by Lyapunov's
   interpolation inequality. The formal proof truncates at
   `y = b^{ξλ/(2k+1)}`, so that all moments up to order `2k` stay within
   the level of distribution, and bounds odd/cross moments by
   Cauchy–Schwarz against the even ones
   (`sq_sum_abs_pow_le`, `Wc_abs_moment_bound`). At fixed `k` this loses
   only constants.
2. **Lemma 3.3(iii), large moduli.** For `m ≥ 3` the paper telescopes
   `∑_{ℓ > u_m} ℓ^{-m/2} ≪ u_m^{1-m/2}`; the formal proof uses the
   slightly cruder `(√ℓ)^{-m} ≤ ℓ^{-1} b^{-ξλ/6}` together with Mertens'
   crude bound `∑_{ℓ ≤ b^λ} 1/ℓ ≤ L + O(1)`, giving `≪ λ²L·b^{-ξλ/6} → 0`
   — same conclusion. Similarly, in Lemma 4.2(ii) the block exponent is
   taken as `j = m` rather than `j = ⌈m/v⌉` (enough for `O(1)`), and in
   Lemma 4.5 the internal level `ξ` is chosen `≤ log 2/(4 log b)` so that
   `ℓ^m ≤ b^{ξλ}` automatically forces `2m ≤ λ`.

Additionally, some `O(1)`-style constants are tracked explicitly (e.g.
`|μ_𝒬 − δL| ≤ c₁` rather than `O(log 2k)`, sufficient at fixed `k`), and
`ε`-management in limit arguments follows Lean idioms rather than the
paper's `o(1)` calculus.

## 5. Sanity checks

`lean/EKRev/Sanity.lean` contains compile-time `#guard`s evaluating the
combinatorial definitions on concrete instances (digit extraction,
reversal `R₃(149) = 941`, palindrome counts `#𝒯₃ = 90` in base 10,
two-digit prime counts, `ω(12) = 2`, `Ω(12) = 3`, …), guarding against
definitional slips (off-by-one in digit ranges, endpoint conventions).

## 6. Reproducing the check

See `README.md`. In short: install `elan`, then, from the `lean/`
directory,

```
lake exe cache get   # fetch the Mathlib binary cache
lake build           # ≈ builds EKRev and the audit prerequisites
lake env lean AxiomAudit.lean   # print the axiom closure of each theorem
```

A successful `lake build` with the recorded `lean-toolchain` and
`lake-manifest.json` reproduces the verification; the expected audit
output is in `lean/axiom_audit.txt`.
