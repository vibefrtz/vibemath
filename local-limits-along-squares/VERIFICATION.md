# Verification report

This repository contains a machine-checked Lean 4 verification of part of the
paper

> *Local limits along squares and prime values of digital functions*

namely: **the prescribed-digit-sum theorem and the entire construction
feeding it** (§7.1 with Theorem 1.8, Corollary 1.9 in bases 2 and 3, and
Remark 7.3), verified **unconditionally** — with no axioms beyond Lean's
three built-in ones — including a full Lean proof of the Bose–Chowla theorem
that the paper quotes; **the engine of the new square local limit
theorem, the two-digit spectral gap Lemma 2.4, in full and in every base**
(the gcd identity (17), a finset Bezout combination, the distance estimate
(18), the lattice direction, the scalar gap `1 − cos 2πx ≥ 8‖x‖²`, and, in
base 2, the explicit constant `2/5`); **the
binary-endpoint audit of Remark 2.3** as exact rational arithmetic; **the
lattice density `ρ_{g,□}`** with its normalisation, its reduced-class mass
`φ(d)` (the constant `κ = 1` of Corollary 1.4), and the restriction
equivalence `(n,d)=1 ⇔ (g(n²),d)=1`; **the whole local-factor theory of
Theorem 5.12** — the values of `N(c,d)` at primes and prime powers, its
multiplicativity by the Chinese remainder theorem, the **product formula
(60) for an arbitrary modulus** and the **mean formula (61)**; **the finite
Fourier identity (37)** that produces `ρ_{g,□}` from the arc-centre
coefficients; **the `h_g`-scaling reduction of Theorem 2.1 to Theorem 1.1**;
**the complement and linear-blocking lemmas of §7.2** for arbitrary digit
weights, together with **the infinitude half of Theorem 7.5 in degree one**;
**the exact reciprocal identity `S₀ = S − S(·/10)/10` of §8** at every
height; the elementary content of §5 and §2; **Corollary 4.6** (the `P₂`
theorem along the primes), proved from exactly two axioms transcribing the
two results the paper's proof quotes; **Corollary 1.3 (`P₂` part), the
almost-prime theorem on squares, machine-checked as an implication**: the
statement of Theorem 1.1 is transcribed as a *definition* (`SquareLLT`,
never an axiom), and

> `SquareLLT g` ∧ (Halberstam–Heath-Brown–Richert, as transcribed in
> `Cited.lean`) ⟹ `#{n ≤ x : g(n²) is a P₂} ≫ x/log log x` when
> `μ_g > 0`, `d_g = 1`

is proved with **`hhbr` as the only axiom** — the build-time guard certifies
that `mmr` does not enter; and — new in this revision — **Theorem 1.2, the
output-distribution theorem on squares, machine-checked as an implication
that uses *no axiom at all***.  Both clauses of Theorem 1.1 are definitions
(`SquareLLT`, `SquareTail`), and

> `SquareLLT g` ∧ `SquareTail g` ⟹
> `∑_{m ≤ Q_η(L), (m,d_g)=1} max_{a mod m} |Δ_{g,□}(x;m,a)| ≪_{η,ε} x·L^{−1/2+ε}`

is proved from them in the unweighted (`B = 1`) form, with **Poisson
summation for the Gaussian — the paper's Lemma 4.3 — proved from Mathlib's
Jacobi theta transformation** rather than assumed; and — also new — **the
Fourier assembly of Theorem 1.1 itself (the paper's §2.4), machine-checked
as an implication with no axiom at all**.  The two remaining analytic
inputs are transcribed as *definitions* — `SquareMinor` for the integrated
minor-arc estimate (Corollary 2.7) and `SquareMajor` for the shrinking
major-arc Gaussian expansion (Proposition 2.8), never axioms — and

> `SquareMinor g` ∧ `SquareMajor g` ⟹ `SquareLLT g`

is proved (`squareLLT_of_arcs`): Fourier inversion over a fundamental
window, the exact splitting into the `d_g` major arcs and the minor set,
the Gaussian Fourier transform
`∫ e(βu)·e^{−αu²} du = √(π/α)·e^{−π²β²/α}`, the Gaussian tail, and the
collection of the arc-centre coefficients into `ρ_{g,□}` by the finite
Fourier identity (37).  The unverified surface of Theorem 1.1 is thereby
exactly the two named square-method estimates, plus Proposition 2.10
(= `SquareTail`) on the tail side.

* **Toolchain**: Lean 4 `v4.33.0`, Mathlib tag `v4.33.0`.
* **Size**: ≈10 400 lines of Lean across 31 modules.
* **`sorry` count**: 0.  **Build warnings**: 0.
* **Axioms declared**: 2, both in `DSS/Cited.lean`, both audited in
  [`SOURCE_AUDIT.md`](SOURCE_AUDIT.md).
* **Audited results**: 107, of which exactly 3 (Corollary 4.6 and its two
  instances) depend on both axioms and 2 (the square `P₂` implication and
  its binary instance) on `hhbr` alone; the other 102 — including
  Theorem 1.8, the complete Lemma 2.4, Theorem 5.12's local factors,
  Lemma 4.3, **Theorem 1.2 as an implication**, and **the §2.4 assembly of
  Theorem 1.1** — depend on none.
* **Axiom discipline**: enforced at build time by `DSS/Guard.lean`
  (`#assert_axioms`), not merely documented.
* **Mathlib surface**: `DSS/Imports.lean`; `import Mathlib` and
  `import Mathlib.Tactic` are deliberately avoided.  The named Mathlib inputs
  to the unconditional half are Bertrand's postulate
  (`Nat.exists_prime_lt_and_le_two_mul`), Dirichlet's theorem on primes in
  arithmetic progressions (`Nat.forall_exists_prime_gt_and_modEq`), the
  finite-field library (`GaloisField`, cyclicity of the unit group),
  Jordan's inequality (`Real.mul_le_sin`) for the spectral gap, and — new —
  the complex Gaussian integral with a real shift
  (`GaussianFourier.integral_cexp_neg_mul_sq_add_real_mul_I`), the real
  Gaussian integral (`integral_gaussian`), and the closed form
  `∫_a^b e^{cx} dx` (`integral_exp_mul_complex`) for the §2.4 assembly.

## 1. The axiom base (`DSS/Cited.lean`)

| Axiom | Source quoted by the paper | Used for |
|---|---|---|
| `mmr` | Martin–Mauduit–Rivat, J. Inst. Math. Jussieu **18** (2019), Théorème 1, at `β = 0` | Corollary 4.6 |
| `hhbr` | Halberstam–Heath-Brown–Richert, *Almost-primes in short intervals*, Durham 1979 proceedings (1981), 69–101, at the admissible exponent `θ = 0.455` | Corollary 4.6 **and** the square implication `square_p2_of_llt` |

`mmr` is **identical, word for word, to the axiom of the predecessor
repository** (`prime-values-digital-functions`), where it was compared with
Théorème 1 of the source clause by clause and validated numerically; that
audit carries over verbatim and is reproduced in `SOURCE_AUDIT.md` §1.
`SOURCE_AUDIT.md` §2 records the `hhbr` transcription and the accessibility
caveat for the Durham proceedings volume.

`Guard.lean` certifies that the square output-distribution theorem
(Theorem 1.2, `square_output_level`) depends on **neither** axiom: it is an
implication between the paper's own statements, and the only external input
is Mathlib.

**The paper's own Theorem 1.1 is *not* an axiom.**  Under the discipline of
this development, axioms transcribe literature results only; and the paper's
proof of Theorem 1.1 adapts the internals of Mauduit–Rivat and Morgenbesser
rather than quoting black-box statements, so those engines cannot be
transcribed faithfully either.  Instead `DSS/SquareLLT.lean` *defines* the
property `SquareLLT g` — the conclusion of Theorem 1.1, with the same
encoding conventions as `mmr` (quantifier order `∀ ε, ∃ C, ∀ x > 2, ∀ k`;
real cut-offs; the congruence by `Int.emod`; the error
`C·x·(max 1 (log L))^{5+ε}/L`, where the `max` is what makes the transcription
non-vacuous near `x = b` and equivalent to the paper's `O`-statement as
`x → ∞`) — and the sieve consequence is proved as an implication.

## 2. Paper ↔ Lean correspondence

### Definitions

| Paper | Lean | File |
|---|---|---|
| `s_b(n)` | `sb b n` | `Digits.lean` |
| Sidon set | `IsSidon` | `Sidon.lean` |
| `a_T = 1 + ∑_{r∈T} b^r`, eq. (75) | `aT b T` | `CarryFree.lean` |
| admissible `q` (`q ≡ □ mod b−1`) | `u ^ 2 ≡ q [MOD b - 1]` | `Squares.lean` |
| the solutions of Thm 1.8 | `sqSols b q` | `Squares.lean` |
| `ℓ_b(n)`; `F_w`, eq. (51) | `lb b n`; `Fw b w n` | `FWeight.lean` |
| `g_w(a) = w_a − w₀` | `gw b w hb` | `FWeight.lean` |
| `Z_b(n)` | `Zb b n` | `FWeight.lean` |
| the zero-count weight of Cor. 5.5/5.9 | `zeroWeight b hb` | `FWeight.lean` |
| Example 5.13's weight `(1,2,−3)` in base 3 | `exWeight3` | `FWeight.lean` |
| the base-4 example `(0,1,2,−3)` | `exWeight4` | `FWeight.lean` |
| the digit sum as a weight | `sbWeight b hb` | `FWeight.lean` |
| `P_2` | `IsP2` | `Cited.lean` |
| `#{p ≤ x : g(p) ∈ P₂}` | `(p2Primes g x).card` | `P2.lean` |
| strongly `b`-additive `g`; `μ_g, σ_g², d_g`; `π(x)`, `π_k(x)`, `#{p ≤ x : g(p)=k}` | `Weight b`; `Weight.mu/sigSq/dg`; `picount`, `piCong`, `countEq` | `Weight.lean`, `Counting.lean` |
| **`ρ_{g,□}(k)`, eq. (4)** | `rhoSq g k` | `RhoSquare.lean` |
| **`#{1 ≤ n ≤ x : g(n²) = k}`** | `sqCountEq g x k` | `SquareLLT.lean` |
| **the main term of eq. (5)** | `sqMain g x k` | `SquareLLT.lean` |
| **the conclusion of Theorem 1.1, as a hypothesis** | `SquareLLT g` (a `def`) | `SquareLLT.lean` |
| **the tail clause (6), as a hypothesis** | `SquareTail g` (a `def`) | `OutputLevel.lean` |
| **`Q_η(L) = √L/(log L)^{1/2+η}`, eq. (7)** | `Qeta η L` | `OutputLevel.lean` |
| **`Δ_{g,□}(x;m,a)`** (defined in §1.2) | `deltaSq g x m a`; `deltaSqMax` for `max_a |·|` | `OutputLevel.lean` |
| **the moduli of eq. (8)** | `moduli g x η` | `OutputLevel.lean` |
| **the Gaussian factor `G_L(k)` of eq. (5)** | `gaussKer s y k` (`s = 2σ_g²L`, `y = 2μ_gL`) | `OutputLevel.lean` |
| **`e(t) = e^{2πit}`; the arc coefficients `η_j`** | `ee t`; `etaSq g j` | `RhoFourier.lean` |
| **`h·g̃` (eq. (12) read backwards); `ρ_{g,□}` of (13)** | `Weight.smulW h g`; `rhoSqGen h g k` | `SquareGeneral.lean` |
| **the conclusion of Theorem 2.1 (eq. (14)), as a `Prop`** | `SquareLLTGen h g` (a `def`) | `SquareGeneral.lean` |
| **`N(c,d)` read in `ZMod d`** | `nbothZ c` | `KappaM.lean` |
| **the constant `C` of Prop. 7.8(i), degree one** | `blockConst g u c` | `Blocking.lean` |
| **`A_θ(t)`, eq. (15)** | `digitalFactor g θ t` | `SpectralGap.lean` |
| **`‖x‖`, distance to the nearest integer** | `dist01 x` | `SpectralGap.lean` |
| **`N(c,d) = #{a mod d : (a,d)=(a−c,d)=1}`, inside (58)** | `nboth c d` | `KappaM.lean` |
| **`∑_{n≤N, Q(g(n²))} 1/n` and its `b∤n` restriction (§8)** | `recipSum`, `recipSumCop` | `ShiftSquares.lean` |

### The paper's own results

| Paper | Lean | Axioms |
|---|---|---|
| eq. (77): digit sums add along blocks | `sb_add_pow_mul` | none |
| eq. (78): the complement rule | `sb_pow_sub` | none |
| carries do not occur below `b` | `sb_sum_pow`, `sb_sum_over` | none |
| **Lemma 7.1** (via Bose–Chowla + Bertrand) | `bose_chowla`, `exists_sidon_of_card`, `transform_props` | none |
| **Lemma 7.2**, case `b ≥ 3` | `sb_aT_sq`, `sb_aT_sq_sub_one`, `sb_two_aT_sub_one`, `sb_shifted_sq` | none |
| **Lemma 7.2**, case `b = 2` | `aT_sq_eq_sum_expSet`, `card_expSet`, `sb_shifted_sq_two` | none |
| distinct `T` give distinct roots | `sum_pow_injective`, `aT_injective` | none |
| `(a_T b^k − 1, b) = 1` | `coprime_shifted` | none |
| **Theorem 1.8**, `b ≥ 3` | `sq_digit_sum_count` | none |
| **Theorem 1.8**, `b = 2` | `sq_digit_sum_count_two` | none |
| **Corollary 1.9**, bases 2 and 3 | `sq_prime_digit_sum_count_two`, `_three` | none |
| **Remark 7.3**: `s_b((2b^k−1)²) = k(b−1)+1` | `sb_singleton` | none |
| Remark 7.3 + Dirichlet: infinitude | `infinite_coprime_sq_prime_digit_sum` | none |
| eq. (52): the split `F_w = w₀ℓ_b + g_w` | `Fw_eq_split`, `Zb_eq_Fw` | none |
| the zero weight's parameters: `μ = −(b−1)/b`, `σ² = (b−1)/b²`, `d = 1`, exact shell centre | `zeroWeight_mu`, `zeroWeight_sigSq`, `zeroWeight_dg`, `zeroWeight_shell_centre` | none |
| **Example 5.13**: odd shells force `F(p) = 2` | `base3_odd_shell_forcing` | none |
| the base-4 example: `d_g = 3`, `μ_g = 0` | `exWeight4_dg`, `exWeight4_mu`, `exWeight4_coprime₁` | none |
| `d = 1`, `μ = 1/2` for the binary digit sum | `sbWeight_two_dg`, `sbWeight_two_mu` | none |
| the `d_g` theory (`σ_g > 0`, `(g(1),d_g)=1`, congruence (3)) | `Weight.sigSq_pos`, `Weight.coprime_w_one_dg`, `Weight.dg_dvd_eval_sub` | none |
| the binomial lower bound `C(m,t) ≥ 2^{m/3}` | `two_pow_le_choose`, `two_pow_le_choose_of_le` | none |
| **eq. (17)**: `gcd((b−1)g(1), m₂, …) = d_g` (the Bezout step of Lemma 2.4) | `gcd_bezout` | none |
| **Lemma 2.4, lattice direction**: `d_gθ ∈ ℤ ⇒ ‖A_θ(t)A_θ(bt)‖ = 1` at `t = −θg(1)` | `lattice_abs_one` | none |
| **Lemma 2.4, scalar gap**: `1 − cos 2πx ≥ 8‖x‖²` | `one_sub_cos_ge` | none |
| **Lemma 2.4, case `b = 2`, in full**: `‖A_θ(t)A_θ(2t)‖ ≤ exp(−(2/5)‖θ‖²)` | `two_digit_gap_two` | none |
| **Lemma 2.4 in every base**: `∃ c_g > 0, ‖A_θ(t)A_θ(bt)‖ ≤ exp(−c_g‖d_gθ‖²)` | `two_digit_gap`; `finset_gcd_bezout`, `dg_combination`, `dist01_dg_le`, `norm_digitalFactor_le_pair` | none |
| **the §2.4 assembly of Theorem 1.1 as an implication**: `SquareMinor ∧ SquareMajor ⟹ SquareLLT` | `squareLLT_of_arcs`; `SquareMinor`, `SquareMajor` are *definitions* | **none** |
| its steps: character orthogonality and Fourier inversion; the window split; the arc translation; the Gaussian transform and tail; `‖η_j‖ ≤ 1`; the bounded-`x` absorption | `integral_ee_mul_int`, `sqPhi_inversion`; `window_split`; `arc_integral_eq`; `integral_ee_gaussian`, `gaussian_tail_bound`; `norm_etaSq_le_one`; `small_x_bound` | none |
| **Remark 2.3** (the binary-endpoint audit): bracket `= (16/9)(1+25ξ/8)`, sum `= 32ν/25+3`, domination for `ν > 10` | `binary_bracket_eval/gt`, `binary_sum_eval`, `binary_domination(_sharp)` | none |
| **`ρ_{g,□}` for `d_g = 1` is `≡ 1`** (the `P₂` situation) | `rhoSq_dg_one` | none |
| **normalisation (40)**: `∑_{k mod d} ρ_{g,□}(k) = d` | `sum_rhoSq` | none |
| **`κ_ρ = 1`** (Cor. 1.4's constant): `∑_{(k,d)=1} ρ_{g,□}(k) = φ(d)` | `sum_rhoSq_coprime` | none |
| **the restriction equivalence of Thm 1.2**: `(n,d)=1 ⇔ (g(n²),d)=1` | `coprime_eval_sq_iff` | none |
| the encoding check `∑_k sqCountEq = #{n ≤ x}` | `sum_sqCountEq` | none |
| **Theorem 5.12 at a prime**: `N(c,ℓ) = ℓ−1` (`ℓ∣c`) or `ℓ−2` | `nboth_prime` | none |
| **Theorem 5.12 at a prime power**: `N(c,ℓ^e) = ℓ^{e−1}N(c,ℓ)`, and the local factor of (60) is unchanged | `nboth_prime_pow`, `kappaM_prime`, `kappaM_prime_pow` | none |
| **the per-prime average identity behind (61)** | `local_average` | none |
| **Theorem 5.12, multiplicativity of (58)**: `N(c,d₁d₂) = N(c,d₁)N(c,d₂)` for `(d₁,d₂)=1`, by `ZMod.chineseRemainder` | `nboth_mul` | none |
| **Theorem 5.12, the product formula (60) for an arbitrary `d`** | `kappaM_product` | none |
| **Theorem 5.12, the mean formula (61)**: `(1/d)∑_{m<d} κ_m(A,d) = ∏_{ℓ∣d, ℓ∣A} ℓ/(ℓ−1)` | `kappaM_average` | none |
| **eq. (37)**: `∑_j η_j e(−jk/d) = ρ_{g,□}(k)`, from root-of-unity orthogonality | `rhoSq_fourier`, `sum_ee_mul_eq` | none |
| **the scaling of §2**: `(h·g)(n) = h·g(n)`, `μ_{hg} = hμ_g`, `σ²_{hg} = h²σ²_g` | `Weight.eval_smulW`, `Weight.mu_smulW`, `Weight.sigSq_smulW` | none |
| **Theorem 2.1 from Theorem 1.1** (the `h_g`-scaling), as an implication | `squareLLT_general` | none |
| **Lemma 4.3** (Gaussian sums in progressions), from Jacobi's theta transformation | `gaussian_progression`; `tsum_gauss_shift`, `abs_tsum_gauss_shift_sub` | none |
| **Theorem 1.2, unweighted (`B = 1`), as an implication from `SquareLLT` and `SquareTail`** | `square_output_level` | **none** |
| the steps of its proof: the CRT class split, the window truncation, the per-class and per-modulus estimates | `sqCountCong_crt`, `sqCountCong_window`, `class_bound`, `modulus_bound` | none |
| the Gaussian mass on a class, and outside the central window | `gaussKer_class`, `gaussKer_tail` | none |
| **Theorem 7.5, the infinitude half in degree one** (via Dirichlet) | `infinite_prime_linear_blocking` | none |
| **`g((bn)²) = g(n²)`** and the exact identity `S₀(N) = S(N) − S(N/b)/b` (§8) | `eval_sq_base_mul`, `recipSum_split` | none |
| **Lemma 7.6** for arbitrary weights: `g(b^k − c) = k·g(b−1) + C_{g,c}` | `ofDigits_comp`, `eval_pow_sub` | none |
| block additivity `g(r + b^k m) = g(r) + g(m)` | `eval_add_pow_mul` | none |
| **Proposition 7.8(i), degree one**: `g(u·b^k − c) = k·g(b−1) + C` | `eval_linear_blocking` | none |
| **Corollary 4.6** (`P₂` along the primes) | `p2_count` | `mmr`, `hhbr` |
| Corollary 4.6 for `S` and for `s_2` | `p2_count_S`, `p2_count_binary` | `mmr`, `hhbr` |
| **Corollary 1.3, `P₂` part, as an implication from Theorem 1.1** | `square_p2_of_llt` | `hhbr` only |
| the `s_2` instance of Corollary 1.3 | `square_p2_binary` | `hhbr` only |

## 3. Encoding conventions, and why they matter

* **Theorem 1.8 is fully explicit.**  Where the paper has unspecified
  constants `c_b, C_b` and "sufficiently large", the Lean statement has
  `2^(√q/(36b))` representations, the digit bound `n² ≤ b^{3q}`, and the
  threshold `q ≥ 2304·b⁴` (`36864` for `b = 2`).  These are *effective* but
  not optimal; any reader can weaken them to the paper's form.  Admissibility
  is the hypothesis `u² ≡ q (mod b−1)`, literally the paper's condition; for
  `b = 2` it is vacuous and the Lean statement drops it, as does the paper.
* **`Nat` subtraction never hides an argument.**  All digit-sum identities
  with subtractions are stated additively (`sb_pow_sub` reads
  `s_b(b^k − c) + s_b(c−1) = k(b−1)`; `ofDigits_comp` reads
  `comp + value + 1 = b^len`), so no truncated subtraction can make a
  statement vacuously true.  In `eval_pow_sub` the subtraction `b^k − c` is
  guarded by the hypothesis `c ≤ b^k`, and the constant is written in `ℤ`.
* **`SquareLLT` is calibrated to be neither vacuous nor overstated.**  The
  error is `C·x·(max 1 (log log_b x))^{5+ε}/log_b x`.  Without the `max` the
  statement would be *false* near `x = b` (where `log L → 0` while the count
  does not), i.e. unprovable and useless as a hypothesis; with it, the
  property is equivalent to the paper's `O_{b,g,ε}(x(log L)^{5+ε}/L)` as
  `x → ∞`, since on any bounded range of `L` both the count and the main
  term are `O(x/L)`.  The quantifier order (`∀ ε, ∃ C, ∀ x, ∀ k`) matches
  the `mmr` axiom's and the paper's uniformity claim.
* **`SquareTail` needs no `max` guard.**  Eq. (6) is transcribed literally,
  `#{n ≤ x : |g(n²) − 2μ_gL| > C√L log L} ≤ A·x·exp(−c(log L)²)` for all
  `x > 2`.  Unlike `SquareLLT`, no truncation is needed: on the bounded range
  of `L` where `log L ≤ 1` the right side is bounded below by a positive
  multiple of `x` (`(log L)²` is bounded there, since `L ≥ log_b 2 > 0`),
  while the left side never exceeds `x`, so a larger `A` absorbs it.  The
  statement is therefore equivalent to the paper's `≪` as `x → ∞`.
* **Theorem 1.2 is stated with `x/m`, not `⌊x⌋/m`.**  This matches eq. (7)
  of the paper and is consistent with `sqMain`, whose main term also carries
  the real `x`; the difference is `O(1)` per modulus and `O(Q_η(L))` after
  the sum, far below `x·L^{−1/2+ε}`.
* **`max_{a mod m}` is a `Finset.fold max`.**  `deltaSqMax g x m` is
  `(range m).fold max 0 (fun a => |Δ_{g,□}(x;m,a)|)`, so that
  `deltaSqMax ≤ B` unfolds (`Finset.fold_max_le`) to `0 ≤ B` together with
  the bound at every residue — exactly the maximum over `a mod m`, with the
  value `0` at `m = 0` where the paper's statement is empty.
* **Lemma 4.3 is stated with explicit constants.**  The paper's
  `O_{σ,η}(e^{−c_η(log L)^{1+2η}})` becomes
  `|(2πs)^{−1/2}∑_{k≡c(M)}e^{−(k−y)²/(2s)} − 1/M| ≤ (4/M)e^{−2π²s/M²}`
  under `M² ≤ 2π²s`; substituting `s = 2σ_g²L` and `M ≤ d_gQ_η(L)` turns the
  rate into `(4π²σ_g²/d_g²)(log L)^{1+2η}`, which is the paper's `c_η`.
* **Theorem 1.2's `≪` is `∃ C, ∃ x₀, ∀ x ≥ x₀`.**  The constants depend on
  `b, g, η, ε` — which are fixed before `C` is produced, matching the paper's
  `≪_{b,g,η,ε}` — and the estimate is uniform in `x` beyond an explicit
  threshold, which is the usual reading of `≪` for an `x → ∞` statement.
* **Corollary 4.6's and Corollary 1.3's normalisation.**  The paper states
  the counts against `x/log₂x`; the Lean statements use `x/log log x` with an
  unspecified constant `c > 0`, the same assertion (the two normalisations
  differ by the bounded factor `log log b`).  In `p2_count` the factor
  `π(x)` is the exact prime count, so no prime number theorem enters
  anywhere; in `square_p2_of_llt` the factor is the real cut-off `x` itself.
* **`g(n²) ∈ P₂` is rendered** `∃ m : ℕ, IsP2 m ∧ g.eval (n²) = (m : ℤ)`,
  never through `natAbs`.
* **The window book-keeping is deterministic.**  Both `p2_count` and
  `square_p2_of_llt` introduce every threshold explicitly
  (`exists_rpow_threshold`), so `x₀` is in principle extractable from the
  proof term.
* **The spectral-gap constant is explicit.**  `two_digit_gap_two` proves the
  binary case of Lemma 2.4 with `c_g = 2/5`: the chain is
  `1 − cos 2πφ ≥ 8‖φ‖²` (Jordan), `‖A‖² ≤ 1 − 4‖φ‖² ≤ e^{−4‖φ‖²}`,
  `‖θ‖ ≤ 2x + y`, and `(2x+y)² ≤ 5(x²+y²)`.

## 4. Where the formal proof differs from the paper's (same theorem)

1. **Bose–Chowla is proved, not quoted.**  The paper's Lemma 7.1 cites Bose
   and Chowla (1962/63) for a Sidon set of size `≥ ½√N` in `[1, N]`.  The
   formalisation instead *proves* the underlying construction: for `p` prime,
   the discrete logarithms of `θ + a`, `a ∈ F_p`, `θ` a generator of
   `F_{p²}^×`, form a Sidon set of `p` integers below `p²` (`bose_chowla`),
   and Bertrand's postulate (Mathlib) turns this into a Sidon set of any
   prescribed size `m` inside `[0, 4m²)` (`exists_sidon_of_card`).  The
   interval normalisation of Lemma 7.1 (translate into the top half, double)
   is `transform_props`, exactly as in the paper.
2. **The `t`-selection is by an explicit residue window.**  The paper picks
   `t ≡ t₀ (mod b−1)` in `[m/3, 2m/3]`; the formal proof takes the least such
   `t ≥ ⌊m/3⌋` (`exists_residue_in_window`) and checks `t ≤ m`,
   `min(t, m−t) ≥ ⌊m/3⌋` — which is all the binomial bound needs.
3. **Corollary 1.9 is formalised for `b = 2, 3` only.**  The paper's proof
   takes a prime `q ≡ 1 (mod b−1)` in a dyadic window, i.e. the prime number
   theorem for progressions.  In bases 2 and 3 admissibility is free
   (mod 1, resp. every odd prime mod 2) and Bertrand suffices; for `b ≥ 4`
   the statement is not formalised (see §5).
4. **The `P₂` targets are collected on an explicit arithmetic progression of
   interval endpoints** `z_i = y + Δ(i+1)`, `Δ = (2y)^{0.455}`, rather than
   by the paper's iteration `z ↦ z − z^θ`; the intervals
   `(z_i − z_i^θ, z_i]` are pairwise disjoint because the spacing `Δ`
   dominates `z_i^θ`, and each carries `hhbr`'s quota.  This changes only
   constants.  The square proof (`square_p2_of_llt`) uses the same
   construction with `y = 2μ_gL` and the doubled variance `2σ_g²`.
5. **The Gaussian window is `H = √L` rather than `σ_g√L`**, so the pointwise
   lower bound at the half-window is `exp(−1/(8s))` times the peak
   (`gaussian_lower`, with `s = σ_g²` on primes and `s = 2σ_g²` on squares);
   again only constants move.
6. **The error absorption in `square_p2_of_llt` is by explicit log-power
   bounds**: `log L ≤ δ⁻¹L^δ` (`log_le_inv_mul_rpow`) at `δ = 1/28` gives
   `(log L)^m ≤ 28^m·L^{1/4}` for `m ≤ 7` (`log_pow_le_rpow`), which is all
   that `O(x(log L)^6/√L) = o(x/log L)` needs.
7. **Theorem 1.2's proof is organised modulo `m·d_g`, not modulo `m`.**  The
   paper splits `∑_{k≡a (m)}ρ(k)G_L(k)` by the residue of `k` modulo `d = d_g`
   and applies the Poisson estimate to each of the `d` resulting classes
   modulo `md`.  The formalisation performs the same split one step earlier,
   on the *counting* side: `#{n ≤ x : g(n²) ≡ a (m)}` is written as a sum of
   `d` counts on classes modulo `md` (`sqCountCong_crt`), on each of which
   `ρ_{g,□}` is *constant* (`rhoSq_class`).  The lattice sums are then single
   applications of Lemma 4.3, with no splitting inside a `tsum`.  The
   normalisation `∑_{r mod d}ρ_{g,□}(r) = d` (`sum_rhoSq`) is what makes the
   `d` main terms add up to `x/m`.
8. **The central window is indexed by `j`, not by `k`.**  For a class
   `c mod M` the window is `{Mj + c : ⌈(y−W−c)/M⌉ ≤ j ≤ ⌊(y+W−c)/M⌋}` with
   `y = 2μ_gL`, `W = C√L log L`.  This makes the window count exactly
   `≤ 2W/M + 1`, makes "outside the window" literally `|Mj+c−y| > W` (so the
   tail clause applies verbatim), and keeps every comparison between the
   finite sum and the `tsum` over `ℤ` a single `tsum_eq_sum`.
9. **The Gaussian tail outside the window is bounded by splitting the
   exponent**, `e^{−t²/(2s)} ≤ e^{−W²/(4s)}e^{−t²/(4s)}` for `|t| ≥ W`, and
   then applying the same theta bound at the halved rate; this gives
   `≤ (3√2/M)e^{−W²/(4s)}` (`gaussKer_tail`) without any new analysis.
10. **The binary spectral gap's constant differs from the paper's.**  The
   paper asserts existence of `c_g`; the formal statement fixes `c_g = 2/5`,
   which the same argument yields.  (Only existence is consumed downstream.)
11. **The general-base gap keeps one phase pair instead of the double sum.**
   The paper expands `1 − |A_θ(t)|²` over all digit pairs; the formal proof
   bounds `‖∑_c E_c‖ ≤ ‖E_0 + E_a‖ + (b−2)` by the triangle inequality,
   giving `‖A_θ(t)‖ ≤ 1 − (4/b)‖θg(a)+at‖²` for each digit `1 ≤ a < b`
   separately, and replaces the paper's Cauchy–Schwarz over the `b − 1`
   distances by the maximal one.  Only the value of `c_g` changes.
12. **The assembly realises `ℝ/ℤ` as the window `(−1/(2d_g), 1 − 1/(2d_g)]`**,
   so that no major arc wraps around once `T/√L < 1/(2d_g)` (a threshold
   made explicit through `log L ≤ 4·L^{1/4}`).  `sqPhi` is the unnormalised
   sum `x·Φ_x`; `SquareMinor`'s domain differs from Corollary 2.7's
   `{θ : dist(θ, d⁻¹ℤ) > T/√L}` only in endpoints, a set of measure zero;
   and `SquareMajor` states Proposition 2.8 with the remainder eliminated —
   the integrated distance of `Φ` from the Gaussian model — which is
   equivalent to the paper's decomposition-plus-`L¹`-bound.  The quantifier
   order `∀ ε, ∃ C, ∃ L₀, ∀ x` matches the `mmr` conventions.

## 5. What is *not* machine-checked (honest inventory)

1. **The two axioms.**  `mmr` and `hhbr` are assumptions; everything that
   uses them is conditional on them.  See `SOURCE_AUDIT.md`.
2. **The two shrinking-frequency estimates behind Theorem 1.1** (§2): the
   quantitative transfer through the Mauduit–Rivat square method
   (Prop. 2.6, hence its integrated Corollary 2.7) and the major-arc moment
   comparison (Prop. 2.8), together with the tail (Prop. 2.10).  These
   adapt the internals of published proofs; they are transcribed as the
   *definitions* `SquareMinor`, `SquareMajor` and `SquareTail`, never as
   axioms.  Everything else in the proof of Theorem 1.1 *is* now checked:
   the engine (Lemma 2.4 in full, in every base), the parameter audit of
   Remark 2.3, and the entire §2.4 assembly
   (`SquareMinor ∧ SquareMajor ⟹ SquareLLT`, `squareLLT_of_arcs`) — so the
   human-trust surface of Theorem 1.1 is exactly the two named estimates.
   Everything downstream of Theorem 1.1's *statement* that the development
   touches is likewise checked as an implication (`SquareLLT g → …`).
3. **The `B^{ω(m)}`-weighted form of Theorem 1.2**, and Proposition 4.4 in
   its abstract form.  The unweighted case `B = 1` of Theorem 1.2 *is*
   verified (`square_output_level`), Lemma 4.3 with it; the weighted case
   needs `∑_{m≤Q}B^{ω(m)}/m ≪ (log Q)^B`, which rests on Mertens'
   `∑_{p≤x}1/p = log log x + O(1)`.  Mathlib at this pin has the divergence
   of `∑1/p` (`not_summable_one_div_on_primes`) but no quantitative form, so
   the weighted sum is out of reach; the unweighted one needs only the
   harmonic bound `H_n ≤ 1 + log n`, which Mathlib does have.  Proposition 4.4
   is verified only in the instance `h(n) = g(n²)`, not for an abstract
   sequence `𝒜` — the abstraction would add no mathematical content here.
   The second sentence of Theorem 1.2 — the same estimate after restricting
   to `(n, d_g) = 1` — is not formalised either; the ingredient it needs,
   `(n,d_g)=1 ⇔ (g(n²),d_g)=1`, *is* (`coprime_eval_sq_iff`).
   **Corollary 4.5 and the `P₃` part of Corollary 1.3** (Richert's weighted
   sieve) remain unformalised: the sieve is exactly the kind of heavy quoted
   machinery whose transcription would dominate the audit.
4. **Theorem 1.7, Theorem 5.2, Theorem 5.4** (zero mean, iterates, exact
   values), **Theorems 5.6, 5.12's shellwise assertions** (the Mertens
   theory beyond the local factors verified here), **Corollaries 1.4, 1.5,
   §6** (the transfer propositions and the Erdős–Kac composition), **§8's
   asymptotic statements**: each needs the prime number theorem (with
   error), Mertens' theorems, or saddle-point analysis, none of which is in
   Mathlib at this pin.  Of Theorem 5.12, the local factor theory is now
   verified in full — the values of `N(c,d)` at prime powers, the
   Chinese-remainder multiplicativity, the product formula (60) for every
   modulus, and the mean formula (61); what is *not* verified is the
   shellwise density statement (59) itself, which needs the prime number
   theorem with error and Mertens' theorems.
5. **Corollary 1.9 for `b ≥ 4`**, as explained in §4.3.
6. **Lemma 7.7 (the stabilising carries) and Proposition 7.8 in degree
   ≥ 2**, and the block-additive case 7.8(ii); the degree-one case, the
   complement lemma, and the infinitude half of Theorem 7.5 in degree one
   are verified.  The *asymptotic count* of Theorem 7.5 needs the prime
   number theorem in progressions, which is not in Mathlib at this pin —
   Dirichlet's theorem, which gives infinitude, is.
7. **The paper's numerical remarks (§5.5)** are checked by the script in
   `validation/`, not by the Lean kernel.  Every quoted number is reproduced
   exactly (the count `629304`, the reciprocal sums, the three shell
   proportions against the `Bin(m−2, 1/10)` model, and the seven-row base-3
   table).  The script also cross-checks the Remark 2.3 arithmetic, the
   `ρ_{g,□}` and `κ_m` identities, the finite-height portrait of
   Theorem 1.1 (the mod-9 lattice of `s_10(n²)` to `2·10⁶`), the §8
   reciprocal identity, and — new — the multiplicativity of `N(c,·)` and the
   mean formula (61), the finite Fourier identity (37), Lemma 4.3 *against
   the explicit constants the Lean proof supplies*, the `ρ/σ` scaling of
   Theorem 2.1, the degree-one affine identity with its Dirichlet count, and
   the output discrepancy of Theorem 1.2 at finite height — 60 checks in
   all.

## 6. Sanity checks

`DSS/Sanity.lean` contains `#guard` checks evaluated at compile time: the
digit sums `s_10(19²) = 10`, `s_10(1101²) = 9`, the complement rule at
concrete values, the singleton identity in bases 2, 3, 10, the carry-free
square of `a_{{2,3}} = 1101` and its shifted form, the binary case on
`T = {2, 6}`, pair counts against `C(t,2)`, admissibility of `s_10(n²)` mod 9
for `n < 30`, the zero counter on concrete numbers, `d = 2` and `d = 3` for
the two examples, `d = 9` for the decimal digit sum and `d = 1` for the
binary one, `IsP2` on `1, 4, 6, 7, 8, 30`; and — new — the quadratic-residue
values `ρ_{s_10,□}(0,1,4,7) = (3,2,2,2)` with the vanishing off-residues,
`ρ_{s_2,□} ≡ 1`, the `κ_m` counts `N(c,d)` at `d = 2, 5, 9` including
the base-3 parity forcing `N(1,2) = 0`, the multiplicativity
`N(3,15) = N(3,3)N(3,5)` and two further instances, and the degree-one
affine identity `s_10(2·10^k − 7) = 9k − 5` with its constant
`blockConst = −5`.

## 7. Reproducing the check

```sh
cd lean
lake exe cache get
lake build                      # no errors, no warnings; Guard.lean enforces the axiom discipline
lake env lean AxiomAudit.lean   # compare with axiom_audit.txt
cd ../validation
uv run --with numpy python check_numerics.py   # a few seconds; ends "ALL CHECKS PASSED"
```
