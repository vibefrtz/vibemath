/-
DSS/OutputLevel.lean

**Theorem 1.2 (distribution of square outputs), as an axiom-free
implication.**

Theorem 1.2 of the paper says that the *output* sequence `(g(n²))_{n≤x}` has
a level of distribution at the near-square-root scale
`Q_η(L) = √L/(log L)^{1/2+η}`, `L = log_b x`:

  `∑_{m ≤ Q_η(L), (m,d_g)=1} max_{a mod m} |Δ_{g,□}(x;m,a)| ≪ x L^{−1/2+ε}`,

where `Δ_{g,□}(x;m,a) = #{n ≤ x : g(n²) ≡ a (mod m)} − x/m`.  This is
Proposition 4.4 applied to `h(n) = g(n²)`, and it uses *only* the two clauses
of Definition 4.1 — the local limit theorem and its Gaussian-scale tail.

Under the discipline of this development the paper's own Theorem 1.1 is never
an axiom: its two clauses are transcribed as the definitions `SquareLLT`
(in `DSS/SquareLLT.lean`) and `SquareTail` (here, eq. (6)), and Theorem 1.2 is
proved as the implication

  `SquareLLT g → SquareTail g → (the display above)`,

**with no axioms at all** — the build-time guard in `DSS/Guard.lean`
certifies that neither `mmr` nor `hhbr` enters.

The proof follows the paper.  For a modulus `m` coprime to `d = d_g`:

1. the class `a mod m` splits, by the Chinese remainder theorem, into the `d`
   classes `c_u mod (md)`, on each of which the lattice density `ρ_{g,□}` is
   *constant* (`sqCountCong_crt`, `rhoSq_class`);
2. on one such class the tail clause confines the relevant targets to a
   window of length `≍ √L log L` about `2μ_gL`, at a cost `T`
   (`sqCountCong_window`);
3. inside the window the local theorem replaces each of the `≤ 2W/(md) + 1`
   counts by its Gaussian main term, at a cost `E` each;
4. the resulting lattice sum of Gaussians over the class is `1/(md)` up to
   the Poisson error of Lemma 4.3 (`gaussKer_class`) and the Gaussian mass
   outside the window (`gaussKer_tail`) — this is `class_bound`;
5. summing the `d` classes gives `modulus_bound`, and summing over
   `m ≤ Q_η(L)` costs `∑_{m≤Q} 1/m ≤ 1 + log Q` (`sum_inv_moduli_le`) —
   the only Mertens-type input, and an elementary one because the weight is
   `B^{ω(m)}` with `B = 1`.

**Only the unweighted form `B = 1` is proved.**  The weighted form of
eq. (8) needs `∑_{m≤Q} B^{ω(m)}/m ≪ (log Q)^B`, which rests on Mertens'
theorem `∑_{p≤x} 1/p = log log x + O(1)`; Mathlib at this pin has the
divergence of `∑ 1/p` (`not_summable_one_div_on_primes`) but no such
quantitative bound, so the weighted form is not formalised.

Nothing in this file is conditional: it imports no axioms.
-/
import DSS.GaussSum
import DSS.SquareLLT

namespace DSS

open Finset

/-! ### Two asymptotic comparisons -/

open Filter in
/-- Any fixed power of `log` is eventually dominated by any positive power. -/
lemma eventually_log_pow_le_rpow (p : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ L : ℝ in atTop, (Real.log L) ^ p ≤ L ^ δ := by
  rcases Nat.eq_zero_or_pos p with hp | hp
  · subst hp
    filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with L hL
    rw [pow_zero, ← Real.rpow_zero L]
    exact Real.rpow_le_rpow_of_exponent_le hL hδ.le
  · have hr : 0 < δ / (p : ℝ) := by positivity
    have hlo := (isLittleO_log_rpow_atTop hr).bound (c := 1) one_pos
    filter_upwards [hlo, Filter.eventually_ge_atTop (1 : ℝ)] with L hbd hL
    have hlog0 : 0 ≤ Real.log L := Real.log_nonneg hL
    have hLp : (0 : ℝ) ≤ L := by linarith
    have h1 : Real.log L ≤ L ^ (δ / (p : ℝ)) := by
      rw [Real.norm_eq_abs, Real.norm_eq_abs, one_mul, abs_of_nonneg hlog0,
        abs_of_nonneg (Real.rpow_nonneg hLp _)] at hbd
      exact hbd
    calc (Real.log L) ^ p ≤ (L ^ (δ / (p : ℝ))) ^ p := by gcongr
      _ = L ^ δ := by
          rw [← Real.rpow_natCast (L ^ (δ / (p : ℝ))) p, ← Real.rpow_mul hLp]
          congr 1
          field_simp

open Filter in
/-- `exp(κ(log L)^{1+θ})` eventually beats `L^{3/2}`, for every `κ, θ > 0`. -/
lemma eventually_rpow_mul_exp_le_one {κ θ : ℝ} (hκ : 0 < κ) (hθ : 0 < θ) :
    ∀ᶠ L : ℝ in atTop,
      L ^ (3 / 2 : ℝ) * Real.exp (-(κ * (Real.log L) ^ (1 + θ))) ≤ 1 := by
  have htend : Filter.Tendsto (fun L : ℝ => (Real.log L) ^ θ) atTop atTop :=
    (tendsto_rpow_atTop hθ).comp Real.tendsto_log_atTop
  filter_upwards [htend.eventually_ge_atTop (3 / (2 * κ)),
    Filter.eventually_gt_atTop (1 : ℝ)] with L hbig hL
  have hL0 : (0 : ℝ) < L := by linarith
  have hlog : (0 : ℝ) < Real.log L := Real.log_pos hL
  have hsplit : (Real.log L) ^ (1 + θ) = Real.log L * (Real.log L) ^ θ := by
    rw [Real.rpow_add hlog, Real.rpow_one]
  have hkey : (3 / 2 : ℝ) * Real.log L ≤ κ * (Real.log L) ^ (1 + θ) := by
    rw [hsplit]
    have h2 : (3 / (2 * κ)) ≤ (Real.log L) ^ θ := hbig
    have h3 : 3 ≤ 2 * κ * (Real.log L) ^ θ := by
      rw [div_le_iff₀ (by positivity)] at h2
      linarith
    nlinarith [hlog]
  rw [Real.rpow_def_of_pos hL0, ← Real.exp_add]
  rw [Real.exp_le_one_iff]
  linarith

/-! ### The Gaussian kernel of the local theorem -/

/-- `G_L(k) = (2πs)^{-1/2} exp(−(k−y)²/(2s))`, the Gaussian factor of eq. (5)
with `s = 2σ_g²L` and `y = 2μ_gL`. -/
noncomputable def gaussKer (s y k : ℝ) : ℝ :=
  (1 / Real.sqrt (2 * Real.pi * s)) * Real.exp (-((k - y) ^ 2) / (2 * s))

lemma gaussKer_nonneg {s : ℝ} (hs : 0 < s) (y k : ℝ) : 0 ≤ gaussKer s y k := by
  unfold gaussKer
  have : (0:ℝ) < Real.sqrt (2 * Real.pi * s) := Real.sqrt_pos.mpr (by positivity)
  positivity

private lemma gaussKer_class_form {s : ℝ} (hs : 0 < s) {M : ℕ} (hM : 0 < M) (c : ℤ) (y : ℝ)
    (j : ℤ) :
    gaussKer s y ((M : ℝ) * (j : ℝ) + (c : ℝ))
      = (1 / Real.sqrt (2 * Real.pi * s))
        * Real.exp (-(((M : ℝ)) ^ 2 / (2 * s)) * ((j : ℝ) + ((c : ℝ) - y) / (M : ℝ)) ^ 2) := by
  have hMR : (0:ℝ) < (M : ℝ) := by exact_mod_cast hM
  unfold gaussKer
  congr 2
  field_simp
  ring

private lemma summable_gaussKer_class {s : ℝ} (hs : 0 < s) {M : ℕ} (hM : 0 < M) (c : ℤ) (y : ℝ) :
    Summable (fun j : ℤ => gaussKer s y ((M : ℝ) * (j : ℝ) + (c : ℝ))) := by
  have hMR : (0:ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hα : (0:ℝ) < ((M : ℝ)) ^ 2 / (2 * s) := by positivity
  refine Summable.congr
    (((summable_gauss_shifted hα (((c : ℝ) - y) / (M : ℝ))).mul_left
      (1 / Real.sqrt (2 * Real.pi * s)))) (fun j => ?_)
  exact (gaussKer_class_form hs hM c y j).symm

/-- **Lemma 4.3 for the kernel `G_L`:** the mass on a class `c mod M` is `1/M`
up to an exponentially small error. -/
theorem gaussKer_class {s : ℝ} (hs : 0 < s) {M : ℕ} (hM : 0 < M) (c : ℤ) (y : ℝ)
    (hMs : ((M : ℝ)) ^ 2 ≤ 2 * Real.pi ^ 2 * s) :
    |(∑' j : ℤ, gaussKer s y ((M : ℝ) * (j : ℝ) + (c : ℝ))) - 1 / (M : ℝ)|
      ≤ (4 / (M : ℝ)) * Real.exp (-(2 * Real.pi ^ 2 * s / ((M : ℝ)) ^ 2)) := by
  have h := gaussian_progression hs hM c y hMs
  have hrw : (∑' j : ℤ, gaussKer s y ((M : ℝ) * (j : ℝ) + (c : ℝ)))
      = (1 / Real.sqrt (2 * Real.pi * s))
        * (∑' j : ℤ, Real.exp (-((((M : ℝ)) * (j : ℝ) + (c : ℝ) - y) ^ 2) / (2 * s))) := by
    rw [← tsum_mul_left]
    exact tsum_congr (fun j => rfl)
  rw [hrw]
  exact h

/-- **The Gaussian mass outside the central window**, along a class `c mod M`:
exponentially small in `W²/s`. -/
theorem gaussKer_tail {s : ℝ} (hs : 0 < s) {M : ℕ} (hM : 0 < M) (c : ℤ) (y W : ℝ)
    (hW : 0 ≤ W) (hMs : ((M : ℝ)) ^ 2 ≤ 4 * Real.pi ^ 2 * s) (S : Finset ℤ)
    (hS : ∀ j : ℤ, j ∉ S → W ≤ |(M : ℝ) * (j : ℝ) + (c : ℝ) - y|) :
    ∑' j : ℤ, (if j ∈ S then 0 else gaussKer s y ((M : ℝ) * (j : ℝ) + (c : ℝ)))
      ≤ (3 * Real.sqrt 2 / (M : ℝ)) * Real.exp (-(W ^ 2 / (4 * s))) := by
  have hMR : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hSq : (0 : ℝ) < Real.sqrt (2 * Real.pi * s) := Real.sqrt_pos.mpr (by positivity)
  have hα : (0 : ℝ) < ((M : ℝ)) ^ 2 / (4 * s) := by positivity
  have h4s : (0 : ℝ) < 4 * s := by linarith
  have hdual : (1 : ℝ) ≤ Real.pi ^ 2 / (((M : ℝ)) ^ 2 / (4 * s)) := by
    rw [le_div_iff₀ hα, one_mul, div_le_iff₀ h4s]
    nlinarith [hMs]
  have hmaj : ∀ j : ℤ, (if j ∈ S then 0 else gaussKer s y ((M : ℝ) * (j : ℝ) + (c : ℝ)))
      ≤ ((1 / Real.sqrt (2 * Real.pi * s)) * Real.exp (-(W ^ 2 / (4 * s))))
        * Real.exp (-(((M : ℝ)) ^ 2 / (4 * s)) * ((j : ℝ) + ((c : ℝ) - y) / (M : ℝ)) ^ 2) := by
    intro j
    have hpos : (0 : ℝ) ≤ ((1 / Real.sqrt (2 * Real.pi * s)) * Real.exp (-(W ^ 2 / (4 * s))))
        * Real.exp (-(((M : ℝ)) ^ 2 / (4 * s)) * ((j : ℝ) + ((c : ℝ) - y) / (M : ℝ)) ^ 2) := by
      positivity
    by_cases hj : j ∈ S
    · rw [if_pos hj]; exact hpos
    · rw [if_neg hj]
      have hWle : W ≤ |(M : ℝ) * (j : ℝ) + (c : ℝ) - y| := hS j hj
      have hsq : W ^ 2 ≤ ((M : ℝ) * (j : ℝ) + (c : ℝ) - y) ^ 2 := by
        nlinarith [sq_abs ((M : ℝ) * (j : ℝ) + (c : ℝ) - y), abs_nonneg
          ((M : ℝ) * (j : ℝ) + (c : ℝ) - y)]
      have hsplit : ((M : ℝ)) ^ 2 / (4 * s) * ((j : ℝ) + ((c : ℝ) - y) / (M : ℝ)) ^ 2
          = ((M : ℝ) * (j : ℝ) + (c : ℝ) - y) ^ 2 / (4 * s) := by
        field_simp
        try ring
      have hexp : Real.exp (-(((M : ℝ) * (j : ℝ) + (c : ℝ) - y) ^ 2) / (2 * s))
          ≤ Real.exp (-(W ^ 2 / (4 * s)))
            * Real.exp (-(((M : ℝ)) ^ 2 / (4 * s))
                * ((j : ℝ) + ((c : ℝ) - y) / (M : ℝ)) ^ 2) := by
        rw [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        rw [neg_mul, hsplit]
        have hA : -(((M : ℝ) * (j : ℝ) + (c : ℝ) - y) ^ 2) / (2 * s)
            = -(((M : ℝ) * (j : ℝ) + (c : ℝ) - y) ^ 2 / (4 * s))
              + -(((M : ℝ) * (j : ℝ) + (c : ℝ) - y) ^ 2 / (4 * s)) := by
          field_simp
          try ring
        have hW4 : W ^ 2 / (4 * s) ≤ ((M : ℝ) * (j : ℝ) + (c : ℝ) - y) ^ 2 / (4 * s) := by
          gcongr
        rw [hA]
        linarith
      unfold gaussKer
      calc (1 / Real.sqrt (2 * Real.pi * s))
            * Real.exp (-(((M : ℝ) * (j : ℝ) + (c : ℝ) - y) ^ 2) / (2 * s))
          ≤ (1 / Real.sqrt (2 * Real.pi * s))
            * (Real.exp (-(W ^ 2 / (4 * s)))
              * Real.exp (-(((M : ℝ)) ^ 2 / (4 * s))
                  * ((j : ℝ) + ((c : ℝ) - y) / (M : ℝ)) ^ 2)) :=
            mul_le_mul_of_nonneg_left hexp (by positivity)
        _ = ((1 / Real.sqrt (2 * Real.pi * s)) * Real.exp (-(W ^ 2 / (4 * s))))
            * Real.exp (-(((M : ℝ)) ^ 2 / (4 * s))
                * ((j : ℝ) + ((c : ℝ) - y) / (M : ℝ)) ^ 2) := by ring
  have hsummaj : Summable (fun j : ℤ =>
      ((1 / Real.sqrt (2 * Real.pi * s)) * Real.exp (-(W ^ 2 / (4 * s))))
        * Real.exp (-(((M : ℝ)) ^ 2 / (4 * s)) * ((j : ℝ) + ((c : ℝ) - y) / (M : ℝ)) ^ 2)) :=
    (summable_gauss_shifted hα (((c : ℝ) - y) / (M : ℝ))).mul_left _
  have hsumlhs : Summable (fun j : ℤ =>
      (if j ∈ S then 0 else gaussKer s y ((M : ℝ) * (j : ℝ) + (c : ℝ)))) := by
    refine Summable.of_nonneg_of_le (fun j => ?_) hmaj hsummaj
    by_cases hj : j ∈ S
    · rw [if_pos hj]
    · rw [if_neg hj]; exact gaussKer_nonneg hs _ _
  calc ∑' j : ℤ, (if j ∈ S then 0 else gaussKer s y ((M : ℝ) * (j : ℝ) + (c : ℝ)))
      ≤ ∑' j : ℤ, ((1 / Real.sqrt (2 * Real.pi * s)) * Real.exp (-(W ^ 2 / (4 * s))))
          * Real.exp (-(((M : ℝ)) ^ 2 / (4 * s)) * ((j : ℝ) + ((c : ℝ) - y) / (M : ℝ)) ^ 2) :=
        hsumlhs.tsum_le_tsum hmaj hsummaj
    _ = ((1 / Real.sqrt (2 * Real.pi * s)) * Real.exp (-(W ^ 2 / (4 * s))))
          * ∑' j : ℤ, Real.exp (-(((M : ℝ)) ^ 2 / (4 * s))
              * ((j : ℝ) + ((c : ℝ) - y) / (M : ℝ)) ^ 2) := tsum_mul_left
    _ ≤ ((1 / Real.sqrt (2 * Real.pi * s)) * Real.exp (-(W ^ 2 / (4 * s))))
          * (3 * Real.sqrt (Real.pi / (((M : ℝ)) ^ 2 / (4 * s)))) :=
        mul_le_mul_of_nonneg_left
          (tsum_gauss_shift_le hα (((c : ℝ) - y) / (M : ℝ)) hdual) (by positivity)
    _ = (3 * Real.sqrt 2 / (M : ℝ)) * Real.exp (-(W ^ 2 / (4 * s))) := by
        have h1 : Real.pi / (((M : ℝ)) ^ 2 / (4 * s)) = (4 * Real.pi * s) / ((M : ℝ)) ^ 2 := by
          field_simp
          try ring
        have h2 : Real.sqrt ((4 * Real.pi * s) / ((M : ℝ)) ^ 2)
            = Real.sqrt (4 * Real.pi * s) / (M : ℝ) := by
          rw [Real.sqrt_div (by positivity), Real.sqrt_sq hMR.le]
        have h3 : Real.sqrt (4 * Real.pi * s) = Real.sqrt 2 * Real.sqrt (2 * Real.pi * s) := by
          rw [← Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]
          congr 1
          ring
        rw [h1, h2, h3]
        field_simp
        try ring

/-! ### The statement of Theorem 1.2 -/

variable {b : ℕ}

/-- **`SquareTail g`: the tail clause (6) of Theorem 1.1 for `g`.**

There are `C, c > 0` with
`#{n ≤ x : |g(n²) − 2μ_gL| > C√L log L} ≪ x exp(−c(log L)²)`,
`L = log_b x`, uniformly for `x > 2`.  A definition, not an axiom; the
constant `A` makes the `≪` explicit, and the quantifier order matches the
paper's (the constants are chosen once and the estimate is uniform in `x`). -/
def SquareTail (g : Weight b) : Prop :=
  ∃ C c A : ℝ, 0 < C ∧ 0 < c ∧ 0 ≤ A ∧ ∀ x : ℝ, 2 < x →
    (((intsLE x).filter (fun n : ℕ =>
        C * Real.sqrt (Real.logb (b : ℝ) x) * Real.log (Real.logb (b : ℝ) x)
          < |(g.eval (n ^ 2) : ℝ) - 2 * g.mu * Real.logb (b : ℝ) x|)).card : ℝ)
      ≤ A * x * Real.exp (-(c * (Real.log (Real.logb (b : ℝ) x)) ^ 2))

/-- `#{1 ≤ n ≤ x : g(n²) ≡ a (mod m)}`; the congruence is by `Int.emod`, as
everywhere in this development. -/
noncomputable def sqCountCong (g : Weight b) (x : ℝ) (m : ℕ) (a : ℤ) : ℕ :=
  ((intsLE x).filter (fun n : ℕ => g.eval (n ^ 2) % (m : ℤ) = a % (m : ℤ))).card

/-- `Δ_{g,□}(x;m,a) = #{n ≤ x : g(n²) ≡ a (mod m)} − x/m`, the discrepancy
defined in §1.2, just before Theorem 1.2. -/
noncomputable def deltaSq (g : Weight b) (x : ℝ) (m : ℕ) (a : ℤ) : ℝ :=
  (sqCountCong g x m a : ℝ) - x / (m : ℝ)

/-- `max_{a mod m} |Δ_{g,□}(x;m,a)|`. -/
noncomputable def deltaSqMax (g : Weight b) (x : ℝ) (m : ℕ) : ℝ :=
  (range m).fold max 0 (fun a : ℕ => |deltaSq g x m (a : ℤ)|)

lemma deltaSqMax_le {g : Weight b} {x : ℝ} {m : ℕ} {B : ℝ} (hB : 0 ≤ B)
    (h : ∀ a : ℕ, a < m → |deltaSq g x m (a : ℤ)| ≤ B) : deltaSqMax g x m ≤ B := by
  unfold deltaSqMax
  rw [Finset.fold_max_le]
  exact ⟨hB, fun a ha => h a (mem_range.mp ha)⟩

lemma deltaSqMax_nonneg (g : Weight b) (x : ℝ) (m : ℕ) : 0 ≤ deltaSqMax g x m := by
  unfold deltaSqMax
  rw [Finset.le_fold_max]
  exact Or.inl (le_refl 0)

/-- `Q_η(L) = √L/(log L)^{1/2+η}`, eq. (7). -/
noncomputable def Qeta (η L : ℝ) : ℝ := Real.sqrt L / (Real.log L) ^ (1 / 2 + η)

/-- The moduli of eq. (8): `m ≤ Q_η(L)` with `(m, d_g) = 1`. -/
noncomputable def moduli (g : Weight b) (x : ℝ) (η : ℝ) : Finset ℕ :=
  (Finset.Icc 1 ⌊Qeta η (Real.logb (b : ℝ) x)⌋₊).filter (fun m => Nat.Coprime m g.dg)

/-! ### Splitting a class count into the central window and a tail -/

/-- The counts on a class `c mod M`, split at the window
`{M j + c : nlo ≤ j ≤ nhi}`: what falls outside the window is part of the
Gaussian-scale tail. -/
theorem sqCountCong_window (g : Weight b) (x : ℝ) {M : ℕ} (hM : 0 < M) (c : ℤ)
    (nlo nhi : ℤ) (y W : ℝ)
    (hout : ∀ j : ℤ, j ∉ Finset.Icc nlo nhi → W < |(M : ℝ) * (j : ℝ) + (c : ℝ) - y|) :
    |(sqCountCong g x M c : ℝ)
        - ∑ j ∈ Finset.Icc nlo nhi, (sqCountEq g x ((M : ℤ) * j + c) : ℝ)|
      ≤ (((intsLE x).filter
          (fun n : ℕ => W < |(g.eval (n ^ 2) : ℝ) - y|)).card : ℝ) := by
  classical
  have hMZ : ((M : ℤ)) ≠ 0 := by exact_mod_cast hM.ne'
  obtain ⟨K, hKdef⟩ : ∃ t : Finset ℤ, t = (Finset.Icc nlo nhi).image (fun j => (M : ℤ) * j + c) :=
    ⟨_, rfl⟩
  -- membership in `K` forces the congruence
  have hKmem : ∀ k : ℤ, k ∈ K → k % (M : ℤ) = c % (M : ℤ) := by
    intro k hk
    rw [hKdef, Finset.mem_image] at hk
    obtain ⟨j, _, rfl⟩ := hk
    simp
  -- the window part is the sum of the single-value counts
  have hwin : ((intsLE x).filter (fun n : ℕ => g.eval (n ^ 2) ∈ K)).card
      = ∑ j ∈ Finset.Icc nlo nhi, sqCountEq g x ((M : ℤ) * j + c) := by
    have hfib := Finset.card_eq_sum_card_fiberwise
      (f := fun n : ℕ => g.eval (n ^ 2)) (s := (intsLE x).filter (fun n : ℕ => g.eval (n ^ 2) ∈ K))
      (t := K) (fun n hn => (Finset.mem_filter.mp hn).2)
    rw [hfib, hKdef]
    rw [Finset.sum_image (by
      intro j₁ _ j₂ _ h
      simp only at h
      have h2 : (M : ℤ) * j₁ = (M : ℤ) * j₂ := by linarith
      exact mul_left_cancel₀ hMZ h2)]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    unfold sqCountEq
    congr 1
    rw [Finset.filter_filter]
    apply Finset.filter_congr
    intro n _
    constructor
    · rintro ⟨_, h2⟩; exact h2
    · intro h2
      refine ⟨?_, h2⟩
      rw [h2]
      exact Finset.mem_image_of_mem _ hj
  -- the complementary part is inside the tail
  have hcompl : (((intsLE x).filter (fun n : ℕ => g.eval (n ^ 2) % (M : ℤ) = c % (M : ℤ))).filter
      (fun n : ℕ => g.eval (n ^ 2) ∉ K))
      ⊆ (intsLE x).filter (fun n : ℕ => W < |(g.eval (n ^ 2) : ℝ) - y|) := by
    intro n hn
    rw [Finset.mem_filter, Finset.mem_filter] at hn
    obtain ⟨⟨hn0, hcong⟩, hnotK⟩ := hn
    rw [Finset.mem_filter]
    refine ⟨hn0, ?_⟩
    -- write `g(n²) = M j + c`
    have hdvd : (M : ℤ) ∣ (g.eval (n ^ 2) - c) := by
      have h1 : (M : ℤ) ∣ (c - g.eval (n ^ 2)) := Int.ModEq.dvd hcong
      simpa using dvd_neg.mpr h1
    obtain ⟨j, hj⟩ := hdvd
    have hval : g.eval (n ^ 2) = (M : ℤ) * j + c := by omega
    have hjout : j ∉ Finset.Icc nlo nhi := by
      intro hjin
      apply hnotK
      rw [hKdef, hval]
      exact Finset.mem_image_of_mem _ hjin
    have := hout j hjout
    rw [hval]
    push_cast
    exact this
  -- assemble
  have hsplit : sqCountCong g x M c
      = ((intsLE x).filter (fun n : ℕ => g.eval (n ^ 2) ∈ K)).card
        + (((intsLE x).filter (fun n : ℕ => g.eval (n ^ 2) % (M : ℤ) = c % (M : ℤ))).filter
            (fun n : ℕ => g.eval (n ^ 2) ∉ K)).card := by
    unfold sqCountCong
    rw [← Finset.card_filter_add_card_filter_not
      (s := (intsLE x).filter (fun n : ℕ => g.eval (n ^ 2) % (M : ℤ) = c % (M : ℤ)))
      (p := fun n : ℕ => g.eval (n ^ 2) ∈ K)]
    congr 1
    rw [Finset.filter_filter]
    congr 1
    apply Finset.filter_congr
    intro n _
    constructor
    · rintro ⟨_, h2⟩; exact h2
    · intro h2
      exact ⟨hKmem _ h2, h2⟩
  rw [hsplit, hwin]
  push_cast
  rw [add_sub_cancel_left]
  rw [abs_of_nonneg (by positivity)]
  exact_mod_cast Finset.card_le_card hcompl

/-! ### Bookkeeping lemmas -/

private lemma tsum_split_finset {F : ℤ → ℝ} (hF : Summable F) (S : Finset ℤ) :
    ∑' j : ℤ, F j = (∑ j ∈ S, F j) + ∑' j : ℤ, (if j ∈ S then 0 else F j) := by
  classical
  have h1 : Summable (fun j : ℤ => if j ∈ S then F j else 0) :=
    summable_of_ne_finset_zero (s := S) (fun j hj => if_neg hj)
  have hfun : (fun j : ℤ => F j - (if j ∈ S then F j else 0))
      = (fun j : ℤ => if j ∈ S then 0 else F j) := by
    funext j
    by_cases h : j ∈ S <;> simp [h]
  have h2 : Summable (fun j : ℤ => if j ∈ S then 0 else F j) := hfun ▸ hF.sub h1
  have h3 : ∑' j : ℤ, (if j ∈ S then F j else 0) = ∑ j ∈ S, F j := by
    rw [tsum_eq_sum (s := S) (fun j hj => if_neg hj)]
    exact Finset.sum_congr rfl (fun j hj => if_pos hj)
  have h4 : ∀ j : ℤ, F j = (if j ∈ S then F j else 0) + (if j ∈ S then 0 else F j) := by
    intro j
    by_cases h : j ∈ S <;> simp [h]
  rw [tsum_congr h4, h1.tsum_add h2, h3]

/-- `ρ_{g,□}` depends only on the residue. -/
lemma rhoSq_congr (g : Weight b) {k l : ℤ} (h : k % (g.dg : ℤ) = l % (g.dg : ℤ)) :
    rhoSq g k = rhoSq g l := by
  unfold rhoSq
  congr 1
  apply Finset.filter_congr
  intro r _
  rw [h]

lemma rhoSq_le_dg (g : Weight b) (k : ℤ) : rhoSq g k ≤ g.dg := by
  unfold rhoSq
  calc ((range g.dg).filter _).card ≤ (range g.dg).card := Finset.card_filter_le _ _
    _ = g.dg := card_range _

/-- On a class modulo a multiple of `d_g`, the lattice density is constant. -/
lemma rhoSq_class (g : Weight b) {M : ℕ} (hdM : g.dg ∣ M) (c j : ℤ) :
    rhoSq g ((M : ℤ) * j + c) = rhoSq g c := by
  refine rhoSq_congr g ?_
  obtain ⟨t, ht⟩ := hdM
  have h : (M : ℤ) * j + c = c + (g.dg : ℤ) * ((t : ℤ) * j) := by
    rw [ht]
    push_cast
    ring
  rw [h, Int.add_mul_emod_self_left]

/-- `sqMain` is `ρ_{g,□}(k)·x` times the Gaussian kernel at variance
`s = 2σ_g²L` and centre `y = 2μ_gL`. -/
lemma sqMain_eq_gaussKer (g : Weight b) (x : ℝ) (k : ℤ) :
    sqMain g x k
      = (rhoSq g k : ℝ) * x
        * gaussKer (2 * g.sigSq * Real.logb (b : ℝ) x)
            (2 * g.mu * Real.logb (b : ℝ) x) (k : ℝ) := by
  unfold sqMain gaussKer
  have h1 : 2 * Real.pi * (2 * g.sigSq * Real.logb (b : ℝ) x)
      = 4 * Real.pi * g.sigSq * Real.logb (b : ℝ) x := by ring
  have h2 : 2 * (2 * g.sigSq * Real.logb (b : ℝ) x)
      = 4 * g.sigSq * Real.logb (b : ℝ) x := by ring
  rw [h1, h2]
  ring

/-! ### The Chinese remainder splitting of a class modulo `m` -/

private lemma isCoprime_of_coprime {m d : ℕ} (hcop : Nat.Coprime m d) :
    IsCoprime ((m : ℤ)) ((d : ℤ)) := by
  rw [Int.isCoprime_iff_gcd_eq_one]
  simpa using hcop

/-- Two congruences to coprime moduli are one congruence to their product. -/
lemma int_crt_iff {m d : ℕ} (hcop : Nat.Coprime m d) (z c : ℤ) :
    (z % (m : ℤ) = c % (m : ℤ) ∧ z % (d : ℤ) = c % (d : ℤ))
      ↔ z % (((m * d : ℕ)) : ℤ) = c % (((m * d : ℕ)) : ℤ) := by
  have hcast : (((m * d : ℕ)) : ℤ) = (m : ℤ) * (d : ℤ) := by push_cast; ring
  rw [hcast]
  constructor
  · rintro ⟨h1, h2⟩
    have d1 : ((m : ℤ)) ∣ (c - z) := Int.ModEq.dvd h1
    have d2 : ((d : ℤ)) ∣ (c - z) := Int.ModEq.dvd h2
    exact Int.modEq_iff_dvd.mpr ((isCoprime_of_coprime hcop).mul_dvd d1 d2)
  · intro h
    exact ⟨Int.ModEq.of_dvd ⟨(d : ℤ), rfl⟩ h,
      Int.ModEq.of_dvd ⟨(m : ℤ), by ring⟩ h⟩

/-- The Chinese remainder theorem: a class modulo `m` and a class modulo `d`
meet, when `(m,d) = 1`. -/
lemma exists_crt {m d : ℕ} (hcop : Nat.Coprime m d) (a u : ℤ) :
    ∃ c : ℤ, c % (m : ℤ) = a % (m : ℤ) ∧ c % (d : ℤ) = u % (d : ℤ) := by
  obtain ⟨p, q, hpq⟩ := isCoprime_of_coprime hcop
  refine ⟨a * (q * (d : ℤ)) + u * (p * (m : ℤ)), ?_, ?_⟩
  · refine Int.ModEq.symm (Int.modEq_iff_dvd.mpr ⟨p * (u - a), ?_⟩)
    have : q * (d : ℤ) = 1 - p * (m : ℤ) := by linarith [hpq]
    rw [this]
    ring
  · refine Int.ModEq.symm (Int.modEq_iff_dvd.mpr ⟨q * (a - u), ?_⟩)
    have : p * (m : ℤ) = 1 - q * (d : ℤ) := by linarith [hpq]
    rw [this]
    ring

/-! ### The estimate on one class modulo `M = m·d_g` -/

/-- **The per-class estimate.**  On a class `c` modulo a multiple `M` of `d_g`,
the count is `x·ρ_{g,□}(c)/M` up to: the Gaussian-scale tail `T`; the local
error `E` on each of the `≤ 2W/M + 1` targets in the central window; and the
Poisson and Gaussian-tail errors of the lattice sum. -/
theorem class_bound (g : Weight b) (x : ℝ) {M : ℕ} (hM : 0 < M) (hdM : g.dg ∣ M) (c : ℤ)
    {s y W E T : ℝ} (hs : 0 < s) (hW : 0 ≤ W) (hx0 : 0 ≤ x)
    (hMs : ((M : ℝ)) ^ 2 ≤ 2 * Real.pi ^ 2 * s)
    (hMs' : ((M : ℝ)) ^ 2 ≤ 4 * Real.pi ^ 2 * s)
    (hker : ∀ k : ℤ, sqMain g x k = (rhoSq g k : ℝ) * x * gaussKer s y (k : ℝ))
    (hE0 : 0 ≤ E)
    (hE : ∀ k : ℤ, |(sqCountEq g x k : ℝ) - sqMain g x k| ≤ E)
    (hT : (((intsLE x).filter (fun n : ℕ => W < |(g.eval (n ^ 2) : ℝ) - y|)).card : ℝ) ≤ T) :
    |(sqCountCong g x M c : ℝ) - x * (rhoSq g c : ℝ) / (M : ℝ)|
      ≤ T + (2 * W / (M : ℝ) + 1) * E
        + x * (g.dg : ℝ) * ((4 / (M : ℝ)) * Real.exp (-(2 * Real.pi ^ 2 * s / ((M : ℝ)) ^ 2))
            + (3 * Real.sqrt 2 / (M : ℝ)) * Real.exp (-(W ^ 2 / (4 * s)))) := by
  classical
  have hMR : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  obtain ⟨nlo, hnlo⟩ : ∃ t : ℤ, t = ⌈(y - W - (c : ℝ)) / (M : ℝ)⌉ := ⟨_, rfl⟩
  obtain ⟨nhi, hnhi⟩ : ∃ t : ℤ, t = ⌊(y + W - (c : ℝ)) / (M : ℝ)⌋ := ⟨_, rfl⟩
  -- outside the window the target is far from the centre
  have hout : ∀ j : ℤ, j ∉ Finset.Icc nlo nhi → W < |(M : ℝ) * (j : ℝ) + (c : ℝ) - y| := by
    intro j hj
    rw [Finset.mem_Icc, not_and_or] at hj
    rcases hj with hj | hj
    · have hjlt : j < nlo := by omega
      have h1 : ((nlo : ℝ)) - 1 < (y - W - (c : ℝ)) / (M : ℝ) := by
        rw [hnlo]
        have := Int.ceil_lt_add_one ((y - W - (c : ℝ)) / (M : ℝ))
        linarith
      have h2 : (j : ℝ) ≤ (nlo : ℝ) - 1 := by
        have : j ≤ nlo - 1 := by omega
        have := (Int.cast_le (R := ℝ)).mpr this
        push_cast at this
        linarith
      have h3 : (j : ℝ) < (y - W - (c : ℝ)) / (M : ℝ) := by linarith
      rw [lt_div_iff₀ hMR] at h3
      refine lt_abs.mpr (Or.inr ?_)
      linarith
    · have hjgt : nhi < j := by omega
      have h1 : (y + W - (c : ℝ)) / (M : ℝ) < (nhi : ℝ) + 1 := by
        rw [hnhi]
        exact Int.lt_floor_add_one _
      have h2 : (nhi : ℝ) + 1 ≤ (j : ℝ) := by
        have : nhi + 1 ≤ j := by omega
        have := (Int.cast_le (R := ℝ)).mpr this
        push_cast at this
        linarith
      have h3 : (y + W - (c : ℝ)) / (M : ℝ) < (j : ℝ) := by linarith
      rw [div_lt_iff₀ hMR] at h3
      refine lt_abs.mpr (Or.inl ?_)
      linarith
  -- the window is short
  have hcard : ((Finset.Icc nlo nhi).card : ℝ) ≤ 2 * W / (M : ℝ) + 1 := by
    by_cases hle : nlo ≤ nhi
    · rw [Int.card_Icc]
      have hnn : (0 : ℤ) ≤ nhi + 1 - nlo := by omega
      have hcast : (((nhi + 1 - nlo).toNat : ℕ) : ℝ) = (nhi : ℝ) + 1 - (nlo : ℝ) := by
        have h := Int.toNat_of_nonneg hnn
        have := congrArg (fun t : ℤ => (t : ℝ)) h
        push_cast at this
        linarith [this]
      rw [hcast]
      have h1 : (nhi : ℝ) ≤ (y + W - (c : ℝ)) / (M : ℝ) := by
        rw [hnhi]; exact Int.floor_le _
      have h2 : (y - W - (c : ℝ)) / (M : ℝ) ≤ (nlo : ℝ) := by
        rw [hnlo]; exact Int.le_ceil _
      have h3 : (nhi : ℝ) - (nlo : ℝ) ≤ 2 * W / (M : ℝ) := by
        have h4 : (y + W - (c : ℝ)) / (M : ℝ) - (y - W - (c : ℝ)) / (M : ℝ)
            = 2 * W / (M : ℝ) := by
          field_simp
          try ring
        linarith
      linarith
    · rw [Finset.Icc_eq_empty (by omega), Finset.card_empty]
      have : (0 : ℝ) ≤ 2 * W / (M : ℝ) := by positivity
      push_cast
      linarith
  -- the three steps
  have hstep1 := sqCountCong_window g x hM c nlo nhi y W hout
  have hstep2 : |(∑ j ∈ Finset.Icc nlo nhi, (sqCountEq g x ((M : ℤ) * j + c) : ℝ))
      - ∑ j ∈ Finset.Icc nlo nhi, sqMain g x ((M : ℤ) * j + c)|
      ≤ ((Finset.Icc nlo nhi).card : ℝ) * E := by
    rw [← Finset.sum_sub_distrib]
    calc |∑ j ∈ Finset.Icc nlo nhi,
            ((sqCountEq g x ((M : ℤ) * j + c) : ℝ) - sqMain g x ((M : ℤ) * j + c))|
        ≤ ∑ j ∈ Finset.Icc nlo nhi,
            |(sqCountEq g x ((M : ℤ) * j + c) : ℝ) - sqMain g x ((M : ℤ) * j + c)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j ∈ Finset.Icc nlo nhi, E := Finset.sum_le_sum (fun j _ => hE _)
      _ = ((Finset.Icc nlo nhi).card : ℝ) * E := by
          rw [Finset.sum_const, nsmul_eq_mul]
  have hcastk : ∀ j : ℤ, (((M : ℤ) * j + c : ℤ) : ℝ) = (M : ℝ) * (j : ℝ) + (c : ℝ) := by
    intro j; push_cast; ring
  have hstep3 : ∑ j ∈ Finset.Icc nlo nhi, sqMain g x ((M : ℤ) * j + c)
      = (rhoSq g c : ℝ) * x
        * ∑ j ∈ Finset.Icc nlo nhi, gaussKer s y ((M : ℝ) * (j : ℝ) + (c : ℝ)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [hker, rhoSq_class g hdM c j, hcastk j]
  -- the lattice sum
  have hsummable := summable_gaussKer_class hs hM c y
  have hsplit := tsum_split_finset hsummable (Finset.Icc nlo nhi)
  have htailnonneg : 0 ≤ ∑' j : ℤ, (if j ∈ Finset.Icc nlo nhi then 0
      else gaussKer s y ((M : ℝ) * (j : ℝ) + (c : ℝ))) := by
    refine tsum_nonneg (fun j => ?_)
    by_cases hj : j ∈ Finset.Icc nlo nhi
    · rw [if_pos hj]
    · rw [if_neg hj]; exact gaussKer_nonneg hs _ _
  have htailbd := gaussKer_tail hs hM c y W hW hMs' (Finset.Icc nlo nhi)
    (fun j hj => le_of_lt (hout j hj))
  have hclassbd := gaussKer_class hs hM c y hMs
  have hstep4 : |(∑ j ∈ Finset.Icc nlo nhi, gaussKer s y ((M : ℝ) * (j : ℝ) + (c : ℝ)))
      - 1 / (M : ℝ)|
      ≤ (4 / (M : ℝ)) * Real.exp (-(2 * Real.pi ^ 2 * s / ((M : ℝ)) ^ 2))
        + (3 * Real.sqrt 2 / (M : ℝ)) * Real.exp (-(W ^ 2 / (4 * s))) := by
    have heq : (∑ j ∈ Finset.Icc nlo nhi, gaussKer s y ((M : ℝ) * (j : ℝ) + (c : ℝ)))
        - 1 / (M : ℝ)
        = ((∑' j : ℤ, gaussKer s y ((M : ℝ) * (j : ℝ) + (c : ℝ))) - 1 / (M : ℝ))
          - ∑' j : ℤ, (if j ∈ Finset.Icc nlo nhi then 0
              else gaussKer s y ((M : ℝ) * (j : ℝ) + (c : ℝ))) := by
      rw [hsplit]; ring
    rw [heq]
    calc |((∑' j : ℤ, gaussKer s y ((M : ℝ) * (j : ℝ) + (c : ℝ))) - 1 / (M : ℝ))
          - ∑' j : ℤ, (if j ∈ Finset.Icc nlo nhi then 0
              else gaussKer s y ((M : ℝ) * (j : ℝ) + (c : ℝ)))|
        ≤ |(∑' j : ℤ, gaussKer s y ((M : ℝ) * (j : ℝ) + (c : ℝ))) - 1 / (M : ℝ)|
          + |∑' j : ℤ, (if j ∈ Finset.Icc nlo nhi then 0
              else gaussKer s y ((M : ℝ) * (j : ℝ) + (c : ℝ)))| := abs_sub _ _
      _ ≤ _ := by
          rw [abs_of_nonneg htailnonneg]
          exact add_le_add hclassbd htailbd
  -- assemble
  have hrho : (0 : ℝ) ≤ (rhoSq g c : ℝ) := by positivity
  have hrhole : (rhoSq g c : ℝ) ≤ (g.dg : ℝ) := by exact_mod_cast rhoSq_le_dg g c
  have hfinal : |(sqCountCong g x M c : ℝ) - x * (rhoSq g c : ℝ) / (M : ℝ)|
      ≤ |(sqCountCong g x M c : ℝ)
          - ∑ j ∈ Finset.Icc nlo nhi, (sqCountEq g x ((M : ℤ) * j + c) : ℝ)|
        + |(∑ j ∈ Finset.Icc nlo nhi, (sqCountEq g x ((M : ℤ) * j + c) : ℝ))
          - ∑ j ∈ Finset.Icc nlo nhi, sqMain g x ((M : ℤ) * j + c)|
        + |(∑ j ∈ Finset.Icc nlo nhi, sqMain g x ((M : ℤ) * j + c))
          - x * (rhoSq g c : ℝ) / (M : ℝ)| := by
    have h := abs_sub_le
      ((sqCountCong g x M c : ℝ))
      (∑ j ∈ Finset.Icc nlo nhi, (sqCountEq g x ((M : ℤ) * j + c) : ℝ))
      (x * (rhoSq g c : ℝ) / (M : ℝ))
    have h2 := abs_sub_le
      (∑ j ∈ Finset.Icc nlo nhi, (sqCountEq g x ((M : ℤ) * j + c) : ℝ))
      (∑ j ∈ Finset.Icc nlo nhi, sqMain g x ((M : ℤ) * j + c))
      (x * (rhoSq g c : ℝ) / (M : ℝ))
    linarith
  have hlast : |(∑ j ∈ Finset.Icc nlo nhi, sqMain g x ((M : ℤ) * j + c))
      - x * (rhoSq g c : ℝ) / (M : ℝ)|
      ≤ x * (g.dg : ℝ) * ((4 / (M : ℝ)) * Real.exp (-(2 * Real.pi ^ 2 * s / ((M : ℝ)) ^ 2))
          + (3 * Real.sqrt 2 / (M : ℝ)) * Real.exp (-(W ^ 2 / (4 * s)))) := by
    rw [hstep3]
    have heq : (rhoSq g c : ℝ) * x
        * ∑ j ∈ Finset.Icc nlo nhi, gaussKer s y ((M : ℝ) * (j : ℝ) + (c : ℝ))
        - x * (rhoSq g c : ℝ) / (M : ℝ)
        = ((rhoSq g c : ℝ) * x)
          * ((∑ j ∈ Finset.Icc nlo nhi, gaussKer s y ((M : ℝ) * (j : ℝ) + (c : ℝ)))
            - 1 / (M : ℝ)) := by ring
    rw [heq, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (rhoSq g c : ℝ) * x)]
    have hb : (0:ℝ) ≤ (4 / (M : ℝ)) * Real.exp (-(2 * Real.pi ^ 2 * s / ((M : ℝ)) ^ 2))
        + (3 * Real.sqrt 2 / (M : ℝ)) * Real.exp (-(W ^ 2 / (4 * s))) := by positivity
    calc (rhoSq g c : ℝ) * x
          * |(∑ j ∈ Finset.Icc nlo nhi, gaussKer s y ((M : ℝ) * (j : ℝ) + (c : ℝ)))
            - 1 / (M : ℝ)|
        ≤ (rhoSq g c : ℝ) * x * ((4 / (M : ℝ))
            * Real.exp (-(2 * Real.pi ^ 2 * s / ((M : ℝ)) ^ 2))
            + (3 * Real.sqrt 2 / (M : ℝ)) * Real.exp (-(W ^ 2 / (4 * s)))) :=
          mul_le_mul_of_nonneg_left hstep4 (by positivity)
      _ ≤ x * (g.dg : ℝ) * ((4 / (M : ℝ))
            * Real.exp (-(2 * Real.pi ^ 2 * s / ((M : ℝ)) ^ 2))
            + (3 * Real.sqrt 2 / (M : ℝ)) * Real.exp (-(W ^ 2 / (4 * s)))) := by
          have : (rhoSq g c : ℝ) * x ≤ x * (g.dg : ℝ) := by nlinarith
          exact mul_le_mul_of_nonneg_right this hb
  have hcardE : ((Finset.Icc nlo nhi).card : ℝ) * E ≤ (2 * W / (M : ℝ) + 1) * E :=
    mul_le_mul_of_nonneg_right hcard hE0
  linarith [hstep1.trans hT]

/-! ### The estimate on one modulus -/

/-- The class `a mod m` splits into the `d_g` classes `c_u mod (m·d_g)`. -/
theorem sqCountCong_crt (g : Weight b) (x : ℝ) {m : ℕ} (hcop : Nat.Coprime m g.dg)
    (a : ℤ) (cu : ℕ → ℤ)
    (hcu : ∀ u : ℕ, u < g.dg → (cu u % (m : ℤ) = a % (m : ℤ)
        ∧ cu u % ((g.dg : ℕ) : ℤ) = (u : ℤ) % ((g.dg : ℕ) : ℤ))) :
    sqCountCong g x m a = ∑ u ∈ range g.dg, sqCountCong g x (m * g.dg) (cu u) := by
  classical
  have hd : 0 < g.dg := g.dg_pos
  have hdZ : (0 : ℤ) < ((g.dg : ℕ) : ℤ) := by exact_mod_cast hd
  unfold sqCountCong
  have hmap : ∀ n ∈ (intsLE x).filter (fun n : ℕ => g.eval (n ^ 2) % (m : ℤ) = a % (m : ℤ)),
      (g.eval (n ^ 2) % ((g.dg : ℕ) : ℤ)).toNat ∈ range g.dg := by
    intro n _
    rw [mem_range]
    have h1 : 0 ≤ g.eval (n ^ 2) % ((g.dg : ℕ) : ℤ) := Int.emod_nonneg _ (ne_of_gt hdZ)
    have h2 : g.eval (n ^ 2) % ((g.dg : ℕ) : ℤ) < ((g.dg : ℕ) : ℤ) := Int.emod_lt_of_pos _ hdZ
    omega
  rw [Finset.card_eq_sum_card_fiberwise hmap]
  refine Finset.sum_congr rfl (fun u hu => ?_)
  have hulm : u < g.dg := mem_range.mp hu
  obtain ⟨hc1, hc2⟩ := hcu u hulm
  have huemod : ((u : ℕ) : ℤ) % ((g.dg : ℕ) : ℤ) = ((u : ℕ) : ℤ) :=
    Int.emod_eq_of_lt (by positivity) (by exact_mod_cast hulm)
  congr 1
  rw [Finset.filter_filter]
  apply Finset.filter_congr
  intro n _
  have hnn : 0 ≤ g.eval (n ^ 2) % ((g.dg : ℕ) : ℤ) := Int.emod_nonneg _ (ne_of_gt hdZ)
  constructor
  · rintro ⟨h1, h2⟩
    rw [← int_crt_iff hcop]
    refine ⟨by rw [h1, hc1], ?_⟩
    have hval : g.eval (n ^ 2) % ((g.dg : ℕ) : ℤ) = ((u : ℕ) : ℤ) := by omega
    rw [hval, hc2, huemod]
  · intro h
    rw [← int_crt_iff hcop] at h
    obtain ⟨h1, h2⟩ := h
    refine ⟨by rw [h1, hc1], ?_⟩
    rw [h2, hc2, huemod]
    omega

/-- **The estimate on one modulus `m`, coprime to `d_g`.** -/
theorem modulus_bound (g : Weight b) (x : ℝ) {m : ℕ} (hm : 0 < m) (hcop : Nat.Coprime m g.dg)
    (a : ℤ) {s y W E T : ℝ} (hs : 0 < s) (hW : 0 ≤ W) (hx0 : 0 ≤ x)
    (hMs : (((m * g.dg : ℕ)) : ℝ) ^ 2 ≤ 2 * Real.pi ^ 2 * s)
    (hMs' : (((m * g.dg : ℕ)) : ℝ) ^ 2 ≤ 4 * Real.pi ^ 2 * s)
    (hker : ∀ k : ℤ, sqMain g x k = (rhoSq g k : ℝ) * x * gaussKer s y (k : ℝ))
    (hE0 : 0 ≤ E)
    (hE : ∀ k : ℤ, |(sqCountEq g x k : ℝ) - sqMain g x k| ≤ E)
    (hT : (((intsLE x).filter (fun n : ℕ => W < |(g.eval (n ^ 2) : ℝ) - y|)).card : ℝ) ≤ T) :
    |deltaSq g x m a| ≤ (g.dg : ℝ) *
      (T + (2 * W / (((m * g.dg : ℕ)) : ℝ) + 1) * E
        + x * (g.dg : ℝ) * ((4 / (((m * g.dg : ℕ)) : ℝ))
            * Real.exp (-(2 * Real.pi ^ 2 * s / (((m * g.dg : ℕ)) : ℝ) ^ 2))
            + (3 * Real.sqrt 2 / (((m * g.dg : ℕ)) : ℝ)) * Real.exp (-(W ^ 2 / (4 * s))))) := by
  classical
  have hd : 0 < g.dg := g.dg_pos
  have hM : 0 < m * g.dg := Nat.mul_pos hm hd
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hdR : (0 : ℝ) < (g.dg : ℝ) := by exact_mod_cast hd
  -- the CRT representatives
  choose cu hcu1 hcu2 using fun u : ℕ => exists_crt hcop a ((u : ℕ) : ℤ)
  have hcu : ∀ u : ℕ, u < g.dg → (cu u % (m : ℤ) = a % (m : ℤ)
      ∧ cu u % ((g.dg : ℕ) : ℤ) = ((u : ℕ) : ℤ) % ((g.dg : ℕ) : ℤ)) :=
    fun u _ => ⟨hcu1 u, hcu2 u⟩
  have hsplit := sqCountCong_crt g x hcop a cu hcu
  -- the main terms add up to `x/m`
  have hrhoeq : ∀ u : ℕ, u ∈ range g.dg → rhoSq g (cu u) = rhoSq g ((u : ℕ) : ℤ) :=
    fun u _ => rhoSq_congr g (hcu2 u)
  have hrhosum : (∑ u ∈ range g.dg, (rhoSq g (cu u) : ℝ)) = (g.dg : ℝ) := by
    rw [Finset.sum_congr rfl (fun u hu => by rw [hrhoeq u hu])]
    have := sum_rhoSq g
    exact_mod_cast congrArg (fun t : ℕ => (t : ℝ)) this
  have hmain : (∑ u ∈ range g.dg, x * (rhoSq g (cu u) : ℝ) / (((m * g.dg : ℕ)) : ℝ))
      = x / (m : ℝ) := by
    have hMcast : (((m * g.dg : ℕ)) : ℝ) = (m : ℝ) * (g.dg : ℝ) := by push_cast; ring
    rw [hMcast]
    have : (∑ u ∈ range g.dg, x * (rhoSq g (cu u) : ℝ) / ((m : ℝ) * (g.dg : ℝ)))
        = (x / ((m : ℝ) * (g.dg : ℝ))) * ∑ u ∈ range g.dg, (rhoSq g (cu u) : ℝ) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun u _ => by ring)
    rw [this, hrhosum]
    field_simp
  -- assemble
  have hdelta : deltaSq g x m a
      = ∑ u ∈ range g.dg,
          ((sqCountCong g x (m * g.dg) (cu u) : ℝ)
            - x * (rhoSq g (cu u) : ℝ) / (((m * g.dg : ℕ)) : ℝ)) := by
    unfold deltaSq
    rw [Finset.sum_sub_distrib, hmain, hsplit]
    push_cast
    ring
  rw [hdelta]
  calc |∑ u ∈ range g.dg, ((sqCountCong g x (m * g.dg) (cu u) : ℝ)
        - x * (rhoSq g (cu u) : ℝ) / (((m * g.dg : ℕ)) : ℝ))|
      ≤ ∑ u ∈ range g.dg, |(sqCountCong g x (m * g.dg) (cu u) : ℝ)
          - x * (rhoSq g (cu u) : ℝ) / (((m * g.dg : ℕ)) : ℝ)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _u ∈ range g.dg,
          (T + (2 * W / (((m * g.dg : ℕ)) : ℝ) + 1) * E
            + x * (g.dg : ℝ) * ((4 / (((m * g.dg : ℕ)) : ℝ))
                * Real.exp (-(2 * Real.pi ^ 2 * s / (((m * g.dg : ℕ)) : ℝ) ^ 2))
                + (3 * Real.sqrt 2 / (((m * g.dg : ℕ)) : ℝ))
                  * Real.exp (-(W ^ 2 / (4 * s))))) :=
        Finset.sum_le_sum (fun u _ =>
          class_bound g x hM (Dvd.intro m (Nat.mul_comm _ _)) (cu u) hs hW hx0 hMs hMs' hker hE0 hE hT)
    _ = _ := by
        rw [Finset.sum_const, card_range, nsmul_eq_mul]

/-! ### Summing over the moduli -/

/-- `∑_{m ≤ Q} 1/m ≤ 1 + log Q`, the only Mertens-type input the unweighted
form needs. -/
lemma sum_inv_moduli_le (g : Weight b) (x η : ℝ) {Q : ℝ} (hQ : 1 ≤ Q)
    (hQdef : Q = Qeta η (Real.logb (b : ℝ) x)) :
    ∑ m ∈ moduli g x η, (1 : ℝ) / (m : ℝ) ≤ 1 + Real.log Q := by
  classical
  have hsub : moduli g x η ⊆ Finset.Icc 1 ⌊Q⌋₊ := by
    rw [hQdef]
    exact Finset.filter_subset _ _
  have h1 : ∑ m ∈ moduli g x η, (1 : ℝ) / (m : ℝ)
      ≤ ∑ m ∈ Finset.Icc 1 ⌊Q⌋₊, (1 : ℝ) / (m : ℝ) := by
    refine Finset.sum_le_sum_of_subset_of_nonneg hsub (fun m _ _ => by positivity)
  have h2 : ∑ m ∈ Finset.Icc 1 ⌊Q⌋₊, (1 : ℝ) / (m : ℝ) = ((harmonic ⌊Q⌋₊ : ℚ) : ℝ) := by
    rw [harmonic_eq_sum_Icc]
    push_cast
    exact Finset.sum_congr rfl (fun m _ => by rw [one_div])
  exact (h1.trans_eq h2).trans (harmonic_floor_le_one_add_log Q hQ)

/-! ### Theorem 1.2 -/

set_option maxHeartbeats 2000000 in
open Filter in
/-- **Theorem 1.2 (distribution of square outputs), unweighted form
(`B = 1`), as an implication.**

If `g` satisfies the conclusion of Theorem 1.1 — the local limit theorem
`SquareLLT g` together with its Gaussian-scale tail `SquareTail g`, both
*definitions*, never axioms — then for every `η > 0` and every `ε > 0`

`∑_{m ≤ Q_η(L), (m,d_g)=1} max_{a mod m} |Δ_{g,□}(x;m,a)| ≪ x L^{−1/2+ε}`,

with `L = log_b x` and `Q_η(L) = √L/(log L)^{1/2+η}`.

The proof is the paper's: the tail clause truncates to a window of length
`≍ √L log L` about `2μ_gL`; on the window the local theorem replaces each
count by its Gaussian main term at a cost `E` per target; the lattice sum of
the main terms over a class is evaluated by Poisson summation
(`gaussKer_class`, i.e. Lemma 4.3) after splitting the class modulo `m` into
the `d_g` classes modulo `m·d_g`, on each of which `ρ_{g,□}` is constant;
and `∑_{m ≤ Q} 1/m ≪ log Q` finishes.

**This implication uses no axioms at all.** -/
theorem square_output_level (g : Weight b) (hg : g.Coprime₁)
    (hllt : SquareLLT g) (htail : SquareTail g) {η ε : ℝ} (hη : 0 < η) (hε : 0 < ε) :
    ∃ C x₀ : ℝ, 0 < C ∧ ∀ x : ℝ, x₀ ≤ x →
      ∑ m ∈ moduli g x η, deltaSqMax g x m
        ≤ C * x * (Real.logb (b : ℝ) x) ^ (-(1 : ℝ) / 2 + ε) := by
  classical
  have hb1 : (1 : ℝ) < (b : ℝ) := by exact_mod_cast g.one_lt_b
  have hσ : 0 < g.sigSq := g.sigSq_pos hg
  have hd : 0 < g.dg := g.dg_pos
  have hdR : (0 : ℝ) < (g.dg : ℝ) := by exact_mod_cast hd
  obtain ⟨CT, cT, AT, hCT, hcT, hAT, htailbd⟩ := htail
  obtain ⟨C1, hC10, hlltbd⟩ := hllt 1 one_pos
  -- the two exponential rates
  obtain ⟨κ₁, hκ₁def⟩ : ∃ t : ℝ, t = 4 * Real.pi ^ 2 * g.sigSq / (g.dg : ℝ) ^ 2 := ⟨_, rfl⟩
  obtain ⟨κ₂, hκ₂def⟩ : ∃ t : ℝ, t = CT ^ 2 / (8 * g.sigSq) := ⟨_, rfl⟩
  have hκ₁ : 0 < κ₁ := by rw [hκ₁def]; positivity
  have hκ₂ : 0 < κ₂ := by rw [hκ₂def]; positivity
  -- the eventual conditions on `L`
  have hev : ∀ᶠ L : ℝ in atTop,
      Real.exp 1 ≤ L
      ∧ (Real.log L) ^ 8 ≤ L ^ ε
      ∧ L ^ (3 / 2 : ℝ) * Real.exp (-(cT * (Real.log L) ^ (1 + (1 : ℝ)))) ≤ 1
      ∧ L ^ (3 / 2 : ℝ) * Real.exp (-(κ₁ * (Real.log L) ^ (1 + 2 * η))) ≤ 1
      ∧ L ^ (3 / 2 : ℝ) * Real.exp (-(κ₂ * (Real.log L) ^ (1 + (1 : ℝ)))) ≤ 1
      ∧ (g.dg : ℝ) ^ 2 ≤ 4 * Real.pi ^ 2 * g.sigSq * (Real.log L) ^ (1 + 2 * η)
      ∧ (Real.log L) ^ (1 + 2 * η) ≤ L := by
    have h6 : ∀ᶠ L : ℝ in atTop,
        (g.dg : ℝ) ^ 2 ≤ 4 * Real.pi ^ 2 * g.sigSq * (Real.log L) ^ (1 + 2 * η) := by
      have htend : Filter.Tendsto (fun L : ℝ => (Real.log L) ^ (1 + 2 * η)) atTop atTop :=
        (tendsto_rpow_atTop (by linarith)).comp Real.tendsto_log_atTop
      filter_upwards [htend.eventually_ge_atTop
        ((g.dg : ℝ) ^ 2 / (4 * Real.pi ^ 2 * g.sigSq))] with L hL
      rw [div_le_iff₀ (by positivity)] at hL
      linarith
    have h7 : ∀ᶠ L : ℝ in atTop, (Real.log L) ^ (1 + 2 * η) ≤ L := by
      obtain ⟨p, hp⟩ : ∃ p : ℕ, 1 + 2 * η ≤ (p : ℝ) := ⟨⌈1 + 2 * η⌉₊, Nat.le_ceil _⟩
      filter_upwards [eventually_log_pow_le_rpow p one_pos,
        Filter.eventually_ge_atTop (Real.exp 1)] with L ha hb
      have hL0 : (0 : ℝ) < L := lt_of_lt_of_le (Real.exp_pos 1) hb
      have hlog : (1 : ℝ) ≤ Real.log L := by
        have h := Real.log_le_log (Real.exp_pos 1) hb
        rwa [Real.log_exp] at h
      have h1 : (Real.log L) ^ (1 + 2 * η) ≤ (Real.log L) ^ ((p : ℕ) : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hlog hp
      rw [Real.rpow_natCast] at h1
      rw [Real.rpow_one] at ha
      linarith
    filter_upwards [Filter.eventually_ge_atTop (Real.exp 1),
      eventually_log_pow_le_rpow 8 hε,
      eventually_rpow_mul_exp_le_one hcT one_pos,
      eventually_rpow_mul_exp_le_one hκ₁ (by linarith : (0:ℝ) < 2 * η),
      eventually_rpow_mul_exp_le_one hκ₂ one_pos, h6, h7] with L a1 a2 a3 a4 a5 a6 a7
    exact ⟨a1, a2, a3, a4, a5, a6, a7⟩
  have hevx := (Real.tendsto_logb_atTop hb1).eventually hev
  obtain ⟨x₀, hx₀⟩ := Filter.eventually_atTop.mp
    (hevx.and (Filter.eventually_gt_atTop (3 : ℝ)))
  refine ⟨(g.dg : ℝ) * AT + (g.dg : ℝ) * C1 + 4 * CT * C1 + 17 * (g.dg : ℝ) + 1,
    x₀, by positivity, fun x hx => ?_⟩
  obtain ⟨⟨hL1, hL2, hL3, hL4, hL5, hL6, hL7⟩, hx3⟩ := hx₀ x hx
  obtain ⟨L, hLdef⟩ : ∃ t : ℝ, t = Real.logb (b : ℝ) x := ⟨_, rfl⟩
  rw [← hLdef] at hL1 hL2 hL3 hL4 hL5 hL6 hL7 ⊢
  -- basic facts about `L`
  have hL0 : (0 : ℝ) < L := lt_of_lt_of_le (Real.exp_pos 1) hL1
  have hlogL : (1 : ℝ) ≤ Real.log L := by
    have h := Real.log_le_log (Real.exp_pos 1) hL1
    rwa [Real.log_exp] at h
  have hlogL0 : (0 : ℝ) < Real.log L := by linarith
  have hL1' : (1 : ℝ) ≤ L := by
    by_contra hcon
    have hlt : L < 1 := lt_of_not_ge hcon
    have : Real.log L ≤ 0 := Real.log_nonpos hL0.le hlt.le
    linarith
  have hsqL : (1 : ℝ) ≤ Real.sqrt L := by
    rw [show (1:ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt hL1'
  have hsqL0 : (0 : ℝ) < Real.sqrt L := by linarith
  have hsqsq : Real.sqrt L * Real.sqrt L = L := Real.mul_self_sqrt hL0.le
  have hsqleL : Real.sqrt L ≤ L := by nlinarith
  have hx0 : (0 : ℝ) ≤ x := by linarith
  have hx2 : (2 : ℝ) < x := by linarith
  -- the parameters
  obtain ⟨s, hsdef⟩ : ∃ t : ℝ, t = 2 * g.sigSq * L := ⟨_, rfl⟩
  obtain ⟨y, hydef⟩ : ∃ t : ℝ, t = 2 * g.mu * L := ⟨_, rfl⟩
  obtain ⟨W, hWdef⟩ : ∃ t : ℝ, t = CT * Real.sqrt L * Real.log L := ⟨_, rfl⟩
  obtain ⟨Q, hQdef⟩ : ∃ t : ℝ, t = Qeta η L := ⟨_, rfl⟩
  obtain ⟨E, hEdef⟩ : ∃ t : ℝ, t = C1 * x * (Real.log L) ^ 6 / L := ⟨_, rfl⟩
  obtain ⟨T, hTdef⟩ : ∃ t : ℝ, t = AT * x * Real.exp (-(cT * (Real.log L) ^ 2)) := ⟨_, rfl⟩
  have hs : (0 : ℝ) < s := by rw [hsdef]; positivity
  have hW : (0 : ℝ) ≤ W := by rw [hWdef]; positivity
  have hE0 : (0 : ℝ) ≤ E := by rw [hEdef]; positivity
  have hT0 : (0 : ℝ) ≤ T := by rw [hTdef]; positivity
  -- the local theorem and the tail, at this `x`
  have hker : ∀ k : ℤ, sqMain g x k = (rhoSq g k : ℝ) * x * gaussKer s y (k : ℝ) := by
    intro k
    rw [hsdef, hydef, hLdef]
    exact sqMain_eq_gaussKer g x k
  have hE : ∀ k : ℤ, |(sqCountEq g x k : ℝ) - sqMain g x k| ≤ E := by
    intro k
    have h := hlltbd x hx2 k
    rw [← hLdef, max_eq_right hlogL,
      show (5 + (1 : ℝ)) = ((6 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at h
    rw [hEdef]
    exact h
  have hTb : (((intsLE x).filter
      (fun n : ℕ => W < |(g.eval (n ^ 2) : ℝ) - y|)).card : ℝ) ≤ T := by
    have h := htailbd x hx2
    rw [← hLdef] at h
    rw [hWdef, hydef, hTdef]
    exact h
  -- the cut-off `Q`
  have hQ2 : Q ^ 2 = L / (Real.log L) ^ (1 + 2 * η) := by
    rw [hQdef, Qeta, div_pow, Real.sq_sqrt hL0.le, ← Real.rpow_natCast
      ((Real.log L) ^ (1 / 2 + η)) 2, ← Real.rpow_mul hlogL0.le]
    norm_num
    ring_nf
  have hQ0 : (0 : ℝ) < Q := by
    rw [hQdef, Qeta]
    have : (0:ℝ) < (Real.log L) ^ (1 / 2 + η) := Real.rpow_pos_of_pos hlogL0 _
    positivity
  have hQ1 : (1 : ℝ) ≤ Q := by
    have hden : (0 : ℝ) < (Real.log L) ^ (1 + 2 * η) := Real.rpow_pos_of_pos hlogL0 _
    have h1 : (1 : ℝ) ≤ Q ^ 2 := by
      rw [hQ2, le_div_iff₀ hden]
      linarith
    nlinarith
  have hQle : Q ≤ Real.sqrt L := by
    rw [hQdef, Qeta]
    have h1 : (1 : ℝ) ≤ (Real.log L) ^ (1 / 2 + η) := by
      have := Real.rpow_le_rpow_of_exponent_le hlogL (by linarith : (0:ℝ) ≤ 1/2 + η)
      rwa [Real.rpow_zero] at this
    exact div_le_self (Real.sqrt_nonneg L) h1
  -- the two exponential factors
  obtain ⟨e1s, he1def⟩ : ∃ t : ℝ, t = Real.exp (-(κ₁ * (Real.log L) ^ (1 + 2 * η))) := ⟨_, rfl⟩
  obtain ⟨e2, he2def⟩ : ∃ t : ℝ, t = Real.exp (-(κ₂ * (Real.log L) ^ 2)) := ⟨_, rfl⟩
  obtain ⟨Kc, hKdef⟩ : ∃ t : ℝ,
      t = 2 * W * E + 4 * x * (g.dg : ℝ) * e1s
        + 3 * Real.sqrt 2 * x * (g.dg : ℝ) * e2 := ⟨_, rfl⟩
  have he1pos : (0 : ℝ) < e1s := by rw [he1def]; positivity
  have he2pos : (0 : ℝ) < e2 := by rw [he2def]; positivity
  have hK0 : (0 : ℝ) ≤ Kc := by rw [hKdef]; positivity
  have hden : (0 : ℝ) < (Real.log L) ^ (1 + 2 * η) := Real.rpow_pos_of_pos hlogL0 _
  -- the per-modulus bound
  have hmod : ∀ m ∈ moduli g x η,
      deltaSqMax g x m ≤ (g.dg : ℝ) * T + (g.dg : ℝ) * E + Kc / (m : ℝ) := by
    intro m hm
    rw [moduli, Finset.mem_filter, Finset.mem_Icc] at hm
    obtain ⟨⟨hm1, hm2⟩, hmcop⟩ := hm
    have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm1
    have hmQ : (m : ℝ) ≤ Q := by
      have h1 : (m : ℝ) ≤ ((⌊Qeta η (Real.logb (b : ℝ) x)⌋₊ : ℕ) : ℝ) := by exact_mod_cast hm2
      have h2 : ((⌊Qeta η (Real.logb (b : ℝ) x)⌋₊ : ℕ) : ℝ) ≤ Qeta η (Real.logb (b : ℝ) x) :=
        Nat.floor_le (by rw [← hLdef]; linarith [hQdef ▸ hQ0.le])
      rw [hQdef, hLdef]
      linarith
    have hMcast : (((m * g.dg : ℕ)) : ℝ) = (m : ℝ) * (g.dg : ℝ) := by push_cast; ring
    have h3 : (m : ℝ) ^ 2 ≤ L / (Real.log L) ^ (1 + 2 * η) := by
      rw [← hQ2]; nlinarith
    have h5 : (m : ℝ) ^ 2 * (Real.log L) ^ (1 + 2 * η) ≤ L := by
      rw [← le_div_iff₀ hden]; exact h3
    -- the modulus is small enough for Poisson summation
    have hMs : (((m * g.dg : ℕ)) : ℝ) ^ 2 ≤ 2 * Real.pi ^ 2 * s := by
      rw [hMcast, hsdef, mul_pow]
      have h4 : (L / (Real.log L) ^ (1 + 2 * η)) * (g.dg : ℝ) ^ 2
          ≤ 2 * Real.pi ^ 2 * (2 * g.sigSq * L) := by
        rw [div_mul_eq_mul_div, div_le_iff₀ hden]
        have h6 := mul_le_mul_of_nonneg_left hL6 hL0.le
        nlinarith [h6]
      calc (m : ℝ) ^ 2 * (g.dg : ℝ) ^ 2
          ≤ (L / (Real.log L) ^ (1 + 2 * η)) * (g.dg : ℝ) ^ 2 :=
            mul_le_mul_of_nonneg_right h3 (sq_nonneg _)
        _ ≤ 2 * Real.pi ^ 2 * (2 * g.sigSq * L) := h4
    have hMs' : (((m * g.dg : ℕ)) : ℝ) ^ 2 ≤ 4 * Real.pi ^ 2 * s := by
      have : (0:ℝ) ≤ 2 * Real.pi ^ 2 * s := by positivity
      linarith [hMs]
    -- the two exponentials
    have hW2 : W ^ 2 = CT ^ 2 * L * (Real.log L) ^ 2 := by
      rw [hWdef]
      have hexp : (CT * Real.sqrt L * Real.log L) ^ 2
          = CT ^ 2 * (Real.sqrt L * Real.sqrt L) * (Real.log L) ^ 2 := by ring
      rw [hexp, hsqsq]
    have he2eq : Real.exp (-(W ^ 2 / (4 * s))) = e2 := by
      rw [he2def, hW2, hsdef, hκ₂def]
      congr 1
      field_simp
      ring
    have he1le : Real.exp (-(2 * Real.pi ^ 2 * s / ((m : ℝ) * (g.dg : ℝ)) ^ 2)) ≤ e1s := by
      rw [he1def]
      apply Real.exp_le_exp.mpr
      have hle : κ₁ * (Real.log L) ^ (1 + 2 * η)
          ≤ 2 * Real.pi ^ 2 * s / ((m : ℝ) * (g.dg : ℝ)) ^ 2 := by
        rw [hsdef, hκ₁def, mul_pow, le_div_iff₀ (by positivity)]
        have hcancel : 4 * Real.pi ^ 2 * g.sigSq / (g.dg : ℝ) ^ 2
              * (Real.log L) ^ (1 + 2 * η) * ((m : ℝ) ^ 2 * (g.dg : ℝ) ^ 2)
            = 4 * Real.pi ^ 2 * g.sigSq * ((m : ℝ) ^ 2 * (Real.log L) ^ (1 + 2 * η)) := by
          field_simp
          try ring
        rw [hcancel]
        have h7 := mul_le_mul_of_nonneg_left h5
          (by positivity : (0 : ℝ) ≤ 4 * Real.pi ^ 2 * g.sigSq)
        linarith
      linarith
    -- apply the per-modulus estimate
    refine deltaSqMax_le (by positivity) (fun a _ => ?_)
    refine le_trans (modulus_bound g x hm1 hmcop (a : ℤ) hs hW hx0 hMs hMs' hker hE0 hE hTb) ?_
    rw [hMcast, he2eq]
    calc (g.dg : ℝ) *
          (T + (2 * W / ((m : ℝ) * (g.dg : ℝ)) + 1) * E
            + x * (g.dg : ℝ) * ((4 / ((m : ℝ) * (g.dg : ℝ)))
                * Real.exp (-(2 * Real.pi ^ 2 * s / ((m : ℝ) * (g.dg : ℝ)) ^ 2))
                + (3 * Real.sqrt 2 / ((m : ℝ) * (g.dg : ℝ))) * e2))
        ≤ (g.dg : ℝ) *
          (T + (2 * W / ((m : ℝ) * (g.dg : ℝ)) + 1) * E
            + x * (g.dg : ℝ) * ((4 / ((m : ℝ) * (g.dg : ℝ))) * e1s
                + (3 * Real.sqrt 2 / ((m : ℝ) * (g.dg : ℝ))) * e2)) := by
          gcongr
      _ = (g.dg : ℝ) * T + (g.dg : ℝ) * E + Kc / (m : ℝ) := by
          rw [hKdef]
          have hd0 : ((g.dg : ℝ)) ≠ 0 := ne_of_gt hdR
          have hm0 : ((m : ℝ)) ≠ 0 := ne_of_gt hmR
          field_simp
          ring
  -- the target scale
  obtain ⟨R, hRdef⟩ : ∃ t : ℝ, t = L ^ (-(1 : ℝ) / 2 + ε) := ⟨_, rfl⟩
  have hR0 : (0 : ℝ) < R := by rw [hRdef]; positivity
  have hRval : R = L ^ ε / Real.sqrt L := by
    rw [hRdef, show (-(1 : ℝ) / 2 + ε) = ε + (-(1 / 2) : ℝ) by ring, Real.rpow_add hL0,
      Real.rpow_neg hL0.le, Real.sqrt_eq_rpow]
    field_simp
  have hLeps : (1 : ℝ) ≤ L ^ ε := by
    have h := Real.rpow_le_rpow_of_exponent_le hL1' hε.le
    rwa [Real.rpow_zero] at h
  have hinvsq : 1 / Real.sqrt L ≤ R := by
    rw [hRval]
    gcongr
  have hinvL : 1 / L ≤ R := by
    have h1 : 1 / L ≤ 1 / Real.sqrt L := by
      apply one_div_le_one_div_of_le hsqL0 hsqleL
    linarith
  have hlogleL : Real.log L ≤ L := by
    have := Real.log_le_sub_one_of_pos hL0
    linarith
  have hlog6 : (Real.log L) ^ 6 ≤ L ^ ε := by
    have h1 : (Real.log L) ^ 6 ≤ (Real.log L) ^ 8 := by
      apply pow_le_pow_right₀ hlogL
      norm_num
    linarith only [h1, hL2]
  -- the exponential factors are `≤ 1/(L√L)`
  have hL32 : L * Real.sqrt L = L ^ (3 / 2 : ℝ) := by
    have h1 : Real.sqrt L = L ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow L
    have h2 : L = L ^ (1 : ℝ) := (Real.rpow_one L).symm
    rw [h1]
    nth_rewrite 1 [h2]
    rw [← Real.rpow_add hL0]
    norm_num
  have hLsq0 : (0 : ℝ) < L * Real.sqrt L := by positivity
  have hrp2 : (Real.log L) ^ (1 + (1 : ℝ)) = (Real.log L) ^ (2 : ℕ) := by
    rw [show (1 + (1 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hexpT : Real.exp (-(cT * (Real.log L) ^ 2)) ≤ 1 / (L * Real.sqrt L) := by
    rw [hrp2] at hL3
    rw [hL32, le_div_iff₀ (by rw [← hL32]; positivity), mul_comm]
    exact hL3
  have hexp2 : e2 ≤ 1 / (L * Real.sqrt L) := by
    rw [hrp2] at hL5
    rw [he2def, hL32, le_div_iff₀ (by rw [← hL32]; positivity), mul_comm]
    exact hL5
  have hexp1 : e1s ≤ 1 / (L * Real.sqrt L) := by
    rw [he1def, hL32, le_div_iff₀ (by rw [← hL32]; positivity), mul_comm]
    exact hL4
  have hTle : T ≤ AT * x * (1 / (L * Real.sqrt L)) := by
    rw [hTdef]
    exact mul_le_mul_of_nonneg_left hexpT (by positivity : (0:ℝ) ≤ AT * x)
  -- the sum over the moduli
  have hcardQ : (((moduli g x η).card : ℕ) : ℝ) ≤ Q := by
    have h1 : (moduli g x η).card ≤ ⌊Qeta η (Real.logb (b : ℝ) x)⌋₊ := by
      rw [moduli]
      have h2 := Finset.card_filter_le (Finset.Icc 1 ⌊Qeta η (Real.logb (b : ℝ) x)⌋₊)
        (fun m => Nat.Coprime m g.dg)
      rw [Nat.card_Icc] at h2
      simpa using h2
    have h3 : ((⌊Qeta η (Real.logb (b : ℝ) x)⌋₊ : ℕ) : ℝ) ≤ Qeta η (Real.logb (b : ℝ) x) :=
      Nat.floor_le (by rw [← hLdef]; linarith [hQdef ▸ hQ0.le])
    have h4 : (((moduli g x η).card : ℕ) : ℝ) ≤ ((⌊Qeta η (Real.logb (b : ℝ) x)⌋₊ : ℕ) : ℝ) := by
      exact_mod_cast h1
    rw [hQdef, hLdef]
    linarith
  have hharm : ∑ m ∈ moduli g x η, (1 : ℝ) / (m : ℝ) ≤ 1 + Real.log Q :=
    sum_inv_moduli_le g x η hQ1 (by rw [hQdef, hLdef])
  have hlogQ : 1 + Real.log Q ≤ 3 / 2 * Real.log L := by
    have h1 : Real.log Q ≤ Real.log (Real.sqrt L) := Real.log_le_log hQ0 hQle
    rw [Real.log_sqrt hL0.le] at h1
    linarith
  -- two algebraic identities about `√L`
  have hsqdiv : Real.sqrt L / L = 1 / Real.sqrt L := by
    rw [div_eq_div_iff (ne_of_gt hL0) (ne_of_gt hsqL0)]
    linarith [hsqsq]
  have hsqinv : Real.sqrt L * (1 / (L * Real.sqrt L)) = 1 / L := by
    field_simp
  have hLinvL : (1 / (L * Real.sqrt L)) * L = 1 / Real.sqrt L := by
    field_simp
  have hxR : L ^ ε * (x * (1 / Real.sqrt L)) = x * R := by
    rw [hRval]
    field_simp
  have hsq2 : Real.sqrt 2 ≤ 3 / 2 := by
    nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
  -- the three groups of terms
  have hA : Q * ((g.dg : ℝ) * T) ≤ (g.dg : ℝ) * AT * (x * R) := by
    have h1 : Q * ((g.dg : ℝ) * T)
        ≤ Real.sqrt L * ((g.dg : ℝ) * (AT * x * (1 / (L * Real.sqrt L)))) :=
      mul_le_mul hQle (mul_le_mul_of_nonneg_left hTle hdR.le) (by positivity)
        (Real.sqrt_nonneg L)
    have h2 : Real.sqrt L * ((g.dg : ℝ) * (AT * x * (1 / (L * Real.sqrt L))))
        = (g.dg : ℝ) * AT * (x * (1 / L)) := by
      have hre : Real.sqrt L * ((g.dg : ℝ) * (AT * x * (1 / (L * Real.sqrt L))))
          = (g.dg : ℝ) * AT * x * (Real.sqrt L * (1 / (L * Real.sqrt L))) := by ring
      rw [hre, hsqinv]
      ring
    have h3 : (g.dg : ℝ) * AT * (x * (1 / L)) ≤ (g.dg : ℝ) * AT * (x * R) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hinvL hx0) (by positivity)
    linarith only [h1, h2, h3]
  have hB : Q * ((g.dg : ℝ) * E) ≤ (g.dg : ℝ) * C1 * (x * R) := by
    have h1 : Q * ((g.dg : ℝ) * E)
        ≤ Real.sqrt L * ((g.dg : ℝ) * (C1 * x * (Real.log L) ^ 6 / L)) :=
      mul_le_mul hQle (le_of_eq (by rw [hEdef])) (by positivity) (Real.sqrt_nonneg L)
    have h2 : Real.sqrt L * ((g.dg : ℝ) * (C1 * x * (Real.log L) ^ 6 / L))
        = (g.dg : ℝ) * C1 * ((Real.log L) ^ 6 * (x * (1 / Real.sqrt L))) := by
      have hre : Real.sqrt L * ((g.dg : ℝ) * (C1 * x * (Real.log L) ^ 6 / L))
          = (g.dg : ℝ) * C1 * (Real.log L) ^ 6 * x * (Real.sqrt L / L) := by ring
      rw [hre, hsqdiv]
      ring
    have h3 : (g.dg : ℝ) * C1 * ((Real.log L) ^ 6 * (x * (1 / Real.sqrt L)))
        ≤ (g.dg : ℝ) * C1 * (L ^ ε * (x * (1 / Real.sqrt L))) := by gcongr
    rw [hxR] at h3
    linarith only [h1, h2, h3]
  have hp1 : 2 * W * E * (3 / 2 * Real.log L) ≤ 3 * CT * C1 * (x * R) := by
    have heq : 2 * W * E * (3 / 2 * Real.log L)
        = 3 * CT * C1 * ((Real.log L) ^ 8 * (x * (Real.sqrt L / L))) := by
      rw [hWdef, hEdef]; ring
    rw [heq, hsqdiv]
    have h1 : 3 * CT * C1 * ((Real.log L) ^ 8 * (x * (1 / Real.sqrt L)))
        ≤ 3 * CT * C1 * (L ^ ε * (x * (1 / Real.sqrt L))) := by gcongr
    rw [hxR] at h1
    exact h1
  have hp2 : 4 * x * (g.dg : ℝ) * e1s * (3 / 2 * Real.log L) ≤ 6 * (g.dg : ℝ) * (x * R) := by
    have h1 : e1s * Real.log L ≤ 1 / Real.sqrt L := by
      have h := mul_le_mul hexp1 hlogleL hlogL0.le (by positivity : (0:ℝ) ≤ 1 / (L * Real.sqrt L))
      rw [hLinvL] at h
      exact h
    have h3 : 4 * x * (g.dg : ℝ) * e1s * (3 / 2 * Real.log L)
        = 6 * (g.dg : ℝ) * (x * (e1s * Real.log L)) := by ring
    rw [h3]
    exact mul_le_mul_of_nonneg_left
      (le_trans (mul_le_mul_of_nonneg_left h1 hx0) (mul_le_mul_of_nonneg_left hinvsq hx0))
      (by positivity)
  have hp3 : 3 * Real.sqrt 2 * x * (g.dg : ℝ) * e2 * (3 / 2 * Real.log L)
      ≤ 7 * (g.dg : ℝ) * (x * R) := by
    have h1 : e2 * Real.log L ≤ 1 / Real.sqrt L := by
      have h := mul_le_mul hexp2 hlogleL hlogL0.le (by positivity : (0:ℝ) ≤ 1 / (L * Real.sqrt L))
      rw [hLinvL] at h
      exact h
    have h3 : 3 * Real.sqrt 2 * x * (g.dg : ℝ) * e2 * (3 / 2 * Real.log L)
        = 9 / 2 * Real.sqrt 2 * ((g.dg : ℝ) * (x * (e2 * Real.log L))) := by ring
    rw [h3]
    have hu0 : (0 : ℝ) ≤ (g.dg : ℝ) * (x * (e2 * Real.log L)) := by positivity
    have h4 : (g.dg : ℝ) * (x * (e2 * Real.log L)) ≤ (g.dg : ℝ) * (x * R) :=
      mul_le_mul_of_nonneg_left
        (le_trans (mul_le_mul_of_nonneg_left h1 hx0) (mul_le_mul_of_nonneg_left hinvsq hx0))
        hdR.le
    have hxR0 : (0 : ℝ) ≤ (g.dg : ℝ) * (x * R) := by positivity
    have hstep1 : 9 / 2 * Real.sqrt 2 * ((g.dg : ℝ) * (x * (e2 * Real.log L)))
        ≤ 9 / 2 * (3 / 2) * ((g.dg : ℝ) * (x * (e2 * Real.log L))) := by
      refine mul_le_mul_of_nonneg_right ?_ hu0
      linarith only [hsq2]
    have hstep2 : 9 / 2 * (3 / 2) * ((g.dg : ℝ) * (x * (e2 * Real.log L)))
        ≤ 9 / 2 * (3 / 2) * ((g.dg : ℝ) * (x * R)) := by
      refine mul_le_mul_of_nonneg_left h4 ?_
      norm_num
    have hstep3 : 9 / 2 * (3 / 2) * ((g.dg : ℝ) * (x * R)) ≤ 7 * (g.dg : ℝ) * (x * R) := by
      have he1 : 9 / 2 * (3 / 2) * ((g.dg : ℝ) * (x * R))
          = 27 / 4 * ((g.dg : ℝ) * (x * R)) := by ring
      have he2' : 7 * (g.dg : ℝ) * (x * R) = 7 * ((g.dg : ℝ) * (x * R)) := by ring
      rw [he1, he2']
      refine mul_le_mul_of_nonneg_right ?_ hxR0
      norm_num
    linarith only [hstep1, hstep2, hstep3]
  have hC : Kc * (3 / 2 * Real.log L) ≤ (3 * CT * C1 + 13 * (g.dg : ℝ)) * (x * R) := by
    rw [hKdef, add_mul, add_mul]
    linarith only [hp1, hp2, hp3]
  -- assemble
  have hDT0 : (0 : ℝ) ≤ (g.dg : ℝ) * T + (g.dg : ℝ) * E := by positivity
  have hsum1 : ∑ m ∈ moduli g x η, deltaSqMax g x m
      ≤ (((moduli g x η).card : ℕ) : ℝ) * ((g.dg : ℝ) * T + (g.dg : ℝ) * E)
        + Kc * ∑ m ∈ moduli g x η, (1 : ℝ) / (m : ℝ) := by
    calc ∑ m ∈ moduli g x η, deltaSqMax g x m
        ≤ ∑ m ∈ moduli g x η, ((g.dg : ℝ) * T + (g.dg : ℝ) * E + Kc / (m : ℝ)) :=
          Finset.sum_le_sum hmod
      _ = _ := by
          rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, Finset.mul_sum]
          congr 1
          exact Finset.sum_congr rfl (fun m _ => by ring)
  have hsum2 : (((moduli g x η).card : ℕ) : ℝ) * ((g.dg : ℝ) * T + (g.dg : ℝ) * E)
        + Kc * ∑ m ∈ moduli g x η, (1 : ℝ) / (m : ℝ)
      ≤ Q * ((g.dg : ℝ) * T + (g.dg : ℝ) * E) + Kc * (3 / 2 * Real.log L) := by
    have h1 : (((moduli g x η).card : ℕ) : ℝ) * ((g.dg : ℝ) * T + (g.dg : ℝ) * E)
        ≤ Q * ((g.dg : ℝ) * T + (g.dg : ℝ) * E) := mul_le_mul_of_nonneg_right hcardQ hDT0
    have h2 : Kc * ∑ m ∈ moduli g x η, (1 : ℝ) / (m : ℝ) ≤ Kc * (3 / 2 * Real.log L) :=
      mul_le_mul_of_nonneg_left (le_trans hharm hlogQ) hK0
    linarith only [h1, h2]
  have hgoal : Q * ((g.dg : ℝ) * T + (g.dg : ℝ) * E) + Kc * (3 / 2 * Real.log L)
      ≤ ((g.dg : ℝ) * AT + (g.dg : ℝ) * C1 + 4 * CT * C1 + 17 * (g.dg : ℝ) + 1) * (x * R) := by
    have hexpand : ((g.dg : ℝ) * AT + (g.dg : ℝ) * C1 + 4 * CT * C1 + 17 * (g.dg : ℝ) + 1)
          * (x * R)
        = (g.dg : ℝ) * AT * (x * R) + (g.dg : ℝ) * C1 * (x * R)
          + (3 * CT * C1 + 13 * (g.dg : ℝ)) * (x * R)
          + (CT * C1 + 4 * (g.dg : ℝ) + 1) * (x * R) := by ring
    have hQsplit : Q * ((g.dg : ℝ) * T + (g.dg : ℝ) * E)
        = Q * ((g.dg : ℝ) * T) + Q * ((g.dg : ℝ) * E) := by ring
    have hrest : (0 : ℝ) ≤ (CT * C1 + 4 * (g.dg : ℝ) + 1) * (x * R) := by positivity
    rw [hexpand, hQsplit]
    linarith only [hA, hB, hC, hrest]
  have hcast : ((g.dg : ℝ) * AT + (g.dg : ℝ) * C1 + 4 * CT * C1 + 17 * (g.dg : ℝ) + 1)
      * x * L ^ (-(1 : ℝ) / 2 + ε)
      = ((g.dg : ℝ) * AT + (g.dg : ℝ) * C1 + 4 * CT * C1 + 17 * (g.dg : ℝ) + 1) * (x * R) := by
    rw [hRdef]; ring
  rw [hcast]
  linarith only [hsum1, hsum2, hgoal]

end DSS
