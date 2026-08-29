/-
DSS/GaussSum.lean

**Lemma 4.3 of the paper: Gaussian sums in arithmetic progressions.**

The output-distribution theorem needs to know how much of a Gaussian of
variance `s` sits in a residue class `c` modulo `M`.  The paper's Lemma 4.3
answers this by Poisson summation:

  `(2πs)^{-1/2} ∑_{k ≡ c (M)} exp(−(k−y)²/(2s)) = 1/M + O(e^{−c_η(log L)^{1+2η}})`,

uniformly in `y` and `c`, once `M` is below the near-square-root cut-off
`Q_η(L)`.

This file proves that, from Mathlib's Jacobi theta transformation
(`Complex.tsum_exp_neg_quadratic`, in
`Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation`):

* `tsum_gauss_shift` — the transformation itself for a *shifted* real
  Gaussian: `∑_{n∈ℤ} e^{−α(n+β)²} = √(π/α) ∑_{n∈ℤ} e^{−π²n²/α} e(βn)`,
  obtained from the Mathlib statement at the real parameters `a = α/π`,
  `b = −αβ/π`;
* `tsum_gaussOff_le` — the `n ≠ 0` frequencies are geometrically small,
  `≤ 2t/(1−t)` with `t = e^{−π²/α}`;
* `abs_tsum_gauss_shift_sub` — hence
  `|∑_{n∈ℤ} e^{−α(n+β)²} − √(π/α)| ≤ √(π/α)·2t/(1−t)`, uniformly in `β`;
* `tsum_gauss_shift_le` — the crude upper bound `≤ 3√(π/α)` once `π²/α ≥ 1`;
* `gaussian_progression` — **Lemma 4.3**, with the explicit constant `4/M`
  and the explicit rate `2π²s/M²`, under the (very weak) hypothesis
  `M² ≤ 2π²s`.

Nothing in this file is conditional: it imports no axioms.
-/
import DSS.Imports

namespace DSS

open Finset

/-! ### Summability of a Gaussian along `ℤ` -/

private lemma exp_sq_le_geom {c : ℝ} (hc : 0 ≤ c) (k : ℕ) :
    Real.exp (-c * ((k : ℝ)) ^ 2) ≤ Real.exp (-c) ^ k := by
  rw [← Real.exp_nat_mul]
  apply Real.exp_le_exp.mpr
  have h1 : (k : ℝ) ≤ (k : ℝ) ^ 2 := by
    rcases Nat.eq_zero_or_pos k with h | h
    · simp [h]
    · have : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast h
      nlinarith
  nlinarith

private lemma summable_gauss_nat {c : ℝ} (hc : 0 < c) :
    Summable (fun k : ℕ => Real.exp (-c * ((k : ℝ)) ^ 2)) := by
  have ht : Real.exp (-c) < 1 := by
    rw [Real.exp_lt_one_iff]
    linarith
  have ht0 : (0 : ℝ) ≤ Real.exp (-c) := (Real.exp_pos _).le
  refine Summable.of_nonneg_of_le (fun k => (Real.exp_pos _).le)
    (fun k => exp_sq_le_geom hc.le k) ?_
  exact summable_geometric_of_lt_one ht0 ht

theorem summable_gauss_int {c : ℝ} (hc : 0 < c) :
    Summable (fun n : ℤ => Real.exp (-c * ((n : ℝ)) ^ 2)) := by
  refine Summable.of_nat_of_neg_add_one ?_ ?_
  · simpa using summable_gauss_nat hc
  · have h : ∀ k : ℕ, Real.exp (-c * (((-(k + 1) : ℤ)) : ℝ) ^ 2)
        = Real.exp (-c * ((k + 1 : ℕ) : ℝ) ^ 2) := by
      intro k
      congr 1
      push_cast
      ring
    simp only [h]
    exact (summable_gauss_nat hc).comp_injective (add_left_injective 1)

/-! ### The off-diagonal terms -/

private lemma summable_geom_shift {c : ℝ} (hc : 0 < c) :
    Summable (fun k : ℕ => Real.exp (-c) ^ (k + 1)) := by
  have ht : Real.exp (-c) < 1 := by rw [Real.exp_lt_one_iff]; linarith
  have ht0 : (0 : ℝ) ≤ Real.exp (-c) := (Real.exp_pos _).le
  exact ((summable_geometric_of_lt_one ht0 ht).mul_left (Real.exp (-c))).congr
    (fun k => by ring)

private lemma summable_gauss_shift {c : ℝ} (hc : 0 < c) :
    Summable (fun k : ℕ => Real.exp (-c * ((k : ℝ) + 1) ^ 2)) := by
  refine Summable.of_nonneg_of_le (fun k => (Real.exp_pos _).le) (fun k => ?_)
    (summable_geom_shift hc)
  have h := exp_sq_le_geom hc.le (k + 1)
  push_cast at h
  exact h

private lemma tsum_shifted_le {c : ℝ} (hc : 0 < c) :
    ∑' k : ℕ, Real.exp (-c * ((k : ℝ) + 1) ^ 2)
      ≤ Real.exp (-c) / (1 - Real.exp (-c)) := by
  have ht : Real.exp (-c) < 1 := by rw [Real.exp_lt_one_iff]; linarith
  have ht0 : (0 : ℝ) ≤ Real.exp (-c) := (Real.exp_pos _).le
  have hgeo : ∑' k : ℕ, Real.exp (-c) ^ (k + 1) = Real.exp (-c) / (1 - Real.exp (-c)) := by
    have h := tsum_geometric_of_lt_one ht0 ht
    calc ∑' k : ℕ, Real.exp (-c) ^ (k + 1)
        = ∑' k : ℕ, Real.exp (-c) * Real.exp (-c) ^ k := tsum_congr (fun k => by ring)
      _ = Real.exp (-c) * ∑' k : ℕ, Real.exp (-c) ^ k := tsum_mul_left
      _ = Real.exp (-c) * (1 - Real.exp (-c))⁻¹ := by rw [h]
      _ = Real.exp (-c) / (1 - Real.exp (-c)) := by ring
  rw [← hgeo]
  refine (summable_gauss_shift hc).tsum_le_tsum (fun k => ?_) (summable_geom_shift hc)
  have h := exp_sq_le_geom hc.le (k + 1)
  push_cast at h
  exact h

/-- The Gaussian along `ℤ` with the `n = 0` term removed. -/
noncomputable def gaussOff (c : ℝ) (n : ℤ) : ℝ :=
  if n = 0 then 0 else Real.exp (-c * ((n : ℝ)) ^ 2)

private lemma gaussOff_nonneg (c : ℝ) (n : ℤ) : 0 ≤ gaussOff c n := by
  unfold gaussOff
  by_cases h : n = 0
  · simp [h]
  · rw [if_neg h]; exact (Real.exp_pos _).le

private lemma gaussOff_le (c : ℝ) (n : ℤ) : gaussOff c n ≤ Real.exp (-c * ((n : ℝ)) ^ 2) := by
  unfold gaussOff
  by_cases h : n = 0
  · rw [if_pos h]; exact (Real.exp_pos _).le
  · rw [if_neg h]

private lemma gaussOff_nat (c : ℝ) (k : ℕ) :
    gaussOff c ((k : ℕ) : ℤ) = if k = 0 then 0 else Real.exp (-c * ((k : ℝ)) ^ 2) := by
  unfold gaussOff
  by_cases h : k = 0 <;> simp [h]

private lemma gaussOff_neg (c : ℝ) (k : ℕ) :
    gaussOff c (-((k : ℤ) + 1)) = Real.exp (-c * ((k : ℝ) + 1) ^ 2) := by
  unfold gaussOff
  rw [if_neg (by omega)]
  congr 1
  push_cast
  ring

theorem summable_gaussOff {c : ℝ} (hc : 0 < c) : Summable (gaussOff c) :=
  Summable.of_nonneg_of_le (gaussOff_nonneg c) (gaussOff_le c) (summable_gauss_int hc)

/-- **The `n ≠ 0` terms of a Gaussian along `ℤ` are geometrically small:**
their total is at most `2t/(1−t)` with `t = e^{−c}`. -/
theorem tsum_gaussOff_le {c : ℝ} (hc : 0 < c) :
    ∑' n : ℤ, gaussOff c n ≤ 2 * (Real.exp (-c) / (1 - Real.exp (-c))) := by
  have hnat : Summable (fun k : ℕ => gaussOff c (k : ℤ)) := by
    refine Summable.of_nonneg_of_le (fun k => gaussOff_nonneg c _) (fun k => ?_)
      (summable_gauss_nat hc)
    simpa using gaussOff_le c (k : ℤ)
  have hneg : Summable (fun k : ℕ => gaussOff c (-((k : ℤ) + 1))) :=
    (summable_gauss_shift hc).congr (fun k => (gaussOff_neg c k).symm)
  rw [tsum_of_nat_of_neg_add_one hnat hneg]
  have h1 : ∑' k : ℕ, gaussOff c ((k : ℕ) : ℤ) ≤ Real.exp (-c) / (1 - Real.exp (-c)) := by
    rw [tsum_congr (gaussOff_nat c)]
    have hz : Summable (fun k : ℕ => if k = 0 then (0 : ℝ)
        else Real.exp (-c * ((k : ℝ)) ^ 2)) := hnat.congr (gaussOff_nat c)
    have hstep : ∀ k : ℕ,
        (if k + 1 = 0 then (0 : ℝ) else Real.exp (-c * (((k + 1 : ℕ) : ℝ)) ^ 2))
          = Real.exp (-c * ((k : ℝ) + 1) ^ 2) := by
      intro k
      rw [if_neg (Nat.succ_ne_zero k)]
      congr 1
      push_cast
      ring
    rw [hz.tsum_eq_zero_add, if_pos rfl, zero_add, tsum_congr hstep]
    exact tsum_shifted_le hc
  have h2 : ∑' k : ℕ, gaussOff c (-((k : ℤ) + 1)) ≤ Real.exp (-c) / (1 - Real.exp (-c)) := by
    rw [tsum_congr (gaussOff_neg c)]
    exact tsum_shifted_le hc
  linarith

/-! ### The theta transformation for a shifted Gaussian -/

/-- The dual (frequency-side) summand of the theta transformation. -/
noncomputable def thetaTerm (α β : ℝ) (n : ℤ) : ℂ :=
  ((Real.exp (-(Real.pi ^ 2 / α) * ((n : ℝ)) ^ 2) : ℝ) : ℂ)
    * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (β : ℂ) * (n : ℂ))

/-- **Poisson summation for a shifted Gaussian** (the identity behind
Lemma 4.3): for `α > 0` and `β ∈ ℝ`,

`∑_{n∈ℤ} e^{−α(n+β)²} = √(π/α) ∑_{n∈ℤ} e^{−π²n²/α} e(βn)`.

This is Jacobi's theta transformation, `Complex.tsum_exp_neg_quadratic`, at
the real parameters `a = α/π`, `b = −αβ/π`. -/
theorem tsum_gauss_shift {α : ℝ} (hα : 0 < α) (β : ℝ) :
    (∑' n : ℤ, ((Real.exp (-α * ((n : ℝ) + β) ^ 2) : ℝ) : ℂ))
      = ((Real.sqrt (Real.pi / α) : ℝ) : ℂ) * ∑' n : ℤ, thetaTerm α β n := by
  unfold thetaTerm
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  have hπC : ((Real.pi : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hπ
  have hαC : ((α : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hα
  have hApos : (0 : ℝ) < α / Real.pi := div_pos hα hπ
  have hAre : 0 < (((α / Real.pi : ℝ)) : ℂ).re := by
    rw [Complex.ofReal_re]; exact hApos
  have key := Complex.tsum_exp_neg_quadratic hAre (((-(α * β) / Real.pi : ℝ)) : ℂ)
  -- the left-hand summand
  have hLHS : ∀ n : ℤ,
      Complex.exp (-(Real.pi : ℂ) * (((α / Real.pi : ℝ)) : ℂ) * (n : ℂ) ^ 2
          + 2 * (Real.pi : ℂ) * (((-(α * β) / Real.pi : ℝ)) : ℂ) * (n : ℂ))
        = ((Real.exp (α * β ^ 2) : ℝ) : ℂ)
          * ((Real.exp (-α * ((n : ℝ) + β) ^ 2) : ℝ) : ℂ) := by
    intro n
    have h1 : -(Real.pi : ℂ) * (((α / Real.pi : ℝ)) : ℂ) * (n : ℂ) ^ 2
        + 2 * (Real.pi : ℂ) * (((-(α * β) / Real.pi : ℝ)) : ℂ) * (n : ℂ)
        = ((α * β ^ 2 : ℝ) : ℂ) + ((-α * ((n : ℝ) + β) ^ 2 : ℝ) : ℂ) := by
      push_cast
      field_simp
      ring
    rw [h1, Complex.exp_add, Complex.ofReal_exp, Complex.ofReal_exp]
  -- the right-hand summand
  have hRHS : ∀ n : ℤ,
      Complex.exp (-(Real.pi : ℂ) / (((α / Real.pi : ℝ)) : ℂ)
          * ((n : ℂ) + Complex.I * (((-(α * β) / Real.pi : ℝ)) : ℂ)) ^ 2)
        = ((Real.exp (α * β ^ 2) : ℝ) : ℂ)
          * ((((Real.exp (-(Real.pi ^ 2 / α) * ((n : ℝ)) ^ 2)) : ℝ) : ℂ)
              * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (β : ℂ) * (n : ℂ))) := by
    intro n
    have h1 : -(Real.pi : ℂ) / (((α / Real.pi : ℝ)) : ℂ)
        * ((n : ℂ) + Complex.I * (((-(α * β) / Real.pi : ℝ)) : ℂ)) ^ 2
        = ((α * β ^ 2 : ℝ) : ℂ) + ((-(Real.pi ^ 2 / α) * ((n : ℝ)) ^ 2 : ℝ) : ℂ)
          + 2 * (Real.pi : ℂ) * Complex.I * (β : ℂ) * (n : ℂ) := by
      have hI : (Complex.I) ^ 2 = -1 := Complex.I_sq
      push_cast
      field_simp
      ring_nf
      rw [hI]
      ring
    rw [h1, Complex.exp_add, Complex.exp_add, Complex.ofReal_exp, Complex.ofReal_exp,
      mul_assoc]
  rw [tsum_congr hLHS, tsum_mul_left, tsum_congr hRHS, tsum_mul_left, ← mul_assoc] at key
  -- identify `1/a^{1/2}` with `√(π/α)`
  have hcpow : (((α / Real.pi : ℝ)) : ℂ) ^ (1 / 2 : ℂ)
      = ((Real.sqrt (α / Real.pi) : ℝ) : ℂ) := by
    have h := Complex.ofReal_cpow hApos.le (1 / 2 : ℝ)
    rw [← Real.sqrt_eq_rpow] at h
    have hc : ((1 / 2 : ℝ) : ℂ) = (1 / 2 : ℂ) := by norm_num
    rw [hc] at h
    exact h.symm
  have hsqrt : Real.sqrt (Real.pi / α) = (Real.sqrt (α / Real.pi))⁻¹ := by
    rw [← Real.sqrt_inv]
    congr 1
    field_simp
  have hE : ((Real.exp (α * β ^ 2) : ℝ) : ℂ) ≠ 0 := by
    simp
  rw [hcpow] at key
  refine mul_left_cancel₀ hE ?_
  rw [key, hsqrt]
  push_cast
  ring

/-! ### The resulting bound -/

private lemma norm_thetaTerm (α β : ℝ) (n : ℤ) :
    ‖thetaTerm α β n‖ = Real.exp (-(Real.pi ^ 2 / α) * ((n : ℝ)) ^ 2) := by
  unfold thetaTerm
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have h : 2 * (Real.pi : ℂ) * Complex.I * (β : ℂ) * (n : ℂ)
      = ((2 * Real.pi * β * (n : ℝ) : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [h, Complex.norm_exp_ofReal_mul_I, mul_one]

private lemma summable_thetaTerm {α : ℝ} (_hα : 0 < α) (β : ℝ) :
    Summable (thetaTerm α β) := by
  refine Summable.of_norm ?_
  refine (summable_gauss_int (c := Real.pi ^ 2 / α) (by positivity)).congr (fun n => ?_)
  exact (norm_thetaTerm α β n).symm

private lemma thetaTerm_zero (α β : ℝ) : thetaTerm α β 0 = 1 := by
  unfold thetaTerm
  norm_num

/-- **The Gaussian sum along a shifted lattice**: the total is `√(π/α)` up to a
relative error that is geometrically small in `π²/α`.  This is the quantitative
form of Poisson summation used by Lemma 4.3. -/
theorem abs_tsum_gauss_shift_sub {α : ℝ} (hα : 0 < α) (β : ℝ) :
    |(∑' n : ℤ, Real.exp (-α * ((n : ℝ) + β) ^ 2)) - Real.sqrt (Real.pi / α)|
      ≤ Real.sqrt (Real.pi / α)
        * (2 * (Real.exp (-(Real.pi ^ 2 / α))
            / (1 - Real.exp (-(Real.pi ^ 2 / α))))) := by
  have hcpos : (0 : ℝ) < Real.pi ^ 2 / α := by positivity
  have hSpos : (0 : ℝ) < Real.sqrt (Real.pi / α) :=
    Real.sqrt_pos.mpr (by positivity)
  -- split off the `n = 0` frequency
  have hsplit : ∑' n : ℤ, thetaTerm α β n
      = 1 + ∑' n : ℤ, (if n = 0 then (0 : ℂ) else thetaTerm α β n) := by
    have h := (summable_thetaTerm hα β).tsum_eq_add_tsum_ite (0 : ℤ)
    rw [thetaTerm_zero α β] at h
    exact h
  -- the off-diagonal remainder is small
  have hoffnorm : ∀ n : ℤ, ‖(if n = 0 then (0 : ℂ) else thetaTerm α β n)‖ = gaussOff (Real.pi ^ 2 / α) n := by
    intro n
    unfold gaussOff
    by_cases h : n = 0
    · simp [h]
    · rw [if_neg h, if_neg h, norm_thetaTerm α β n]
  have hsummoff : Summable (fun n : ℤ => ‖(if n = 0 then (0 : ℂ) else thetaTerm α β n)‖) :=
    (summable_gaussOff hcpos).congr (fun n => (hoffnorm n).symm)
  have hbound : ‖∑' n : ℤ, (if n = 0 then (0 : ℂ) else thetaTerm α β n)‖
      ≤ 2 * (Real.exp (-(Real.pi ^ 2 / α)) / (1 - Real.exp (-(Real.pi ^ 2 / α)))) := by
    calc ‖∑' n : ℤ, (if n = 0 then (0 : ℂ) else thetaTerm α β n)‖
        ≤ ∑' n : ℤ, ‖(if n = 0 then (0 : ℂ) else thetaTerm α β n)‖ :=
          norm_tsum_le_tsum_norm hsummoff
      _ = ∑' n : ℤ, gaussOff (Real.pi ^ 2 / α) n := tsum_congr hoffnorm
      _ ≤ _ := tsum_gaussOff_le hcpos
  -- transport to the real statement
  have hre : ((∑' n : ℤ, Real.exp (-α * ((n : ℝ) + β) ^ 2) : ℝ) : ℂ)
      = ∑' n : ℤ, ((Real.exp (-α * ((n : ℝ) + β) ^ 2) : ℝ) : ℂ) := Complex.ofReal_tsum _
  have hkey : (((∑' n : ℤ, Real.exp (-α * ((n : ℝ) + β) ^ 2)) - Real.sqrt (Real.pi / α) : ℝ) : ℂ)
      = ((Real.sqrt (Real.pi / α) : ℝ) : ℂ)
        * ∑' n : ℤ, (if n = 0 then (0 : ℂ) else thetaTerm α β n) := by
    rw [Complex.ofReal_sub, hre, tsum_gauss_shift hα β, hsplit]
    ring
  have habs : |(∑' n : ℤ, Real.exp (-α * ((n : ℝ) + β) ^ 2)) - Real.sqrt (Real.pi / α)|
      = Real.sqrt (Real.pi / α)
        * ‖∑' n : ℤ, (if n = 0 then (0 : ℂ) else thetaTerm α β n)‖ := by
    have h1 : |(∑' n : ℤ, Real.exp (-α * ((n : ℝ) + β) ^ 2)) - Real.sqrt (Real.pi / α)|
        = ‖(((∑' n : ℤ, Real.exp (-α * ((n : ℝ) + β) ^ 2)) - Real.sqrt (Real.pi / α) : ℝ) : ℂ)‖ := by
      rw [Complex.norm_real, Real.norm_eq_abs]
    rw [h1, hkey, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hSpos]
  rw [habs]
  exact mul_le_mul_of_nonneg_left hbound hSpos.le

private lemma exp_neg_le_half {u : ℝ} (hu : 1 ≤ u) : Real.exp (-u) ≤ 1 / 2 := by
  have h1 : Real.exp (-u) ≤ Real.exp (-1) := Real.exp_le_exp.mpr (by linarith)
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by
    have := Real.add_one_le_exp (1 : ℝ)
    linarith
  have h3 : Real.exp (-1) = (Real.exp 1)⁻¹ := by rw [Real.exp_neg]
  have h4 : (Real.exp 1)⁻¹ ≤ 1 / 2 := by
    rw [inv_le_comm₀ (Real.exp_pos 1) (by norm_num)]
    linarith
  linarith [h3 ▸ h1]

/-! ### Lemma 4.3: Gaussian sums in progressions -/

/-- **Lemma 4.3 (Gaussian sums in progressions).**  For a Gaussian of variance
`s` centred anywhere, the mass carried by a residue class `c` modulo `M` is
`1/M` up to an error that is exponentially small in `s/M²`:

`(1/√(2πs)) ∑_{k ≡ c (M)} exp(−(k−y)²/(2s)) = 1/M + O(M⁻¹ exp(−2π²s/M²))`,

uniformly in `y` and `c`, under `M² ≤ 2π²s` (which is what `M ≤ Q_η(L)`
provides, with room to spare).  The proof is Poisson summation for the
Gaussian: the `j = 0` frequency gives `1/M` and the rest is geometric. -/
theorem gaussian_progression {s : ℝ} (hs : 0 < s) {M : ℕ} (hM : 0 < M) (c : ℤ) (y : ℝ)
    (hMs : ((M : ℝ)) ^ 2 ≤ 2 * Real.pi ^ 2 * s) :
    |(1 / Real.sqrt (2 * Real.pi * s))
        * (∑' n : ℤ, Real.exp (-((((M : ℝ)) * (n : ℝ) + (c : ℝ) - y) ^ 2) / (2 * s)))
      - 1 / (M : ℝ)|
      ≤ (4 / (M : ℝ)) * Real.exp (-(2 * Real.pi ^ 2 * s / ((M : ℝ)) ^ 2)) := by
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  have hMR : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hα : (0 : ℝ) < ((M : ℝ)) ^ 2 / (2 * s) := by positivity
  have hS : (0 : ℝ) < Real.sqrt (2 * Real.pi * s) := Real.sqrt_pos.mpr (by positivity)
  -- the summand is a shifted Gaussian
  have hterm : ∀ n : ℤ,
      Real.exp (-((((M : ℝ)) * (n : ℝ) + (c : ℝ) - y) ^ 2) / (2 * s))
        = Real.exp (-(((M : ℝ)) ^ 2 / (2 * s)) * ((n : ℝ) + ((c : ℝ) - y) / (M : ℝ)) ^ 2) := by
    intro n
    congr 1
    field_simp
    try ring
  -- the dual scale
  have hdual : Real.pi ^ 2 / (((M : ℝ)) ^ 2 / (2 * s)) = 2 * Real.pi ^ 2 * s / ((M : ℝ)) ^ 2 := by
    field_simp
    try ring
  have hroot : Real.sqrt (Real.pi / (((M : ℝ)) ^ 2 / (2 * s)))
      = Real.sqrt (2 * Real.pi * s) / (M : ℝ) := by
    have h1 : Real.pi / (((M : ℝ)) ^ 2 / (2 * s)) = (2 * Real.pi * s) / ((M : ℝ)) ^ 2 := by
      field_simp
      try ring
    rw [h1, Real.sqrt_div (by positivity), Real.sqrt_sq hMR.le]
  have hbase := abs_tsum_gauss_shift_sub hα (((c : ℝ) - y) / (M : ℝ))
  rw [hroot, hdual] at hbase
  rw [tsum_congr hterm]
  -- geometric factor
  have hu : (1 : ℝ) ≤ 2 * Real.pi ^ 2 * s / ((M : ℝ)) ^ 2 := by
    rw [le_div_iff₀ (by positivity)]
    linarith
  have ht : Real.exp (-(2 * Real.pi ^ 2 * s / ((M : ℝ)) ^ 2)) ≤ 1 / 2 := exp_neg_le_half hu
  have ht0 : (0 : ℝ) < Real.exp (-(2 * Real.pi ^ 2 * s / ((M : ℝ)) ^ 2)) := Real.exp_pos _
  have hgeo : 2 * (Real.exp (-(2 * Real.pi ^ 2 * s / ((M : ℝ)) ^ 2))
      / (1 - Real.exp (-(2 * Real.pi ^ 2 * s / ((M : ℝ)) ^ 2))))
      ≤ 4 * Real.exp (-(2 * Real.pi ^ 2 * s / ((M : ℝ)) ^ 2)) := by
    have h1t : (0 : ℝ) < 1 - Real.exp (-(2 * Real.pi ^ 2 * s / ((M : ℝ)) ^ 2)) := by linarith
    rw [← mul_div_assoc, div_le_iff₀ h1t]
    nlinarith [ht0, ht]
  -- assemble
  have hstep : |(∑' n : ℤ, Real.exp (-(((M : ℝ)) ^ 2 / (2 * s))
        * ((n : ℝ) + ((c : ℝ) - y) / (M : ℝ)) ^ 2)) - Real.sqrt (2 * Real.pi * s) / (M : ℝ)|
      ≤ (Real.sqrt (2 * Real.pi * s) / (M : ℝ))
        * (4 * Real.exp (-(2 * Real.pi ^ 2 * s / ((M : ℝ)) ^ 2))) := by
    refine le_trans hbase ?_
    exact mul_le_mul_of_nonneg_left hgeo (by positivity)
  have hsplit2 : (1 / Real.sqrt (2 * Real.pi * s))
      * (∑' n : ℤ, Real.exp (-(((M : ℝ)) ^ 2 / (2 * s))
          * ((n : ℝ) + ((c : ℝ) - y) / (M : ℝ)) ^ 2)) - 1 / (M : ℝ)
      = (1 / Real.sqrt (2 * Real.pi * s))
        * ((∑' n : ℤ, Real.exp (-(((M : ℝ)) ^ 2 / (2 * s))
            * ((n : ℝ) + ((c : ℝ) - y) / (M : ℝ)) ^ 2))
          - Real.sqrt (2 * Real.pi * s) / (M : ℝ)) := by
    field_simp
  rw [hsplit2, abs_mul, abs_of_pos (show (0:ℝ) < 1 / Real.sqrt (2 * Real.pi * s) by positivity)]
  calc (1 / Real.sqrt (2 * Real.pi * s))
        * |(∑' n : ℤ, Real.exp (-(((M : ℝ)) ^ 2 / (2 * s))
            * ((n : ℝ) + ((c : ℝ) - y) / (M : ℝ)) ^ 2))
          - Real.sqrt (2 * Real.pi * s) / (M : ℝ)|
      ≤ (1 / Real.sqrt (2 * Real.pi * s))
        * ((Real.sqrt (2 * Real.pi * s) / (M : ℝ))
          * (4 * Real.exp (-(2 * Real.pi ^ 2 * s / ((M : ℝ)) ^ 2)))) :=
        mul_le_mul_of_nonneg_left hstep (by positivity)
    _ = (4 / (M : ℝ)) * Real.exp (-(2 * Real.pi ^ 2 * s / ((M : ℝ)) ^ 2)) := by
        field_simp
        try ring

/-- Summability of the shifted Gaussian along `ℤ`. -/
theorem summable_gauss_shifted {α : ℝ} (hα : 0 < α) (β : ℝ) :
    Summable (fun n : ℤ => Real.exp (-α * ((n : ℝ) + β) ^ 2)) := by
  have hmaj : ∀ n : ℤ, Real.exp (-α * ((n : ℝ) + β) ^ 2)
      ≤ Real.exp (α * β ^ 2) * Real.exp (-(α / 2) * ((n : ℝ)) ^ 2) := by
    intro n
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [sq_nonneg ((n : ℝ) + 2 * β), sq_nonneg ((n : ℝ) + β), hα.le]
  exact Summable.of_nonneg_of_le (fun n => (Real.exp_pos _).le) hmaj
    ((summable_gauss_int (c := α / 2) (by positivity)).mul_left _)

/-! ### An upper bound for the whole lattice sum -/

/-- A crude upper bound for the shifted Gaussian lattice sum, valid once the
dual scale `π²/α` is at least `1`: the sum is at most `3√(π/α)`. -/
theorem tsum_gauss_shift_le {α : ℝ} (hα : 0 < α) (β : ℝ) (hd : 1 ≤ Real.pi ^ 2 / α) :
    ∑' n : ℤ, Real.exp (-α * ((n : ℝ) + β) ^ 2) ≤ 3 * Real.sqrt (Real.pi / α) := by
  have hS : (0 : ℝ) < Real.sqrt (Real.pi / α) := Real.sqrt_pos.mpr (by positivity)
  have ht : Real.exp (-(Real.pi ^ 2 / α)) ≤ 1 / 2 := exp_neg_le_half hd
  have ht0 : (0 : ℝ) < Real.exp (-(Real.pi ^ 2 / α)) := Real.exp_pos _
  have hgeo : 2 * (Real.exp (-(Real.pi ^ 2 / α)) / (1 - Real.exp (-(Real.pi ^ 2 / α))))
      ≤ 4 * Real.exp (-(Real.pi ^ 2 / α)) := by
    have h1t : (0 : ℝ) < 1 - Real.exp (-(Real.pi ^ 2 / α)) := by linarith
    rw [← mul_div_assoc, div_le_iff₀ h1t]
    nlinarith [ht0, ht]
  have hbase := le_of_abs_le (abs_tsum_gauss_shift_sub hα β)
  nlinarith [hbase, hgeo, hS, ht]

end DSS
