/-
EKRev/Phi.lean

The standard normal distribution function
`Φ(t) = (2π)^{-1/2} ∫_{-∞}^t e^{-u²/2} du` (§1.1) and its properties:
monotonicity, the Lipschitz bound `Φ(t) - Φ(s) ≤ (t-s)/√(2π)` (used at the
end of the proof of Proposition 2.1), continuity, `Φ(-t) = 1 - Φ(t)`, and the
limits `Φ(∞) = 1`, `Φ(-∞) = 0`.

Everything in this file is fully proved (no axioms); the normalization
`∫ e^{-u²/2} = √(2π)` is Mathlib's `integral_gaussian`.
-/
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

namespace EKRev

open MeasureTheory Real Filter Topology

/-- The Gaussian density (unnormalized). -/
noncomputable def gauss (u : ℝ) : ℝ := Real.exp (-u ^ 2 / 2)

lemma gauss_eq (u : ℝ) : gauss u = Real.exp (-(1/2 : ℝ) * u ^ 2) := by
  unfold gauss
  congr 1
  ring

lemma gauss_pos (u : ℝ) : 0 < gauss u := Real.exp_pos _

lemma gauss_nonneg (u : ℝ) : 0 ≤ gauss u := (gauss_pos u).le

lemma gauss_le_one (u : ℝ) : gauss u ≤ 1 := by
  unfold gauss
  rw [Real.exp_le_one_iff]
  have : (0:ℝ) ≤ u ^ 2 := sq_nonneg u
  linarith

lemma gauss_even (u : ℝ) : gauss (-u) = gauss u := by
  unfold gauss
  congr 1
  ring

lemma integrable_gauss : Integrable gauss := by
  have h := integrable_exp_neg_mul_sq (by norm_num : (0:ℝ) < 1/2)
  refine h.congr ?_
  filter_upwards with u
  rw [gauss_eq]

lemma integral_gauss : ∫ u, gauss u = Real.sqrt (2 * Real.pi) := by
  have h := integral_gaussian (1/2 : ℝ)
  have heq : ∫ u, gauss u = ∫ u : ℝ, Real.exp (-(1/2 : ℝ) * u ^ 2) := by
    congr 1
    ext u
    rw [gauss_eq]
  rw [heq, h]
  congr 1
  rw [div_div_eq_mul_div, mul_comm]
  norm_num

lemma sqrt_two_pi_pos : 0 < Real.sqrt (2 * Real.pi) :=
  Real.sqrt_pos.mpr (by positivity)

/-- `Φ`, the standard normal distribution function (§1.1). -/
noncomputable def Phi (t : ℝ) : ℝ :=
  (Real.sqrt (2 * Real.pi))⁻¹ * ∫ u in Set.Iic t, gauss u

lemma Phi_mono : Monotone Phi := by
  intro s t hst
  unfold Phi
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine setIntegral_mono_set integrable_gauss.integrableOn ?_ ?_
  · filter_upwards with u using gauss_nonneg u
  · filter_upwards with u hu using le_trans hu hst

lemma Phi_nonneg (t : ℝ) : 0 ≤ Phi t := by
  unfold Phi
  refine mul_nonneg (by positivity) ?_
  exact setIntegral_nonneg measurableSet_Iic fun u _ => gauss_nonneg u

lemma setIntegral_gauss_le (s : Set ℝ) : ∫ u in s, gauss u ≤ ∫ u, gauss u := by
  refine setIntegral_le_integral integrable_gauss ?_
  filter_upwards with u using gauss_nonneg u

lemma Phi_le_one (t : ℝ) : Phi t ≤ 1 := by
  unfold Phi
  rw [← inv_mul_cancel₀ (ne_of_gt sqrt_two_pi_pos)]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  rw [← integral_gauss]
  exact setIntegral_gauss_le _

/-- The Lipschitz estimate `Φ(t) - Φ(s) ≤ (t-s)/√(2π)` for `s ≤ t`
(the paper's `Φ' ≤ (2π)^{-1/2}`, end of §2). -/
lemma Phi_sub_Phi_le {s t : ℝ} (hst : s ≤ t) :
    Phi t - Phi s ≤ (t - s) / Real.sqrt (2 * Real.pi) := by
  unfold Phi
  rw [← mul_sub]
  have hsplit : (∫ u in Set.Iic t, gauss u) - ∫ u in Set.Iic s, gauss u
      = ∫ u in Set.Ioc s t, gauss u := by
    have hunion : Set.Iic s ∪ Set.Ioc s t = Set.Iic t := Set.Iic_union_Ioc_eq_Iic hst
    have hdisj : Disjoint (Set.Iic s) (Set.Ioc s t) := by
      rw [Set.disjoint_left]
      intro u hu1 hu2
      exact absurd hu2.1 (not_lt.mpr hu1)
    rw [← hunion, setIntegral_union hdisj measurableSet_Ioc
      integrable_gauss.integrableOn integrable_gauss.integrableOn]
    ring
  rw [hsplit]
  have hbound : ∫ u in Set.Ioc s t, gauss u ≤ t - s := by
    have h1 : ∫ u in Set.Ioc s t, gauss u ≤ ∫ _ in Set.Ioc s t, (1:ℝ) := by
      refine setIntegral_mono_on integrable_gauss.integrableOn ?_ measurableSet_Ioc
        fun u _ => gauss_le_one u
      exact integrableOn_const measure_Ioc_lt_top.ne
    have h2 : ∫ _ in Set.Ioc s t, (1:ℝ) = t - s := by
      rw [setIntegral_const, smul_eq_mul, mul_one,
        Real.volume_real_Ioc_of_le hst]
    rwa [h2] at h1
  calc (Real.sqrt (2 * Real.pi))⁻¹ * ∫ u in Set.Ioc s t, gauss u
      ≤ (Real.sqrt (2 * Real.pi))⁻¹ * (t - s) :=
        mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = (t - s) / Real.sqrt (2 * Real.pi) := by ring

lemma abs_Phi_sub_Phi_le (s t : ℝ) :
    |Phi s - Phi t| ≤ |s - t| / Real.sqrt (2 * Real.pi) := by
  rcases le_total s t with h | h
  · rw [abs_sub_comm, abs_of_nonneg (by linarith [Phi_mono h] : (0:ℝ) ≤ Phi t - Phi s),
      abs_sub_comm s t, abs_of_nonneg (by linarith : (0:ℝ) ≤ t - s)]
    exact Phi_sub_Phi_le h
  · rw [abs_of_nonneg (by linarith [Phi_mono h] : (0:ℝ) ≤ Phi s - Phi t),
      abs_of_nonneg (by linarith : (0:ℝ) ≤ s - t)]
    exact Phi_sub_Phi_le h

lemma Phi_continuous : Continuous Phi := by
  rw [Metric.continuous_iff]
  intro t ε hε
  refine ⟨ε * Real.sqrt (2 * Real.pi), by positivity, fun s hs => ?_⟩
  rw [Real.dist_eq] at hs ⊢
  calc |Phi s - Phi t| ≤ |s - t| / Real.sqrt (2 * Real.pi) := abs_Phi_sub_Phi_le s t
    _ < ε := (div_lt_iff₀ sqrt_two_pi_pos).mpr hs

/-- Reflection: `Φ(-t) = 1 - Φ(t)`. -/
lemma Phi_neg (t : ℝ) : Phi (-t) = 1 - Phi t := by
  have h1 : ∫ u in Set.Iic (-t), gauss u = ∫ u in Set.Ioi t, gauss u := by
    calc ∫ u in Set.Iic (-t), gauss u
        = ∫ u in Set.Iic (-t), gauss (-u) := by
          congr 1
          ext u
          rw [gauss_even]
      _ = ∫ u in Set.Ioi (-(-t)), gauss u := integral_comp_neg_Iic _ _
      _ = ∫ u in Set.Ioi t, gauss u := by rw [neg_neg]
  have h4 : (∫ u in Set.Iic t, gauss u) + ∫ u in Set.Ioi t, gauss u = ∫ u, gauss u := by
    have := MeasureTheory.integral_add_compl (s := Set.Iic t) (f := gauss)
      (μ := volume) measurableSet_Iic integrable_gauss
    rwa [Set.compl_Iic] at this
  unfold Phi
  rw [h1]
  have h5 : ∫ u in Set.Ioi t, gauss u = Real.sqrt (2 * Real.pi) - ∫ u in Set.Iic t, gauss u := by
    rw [← integral_gauss]
    linarith [h4]
  rw [h5, mul_sub, inv_mul_cancel₀ (ne_of_gt sqrt_two_pi_pos)]

/-- `Φ(t) → 1` as `t → ∞`. -/
lemma tendsto_Phi_atTop : Tendsto Phi atTop (𝓝 1) := by
  have hbdd : BddAbove (Set.range Phi) := ⟨1, by rintro x ⟨t, rfl⟩; exact Phi_le_one t⟩
  have hlim : Tendsto Phi atTop (𝓝 (⨆ t, Phi t)) := tendsto_atTop_ciSup Phi_mono hbdd
  -- identify the limit along the natural numbers
  have hseq : Tendsto (fun n : ℕ => Phi n) atTop (𝓝 (⨆ t, Phi t)) :=
    hlim.comp tendsto_natCast_atTop_atTop
  have hseq1 : Tendsto (fun n : ℕ => Phi n) atTop (𝓝 1) := by
    have hsm : ∀ n : ℕ, MeasurableSet (Set.Iic (n : ℝ)) := fun _ => measurableSet_Iic
    have hmono : Monotone fun n : ℕ => Set.Iic (n : ℝ) := by
      intro m n h
      exact Set.Iic_subset_Iic.mpr (by exact_mod_cast h)
    have hint : Tendsto (fun n : ℕ => ∫ u in Set.Iic (n : ℝ), gauss u) atTop
        (𝓝 (∫ u in ⋃ n : ℕ, Set.Iic (n : ℝ), gauss u)) :=
      MeasureTheory.tendsto_setIntegral_of_monotone hsm hmono
        integrable_gauss.integrableOn
    have hcov : ⋃ n : ℕ, Set.Iic (n : ℝ) = Set.univ := by
      ext u
      simp only [Set.mem_iUnion, Set.mem_Iic, Set.mem_univ, iff_true]
      exact exists_nat_ge u
    rw [hcov] at hint
    have hint1 : Tendsto (fun n : ℕ => ∫ u in Set.Iic (n : ℝ), gauss u) atTop
        (𝓝 (Real.sqrt (2 * Real.pi))) := by
      rwa [MeasureTheory.setIntegral_univ, integral_gauss] at hint
    have := hint1.const_mul (Real.sqrt (2 * Real.pi))⁻¹
    rw [inv_mul_cancel₀ (ne_of_gt sqrt_two_pi_pos)] at this
    exact this
  have hsup : (⨆ t, Phi t) = 1 := tendsto_nhds_unique hseq hseq1
  rwa [hsup] at hlim

/-- `Φ(t) → 0` as `t → -∞`. -/
lemma tendsto_Phi_atBot : Tendsto Phi atBot (𝓝 0) := by
  have h1 : Tendsto (fun t : ℝ => Phi (-t)) atBot (𝓝 1) :=
    tendsto_Phi_atTop.comp tendsto_neg_atBot_atTop
  have h2 : Tendsto (fun t : ℝ => 1 - Phi (-t)) atBot (𝓝 (1 - 1)) :=
    tendsto_const_nhds.sub h1
  have h3 : (fun t : ℝ => 1 - Phi (-t)) = Phi := by
    ext t
    have := Phi_neg (-t)
    rw [neg_neg] at this
    linarith
  rw [h3] at h2
  simpa using h2

end EKRev
