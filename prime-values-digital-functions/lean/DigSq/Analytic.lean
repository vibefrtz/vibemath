/-
DigSq/Analytic.lean

The one real-analysis inequality behind Theorem 1.1: at the peak
`k = μ_g log_b x` the Gaussian main term of the local limit theorem, of size
`π(x)/√(log x)`, eventually beats the error term `π(x)/(log x)^{3/4}`.

Stripped of the number theory, that is: `B √L < A L^{3/4}` for large `L`.

Nothing in this file is conditional: it imports no axioms.
-/
import DigSq.Imports

namespace DigSq

open Real

/-- For `A > 0` and `B ≥ 0`, one has `B √L < A L^{3/4}` for all large `L`.

This is the whole of the asymptotic content of Theorem 1.1(i): with
`A = (log b)^{3/4}` and `B = C √(2π σ_g²)` it says the main term of the local
limit theorem dominates its error term at the peak. -/
theorem sqrt_lt_rpow_three_quarters {A B : ℝ} (hA : 0 < A) (hB : 0 ≤ B) :
    ∃ L₀ : ℝ, 1 ≤ L₀ ∧ ∀ L : ℝ, L₀ ≤ L → B * Real.sqrt L < A * L ^ ((3 : ℝ) / 4) := by
  set M : ℝ := B / A + 1 with hMdef
  have hMpos : 0 < M := by
    have : 0 ≤ B / A := div_nonneg hB hA.le
    linarith
  refine ⟨max (M ^ (4 : ℕ)) 1, le_max_right _ _, ?_⟩
  intro L hL
  have hL1 : (1 : ℝ) ≤ L := le_trans (le_max_right _ _) hL
  have hL0 : (0 : ℝ) < L := lt_of_lt_of_le one_pos hL1
  have hLM : M ^ (4 : ℕ) ≤ L := le_trans (le_max_left _ _) hL
  -- `M ≤ L^{1/4}`
  have hM4 : (M ^ (4 : ℕ)) ^ ((1 : ℝ) / 4) = M := by
    rw [← Real.rpow_natCast M 4, ← Real.rpow_mul hMpos.le]
    norm_num
  have hstep1 : M ≤ L ^ ((1 : ℝ) / 4) := by
    rw [← hM4]
    exact Real.rpow_le_rpow (by positivity) hLM (by norm_num)
  -- `L^{3/4} = L^{1/4} · √L`
  have hsplit : L ^ ((3 : ℝ) / 4) = L ^ ((1 : ℝ) / 4) * Real.sqrt L := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hL0]
    norm_num
  have hsqrt : 0 < Real.sqrt L := Real.sqrt_pos.mpr hL0
  -- `B < A·M ≤ A·L^{1/4}`
  have hAM : B < A * M := by
    have : A * M = B + A := by
      rw [hMdef]; field_simp
    rw [this]; linarith
  have hAL : A * M ≤ A * L ^ ((1 : ℝ) / 4) := by
    exact mul_le_mul_of_nonneg_left hstep1 hA.le
  calc B * Real.sqrt L < (A * M) * Real.sqrt L := by
        exact mul_lt_mul_of_pos_right hAM hsqrt
    _ ≤ (A * L ^ ((1 : ℝ) / 4)) * Real.sqrt L := by
        exact mul_le_mul_of_nonneg_right hAL hsqrt.le
    _ = A * L ^ ((3 : ℝ) / 4) := by rw [hsplit]; ring

end DigSq
