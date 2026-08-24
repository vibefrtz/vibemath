/-
EKRev/Sums.lean

Analytic helper lemmas for the proof of Proposition 2.1 and the hypothesis
verifications:

* positivity of the sieve mean and variance;
* Cauchy–Schwarz `(∑ |W|^m)² ≤ #B ∑ W^{2m}` (fixed-order substitute for the
  paper's Lyapunov step in the qualitative part of Prop. 2.1);
* the bridge `a^{m/2} = (√a)^m` between the `rpow` normalization of the GS
  axiom and natural powers of `√(δL)`;
* `(log x)^c / x → 0` ("smaller than any fixed power of `L⁻¹`", proof of
  Prop. 2.1);
* the elementary tail bound `∑_{u<n≤N} n^{-m} ≤ u^{-(m-1)}` for `m ≥ 2`
  (proof of Lemma 4.5, "∑_{n>u} n^{-m} ≤ 2u^{1-m}");
* the geometric bound `∑_{m=2}^{M} (√ℓ)^{-m} ≤ 2` for `ℓ ≥ 2`
  (proof of Lemma 3.3(iii), contribution of the primes dividing `b³-b`).

Everything in this file is fully proved (no axioms).
-/
import Mathlib.Tactic
import EKRev.Defs

namespace EKRev

open Finset Filter Real Topology

/-! ### Positivity of the sieve quantities -/

lemma one_div_nat_le_one {ℓ : ℕ} : (1:ℝ) / ℓ ≤ 1 := by
  rcases Nat.eq_zero_or_pos ℓ with h | h
  · subst h; norm_num
  · have h1 : (1:ℝ) ≤ ℓ := by exact_mod_cast h
    rw [div_le_one (by linarith)]
    exact h1

lemma muR_nonneg (R : Finset ℕ) : 0 ≤ muR R := by
  unfold muR
  refine Finset.sum_nonneg fun ℓ _ => by positivity

lemma sigSq_nonneg (R : Finset ℕ) : 0 ≤ sigSq R := by
  unfold sigSq
  refine Finset.sum_nonneg fun ℓ _ => ?_
  have h1 : (0:ℝ) ≤ 1 / ℓ := by positivity
  have h2 : (1:ℝ) / ℓ ≤ 1 := one_div_nat_le_one
  nlinarith

lemma div_le_div_of_le' {a b c : ℝ} (hc : 0 < c) (h : a ≤ b) : a / c ≤ b / c :=
  (div_le_div_iff_of_pos_right hc).mpr h

/-! ### Cauchy–Schwarz for empirical moments -/

lemma abs_pow_two_mul (x : ℝ) (m : ℕ) : |x| ^ (2 * m) = x ^ (2 * m) := by
  rw [pow_mul, pow_mul, sq_abs]

lemma inv_le_inv_of_le' {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) : b⁻¹ ≤ a⁻¹ := by
  rw [inv_eq_one_div, inv_eq_one_div]
  exact one_div_le_one_div_of_le ha hab

lemma pow_le_pow_left' {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (n : ℕ) :
    a ^ n ≤ b ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      calc a ^ (n + 1) = a ^ n * a := by rw [pow_succ]
        _ ≤ b ^ n * b := mul_le_mul ih hab ha (pow_nonneg (le_trans ha hab) n)
        _ = b ^ (n + 1) := by rw [pow_succ]

/-- Cauchy–Schwarz: `(∑ |W|^m)² ≤ #B · ∑ W^{2m}`. -/
lemma sq_sum_abs_pow_le (B : Finset ℕ) (W : ℕ → ℝ) (m : ℕ) :
    (∑ n ∈ B, |W n| ^ m) ^ 2 ≤ (B.card : ℝ) * ∑ n ∈ B, W n ^ (2 * m) := by
  have h2 := Finset.sum_mul_sq_le_sq_mul_sq B (fun _ => (1 : ℝ)) (fun n => |W n| ^ m)
  simp only [one_mul, one_pow] at h2
  calc (∑ n ∈ B, |W n| ^ m) ^ 2
      ≤ (∑ _n ∈ B, (1 : ℝ)) * ∑ n ∈ B, (|W n| ^ m) ^ 2 := h2
    _ = (B.card : ℝ) * ∑ n ∈ B, (|W n| ^ m) ^ 2 := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    _ = (B.card : ℝ) * ∑ n ∈ B, W n ^ (2 * m) := by
        congr 1
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [← pow_mul, mul_comm m 2, abs_pow_two_mul]

/-! ### rpow / sqrt bridge -/

lemma rpow_natCast_div_two {a : ℝ} (ha : 0 ≤ a) (m : ℕ) :
    a ^ ((m : ℝ) / 2) = Real.sqrt a ^ m := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast (a ^ ((1:ℝ)/2)) m, ← Real.rpow_mul ha]
  congr 1
  ring

/-! ### `(log x)^c / x → 0` -/

lemma tendsto_pow_log_div_atTop (c : ℕ) :
    Tendsto (fun x : ℝ => (Real.log x) ^ c / x) atTop (𝓝 0) := by
  have h1 : Tendsto (fun u : ℝ => u ^ c * Real.exp (-u)) atTop (𝓝 0) :=
    tendsto_pow_mul_exp_neg_atTop_nhds_zero c
  have h3 : Tendsto (fun x : ℝ => (Real.log x) ^ c * Real.exp (-(Real.log x)))
      atTop (𝓝 0) := h1.comp Real.tendsto_log_atTop
  refine h3.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  rw [Real.exp_neg, Real.exp_log hx, div_eq_mul_inv]

/-! ### Elementary tail bounds -/

/-- Telescoping bound: `∑_{u<n≤N} n^{-2} ≤ u^{-1} - N^{-1}` for `1 ≤ u ≤ N`. -/
lemma sum_Ioc_inv_sq_le {u N : ℕ} (hu : 1 ≤ u) (hN : u ≤ N) :
    ∑ n ∈ Finset.Ioc u N, ((n : ℝ))⁻¹ ^ 2 ≤ (u : ℝ)⁻¹ - (N : ℝ)⁻¹ := by
  induction N, hN using Nat.le_induction with
  | base => simp
  | succ N hN ih =>
      rw [Finset.sum_Ioc_succ_top (by omega)]
      have hN0 : (0:ℝ) < (N:ℝ) := by exact_mod_cast (by omega : 0 < N)
      have hN1 : (0:ℝ) < (N:ℝ) + 1 := by linarith
      have hstep : (((N:ℝ) + 1))⁻¹ ^ 2 ≤ (N:ℝ)⁻¹ - ((N:ℝ) + 1)⁻¹ := by
        have e1 : (N:ℝ)⁻¹ - ((N:ℝ) + 1)⁻¹ = ((N:ℝ) * ((N:ℝ) + 1))⁻¹ := by
          rw [inv_eq_one_div, inv_eq_one_div, inv_eq_one_div]
          field_simp
          ring
        rw [e1, inv_pow]
        refine inv_le_inv_of_le' (by positivity) ?_
        nlinarith
      push_cast
      push_cast at ih
      linarith

/-- Tail bound for higher powers: `∑_{u<n≤N} n^{-m} ≤ u^{-(m-1)}` for `m ≥ 2`,
`u ≥ 1` (the paper's `∑_{n>u} n^{-m} ≤ 2u^{1-m}`, proof of Lemma 4.5). -/
lemma sum_Ioc_inv_pow_le {u m : ℕ} (hu : 1 ≤ u) (hm : 2 ≤ m) (N : ℕ) :
    ∑ n ∈ Finset.Ioc u N, ((n : ℝ))⁻¹ ^ m ≤ ((u : ℝ)⁻¹) ^ (m - 1) := by
  have hu0 : (0:ℝ) < (u:ℝ) := by exact_mod_cast hu
  rcases Nat.lt_or_ge N u with h | h
  · rw [Finset.Ioc_eq_empty (by omega)]
    simp only [Finset.sum_empty]
    positivity
  · have hterm : ∀ n ∈ Finset.Ioc u N, ((n : ℝ))⁻¹ ^ m
        ≤ ((u : ℝ)⁻¹) ^ (m - 2) * ((n : ℝ))⁻¹ ^ 2 := by
      intro n hn
      rw [Finset.mem_Ioc] at hn
      have hn0 : (0:ℝ) < (n:ℝ) := by
        exact_mod_cast (by omega : 0 < n)
      have hun : (u:ℝ) ≤ (n:ℝ) := by exact_mod_cast (by omega : u ≤ n)
      have hinv : ((n:ℝ))⁻¹ ≤ ((u:ℝ))⁻¹ := by
        exact inv_le_inv_of_le' hu0 hun
      have hsplit : m = (m - 2) + 2 := by omega
      calc ((n : ℝ))⁻¹ ^ m = ((n : ℝ))⁻¹ ^ (m - 2) * ((n : ℝ))⁻¹ ^ 2 := by
            rw [← pow_add, ← hsplit]
        _ ≤ ((u : ℝ)⁻¹) ^ (m - 2) * ((n : ℝ))⁻¹ ^ 2 := by
            refine mul_le_mul_of_nonneg_right ?_ (by positivity)
            exact pow_le_pow_left' (by positivity) hinv _
    calc ∑ n ∈ Finset.Ioc u N, ((n : ℝ))⁻¹ ^ m
        ≤ ∑ n ∈ Finset.Ioc u N, ((u : ℝ)⁻¹) ^ (m - 2) * ((n : ℝ))⁻¹ ^ 2 :=
          Finset.sum_le_sum hterm
      _ = ((u : ℝ)⁻¹) ^ (m - 2) * ∑ n ∈ Finset.Ioc u N, ((n : ℝ))⁻¹ ^ 2 := by
          rw [Finset.mul_sum]
      _ ≤ ((u : ℝ)⁻¹) ^ (m - 2) * ((u : ℝ))⁻¹ := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          calc ∑ n ∈ Finset.Ioc u N, ((n : ℝ))⁻¹ ^ 2
              ≤ (u : ℝ)⁻¹ - (N : ℝ)⁻¹ := sum_Ioc_inv_sq_le hu h
            _ ≤ (u : ℝ)⁻¹ := by
                have : (0:ℝ) ≤ (N:ℝ)⁻¹ := by positivity
                linarith
      _ = ((u : ℝ)⁻¹) ^ (m - 1) := by
          rw [← pow_succ]
          congr 1
          omega

/-- Geometric bound `∑_{m=2}^{M} q^m ≤ 2 - 4 q^{M+1}` for `q = 1/√2`, `M ≥ 1`. -/
private lemma sum_Icc_q_pow_le {M : ℕ} (hM : 1 ≤ M) :
    ∑ m ∈ Finset.Icc 2 M, ((Real.sqrt 2)⁻¹) ^ m
      ≤ 2 - 4 * ((Real.sqrt 2)⁻¹) ^ (M + 1) := by
  set q : ℝ := (Real.sqrt 2)⁻¹ with hq
  have hq0 : 0 < q := by
    rw [hq]
    positivity
  have hqsq : q ^ 2 = 1 / 2 := by
    rw [hq, inv_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
    norm_num
  have hq34 : q ≤ 3 / 4 := by
    rw [hq]
    rw [inv_le_iff_one_le_mul₀ (by positivity)]
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2),
      Real.sqrt_nonneg (2:ℝ), sq_nonneg (Real.sqrt 2 - 4/3)]
  induction M, hM using Nat.le_induction with
  | base =>
      rw [Finset.Icc_eq_empty (by omega)]
      simp only [Finset.sum_empty]
      have : q ^ (1 + 1) = 1 / 2 := by rw [← hqsq]
      rw [this]
      norm_num
  | succ M hM ih =>
      rw [Finset.sum_Icc_succ_top (by omega)]
      have h1 : q ^ (M + 1 + 1) = q * q ^ (M + 1) := by rw [pow_succ]; ring
      have h2 : (0:ℝ) < q ^ (M + 1) := by positivity
      calc (∑ m ∈ Finset.Icc 2 M, q ^ m) + q ^ (M + 1)
          ≤ (2 - 4 * q ^ (M + 1)) + q ^ (M + 1) := by linarith
        _ = 2 - 3 * q ^ (M + 1) := by ring
        _ ≤ 2 - 4 * q ^ (M + 1 + 1) := by
            rw [h1]
            nlinarith [h2, hq34, hq0]

/-- For a prime power base `ℓ ≥ 2`:
`∑_{m=2}^{M} (√ℓ)^{-m} ≤ 2` (proof of Lemma 3.3(iii), `ℓ ∣ b³-b` part). -/
lemma sum_Icc_inv_sqrt_pow_le {ℓ : ℕ} (hℓ : 2 ≤ ℓ) (M : ℕ) :
    ∑ m ∈ Finset.Icc 2 M, ((Real.sqrt ℓ)⁻¹) ^ m ≤ 2 := by
  rcases Nat.lt_or_ge M 2 with h | h
  · rw [Finset.Icc_eq_empty (by omega)]
    simp only [Finset.sum_empty]
    norm_num
  · have hterm : ∀ m ∈ Finset.Icc 2 M,
        ((Real.sqrt ℓ)⁻¹) ^ m ≤ ((Real.sqrt 2)⁻¹) ^ m := by
      intro m _
      have h2 : Real.sqrt 2 ≤ Real.sqrt ℓ := by
        refine Real.sqrt_le_sqrt ?_
        exact_mod_cast hℓ
      have h3 : (0:ℝ) < Real.sqrt 2 := by positivity
      refine pow_le_pow_left' (by positivity) ?_ m
      exact inv_le_inv_of_le' h3 h2
    calc ∑ m ∈ Finset.Icc 2 M, ((Real.sqrt ℓ)⁻¹) ^ m
        ≤ ∑ m ∈ Finset.Icc 2 M, ((Real.sqrt 2)⁻¹) ^ m := Finset.sum_le_sum hterm
      _ ≤ 2 - 4 * ((Real.sqrt 2)⁻¹) ^ (M + 1) := sum_Icc_q_pow_le (by omega)
      _ ≤ 2 := by
          have : (0:ℝ) ≤ ((Real.sqrt 2)⁻¹) ^ (M + 1) := by positivity
          linarith

end EKRev
