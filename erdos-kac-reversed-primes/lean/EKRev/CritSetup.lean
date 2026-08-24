/-
EKRev/CritSetup.lean

The hypotheses of Proposition 2.1 as a structure (`CritHyps`), the truncation
`y = b^{ξλ/K}` and the set `𝒬` of eq. (2.2), and the three parts of
Lemma 2.3 in the quantitative, fixed-order form used here:

* (i)  `μ = δL + O(1)` and `σ² = δL + O(1)`  (constant depending on
       `ξ, K, ℰ, S` — for fixed moment order this is all that is needed;
       the paper's `O(log 2k)` refines this only for the uniform range);
* (ii) `|ω_S(n) - ω_𝒬(n)| ≤ #ℰ + 2K/ξ` eventually;
* (iii) `Π_j(𝒬) ⊆ {d ≤ b^{ξλ} : d squarefree, d ∈ 𝒟(ℰ)}` for `j ≤ K`,
       hence the remainder sum over `Π_j(𝒬)` obeys hypothesis (ii) of
       Proposition 2.1.

Everything in this file is fully proved (no axioms beyond the imported ones).
-/
import Mathlib.Tactic
import EKRev.Cited
import Mathlib.Analysis.Complex.ExponentialBounds
import EKRev.Sums

namespace EKRev

open Finset Filter Real Topology

/-! ### The hypotheses of Proposition 2.1 -/

/-- Hypotheses (i) and (ii) of Proposition 2.1, for a family `B_λ`,
an exceptional set `ℰ`, and a level exponent `ξ`. -/
structure CritHyps (b : ℕ) (BB : ℕ → Finset ℕ) (E : Finset ℕ) (ξ : ℝ) : Prop where
  b_ge : 2 ≤ b
  xi_pos : 0 < ξ
  xi_le_one : ξ ≤ 1
  nonempty : ∀ᶠ lam in atTop, (BB lam).Nonempty
  mem_pos : ∀ lam, ∀ n ∈ BB lam, 0 < n
  mem_le : ∀ lam, ∀ n ∈ BB lam, n ≤ b ^ lam
  remainder : ∀ A : ℝ, 0 < A → ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ lam : ℕ in atTop,
    ∑ d ∈ (Finset.Icc 1 (b ^ lam)).filter
        (fun d => Squarefree d ∧ noFactorIn E d ∧ (d : ℝ) ≤ (b : ℝ) ^ (ξ * (lam : ℝ))),
      |rem (BB lam) d|
      ≤ C * ((BB lam).card : ℝ) / (lam : ℝ) ^ A

/-- Hypothesis (iii) of Proposition 2.1. -/
def OmegaHyp (BB : ℕ → Finset ℕ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ lam in atTop,
    ∑ n ∈ BB lam, ((bigOmega n : ℝ) - (smallOmega n : ℝ)) ≤ C * ((BB lam).card : ℝ)

/-! ### The truncation -/

/-- The truncation point `y = b^{ξλ/K}` (eq. (2.2); the proof at fixed order
`k` uses `K = 2k+1`). -/
noncomputable def ytr (b : ℕ) (ξ : ℝ) (K lam : ℕ) : ℝ :=
  (b : ℝ) ^ (ξ * (lam : ℝ) / (K : ℝ))

section Trunc

variable {b : ℕ} {ξ : ℝ} {K : ℕ}

lemma ytr_pos (hb : 2 ≤ b) : 0 < ytr b ξ K lam :=
  Real.rpow_pos_of_pos (by exact_mod_cast (by omega : 0 < b)) _

lemma ytr_nonneg (hb : 2 ≤ b) : 0 ≤ ytr b ξ K lam := (ytr_pos hb).le

lemma log_ytr (hb : 2 ≤ b) :
    Real.log (ytr b ξ K lam) = ξ * (lam : ℝ) / (K : ℝ) * Real.log b := by
  unfold ytr
  rw [Real.log_rpow (by exact_mod_cast (by omega : 0 < b))]

lemma one_le_ytr (hb : 2 ≤ b) (hξ : 0 < ξ) (hK : 1 ≤ K) : 1 ≤ ytr b ξ K lam := by
  unfold ytr
  have hx : 0 ≤ ξ * (lam : ℝ) / (K : ℝ) := by positivity
  have hb1 : (1:ℝ) ≤ (b:ℝ) := by exact_mod_cast (by omega : 1 ≤ b)
  calc (1:ℝ) = (b:ℝ) ^ (0:ℝ) := (Real.rpow_zero _).symm
    _ ≤ (b:ℝ) ^ (ξ * (lam : ℝ) / (K : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le hb1 hx

/-- `y → ∞` as `λ → ∞`. -/
lemma tendsto_ytr_atTop (hb : 2 ≤ b) (hξ : 0 < ξ) (hK : 1 ≤ K) :
    Tendsto (fun lam : ℕ => ytr b ξ K lam) atTop atTop := by
  have hb1 : (1:ℝ) < (b:ℝ) := by exact_mod_cast (by omega : 1 < b)
  have hlogb : 0 < Real.log b := Real.log_pos hb1
  have hc : 0 < ξ * Real.log b / (K : ℝ) := by
    have : (0:ℝ) < (K:ℝ) := by exact_mod_cast hK
    positivity
  have heq : ∀ lam : ℕ, ytr b ξ K lam
      = Real.exp ((ξ * Real.log b / (K : ℝ)) * (lam : ℝ)) := by
    intro lam
    unfold ytr
    rw [Real.rpow_def_of_pos (by linarith : (0:ℝ) < (b:ℝ))]
    congr 1
    ring
  have h1 : Tendsto (fun lam : ℕ => (ξ * Real.log b / (K : ℝ)) * (lam : ℝ))
      atTop atTop :=
    Tendsto.const_mul_atTop hc tendsto_natCast_atTop_atTop
  have h2 := Real.tendsto_exp_atTop.comp h1
  refine h2.congr fun lam => ?_
  rw [heq lam]
  rfl

end Trunc

/-! ### `L → ∞` -/

lemma tendsto_LL_atTop (hb : 2 ≤ b) :
    Tendsto (fun lam : ℕ => LL b lam) atTop atTop := by
  have hb1 : (1:ℝ) < (b:ℝ) := by exact_mod_cast (by omega : 1 < b)
  have hlogb : 0 < Real.log b := Real.log_pos hb1
  have h1 : Tendsto (fun lam : ℕ => (lam : ℝ) * Real.log b) atTop atTop :=
    Tendsto.atTop_mul_const hlogb tendsto_natCast_atTop_atTop
  have h2 := Real.tendsto_log_atTop.comp h1
  have h3 : Tendsto (fun lam : ℕ => Real.log ((lam : ℝ) * Real.log b)) atTop atTop := h2
  refine h3.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with lam hlam
  rw [← LL_eq hb hlam]

/-! ### The set `𝒬` at the truncation -/

section QsetFacts

variable {b : ℕ} {ξ δ : ℝ} {K : ℕ} {S : Set ℕ} {E : Finset ℕ}

/-- The truncated prime set of eq. (2.2). -/
noncomputable def Qtr (b : ℕ) (ξ : ℝ) (K : ℕ) (S : Set ℕ) (E : Finset ℕ)
    (lam : ℕ) : Finset ℕ :=
  Qset S E (ytr b ξ K lam)

lemma Qtr_prime (hb : 2 ≤ b) : ∀ ℓ ∈ Qtr b ξ K S E lam, ℓ.Prime := by
  intro ℓ hℓ
  exact ((mem_Qset_iff (ytr_nonneg hb)).mp hℓ).1

lemma Qtr_two_le (hb : 2 ≤ b) : ∀ ℓ ∈ Qtr b ξ K S E lam, 2 ≤ ℓ := fun ℓ hℓ =>
  (Qtr_prime hb ℓ hℓ).two_le

end QsetFacts

/-! ### Lemma 2.3(i): `μ = δL + O(1)`, `σ² = δL + O(1)` -/

section SetupLemma

variable {b : ℕ} {ξ δ : ℝ} {K : ℕ} {S : Set ℕ} {E : Finset ℕ} {BB : ℕ → Finset ℕ}

open Classical in
/-- `𝒬` and the regularity sum differ by at most `#ℰ`. -/
lemma muR_Qset_vs_primeRecipSum (S : Set ℕ) (E : Finset ℕ) {y : ℝ} (hy : 0 ≤ y) :
    muR (Qset S E y) ≤ primeRecipSum S ⌊y⌋₊ ∧
    primeRecipSum S ⌊y⌋₊ ≤ muR (Qset S E y) + (E.card : ℝ) := by
  unfold muR primeRecipSum
  have hsub : Qset S E y ⊆ (Finset.range (⌊y⌋₊ + 1)).filter (fun ℓ => ℓ.Prime ∧ ℓ ∈ S) := by
    intro ℓ hℓ
    obtain ⟨hp, hS, hle, hE⟩ := (mem_Qset_iff hy).mp hℓ
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨by have := Nat.le_floor hle; omega, hp, hS⟩
  constructor
  · exact Finset.sum_le_sum_of_subset_of_nonneg hsub fun ℓ _ _ => by positivity
  · rw [← Finset.sum_sdiff hsub]
    have hbound : ∑ ℓ ∈ ((Finset.range (⌊y⌋₊ + 1)).filter (fun ℓ => ℓ.Prime ∧ ℓ ∈ S))
        \ Qset S E y, (1 : ℝ) / ℓ ≤ (E.card : ℝ) := by
      have hsubE : ((Finset.range (⌊y⌋₊ + 1)).filter (fun ℓ => ℓ.Prime ∧ ℓ ∈ S))
          \ Qset S E y ⊆ E := by
        intro ℓ hℓ
        rw [Finset.mem_sdiff] at hℓ
        obtain ⟨hmem, hnot⟩ := hℓ
        rw [Finset.mem_filter, Finset.mem_range] at hmem
        obtain ⟨hrange, hp, hS⟩ := hmem
        by_contra hE
        refine hnot ((mem_Qset_iff hy).mpr ⟨hp, hS, ?_, hE⟩)
        have h1 : ℓ ≤ ⌊y⌋₊ := by omega
        calc (ℓ : ℝ) ≤ (⌊y⌋₊ : ℝ) := by exact_mod_cast h1
          _ ≤ y := Nat.floor_le hy
      calc ∑ ℓ ∈ _ \ Qset S E y, (1 : ℝ) / ℓ
          ≤ ∑ ℓ ∈ _ \ Qset S E y, (1 : ℝ) := by
            refine Finset.sum_le_sum fun ℓ _ => one_div_nat_le_one
        _ = ((_ \ Qset S E y).card : ℝ) := by
            rw [Finset.sum_const, nsmul_eq_mul, mul_one]
        _ ≤ (E.card : ℝ) := by exact_mod_cast Finset.card_le_card hsubE
    linarith

/-- Comparison of `log log ⌊y⌋` and `log log y` for `y ≥ 3`. -/
lemma loglog_floor_close {y : ℝ} (hy : 3 ≤ y) :
    Real.log (Real.log (⌊y⌋₊ : ℝ)) ≤ Real.log (Real.log y) ∧
    Real.log (Real.log y) ≤ Real.log (Real.log (⌊y⌋₊ : ℝ)) + 1 := by
  have hy0 : (0:ℝ) ≤ y := by linarith
  have hfl3 : 3 ≤ ⌊y⌋₊ := Nat.le_floor (by exact_mod_cast hy)
  have hfl3' : (3:ℝ) ≤ (⌊y⌋₊ : ℝ) := by exact_mod_cast hfl3
  have hfle : (⌊y⌋₊ : ℝ) ≤ y := Nat.floor_le hy0
  have hlog3 : (1:ℝ) < Real.log 3 := by
    rw [show (1:ℝ) = Real.log (Real.exp 1) from (Real.log_exp 1).symm]
    refine Real.log_lt_log (Real.exp_pos 1) ?_
    have := Real.exp_one_lt_three
    linarith
  have hlogfl : 1 < Real.log (⌊y⌋₊ : ℝ) := by
    calc (1:ℝ) < Real.log 3 := hlog3
      _ ≤ Real.log (⌊y⌋₊ : ℝ) := Real.log_le_log (by norm_num) hfl3'
  have hlogy : 1 < Real.log y := by
    calc (1:ℝ) < Real.log (⌊y⌋₊ : ℝ) := hlogfl
      _ ≤ Real.log y := Real.log_le_log (by linarith) hfle
  constructor
  · refine Real.log_le_log (by linarith) ?_
    exact Real.log_le_log (by linarith) hfle
  · have hy2 : y ≤ 2 * (⌊y⌋₊ : ℝ) := by
      have h1 : y < (⌊y⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one y
      linarith
    have hlog2 : Real.log 2 ≤ 1 := by
      rw [show (1:ℝ) = Real.log (Real.exp 1) from (Real.log_exp 1).symm]
      refine Real.log_le_log (by norm_num) ?_
      have := Real.exp_one_gt_two
      linarith
    have h3 : Real.log y ≤ Real.log 2 + Real.log (⌊y⌋₊ : ℝ) := by
      calc Real.log y ≤ Real.log (2 * (⌊y⌋₊ : ℝ)) :=
            Real.log_le_log (by linarith) hy2
        _ = Real.log 2 + Real.log (⌊y⌋₊ : ℝ) :=
            Real.log_mul (by norm_num) (by linarith)
    have h4 : Real.log y ≤ 2 * Real.log (⌊y⌋₊ : ℝ) := by linarith
    calc Real.log (Real.log y) ≤ Real.log (2 * Real.log (⌊y⌋₊ : ℝ)) :=
          Real.log_le_log (by linarith) h4
      _ = Real.log 2 + Real.log (Real.log (⌊y⌋₊ : ℝ)) :=
          Real.log_mul (by norm_num) (by linarith)
      _ ≤ Real.log (Real.log (⌊y⌋₊ : ℝ)) + 1 := by linarith

/-- `log log y = L + log(ξ/K)` for the truncation `y = b^{ξλ/K}` (eq. (2.2)
context: "log log y = L + log ξ - log(k+1)"). -/
lemma loglog_ytr (hb : 2 ≤ b) (hξ : 0 < ξ) (hK : 1 ≤ K) (hlam : 1 ≤ lam) :
    Real.log (Real.log (ytr b ξ K lam)) = LL b lam + Real.log (ξ / (K : ℝ)) := by
  have hb1 : (1:ℝ) < (b:ℝ) := by exact_mod_cast (by omega : 1 < b)
  have hlogb : 0 < Real.log b := Real.log_pos hb1
  have hlam0 : (0:ℝ) < (lam : ℝ) := by exact_mod_cast hlam
  have hK0 : (0:ℝ) < (K:ℝ) := by exact_mod_cast hK
  rw [log_ytr hb, LL_eq hb hlam]
  have e1 : ξ * (lam:ℝ) / (K:ℝ) * Real.log b
      = (ξ / (K:ℝ)) * ((lam:ℝ) * Real.log b) := by ring
  rw [e1, Real.log_mul (by positivity) (by positivity)]
  ring

/-- Lemma 2.3(i), fixed-order form. -/
lemma setup_mu_sigma (hb : 2 ≤ b) (hξ : 0 < ξ) (hK : 1 ≤ K)
    (hS : IsRegular S δ) :
    ∃ c1 : ℝ, 0 ≤ c1 ∧ ∀ᶠ lam : ℕ in atTop,
      |muR (Qtr b ξ K S E lam) - δ * LL b lam| ≤ c1 ∧
      |sigSq (Qtr b ξ K S E lam) - δ * LL b lam| ≤ c1 := by
  obtain ⟨CS, hCS0, hCS⟩ := hS.bound
  refine ⟨(E.card : ℝ) + CS + 1 + |Real.log (ξ / (K : ℝ))| + 1, by positivity, ?_⟩
  have hev1 : ∀ᶠ lam : ℕ in atTop, (3:ℝ) ≤ ytr b ξ K lam :=
    (tendsto_ytr_atTop hb hξ hK).eventually_ge_atTop 3
  filter_upwards [hev1, eventually_ge_atTop 1] with lam hy3 hlam
  set y := ytr b ξ K lam with hydef
  have hy0 : (0:ℝ) ≤ y := by linarith
  have hfl3 : 3 ≤ ⌊y⌋₊ := Nat.le_floor (by exact_mod_cast hy3)
  -- the four comparison steps
  obtain ⟨hcmp1, hcmp2⟩ := muR_Qset_vs_primeRecipSum S E hy0
  have hreg := hCS ⌊y⌋₊ hfl3
  obtain ⟨hfl1, hfl2⟩ := loglog_floor_close hy3
  have hexact := loglog_ytr hb hξ hK hlam
  rw [abs_le] at hreg
  obtain ⟨hreg1, hreg2⟩ := hreg
  -- shorthands
  set P := primeRecipSum S ⌊y⌋₊
  set G := Real.log (Real.log (⌊y⌋₊ : ℝ))
  set Y := Real.log (Real.log y)
  have hδ0 := hS.delta_pos
  have hδ1 := hS.delta_le_one
  have habs : δ * Real.log (ξ / (K:ℝ)) ≤ |Real.log (ξ / (K:ℝ))| ∧
      -|Real.log (ξ / (K:ℝ))| ≤ δ * Real.log (ξ / (K:ℝ)) := by
    constructor
    · calc δ * Real.log (ξ / (K:ℝ)) ≤ |δ * Real.log (ξ / (K:ℝ))| := le_abs_self _
        _ = δ * |Real.log (ξ / (K:ℝ))| := by
            rw [abs_mul, abs_of_pos hδ0]
        _ ≤ 1 * |Real.log (ξ / (K:ℝ))| := by
            refine mul_le_mul_of_nonneg_right hδ1 (abs_nonneg _)
        _ = |Real.log (ξ / (K:ℝ))| := by ring
    · calc -|Real.log (ξ / (K:ℝ))| ≤ -(δ * |Real.log (ξ / (K:ℝ))|) := by
            have : δ * |Real.log (ξ / (K:ℝ))| ≤ |Real.log (ξ / (K:ℝ))| := by
              calc δ * |Real.log (ξ / (K:ℝ))| ≤ 1 * |Real.log (ξ / (K:ℝ))| :=
                    mul_le_mul_of_nonneg_right hδ1 (abs_nonneg _)
                _ = |Real.log (ξ / (K:ℝ))| := by ring
            linarith
        _ ≤ δ * Real.log (ξ / (K:ℝ)) := by
            have h1 : -|Real.log (ξ / (K:ℝ))| ≤ Real.log (ξ / (K:ℝ)) := neg_abs_le _
            nlinarith [hδ0.le]
  -- Y = δ-free identity: Y = LL + log(ξ/K)
  -- δ G bounds: δ(Y-1) ≤ δ G ≤ δ Y
  have hG1 : δ * G ≤ δ * Y := by
    refine mul_le_mul_of_nonneg_left hfl1 hδ0.le
  have hG2 : δ * (Y - 1) ≤ δ * G := by
    refine mul_le_mul_of_nonneg_left (by linarith) hδ0.le
  have hYval : δ * Y = δ * LL b lam + δ * Real.log (ξ / (K:ℝ)) := by
    rw [hexact]
    ring
  have hmu : |muR (Qtr b ξ K S E lam) - δ * LL b lam|
      ≤ (E.card : ℝ) + CS + 1 + |Real.log (ξ / (K:ℝ))| := by
    rw [abs_le]
    constructor
    · -- lower: muR ≥ P - #E ≥ δG - CS - #E ≥ δ(Y-1) - CS - #E
      have h1 : muR (Qtr b ξ K S E lam) ≥ P - (E.card : ℝ) := by
        unfold Qtr
        linarith [hcmp2]
      nlinarith [habs.2, hδ1, hδ0.le]
    · have h1 : muR (Qtr b ξ K S E lam) ≤ P := by
        unfold Qtr
        exact hcmp1
      nlinarith [habs.1, hδ1, hδ0.le]
  refine ⟨by linarith [hmu, abs_nonneg (muR (Qtr b ξ K S E lam) - δ * LL b lam)], ?_⟩
  -- σ²: |σ² - μ| ≤ 1
  have hp2 : ∀ ℓ ∈ Qtr b ξ K S E lam, 2 ≤ ℓ := Qtr_two_le hb
  have hs1 : sigSq (Qtr b ξ K S E lam) ≤ muR (Qtr b ξ K S E lam) := sigSq_le_muR _
  have hs2 : muR (Qtr b ξ K S E lam) - sigSq (Qtr b ξ K S E lam) ≤ 1 :=
    muR_sub_sigSq_le_one hp2
  rw [abs_le] at hmu ⊢
  constructor
  · linarith [hmu.1]
  · linarith [hmu.2]

/-! ### Lemma 2.3(ii): `|ω_S - ω_𝒬| ≤ #ℰ + 2K/ξ` eventually -/

/-- The number of prime factors exceeding the truncation is `≤ 2K/ξ`,
eventually in `λ`, uniformly over `n ≤ b^λ` (Lemma 2.3(ii)). -/
lemma setup_large_primes (hb : 2 ≤ b) (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) (hK : 1 ≤ K) :
    ∀ᶠ lam : ℕ in atTop, ∀ n : ℕ, 1 ≤ n → n ≤ b ^ lam →
      ((n.primeFactors.filter fun ℓ : ℕ => ytr b ξ K lam < (ℓ : ℝ)).card : ℝ)
        ≤ 2 * (K : ℝ) / ξ := by
  have hb1 : (1:ℝ) < (b:ℝ) := by exact_mod_cast (by omega : 1 < b)
  have hlogb : 0 < Real.log b := Real.log_pos hb1
  have hK0 : (0:ℝ) < (K:ℝ) := by exact_mod_cast hK
  -- eventually: y ≥ 4 and log ⌊y⌋ ≥ (ξ λ log b)/(2K), λ ≥ 1
  have hev1 : ∀ᶠ lam : ℕ in atTop, (4:ℝ) ≤ ytr b ξ K lam :=
    (tendsto_ytr_atTop hb hξ hK).eventually_ge_atTop 4
  have hev2 : ∀ᶠ lam : ℕ in atTop, (2:ℝ) ≤ Real.log (ytr b ξ K lam) :=
    (Real.tendsto_log_atTop.comp (tendsto_ytr_atTop hb hξ hK)).eventually_ge_atTop 2
  filter_upwards [hev1, hev2, eventually_ge_atTop 1] with lam hy4 hlogy2 hlam
  intro n hn1 hnb
  set y := ytr b ξ K lam with hydef
  have hy0 : (0:ℝ) ≤ y := by linarith
  set u := ⌊y⌋₊ with hu
  have hu2 : 2 ≤ u := Nat.le_floor (by exact_mod_cast (by linarith : (2:ℝ) ≤ y))
  -- the real filter equals the ℕ filter at u
  have hfeq : n.primeFactors.filter (fun ℓ : ℕ => y < (ℓ : ℝ))
      = n.primeFactors.filter (fun ℓ : ℕ => u < ℓ) := by
    refine Finset.filter_congr fun ℓ _ => ?_
    constructor
    · intro h
      exact (Nat.floor_lt hy0).mpr h
    · intro h
      exact (Nat.floor_lt hy0).mp h
  rw [hfeq]
  set m := (n.primeFactors.filter fun ℓ : ℕ => u < ℓ).card with hm
  have hpow : u ^ m ≤ n := pow_card_large_primeFactors_le hn1 u
  have hpowb : u ^ m ≤ b ^ lam := le_trans hpow hnb
  -- take real logarithms
  have hu0 : (0:ℝ) < (u:ℝ) := by exact_mod_cast (by omega : 0 < u)
  have hlogcast : (m : ℝ) * Real.log u ≤ (lam : ℝ) * Real.log b := by
    have h1 : ((u ^ m : ℕ) : ℝ) ≤ ((b ^ lam : ℕ) : ℝ) := by exact_mod_cast hpowb
    have h2 : Real.log ((u ^ m : ℕ) : ℝ) ≤ Real.log ((b ^ lam : ℕ) : ℝ) := by
      refine Real.log_le_log (by positivity) h1
    rw [Nat.cast_pow, Nat.cast_pow, Real.log_pow, Real.log_pow] at h2
    exact_mod_cast h2
  -- log u ≥ (log y) - 1 ≥ (1/2) log y = ξ λ log b / (2K)
  have hufl : y - 1 ≤ (u:ℝ) := by
    have h := Nat.lt_floor_add_one y
    have h2 : (⌊y⌋₊ : ℝ) = (u : ℝ) := by rw [hu]
    linarith [h, h2.le, h2.ge]
  have hlogu : Real.log (u:ℝ) ≥ Real.log y - 1 := by
    have hy1 : y - 1 ≥ y / 2 := by linarith
    have h1 : Real.log (u:ℝ) ≥ Real.log (y / 2) := by
      refine Real.log_le_log (by linarith) (by linarith)
    have h2 : Real.log (y / 2) = Real.log y - Real.log 2 := by
      rw [Real.log_div (by linarith) (by norm_num)]
    have hlog2 : Real.log 2 ≤ 1 := by
      rw [show (1:ℝ) = Real.log (Real.exp 1) from (Real.log_exp 1).symm]
      refine Real.log_le_log (by norm_num) ?_
      have := Real.exp_one_gt_two
      linarith
    linarith
  have hlogu2 : Real.log (u:ℝ) ≥ (ξ * (lam:ℝ) * Real.log b) / (2 * (K:ℝ)) := by
    have h1 : Real.log y = ξ * (lam:ℝ) / (K:ℝ) * Real.log b := log_ytr hb
    have h2 : Real.log (u:ℝ) ≥ Real.log y / 2 := by linarith
    rw [h1] at h2
    calc Real.log (u:ℝ) ≥ (ξ * (lam:ℝ) / (K:ℝ) * Real.log b) / 2 := h2
      _ = (ξ * (lam:ℝ) * Real.log b) / (2 * (K:ℝ)) := by ring
  -- conclude m ξ ≤ 2K
  have hlam0 : (0:ℝ) < (lam:ℝ) := by exact_mod_cast hlam
  have hX : (0:ℝ) < (lam:ℝ) * Real.log b := by positivity
  have hchain : (m:ℝ) * ξ * ((lam:ℝ) * Real.log b)
      ≤ (2 * (K:ℝ)) * ((lam:ℝ) * Real.log b) := by
    have hm0 : (0:ℝ) ≤ (m:ℝ) := by positivity
    calc (m:ℝ) * ξ * ((lam:ℝ) * Real.log b)
        = (2 * (K:ℝ)) * ((m:ℝ) * ((ξ * (lam:ℝ) * Real.log b) / (2 * (K:ℝ)))) := by
          field_simp
      _ ≤ (2 * (K:ℝ)) * ((m:ℝ) * Real.log (u:ℝ)) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact mul_le_mul_of_nonneg_left hlogu2 hm0
      _ ≤ (2 * (K:ℝ)) * ((lam:ℝ) * Real.log b) := by
          refine mul_le_mul_of_nonneg_left hlogcast (by positivity)
  have hfinal : (m:ℝ) * ξ ≤ 2 * (K:ℝ) := le_of_mul_le_mul_right hchain hX
  rw [le_div_iff₀ hξ]
  exact hfinal

/-! ### Lemma 2.3(iii): the products stay within the level -/

lemma squarefree_prod_primes {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime) :
    Squarefree (∏ p ∈ s, p) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa using squarefree_one
  | insert p s hp ih =>
      rw [Finset.prod_insert hp]
      have hpp : p.Prime := hs p (Finset.mem_insert_self p s)
      have hrest : ∀ q ∈ s, q.Prime := fun q hq => hs q (Finset.mem_insert_of_mem hq)
      have hcop : Nat.Coprime p (∏ q ∈ s, q) := by
        refine Nat.Coprime.prod_right fun q hq => ?_
        refine (Nat.coprime_primes hpp (hrest q hq)).mpr ?_
        intro he
        exact hp (he ▸ hq)
      exact (Nat.squarefree_mul hcop).mpr ⟨hpp.squarefree, ih hrest⟩

lemma prod_cast_le_pow_card {s : Finset ℕ} {y : ℝ} (hy : 0 ≤ y)
    (h : ∀ p ∈ s, (p : ℝ) ≤ y) : ((∏ p ∈ s, p : ℕ) : ℝ) ≤ y ^ s.card := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert p s hp ih =>
      rw [Finset.prod_insert hp, Finset.card_insert_of_notMem hp, Nat.cast_mul]
      have h1 : (p:ℝ) ≤ y := h p (Finset.mem_insert_self p s)
      have h2 : ((∏ q ∈ s, q : ℕ) : ℝ) ≤ y ^ s.card :=
        ih fun q hq => h q (Finset.mem_insert_of_mem hq)
      have h3 : (0:ℝ) ≤ ((∏ q ∈ s, q : ℕ) : ℝ) := by positivity
      calc (p:ℝ) * ((∏ q ∈ s, q : ℕ) : ℝ) ≤ y * y ^ s.card :=
            mul_le_mul h1 h2 h3 hy
        _ = y ^ (s.card + 1) := by rw [pow_succ]; ring

lemma ytr_pow_K (hb : 2 ≤ b) (hK : 1 ≤ K) (hξ : 0 < ξ) :
    (ytr b ξ K lam) ^ K = (b:ℝ) ^ (ξ * (lam:ℝ)) := by
  unfold ytr
  rw [← Real.rpow_natCast ((b:ℝ) ^ (ξ * (lam:ℝ) / (K:ℝ))) K,
    ← Real.rpow_mul (by positivity)]
  congr 1
  have hK0 : (K:ℝ) ≠ 0 := by
    exact_mod_cast (by omega : K ≠ 0)
  field_simp

/-- Lemma 2.3(iii): `Π_j(𝒬) ⊆ {1 ≤ d ≤ b^λ : d squarefree, d ∈ 𝒟(ℰ),
d ≤ b^{ξλ}}` for `j ≤ K`; consequently the remainder sum over `Π_j(𝒬)`
satisfies the bound of hypothesis (ii). -/
lemma setup_remainder {BB : ℕ → Finset ℕ} (h : CritHyps b BB E ξ) (hK : 1 ≤ K)
    {S : Set ℕ} (A : ℝ) (hA : 0 < A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ lam : ℕ in atTop, ∀ j ≤ K,
      ∑ d ∈ piProds (Qtr b ξ K S E lam) j, |rem (BB lam) d|
        ≤ C * ((BB lam).card : ℝ) / (lam : ℝ) ^ A := by
  obtain ⟨C, hC0, hC⟩ := h.remainder A hA
  refine ⟨C, hC0, ?_⟩
  filter_upwards [hC] with lam hlam j hj
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_
    (fun d _ _ => abs_nonneg _)) hlam
  intro d hd
  simp only [piProds, Finset.mem_image, Finset.mem_filter, Finset.mem_powerset] at hd
  obtain ⟨s, ⟨hsub, hcard⟩, rfl⟩ := hd
  have hyb : (0:ℝ) ≤ ytr b ξ K lam := ytr_nonneg h.b_ge
  have hprimes : ∀ p ∈ s, p.Prime := fun p hp =>
    Qtr_prime h.b_ge p (hsub hp)
  have hpos : 0 < ∏ p ∈ s, p :=
    Finset.prod_pos fun p hp => (hprimes p hp).pos
  have hle : ((∏ p ∈ s, p : ℕ) : ℝ) ≤ (b:ℝ) ^ (ξ * (lam:ℝ)) := by
    calc ((∏ p ∈ s, p : ℕ) : ℝ)
        ≤ (ytr b ξ K lam) ^ s.card :=
          prod_cast_le_pow_card hyb fun p hp =>
            ((mem_Qset_iff hyb).mp (hsub hp)).2.2.1
      _ ≤ (ytr b ξ K lam) ^ K := by
          refine pow_le_pow_right₀ (one_le_ytr h.b_ge h.xi_pos hK) ?_
          omega
      _ = (b:ℝ) ^ (ξ * (lam:ℝ)) := ytr_pow_K h.b_ge hK h.xi_pos
  rw [Finset.mem_filter, Finset.mem_Icc]
  refine ⟨⟨hpos, ?_⟩, squarefree_prod_primes hprimes, ?_, hle⟩
  · -- ∏ ≤ b^λ in ℕ
    have h2 : (b:ℝ) ^ (ξ * (lam:ℝ)) ≤ (b:ℝ) ^ ((lam:ℝ)) := by
      refine Real.rpow_le_rpow_of_exponent_le
        (by have := h.b_ge; exact_mod_cast (by omega : 1 ≤ b)) ?_
      nlinarith [h.xi_pos.le, h.xi_le_one, (by positivity : (0:ℝ) ≤ (lam:ℝ))]
    have h3 : ((∏ p ∈ s, p : ℕ) : ℝ) ≤ ((b ^ lam : ℕ) : ℝ) := by
      calc ((∏ p ∈ s, p : ℕ) : ℝ) ≤ (b:ℝ) ^ (ξ * (lam:ℝ)) := hle
        _ ≤ (b:ℝ) ^ ((lam:ℝ)) := h2
        _ = ((b ^ lam : ℕ) : ℝ) := by
            push_cast
            rw [Real.rpow_natCast]
    exact_mod_cast h3
  · -- no prime factor in ℰ
    intro ℓ hℓ
    have hℓp := Nat.prime_of_mem_primeFactors hℓ
    have hdvd := Nat.dvd_of_mem_primeFactors hℓ
    obtain ⟨q, hqs, hdq⟩ := (Prime.dvd_finset_prod_iff hℓp.prime _).mp hdvd
    have hqp := hprimes q hqs
    have heq : ℓ = q := (Nat.prime_dvd_prime_iff_eq hℓp hqp).mp hdq
    subst heq
    exact ((mem_Qset_iff hyb).mp (hsub hqs)).2.2.2

end SetupLemma

end EKRev
