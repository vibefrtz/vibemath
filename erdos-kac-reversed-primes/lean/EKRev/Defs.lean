/-
EKRev/Defs.lean

The remaining objects of the paper: the normalization `L = log log b^λ`
(eq. (1.5)), the normal-moment constants `C_k` (eq. (1.5)), remainders `r_d`
(eq. (1.8)), the exceptional-set condition `𝒟(ℰ)` (eq. (1.9)), regular sets of
primes (eq. (1.10)), the truncation set `𝒬` and the sieve mean/variance `μ, σ²`
(eq. (2.2) and before Prop. 2.2), the product sets `Π_j(R)`, and empirical
averages/distribution functions.
-/
import Mathlib.Tactic
import EKRev.Phi
import EKRev.OmegaS

namespace EKRev

open Finset

/-! ### The normalization `L` and the constants `C_k` -/

/-- `L = log log b^λ` (eq. (1.5)). -/
noncomputable def LL (b lam : ℕ) : ℝ := Real.log (Real.log ((b : ℝ) ^ lam))

lemma LL_eq (hb : 2 ≤ b) (hlam : 1 ≤ lam) :
    LL b lam = Real.log (lam * Real.log b) := by
  unfold LL
  congr 1
  rw [Real.log_pow]

/-- `C_k = Γ(k+1)/(2^{k/2} Γ(k/2+1))` (eq. (1.5)): the `k`-th moment of the
standard normal law for `k` even. -/
noncomputable def Ck (k : ℕ) : ℝ :=
  Real.Gamma ((k : ℝ) + 1) / ((2 : ℝ) ^ ((k : ℝ) / 2) * Real.Gamma ((k : ℝ) / 2 + 1))

/-- The `k`-th moment of the standard normal law: `C_k` for even `k`, `0` for
odd `k`. -/
noncomputable def normalMoment (k : ℕ) : ℝ := if Even k then Ck k else 0

lemma Ck_pos (k : ℕ) : 0 < Ck k := by
  unfold Ck
  have h1 : 0 < Real.Gamma ((k : ℝ) + 1) := Real.Gamma_pos_of_pos (by positivity)
  have h2 : (0:ℝ) < (2 : ℝ) ^ ((k : ℝ) / 2) := Real.rpow_pos_of_pos (by norm_num) _
  have h3 : 0 < Real.Gamma ((k : ℝ) / 2 + 1) := Real.Gamma_pos_of_pos (by positivity)
  positivity

lemma Ck_zero : Ck 0 = 1 := by
  unfold Ck
  norm_num [Real.Gamma_one]

/-! ### Remainders and the exceptional set -/

/-- The remainder `r_d = #{n ∈ B : d ∣ n} - #B/d` (eq. (1.8)). -/
noncomputable def rem (B : Finset ℕ) (d : ℕ) : ℝ :=
  ((B.filter fun n => d ∣ n).card : ℝ) - (B.card : ℝ) / d

/-- Membership in `𝒟(ℰ)` (eq. (1.9)): no prime factor of `d` lies in `ℰ`. -/
def noFactorIn (E : Finset ℕ) (d : ℕ) : Prop := ∀ ℓ ∈ d.primeFactors, ℓ ∉ E

instance (E : Finset ℕ) : DecidablePred (noFactorIn E) := fun d =>
  inferInstanceAs (Decidable (∀ ℓ ∈ d.primeFactors, ℓ ∉ E))

/-- For `d ≥ 1`, `d ∈ 𝒟(ℰ_b)` is exactly coprimality to `b(b²-1)` when
`ℰ_b` is the set of primes dividing `b(b²-1)` (after eq. (3.4)). -/
lemma noFactorIn_primeFactors_iff (hm : 1 ≤ m) (hd : 1 ≤ d) :
    noFactorIn m.primeFactors d ↔ Nat.Coprime d m := by
  unfold noFactorIn
  constructor
  · intro h
    by_contra hcon
    have h1 : 2 ≤ Nat.gcd d m := by
      have := Nat.gcd_pos_of_pos_right d (by omega : 0 < m)
      unfold Nat.Coprime at hcon
      omega
    obtain ⟨ℓ, hℓp, hℓd⟩ := Nat.exists_prime_and_dvd (by omega : Nat.gcd d m ≠ 1)
    have hℓdd : ℓ ∣ d := hℓd.trans (Nat.gcd_dvd_left d m)
    have hℓm : ℓ ∣ m := hℓd.trans (Nat.gcd_dvd_right d m)
    exact h ℓ (Nat.mem_primeFactors.mpr ⟨hℓp, hℓdd, by omega⟩)
      (Nat.mem_primeFactors.mpr ⟨hℓp, hℓm, by omega⟩)
  · intro h ℓ hℓd hℓm
    have h1 : ℓ ∣ Nat.gcd d m :=
      Nat.dvd_gcd (Nat.dvd_of_mem_primeFactors hℓd) (Nat.dvd_of_mem_primeFactors hℓm)
    have h2 : ℓ.Prime := Nat.prime_of_mem_primeFactors hℓd
    unfold Nat.Coprime at h
    rw [h] at h1
    exact absurd (Nat.le_of_dvd one_pos h1) (by have := h2.two_le; omega)

/-! ### Regular sets of primes (eq. (1.10)) -/

open Classical in
/-- `∑_{ℓ ≤ y, ℓ ∈ S} 1/ℓ` over primes `ℓ`. -/
noncomputable def primeRecipSum (S : Set ℕ) (y : ℕ) : ℝ :=
  ∑ ℓ ∈ (Finset.range (y + 1)).filter (fun ℓ => ℓ.Prime ∧ ℓ ∈ S), (1 : ℝ) / ℓ

/-- A set `S` of primes is regular of density `δ` (eq. (1.10)):
`∑_{ℓ≤y, ℓ∈S} 1/ℓ = δ log log y + O(1)`. -/
structure IsRegular (S : Set ℕ) (δ : ℝ) : Prop where
  mem_prime : ∀ n ∈ S, Nat.Prime n
  delta_pos : 0 < δ
  delta_le_one : δ ≤ 1
  bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ y : ℕ, 3 ≤ y →
    |primeRecipSum S y - δ * Real.log (Real.log y)| ≤ C

/-! ### The truncation set `𝒬` and the sieve mean and variance -/

open Classical in
/-- `𝒬 = {ℓ ≤ y : ℓ ∈ S, ℓ ∉ ℰ}` for a real threshold `y` (eq. (2.2)). -/
noncomputable def Qset (S : Set ℕ) (E : Finset ℕ) (y : ℝ) : Finset ℕ :=
  (Finset.range (⌊y⌋₊ + 1)).filter fun ℓ => ℓ.Prime ∧ ℓ ∈ S ∧ (ℓ : ℝ) ≤ y ∧ ℓ ∉ E

open Classical in
lemma mem_Qset_iff {S : Set ℕ} {E : Finset ℕ} {y : ℝ} (hy : 0 ≤ y) :
    ℓ ∈ Qset S E y ↔ ℓ.Prime ∧ ℓ ∈ S ∧ (ℓ : ℝ) ≤ y ∧ ℓ ∉ E := by
  unfold Qset
  rw [Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨_, h⟩
    exact h
  · rintro ⟨hp, hS, hle, hE⟩
    refine ⟨?_, hp, hS, hle, hE⟩
    have := Nat.le_floor hle
    omega

/-- `μ_R = ∑_{ℓ∈R} 1/ℓ` (§2, with `h ≡ 1`). -/
noncomputable def muR (R : Finset ℕ) : ℝ := ∑ ℓ ∈ R, (1 : ℝ) / ℓ

/-- `σ_R² = ∑_{ℓ∈R} (1/ℓ)(1 - 1/ℓ)` (§2, with `h ≡ 1`). -/
noncomputable def sigSq (R : Finset ℕ) : ℝ := ∑ ℓ ∈ R, (1 : ℝ) / ℓ * (1 - 1 / ℓ)

/-- `Π_j(R)`: squarefree products of at most `j` primes of `R`
(§2, before Prop. 2.2). -/
def piProds (R : Finset ℕ) (j : ℕ) : Finset ℕ :=
  (R.powerset.filter fun s => s.card ≤ j).image fun s => ∏ p ∈ s, p

/-- `μ_R ≥ σ_R²`. -/
lemma sigSq_le_muR (R : Finset ℕ) : sigSq R ≤ muR R := by
  unfold sigSq muR
  refine Finset.sum_le_sum fun ℓ _ => ?_
  rcases Nat.eq_zero_or_pos ℓ with h | h
  · subst h
    norm_num
  · have h1 : (0:ℝ) < ℓ := by exact_mod_cast h
    have h2 : (0:ℝ) ≤ 1 / ℓ := by positivity
    nlinarith [h2, sq_nonneg (1 / (ℓ:ℝ))]

/-- `μ_R - σ_R² = ∑ 1/ℓ² ≤ 1` for a set of primes (used for
Lemma 2.3(i), second assertion). -/
lemma muR_sub_sigSq_le_one (hR : ∀ ℓ ∈ R, 2 ≤ ℓ) : muR R - sigSq R ≤ 1 := by
  unfold muR sigSq
  rw [← Finset.sum_sub_distrib]
  have heq : ∀ ℓ ∈ R, (1:ℝ) / ℓ - 1 / ℓ * (1 - 1 / ℓ) = (1 / ℓ) ^ 2 := by
    intro ℓ hℓ
    have h1 : (0:ℝ) < ℓ := by
      have := hR ℓ hℓ
      exact_mod_cast (by omega : 0 < ℓ)
    field_simp
    ring
  rw [Finset.sum_congr rfl heq]
  -- ∑_{ℓ∈R} 1/ℓ² ≤ ∑_{n=2}^{N} 1/n² ≤ 1 via telescoping 1/n² ≤ 1/(n-1) - 1/n
  have hsub : R ⊆ Finset.Icc 2 (R.sup id) := by
    intro ℓ hℓ
    rw [Finset.mem_Icc]
    exact ⟨hR ℓ hℓ, Finset.le_sup (f := id) hℓ⟩
  calc ∑ ℓ ∈ R, ((1:ℝ) / ℓ) ^ 2
      ≤ ∑ ℓ ∈ Finset.Icc 2 (R.sup id), ((1:ℝ) / ℓ) ^ 2 := by
        refine Finset.sum_le_sum_of_subset_of_nonneg hsub fun ℓ _ _ => by positivity
    _ ≤ ∑ ℓ ∈ Finset.Icc 2 (R.sup id), ((1:ℝ) / (ℓ - 1) - 1 / ℓ) := by
        refine Finset.sum_le_sum fun ℓ hℓ => ?_
        rw [Finset.mem_Icc] at hℓ
        have h2 : (2:ℝ) ≤ ℓ := by exact_mod_cast hℓ.1
        have h1 : (1:ℝ) ≤ (ℓ:ℝ) - 1 := by linarith
        have h0 : (0:ℝ) < ℓ := by linarith
        have h0' : (0:ℝ) < (ℓ:ℝ) - 1 := by linarith
        have key : (1:ℝ) / ((ℓ:ℝ) - 1) - 1 / ℓ = 1 / (((ℓ:ℝ) - 1) * ℓ) := by
          field_simp
          ring
        rw [key, div_pow, one_pow]
        refine one_div_le_one_div_of_le (by positivity) ?_
        nlinarith [h2]
    _ ≤ 1 := by
        -- telescoping sum
        set N := R.sup id
        rcases Nat.lt_or_ge N 2 with h | h
        · rw [Finset.Icc_eq_empty (by omega)]
          norm_num
        · have htel : ∀ M : ℕ, 2 ≤ M →
              ∑ ℓ ∈ Finset.Icc 2 M, ((1:ℝ) / (ℓ - 1) - 1 / ℓ) = 1 - 1 / M := by
            intro M hM
            induction M with
            | zero => omega
            | succ M ih =>
                rcases Nat.lt_or_ge M 2 with hM2 | hM2
                · have hM1 : M = 1 := by omega
                  subst hM1
                  rw [show Finset.Icc 2 2 = {2} from rfl]
                  norm_num
                · rw [Finset.sum_Icc_succ_top (by omega), ih hM2]
                  have hM0 : (0:ℝ) < (M:ℝ) := by exact_mod_cast (by omega : 0 < M)
                  have h2 : (M:ℝ) ≠ 0 := ne_of_gt hM0
                  have h3 : (M:ℝ) + 1 ≠ 0 := by positivity
                  push_cast
                  have h4 : ((M:ℝ) + 1) - 1 = (M:ℝ) := by ring
                  rw [h4]
                  field_simp
                  ring
          rw [htel N h]
          have hN0 : (0:ℝ) < N := by exact_mod_cast (by omega : 0 < N)
          have : (0:ℝ) ≤ 1 / N := by positivity
          linarith

/-! ### Empirical averages and distribution functions -/

/-- The average of `f` over a finite set `B`. -/
noncomputable def avg (B : Finset ℕ) (f : ℕ → ℝ) : ℝ := (∑ n ∈ B, f n) / B.card

/-- The empirical distribution function: the proportion of `n ∈ B` with
`f n ≤ t`. -/
noncomputable def edf (B : Finset ℕ) (f : ℕ → ℝ) (t : ℝ) : ℝ :=
  ((B.filter fun n => f n ≤ t).card : ℝ) / B.card

lemma edf_nonneg (B : Finset ℕ) (f : ℕ → ℝ) (t : ℝ) : 0 ≤ edf B f t := by
  unfold edf
  positivity

lemma edf_le_one (B : Finset ℕ) (f : ℕ → ℝ) (t : ℝ) : edf B f t ≤ 1 := by
  unfold edf
  rcases Nat.eq_zero_or_pos B.card with h | h
  · rw [h]
    norm_num
  · rw [div_le_one (by exact_mod_cast h)]
    exact_mod_cast Finset.card_filter_le _ _

lemma edf_mono (B : Finset ℕ) (f : ℕ → ℝ) : Monotone (edf B f) := by
  intro s t hst
  unfold edf
  have hsub : B.filter (fun n => f n ≤ s) ⊆ B.filter (fun n => f n ≤ t) := by
    intro n hn
    rw [Finset.mem_filter] at hn ⊢
    exact ⟨hn.1, le_trans hn.2 hst⟩
  have hc : ((B.filter fun n => f n ≤ s).card : ℝ)
      ≤ ((B.filter fun n => f n ≤ t).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  gcongr

end EKRev
