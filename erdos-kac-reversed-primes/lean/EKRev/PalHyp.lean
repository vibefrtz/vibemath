/-
EKRev/PalHyp.lean

Verification of the hypotheses of Proposition 2.1 for the palindrome family
`𝒯_λ` (Lemma 3.3 of the paper), from the two quoted inputs:

* Col's level of distribution (`col_thm2`, Theorem 3.1) supplies hypothesis
  (ii) — for all admissible moduli, not only the squarefree ones;
* Banks–Shparlinski (`bsh_thm7`, Theorem 3.2) together with Mertens'
  theorem (`mertens_regular`) supplies hypothesis (iii).

Also contains shared infrastructure used again for reversed primes in
`RevHyp.lean`: the exceptional set `ℰ_b`, the ambient prime set, the
`Ω-ω = ∑_{m≥2} #{ℓ^m ∣ ·}` double-counting identity, geometric and
Mertens-type sum bounds, and a decay lemma for `λ·L/b^{cλ}`.

Everything here is proved (the only axioms used are those of `Cited.lean`).
-/
import Mathlib.Tactic
import EKRev.Cited
import EKRev.PalCount
import EKRev.OmegaS
import EKRev.Sums
import EKRev.CritSetup

namespace EKRev

open Finset Filter Real Topology

variable {b lam d ℓ m : ℕ} {ξ : ℝ}

/-! ### The exceptional set `ℰ_b` (eq. (3.4)) -/

/-- `ℰ_b := {ℓ prime : ℓ ∣ b³ - b}` (eq. (3.4)). -/
def Eb (b : ℕ) : Finset ℕ := (b ^ 3 - b).primeFactors

lemma b_cubed_sub_pos (hb : 2 ≤ b) : 1 ≤ b ^ 3 - b := by
  have e : b ^ 3 = b * b * b := by ring
  have h4 : 2 * 2 * b ≤ b * b * b :=
    Nat.mul_le_mul (Nat.mul_le_mul hb hb) le_rfl
  omega

lemma mem_Eb_prime (h : ℓ ∈ Eb b) : ℓ.Prime := Nat.prime_of_mem_primeFactors h

/-- A prime outside `ℰ_b` is coprime to `b³-b`. -/
lemma prime_not_Eb_coprime (hb : 2 ≤ b) (hp : ℓ.Prime) (hnot : ℓ ∉ Eb b) :
    Nat.Coprime ℓ (b ^ 3 - b) := by
  rw [Nat.Prime.coprime_iff_not_dvd hp]
  intro hdvd
  exact hnot (Nat.mem_primeFactors.mpr
    ⟨hp, hdvd, by have := b_cubed_sub_pos hb; omega⟩)

/-- `d ∈ 𝒟(ℰ_b)` is coprimality to `b³-b` for `d ≥ 1` (after eq. (3.4)). -/
lemma noFactorIn_Eb_iff (hb : 2 ≤ b) (hd : 1 ≤ d) :
    noFactorIn (Eb b) d ↔ Nat.Coprime d (b ^ 3 - b) :=
  noFactorIn_primeFactors_iff (b_cubed_sub_pos hb) hd

/-- `b(b²-1) = b³-b` (the two forms of the exceptional modulus). -/
lemma b_mul_sq_sub_one (hb : 1 ≤ b) : b * (b ^ 2 - 1) = b ^ 3 - b := by
  have h1 : 1 ≤ b ^ 2 := Nat.one_le_pow _ _ (by omega)
  have e1 : b ^ 3 = b * (b ^ 2 - 1) + b := by
    have e2 : b * (b ^ 2 - 1) + b = b * ((b ^ 2 - 1) + 1) := by ring
    rw [e2, Nat.sub_add_cancel h1]
    ring
  omega

/-! ### The ambient prime set and the prime-power double count -/

/-- All primes below `b^λ`. -/
def Pamb (b lam : ℕ) : Finset ℕ := (Finset.range (b ^ lam)).filter Nat.Prime

lemma mem_Pamb : ℓ ∈ Pamb b lam ↔ ℓ < b ^ lam ∧ ℓ.Prime := by
  unfold Pamb
  rw [Finset.mem_filter, Finset.mem_range]

/-- The double-counting identity behind Lemma 3.3(iii) and Lemma 4.5:
for a finite family `B` whose members have images `F n ∈ [1, b^λ)`,
`∑_{n∈B} (Ω(F n) - ω(F n)) = ∑_{m=2}^{bλ} ∑_{ℓ < b^λ prime} #{n ∈ B : ℓ^m ∣ F n}`. -/
lemma sum_excess_eq (hb : 2 ≤ b) (lam : ℕ) (B : Finset ℕ) (F : ℕ → ℕ)
    (hF1 : ∀ n ∈ B, 1 ≤ F n) (hFlt : ∀ n ∈ B, F n < b ^ lam) :
    ∑ n ∈ B, ((bigOmega (F n) : ℝ) - (smallOmega (F n) : ℝ))
      = ∑ m ∈ Finset.Icc 2 (b * lam), ∑ ℓ ∈ Pamb b lam,
          ((B.filter fun n => ℓ ^ m ∣ F n).card : ℝ) := by
  have hpow : b ^ lam ≤ 2 ^ (b * lam) := by
    calc b ^ lam ≤ (2 ^ b) ^ lam :=
          Nat.pow_le_pow_left (Nat.le_of_lt b.lt_two_pow_self) lam
      _ = 2 ^ (b * lam) := by rw [← pow_mul]
  have hpt : ∀ n ∈ B, (bigOmega (F n) : ℝ) - (smallOmega (F n) : ℝ)
      = ∑ m ∈ Finset.Icc 2 (b * lam),
          (((F n).primeFactors.filter fun ℓ => ℓ ^ m ∣ F n).card : ℝ) := by
    intro n hn
    have hid := bigOmega_eq_add_sum_powers (hF1 n hn)
      (lt_of_lt_of_le (hFlt n hn) hpow)
    have hidR := congrArg (fun k : ℕ => (k : ℝ)) hid
    push_cast at hidR
    linarith
  rw [Finset.sum_congr rfl hpt, Finset.sum_comm]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [Finset.mem_Icc] at hm
  have hsets : ∀ n ∈ B, ((F n).primeFactors.filter fun ℓ => ℓ ^ m ∣ F n)
      = (Pamb b lam).filter (fun ℓ => ℓ ^ m ∣ F n) := by
    intro n hn
    ext ℓ
    simp only [Finset.mem_filter, Nat.mem_primeFactors, Pamb, Finset.mem_range]
    constructor
    · rintro ⟨⟨hp, hdvd, _⟩, hpm⟩
      have h1 : 1 ≤ F n := hF1 n hn
      exact ⟨⟨Nat.lt_of_le_of_lt (Nat.le_of_dvd (by omega) hdvd) (hFlt n hn), hp⟩, hpm⟩
    · rintro ⟨⟨_, hp⟩, hpm⟩
      have h1 : 1 ≤ F n := hF1 n hn
      exact ⟨⟨hp, dvd_trans (dvd_pow_self ℓ (by omega : m ≠ 0)) hpm, by omega⟩, hpm⟩
  have key : ∑ n ∈ B, ((Pamb b lam).filter fun ℓ => ℓ ^ m ∣ F n).card
      = ∑ ℓ ∈ Pamb b lam, (B.filter fun n => ℓ ^ m ∣ F n).card := by
    simp only [Finset.card_filter]
    rw [Finset.sum_comm]
  calc ∑ n ∈ B, (((F n).primeFactors.filter fun ℓ => ℓ ^ m ∣ F n).card : ℝ)
      = ∑ n ∈ B, ((((Pamb b lam).filter fun ℓ => ℓ ^ m ∣ F n).card : ℕ) : ℝ) := by
        refine Finset.sum_congr rfl fun n hn => ?_
        rw [hsets n hn]
    _ = ((∑ n ∈ B, ((Pamb b lam).filter fun ℓ => ℓ ^ m ∣ F n).card : ℕ) : ℝ) := by
        push_cast
        rfl
    _ = ((∑ ℓ ∈ Pamb b lam, (B.filter fun n => ℓ ^ m ∣ F n).card : ℕ) : ℝ) := by
        rw [key]
    _ = ∑ ℓ ∈ Pamb b lam, ((B.filter fun n => ℓ ^ m ∣ F n).card : ℝ) := by
        push_cast
        rfl

/-! ### Geometric and Mertens-type sum bounds -/

/-- `∑_{m=2}^{M} x^m ≤ 2x²` for `0 ≤ x ≤ 1/2`. -/
lemma sum_Icc_geom_le {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) (M : ℕ) :
    ∑ m ∈ Finset.Icc 2 M, x ^ m ≤ 2 * x ^ 2 := by
  have key : ∀ N, 1 ≤ N → ∑ m ∈ Finset.Icc 2 N, x ^ m ≤ 2 * x ^ 2 - 2 * x ^ (N + 1) := by
    intro N hN
    induction N, hN using Nat.le_induction with
    | base =>
        rw [Finset.Icc_eq_empty (by omega)]
        simp only [Finset.sum_empty]
        norm_num
    | succ N hN ih =>
        rw [Finset.sum_Icc_succ_top (by omega)]
        have h1 : x ^ (N + 1 + 1) = x * x ^ (N + 1) := by
          rw [pow_succ]
          ring
        have h2 : (0:ℝ) ≤ x ^ (N + 1) := pow_nonneg hx0 _
        calc (∑ m ∈ Finset.Icc 2 N, x ^ m) + x ^ (N + 1)
            ≤ (2 * x ^ 2 - 2 * x ^ (N + 1)) + x ^ (N + 1) := by linarith
          _ = 2 * x ^ 2 - x ^ (N + 1) := by ring
          _ ≤ 2 * x ^ 2 - 2 * x ^ (N + 1 + 1) := by
              rw [h1]
              nlinarith
  rcases Nat.lt_or_ge M 1 with hM | hM
  · rw [Finset.Icc_eq_empty (by omega)]
    simp only [Finset.sum_empty]
    positivity
  · calc ∑ m ∈ Finset.Icc 2 M, x ^ m ≤ 2 * x ^ 2 - 2 * x ^ (M + 1) := key M hM
      _ ≤ 2 * x ^ 2 := by nlinarith [pow_nonneg hx0 (M + 1)]

/-- Sums over subsets of a difference of index sets. -/
lemma sum_le_sum_diff {F s t : Finset ℕ} {f : ℕ → ℝ} (hst : s ⊆ t)
    (hF : F ⊆ t \ s) (h0 : ∀ ℓ ∈ t \ s, 0 ≤ f ℓ) :
    ∑ ℓ ∈ F, f ℓ ≤ ∑ ℓ ∈ t, f ℓ - ∑ ℓ ∈ s, f ℓ := by
  calc ∑ ℓ ∈ F, f ℓ ≤ ∑ ℓ ∈ t \ s, f ℓ :=
        Finset.sum_le_sum_of_subset_of_nonneg hF (fun ℓ h _ => h0 ℓ h)
    _ = _ := Finset.sum_sdiff_eq_sub hst

/-- Any sum of prime reciprocals over primes `≤ N` is at most
`∑_{ℓ≤N, ℓ prime} 1/ℓ`. -/
lemma sum_primes_le {F : Finset ℕ} {N : ℕ}
    (hF : ∀ ℓ ∈ F, ℓ.Prime ∧ ℓ ≤ N) :
    ∑ ℓ ∈ F, (1:ℝ) / ℓ ≤ primeRecipSum {p : ℕ | p.Prime} N := by
  unfold primeRecipSum
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
  · intro ℓ hℓ
    simp only [Finset.mem_filter, Finset.mem_range, Set.mem_setOf_eq]
    obtain ⟨hp, hle⟩ := hF ℓ hℓ
    exact ⟨by omega, hp, hp⟩
  · intro ℓ _ _
    positivity

/-- Windowed Mertens comparison: a sum of prime reciprocals over primes in
`(u, N]` is at most the difference of the cumulative sums. -/
lemma sum_primes_window_le {F : Finset ℕ} {u N : ℕ} (huN : u ≤ N)
    (hF : ∀ ℓ ∈ F, ℓ.Prime ∧ u < ℓ ∧ ℓ ≤ N) :
    ∑ ℓ ∈ F, (1:ℝ) / ℓ
      ≤ primeRecipSum {p : ℕ | p.Prime} N - primeRecipSum {p : ℕ | p.Prime} u := by
  unfold primeRecipSum
  refine sum_le_sum_diff ?_ ?_ ?_
  · intro ℓ hℓ
    simp only [Finset.mem_filter, Finset.mem_range] at hℓ ⊢
    exact ⟨by omega, hℓ.2⟩
  · intro ℓ hℓ
    obtain ⟨hp, hu, hN⟩ := hF ℓ hℓ
    simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_range, Set.mem_setOf_eq]
    constructor
    · exact ⟨by omega, hp, hp⟩
    · intro hcon
      exact absurd hcon.1 (by omega)
  · intro ℓ _
    positivity

/-! ### `√`-power commutation and a decay lemma -/

lemma sqrt_pow_comm {x : ℝ} (hx : 0 ≤ x) (m : ℕ) :
    Real.sqrt (x ^ m) = (Real.sqrt x) ^ m := by
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_natCast x m,
    ← Real.rpow_mul hx, ← Real.rpow_natCast (x ^ ((1:ℝ)/2)) m,
    ← Real.rpow_mul hx, mul_comm]

/-- `c λ (L + c') / b^{ξλ/K} → 0`: exponential beats polynomial-times-log. -/
lemma tendsto_linLL_div_ytr (hb : 2 ≤ b) (hξ : 0 < ξ) {K : ℕ} (hK : 1 ≤ K)
    (c c' : ℝ) (hc : 0 ≤ c) (hc' : 0 ≤ c') :
    Tendsto (fun lam : ℕ => c * (lam:ℝ) * (LL b lam + c') / ytr b ξ K lam)
      atTop (𝓝 0) := by
  have hbR : (1:ℝ) < (b:ℝ) := by exact_mod_cast (by omega : 1 < b)
  have hb0R : (0:ℝ) < (b:ℝ) := by linarith
  have hlogb : 0 < Real.log b := Real.log_pos hbR
  have hK0 : (0:ℝ) < (K:ℝ) := by exact_mod_cast hK
  set a : ℝ := ξ * Real.log b / (K:ℝ) with hadef
  have ha : 0 < a := div_pos (mul_pos hξ hlogb) hK0
  have hytr : ∀ lam : ℕ, ytr b ξ K lam = Real.exp (a * lam) := by
    intro lam
    unfold ytr
    rw [Real.rpow_def_of_pos hb0R]
    congr 1
    rw [hadef]
    ring
  set Kc : ℝ := c * (Real.log b + c') with hKcdef
  have hKc0 : 0 ≤ Kc := mul_nonneg hc (by linarith)
  have hg2 : Tendsto (fun x : ℝ => x ^ (((2:ℕ)):ℝ) * Real.exp (-a * x))
      atTop (𝓝 0) := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero _ a ha
  have hg3 : Tendsto (fun x : ℝ => (x:ℝ) ^ (2:ℕ) * Real.exp (-a * x))
      atTop (𝓝 0) := by
    refine hg2.congr' ?_
    filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
    rw [Real.rpow_natCast]
  have hg4 : Tendsto (fun x : ℝ => Kc * (x ^ (2:ℕ) * Real.exp (-a * x)))
      atTop (𝓝 0) := by
    have := hg3.const_mul Kc
    rwa [mul_zero] at this
  have hgn : Tendsto (fun lam : ℕ => Kc * ((lam:ℝ) ^ (2:ℕ) * Real.exp (-a * lam)))
      atTop (𝓝 0) := hg4.comp tendsto_natCast_atTop_atTop
  have h0f : ∀ᶠ lam : ℕ in atTop,
      0 ≤ c * (lam:ℝ) * (LL b lam + c') / ytr b ξ K lam := by
    filter_upwards [(tendsto_LL_atTop hb).eventually_ge_atTop 0] with lam hLL
    have hy := ytr_pos (b := b) (ξ := ξ) (K := K) (lam := lam) hb
    have hlm0 : (0:ℝ) ≤ (lam:ℝ) := by positivity
    exact div_nonneg (mul_nonneg (mul_nonneg hc hlm0) (by linarith)) hy.le
  have hfg : ∀ᶠ lam : ℕ in atTop,
      c * (lam:ℝ) * (LL b lam + c') / ytr b ξ K lam
        ≤ Kc * ((lam:ℝ) ^ (2:ℕ) * Real.exp (-a * lam)) := by
    filter_upwards [eventually_ge_atTop 1,
      (tendsto_LL_atTop hb).eventually_ge_atTop 0] with lam hlm1 hLL0
    rw [hytr lam]
    have hlmR : (1:ℝ) ≤ (lam:ℝ) := by exact_mod_cast hlm1
    have hLLle : LL b lam ≤ (lam:ℝ) * Real.log b := by
      unfold LL
      have hlogpow : Real.log ((b:ℝ) ^ (lam:ℕ)) = (lam:ℝ) * Real.log b :=
        Real.log_pow (b:ℝ) lam
      have hlog0 : 0 < Real.log ((b:ℝ) ^ (lam:ℕ)) := by
        rw [hlogpow]
        have : (0:ℝ) < (lam:ℝ) := by linarith
        positivity
      calc Real.log (Real.log ((b:ℝ) ^ (lam:ℕ)))
          ≤ Real.log ((b:ℝ) ^ (lam:ℕ)) - 1 := Real.log_le_sub_one_of_pos hlog0
        _ ≤ Real.log ((b:ℝ) ^ (lam:ℕ)) := by linarith
        _ = (lam:ℝ) * Real.log b := hlogpow
    have hnum : c * (lam:ℝ) * (LL b lam + c') ≤ Kc * (lam:ℝ) ^ (2:ℕ) := by
      have h1 : LL b lam + c' ≤ (lam:ℝ) * (Real.log b + c') := by
        have h2 : c' * 1 ≤ c' * (lam:ℝ) := by
          refine mul_le_mul_of_nonneg_left hlmR hc'
        nlinarith [hLLle]
      have h3 : (0:ℝ) ≤ (lam:ℝ) := by linarith
      calc c * (lam:ℝ) * (LL b lam + c')
          ≤ c * (lam:ℝ) * ((lam:ℝ) * (Real.log b + c')) := by
            refine mul_le_mul_of_nonneg_left h1 (mul_nonneg hc h3)
        _ = Kc * (lam:ℝ) ^ (2:ℕ) := by
            rw [hKcdef]
            ring
    have hexp : (0:ℝ) < Real.exp (a * lam) := Real.exp_pos _
    calc c * (lam:ℝ) * (LL b lam + c') / Real.exp (a * lam)
        ≤ Kc * (lam:ℝ) ^ (2:ℕ) / Real.exp (a * lam) :=
          div_le_div_of_le' hexp hnum
      _ = Kc * ((lam:ℝ) ^ (2:ℕ) * Real.exp (-a * lam)) := by
          rw [neg_mul, Real.exp_neg, div_eq_mul_inv]
          ring
  exact squeeze_zero' h0f hfg hgn

/-! ### Counting palindromes: block splitting and the remainder bound -/

/-- `𝒯(b^λ)` splits into the shorter palindromes and `𝒯_λ`. -/
lemma palBelow_pow_union (hb : 2 ≤ b) (hlam : 1 ≤ lam) :
    palBelow b (b ^ lam) = palBelow b (b ^ (lam - 1)) ∪ palSet b lam := by
  have hle : b ^ (lam - 1) ≤ b ^ lam := Nat.pow_le_pow_right (by omega) (by omega)
  rw [palSet_eq_filter_isPal hb hlam]
  unfold palBelow
  rw [Finset.range_eq_Ico, Finset.range_eq_Ico, ← Finset.filter_union,
    Finset.Ico_union_Ico_eq_Ico (Nat.zero_le _) hle]

lemma palBelow_palSet_disjoint (hb : 2 ≤ b) (hlam : 1 ≤ lam) :
    Disjoint (palBelow b (b ^ (lam - 1))) (palSet b lam) := by
  refine Finset.disjoint_left.mpr fun n hn1 hn2 => ?_
  have h1 : n < b ^ (lam - 1) := by
    unfold palBelow at hn1
    rw [Finset.mem_filter, Finset.mem_range] at hn1
    exact hn1.1
  have h2 : b ^ (lam - 1) ≤ n := (mem_palSet_iff.mp hn2).1
  omega

lemma palBelow_card_split (hb : 2 ≤ b) (hlam : 1 ≤ lam) :
    (palBelow b (b ^ (lam - 1))).card + (palSet b lam).card
      = (palBelow b (b ^ lam)).card := by
  rw [palBelow_pow_union hb hlam,
    Finset.card_union_of_disjoint (palBelow_palSet_disjoint hb hlam)]

lemma palBelow_filter_split (hb : 2 ≤ b) (hlam : 1 ≤ lam)
    (P : ℕ → Prop) [DecidablePred P] :
    ((palBelow b (b ^ (lam - 1))).filter P).card + ((palSet b lam).filter P).card
      = ((palBelow b (b ^ lam)).filter P).card := by
  rw [palBelow_pow_union hb hlam, Finset.filter_union,
    Finset.card_union_of_disjoint
      (Finset.disjoint_filter_filter (palBelow_palSet_disjoint hb hlam))]

/-- The two-endpoint estimate `|r_q(λ)| ≤ 2 sup_z |·|` from the proof of
Lemma 3.3(ii). -/
lemma pal_rem_le (hb : 2 ≤ b) (hlam : 1 ≤ lam) {q : ℕ} (hq : 1 ≤ q) {Bd : ℝ}
    (h1 : |((palBelowMod b (b ^ lam) 0 q).card : ℝ)
        - ((palBelow b (b ^ lam)).card : ℝ) / q| ≤ Bd)
    (h2 : |((palBelowMod b (b ^ (lam - 1)) 0 q).card : ℝ)
        - ((palBelow b (b ^ (lam - 1))).card : ℝ) / q| ≤ Bd) :
    |rem (palSet b lam) q| ≤ 2 * Bd := by
  have hmod : ∀ z : ℕ, (palBelow b z).filter (fun n => q ∣ n) = palBelowMod b z 0 q := by
    intro z
    unfold palBelowMod
    refine Finset.filter_congr fun n _ => ?_
    rw [Nat.zero_mod]
    constructor
    · rintro ⟨c, rfl⟩
      exact Nat.mul_mod_right q c
    · intro h
      exact Nat.dvd_of_mod_eq_zero h
  have e1 : (((palSet b lam).filter fun n => q ∣ n).card : ℝ)
      = ((palBelowMod b (b ^ lam) 0 q).card : ℝ)
        - ((palBelowMod b (b ^ (lam - 1)) 0 q).card : ℝ) := by
    have h := palBelow_filter_split hb hlam (fun n => q ∣ n)
    rw [hmod (b ^ lam), hmod (b ^ (lam - 1))] at h
    have hR := congrArg (fun k : ℕ => (k : ℝ)) h
    push_cast at hR
    linarith
  have e2 : ((palSet b lam).card : ℝ)
      = ((palBelow b (b ^ lam)).card : ℝ)
        - ((palBelow b (b ^ (lam - 1))).card : ℝ) := by
    have h := palBelow_card_split hb hlam
    have hR := congrArg (fun k : ℕ => (k : ℝ)) h
    push_cast at hR
    linarith
  unfold rem
  rw [e1, e2]
  have e3 : ((palBelowMod b (b ^ lam) 0 q).card : ℝ)
        - ((palBelowMod b (b ^ (lam - 1)) 0 q).card : ℝ)
        - (((palBelow b (b ^ lam)).card : ℝ)
            - ((palBelow b (b ^ (lam - 1))).card : ℝ)) / q
      = (((palBelowMod b (b ^ lam) 0 q).card : ℝ)
          - ((palBelow b (b ^ lam)).card : ℝ) / q)
        - (((palBelowMod b (b ^ (lam - 1)) 0 q).card : ℝ)
          - ((palBelow b (b ^ (lam - 1))).card : ℝ) / q) := by
    ring
  rw [e3]
  calc |_ - _| ≤ |((palBelowMod b (b ^ lam) 0 q).card : ℝ)
          - ((palBelow b (b ^ lam)).card : ℝ) / q|
        + |((palBelowMod b (b ^ (lam - 1)) 0 q).card : ℝ)
          - ((palBelow b (b ^ (lam - 1))).card : ℝ) / q| := abs_sub _ _
    _ ≤ Bd + Bd := add_le_add h1 h2
    _ = 2 * Bd := by ring

/-- `𝒯_λ ≠ ∅` for `λ ≥ 1`. -/
lemma palSet_nonempty (hb : 2 ≤ b) (hlam : 1 ≤ lam) : (palSet b lam).Nonempty := by
  rw [← Finset.card_pos, palSet_card hb hlam]
  exact Nat.mul_pos (by omega) (Nat.pos_pow_of_pos _ (by omega))



/-! ### The packaged Col input (Lemma 3.3(ii), for all admissible moduli) -/

/-- Lemma 3.3(ii), packaged: a level `0 < ξ ≤ 1/2` for the palindrome family
together with, for every `A > 0`, a constant `C` and, for each `λ ≥ 1`, a
bound function `Bnd` dominating `|r_q(λ)|` at every admissible modulus `q`
(squarefree or not — the "stronger form" recorded in the proof of
Lemma 3.3), whose sum over admissible moduli is `≤ C·#𝒯_λ/λ^A`. -/
theorem pal_col_package (hb : 2 ≤ b) :
    ∃ ξ : ℝ, 0 < ξ ∧ ξ ≤ 1/2 ∧
      ∀ A : ℝ, 0 < A → ∃ C : ℝ, 0 ≤ C ∧ ∀ lam : ℕ, 1 ≤ lam →
        ∃ Bnd : ℕ → ℝ,
          (∀ q, 0 ≤ Bnd q) ∧
          (∀ q, 1 ≤ q → Nat.Coprime q (b ^ 3 - b) →
            (q : ℝ) ≤ (b : ℝ) ^ (ξ * (lam : ℝ)) →
            |rem (palSet b lam) q| ≤ 2 * Bnd q) ∧
          ((∑ q ∈ (Finset.Icc 1 (b ^ lam)).filter
              (fun q => Nat.Coprime q (b ^ 3 - b)
                ∧ (q : ℝ) ≤ (b : ℝ) ^ (ξ * (lam : ℝ))), Bnd q)
            ≤ C * ((palSet b lam).card : ℝ) / (lam : ℝ) ^ A) := by
  obtain ⟨β, hβ0, hcol⟩ := col_thm2 b hb
  have hbR : (1:ℝ) < (b:ℝ) := by exact_mod_cast (by omega : 1 < b)
  have hb0R : (0:ℝ) < (b:ℝ) := by linarith
  have hlogb : 0 < Real.log b := Real.log_pos hbR
  refine ⟨min (β/2) (1/2), lt_min (by linarith) (by norm_num), min_le_right _ _, ?_⟩
  set ξ' : ℝ := min (β/2) (1/2) with hxdef
  have hx0 : 0 < ξ' := lt_min (by linarith) (by norm_num)
  have hxβ : ξ' < β := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  set η : ℝ := (β - ξ') / 2 with hetadef
  have heta0 : 0 < η := by rw [hetadef]; linarith
  have hetaβ : η < β := by rw [hetadef]; linarith
  have hxβη : ξ' < β - η := by rw [hetadef]; linarith
  intro A hA
  obtain ⟨C, hC0, hcolA⟩ := hcol A η hA heta0 hetaβ
  refine ⟨4 * C / (Real.log b) ^ A, by positivity, ?_⟩
  intro lam hlam
  obtain ⟨Bnd, hB0, hBptw, hBsum⟩ := hcolA lam hlam
  have hlamR : (1:ℝ) ≤ (lam:ℝ) := by exact_mod_cast hlam
  have hconv : ((b:ℝ) ^ (lam:ℕ)) ^ (β - η) = (b:ℝ) ^ ((lam:ℝ) * (β - η)) := by
    rw [← Real.rpow_natCast (b:ℝ) lam, ← Real.rpow_mul hb0R.le]
  have hlt : ∀ q : ℕ, (q:ℝ) ≤ (b:ℝ) ^ (ξ' * (lam:ℝ)) →
      (q:ℝ) < ((b:ℝ) ^ (lam:ℕ)) ^ (β - η) := by
    intro q hq
    rw [hconv]
    refine lt_of_le_of_lt hq ?_
    rw [Real.rpow_lt_rpow_left_iff hbR]
    nlinarith [hxβη, hlamR]
  refine ⟨Bnd, hB0, ?_, ?_⟩
  · intro q hq1 hqcop hqle
    have h1 := hBptw q hq1 hqcop (hlt q hqle) (b ^ lam) le_rfl 0
    have h2 := hBptw q hq1 hqcop (hlt q hqle) (b ^ (lam - 1))
      (Nat.pow_le_pow_right (by omega) (by omega)) 0
    exact pal_rem_le hb hlam hq1 h1 h2
  · have hsub : (Finset.Icc 1 (b ^ lam)).filter
        (fun q => Nat.Coprime q (b ^ 3 - b) ∧ (q:ℝ) ≤ (b:ℝ) ^ (ξ' * (lam:ℝ)))
        ⊆ (Finset.Icc 1 (⌈((b : ℝ) ^ (lam : ℕ)) ^ (β - η)⌉₊)).filter
            (fun q => Nat.Coprime q (b ^ 3 - b)
              ∧ (q : ℝ) < ((b : ℝ) ^ (lam : ℕ)) ^ (β - η)) := by
      intro q hq
      simp only [Finset.mem_filter, Finset.mem_Icc] at hq ⊢
      obtain ⟨⟨hq1, _⟩, hqc, hqle⟩ := hq
      have hqlt := hlt q hqle
      refine ⟨⟨hq1, ?_⟩, hqc, hqlt⟩
      have hle2 : (q:ℝ) ≤ (⌈((b : ℝ) ^ (lam : ℕ)) ^ (β - η)⌉₊ : ℝ) :=
        le_trans hqlt.le (Nat.le_ceil _)
      exact_mod_cast hle2
    have hPB : ((palBelow b (b ^ lam)).card : ℝ) ≤ 4 * ((palSet b lam).card : ℝ) := by
      exact_mod_cast palBelow_card_le hb hlam
    have hlam0 : (0:ℝ) < (lam:ℝ) := by linarith
    have hpowA : (Real.log ((b:ℝ) ^ (lam:ℕ))) ^ A
        = (lam:ℝ) ^ A * (Real.log b) ^ A := by
      rw [Real.log_pow (b:ℝ) lam]
      exact Real.mul_rpow hlam0.le hlogb.le
    have hlamA : (0:ℝ) < (lam:ℝ) ^ A := Real.rpow_pos_of_pos hlam0 _
    have hlogA : (0:ℝ) < (Real.log b) ^ A := Real.rpow_pos_of_pos hlogb _
    calc (∑ q ∈ (Finset.Icc 1 (b ^ lam)).filter
          (fun q => Nat.Coprime q (b ^ 3 - b)
            ∧ (q:ℝ) ≤ (b:ℝ) ^ (ξ' * (lam:ℝ))), Bnd q)
        ≤ ∑ q ∈ (Finset.Icc 1 (⌈((b : ℝ) ^ (lam : ℕ)) ^ (β - η)⌉₊)).filter
            (fun q => Nat.Coprime q (b ^ 3 - b)
              ∧ (q : ℝ) < ((b : ℝ) ^ (lam : ℕ)) ^ (β - η)), Bnd q :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun q _ _ => hB0 q)
      _ ≤ C * ((palBelow b (b ^ lam)).card : ℝ)
            / (Real.log ((b : ℝ) ^ (lam : ℕ))) ^ A := hBsum
      _ ≤ 4 * C / (Real.log b) ^ A * ((palSet b lam).card : ℝ) / (lam : ℝ) ^ A := by
          rw [hpowA]
          have e1 : C * ((palBelow b (b ^ lam)).card : ℝ)
                / ((lam:ℝ)^A * (Real.log b)^A)
              = (C * ((palBelow b (b ^ lam)).card : ℝ) / (Real.log b)^A)
                / (lam:ℝ)^A := by
            ring
          have e2 : 4 * C / (Real.log b) ^ A * ((palSet b lam).card : ℝ)
                / (lam : ℝ) ^ A
              = (C * (4 * ((palSet b lam).card : ℝ)) / (Real.log b)^A)
                / (lam:ℝ)^A := by
            ring
          rw [e1, e2]
          refine div_le_div_of_le' hlamA ?_
          refine div_le_div_of_le' hlogA ?_
          nlinarith [hPB, hC0]

/-! ### Hypotheses (i) and (ii) for palindromes (Lemma 3.3(ii)) -/

/-- Palindromes satisfy the hypotheses of Proposition 2.1, for some level
`ξ > 0` (Lemma 3.3, parts (i)–(ii); Theorem 3.1 via `pal_col_package`). -/
theorem palCritHyps (hb : 2 ≤ b) :
    ∃ ξ : ℝ, 0 < ξ ∧ CritHyps b (fun lam => palSet b lam) (Eb b) ξ := by
  obtain ⟨ξ', hx0, hxh, hpkg⟩ := pal_col_package hb
  refine ⟨ξ', hx0, ⟨hb, hx0, by linarith, ?_, ?_, ?_, ?_⟩⟩
  · filter_upwards [eventually_ge_atTop 1] with lam hlam
    exact palSet_nonempty hb hlam
  · intro lam n hn
    have h := (mem_palSet_iff.mp hn).1
    have h2 : 1 ≤ b ^ (lam - 1) := Nat.one_le_pow _ _ (by omega)
    omega
  · intro lam n hn
    exact le_of_lt (mem_palSet_iff.mp hn).2.1
  · intro A hA
    obtain ⟨C, hC0, hpkgA⟩ := hpkg A hA
    refine ⟨2 * C, by linarith, ?_⟩
    filter_upwards [eventually_ge_atTop 1] with lam hlam
    obtain ⟨Bnd, hB0, hBrem, hBsum⟩ := hpkgA lam hlam
    have hptw : ∀ d ∈ (Finset.Icc 1 (b ^ lam)).filter
        (fun d => Squarefree d ∧ noFactorIn (Eb b) d
          ∧ (d:ℝ) ≤ (b:ℝ) ^ (ξ' * (lam:ℝ))),
        |rem (palSet b lam) d| ≤ 2 * Bnd d := by
      intro d hd
      simp only [Finset.mem_filter, Finset.mem_Icc] at hd
      obtain ⟨⟨hd1, _⟩, _, hdE, hdle⟩ := hd
      exact hBrem d hd1 ((noFactorIn_Eb_iff hb hd1).mp hdE) hdle
    have hsub : (Finset.Icc 1 (b ^ lam)).filter
        (fun d => Squarefree d ∧ noFactorIn (Eb b) d
          ∧ (d:ℝ) ≤ (b:ℝ) ^ (ξ' * (lam:ℝ)))
        ⊆ (Finset.Icc 1 (b ^ lam)).filter
          (fun q => Nat.Coprime q (b ^ 3 - b)
            ∧ (q : ℝ) ≤ (b : ℝ) ^ (ξ' * (lam : ℝ))) := by
      intro d hd
      simp only [Finset.mem_filter, Finset.mem_Icc] at hd ⊢
      obtain ⟨⟨hd1, hd2⟩, _, hdE, hdle⟩ := hd
      exact ⟨⟨hd1, hd2⟩, (noFactorIn_Eb_iff hb hd1).mp hdE, hdle⟩
    calc ∑ d ∈ (Finset.Icc 1 (b ^ lam)).filter
          (fun d => Squarefree d ∧ noFactorIn (Eb b) d
            ∧ (d:ℝ) ≤ (b:ℝ) ^ (ξ' * (lam:ℝ))),
          |rem (palSet b lam) d|
        ≤ ∑ d ∈ (Finset.Icc 1 (b ^ lam)).filter
            (fun d => Squarefree d ∧ noFactorIn (Eb b) d
              ∧ (d:ℝ) ≤ (b:ℝ) ^ (ξ' * (lam:ℝ))), 2 * Bnd d :=
          Finset.sum_le_sum hptw
      _ ≤ ∑ d ∈ (Finset.Icc 1 (b ^ lam)).filter
            (fun q => Nat.Coprime q (b ^ 3 - b)
              ∧ (q : ℝ) ≤ (b : ℝ) ^ (ξ' * (lam : ℝ))), 2 * Bnd d :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub
            (fun d _ _ => by linarith [hB0 d])
      _ = 2 * ∑ d ∈ (Finset.Icc 1 (b ^ lam)).filter
            (fun q => Nat.Coprime q (b ^ 3 - b)
              ∧ (q : ℝ) ≤ (b : ℝ) ^ (ξ' * (lam : ℝ))), Bnd d := by
          rw [Finset.mul_sum]
      _ ≤ 2 * (C * ((palSet b lam).card : ℝ) / (lam : ℝ) ^ A) := by
          linarith [hBsum]
      _ = 2 * C * ((palSet b lam).card : ℝ) / (lam : ℝ) ^ A := by
          ring

lemma Icc_two_split (M : ℕ) (hM : 2 ≤ M) :
    Finset.Icc 2 M = insert 2 (Finset.Icc 3 M) := by
  ext m
  simp only [Finset.mem_Icc, Finset.mem_insert]
  omega

end EKRev
