/-
EKRev/Main.lean

The paper's theorems, assembled from the criterion (`Criterion.lean`,
`CritMoments.lean`) and the hypothesis verifications (`PalHyp.lean`,
`PalOmega.lean`, `RevHyp.lean`, `RevOmega.lean`).

* `pal_moments`, `rev_moments_loc` — Theorem 1.5 at each fixed moment
  order `k` (and its `ω_S`-generalisation, Corollary 1.6), for `𝒯_λ` and
  `𝒜_{λ,i}`;
* `pal_EK_omegaS`/`pal_EK_OmegaS` (+ `_uniform`) — Theorem 1.1 in the
  general regular-`S` form of Corollary 1.6;
* `pal_EK_omega`/`pal_EK_Omega` (+ `_uniform`) — Theorem 1.1 itself
  (`S` = all primes, by Mertens' theorem);
* `rev_EK_omegaS_loc` … — the localised Theorem 1.2 (fixed leading digit),
  in both forms;
* `rev_EK_omega`/`rev_EK_Omega` (+ `_uniform`) — the unlocalised
  Theorem 1.2, by the convex-combination argument over the leading digit;
* `normal_order_of_uniform` and the four corollaries `pal_normal_order_*`,
  `rev_normal_order_*` — Corollary 1.3.

Everything here is proved from the axioms of `Cited.lean` only.
-/
import Mathlib.Tactic
import EKRev.Criterion
import EKRev.PalOmega
import EKRev.RevOmega

namespace EKRev

open Finset Filter Real Topology

variable {b i lam : ℕ} {S : Set ℕ} {δ : ℝ}

/-! ### Transfer through the reversal -/

/-- Counting transfer: `#{n ∈ 𝒜_{λ,i} : P n} = #{p ∈ 𝒫_{λ,i} : P (R_λ p)}`. -/
lemma ALamI_filter_card (hb : 2 ≤ b) (hlam : 1 ≤ lam) (hib : i + 1 ≤ b)
    (P : ℕ → Prop) [DecidablePred P] :
    ((ALamI b lam i).filter P).card
      = ((PLamI b lam i).filter fun p => P (rev b lam p)).card := by
  unfold ALamI
  rw [Finset.filter_image]
  refine Finset.card_image_of_injOn ?_
  intro x hx y hy hxy
  rw [Finset.mem_coe, Finset.mem_filter] at hx hy
  have hsub : ∀ q ∈ PLamI b lam i, q < b ^ lam := by
    intro q hq
    rw [mem_PLamI_iff] at hq
    calc q < (i + 1) * b ^ (lam - 1) := hq.2.1
      _ ≤ b * b ^ (lam - 1) := Nat.mul_le_mul_right _ hib
      _ = b ^ lam := by
          rw [← pow_succ']
          congr 1
          omega
  exact rev_injOn (by omega) lam (hsub x hx.1) (hsub y hy.1) hxy

/-! ### Convex combinations of empirical distributions -/

/-- If every group is within `ε` of `L`, so is the pooled ratio. -/
lemma convex_combination_abs_le {ι : Type*} (s : Finset ι)
    (num den : ι → ℝ) (L ε : ℝ)
    (hden : ∀ j ∈ s, 0 < den j)
    (hdenpos : 0 < ∑ j ∈ s, den j)
    (h : ∀ j ∈ s, |num j / den j - L| ≤ ε) :
    |(∑ j ∈ s, num j) / (∑ j ∈ s, den j) - L| ≤ ε := by
  have hε0 : 0 ≤ ε := by
    rcases s.eq_empty_or_nonempty with rfl | ⟨j, hj⟩
    · simp at hdenpos
    · exact le_trans (abs_nonneg _) (h j hj)
  have key : |(∑ j ∈ s, num j) - L * ∑ j ∈ s, den j| ≤ ε * ∑ j ∈ s, den j := by
    have e1 : (∑ j ∈ s, num j) - L * ∑ j ∈ s, den j
        = ∑ j ∈ s, (num j - L * den j) := by
      rw [Finset.sum_sub_distrib, Finset.mul_sum]
    rw [e1]
    calc |∑ j ∈ s, (num j - L * den j)| ≤ ∑ j ∈ s, |num j - L * den j| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j ∈ s, ε * den j := by
          refine Finset.sum_le_sum fun j hj => ?_
          have hdj := hden j hj
          have e2 : num j - L * den j = (num j / den j - L) * den j := by
            field_simp
          rw [e2, abs_mul, abs_of_pos hdj]
          exact mul_le_mul_of_nonneg_right (h j hj) hdj.le
      _ = ε * ∑ j ∈ s, den j := by rw [Finset.mul_sum]
  have e3 : (∑ j ∈ s, num j) / (∑ j ∈ s, den j) - L
      = ((∑ j ∈ s, num j) - L * ∑ j ∈ s, den j) / (∑ j ∈ s, den j) := by
    field_simp
  rw [e3, abs_div, abs_of_pos hdenpos, div_le_iff₀ hdenpos]
  exact key

/-! ### Theorem 1.5 (fixed moment order) and Corollary 1.6 (moments) -/

/-- **Theorem 1.5 for `𝒯_λ`** (fixed `k`; `ω_S`-form of Corollary 1.6):
the standardised moments of `ω_S` over the palindromes converge to the
Gaussian moments. -/
theorem pal_moments (hb : 2 ≤ b) (hS : IsRegular S δ) (k : ℕ) :
    Tendsto (fun lam => avg (palSet b lam)
        (fun n => (((omegaS S n : ℝ) - δ * LL b lam) / sdl b δ lam) ^ k))
      atTop (𝓝 (normalMoment k)) := by
  obtain ⟨ξ, hξ0, hch⟩ := palCritHyps hb
  exact criterion_moments hch hS k

/-- **Theorem 1.5 for `𝒜_{λ,i}`** (fixed `k`, fixed leading digit;
stated for the patched family, which eventually equals `𝒜_{λ,i}`). -/
theorem rev_moments_loc (hb : 2 ≤ b) (hi1 : 1 ≤ i) (hi2 : i ≤ b - 1)
    (hS : IsRegular S δ) (k : ℕ) :
    Tendsto (fun lam => avg (ALamI b lam i)
        (fun n => (((omegaS S n : ℝ) - δ * LL b lam) / sdl b δ lam) ^ k))
      atTop (𝓝 (normalMoment k)) := by
  obtain ⟨ξ, hξ0, hch⟩ := revCritHyps hb hi1 hi2
  have h := criterion_moments hch hS k
  refine h.congr' ?_
  filter_upwards [AFam_eventually_eq hb hi1 hi2] with lam hAeq
  rw [hAeq]

/-! ### Theorem 1.1 / Corollary 1.6 for palindromes -/

/-- **Corollary 1.6 for `𝒯_λ`, `ω_S`, pointwise in `t`.** -/
theorem pal_EK_omegaS (hb : 2 ≤ b) (hS : IsRegular S δ) (t : ℝ) :
    Tendsto (fun lam : ℕ =>
      (((palSet b lam).filter fun n => (omegaS S n : ℝ) ≤ δ * LL b lam
          + t * Real.sqrt (δ * LL b lam)).card : ℝ) / ((palSet b lam).card : ℝ))
      atTop (𝓝 (Phi t)) := by
  obtain ⟨ξ, hξ0, hch⟩ := palCritHyps hb
  exact criterion_EK_omega hch hS t

/-- **Corollary 1.6 for `𝒯_λ`, `Ω_S`, pointwise in `t`.** -/
theorem pal_EK_OmegaS (hb : 2 ≤ b) (hS : IsRegular S δ) (t : ℝ) :
    Tendsto (fun lam : ℕ =>
      (((palSet b lam).filter fun n => (bigOmegaS S n : ℝ) ≤ δ * LL b lam
          + t * Real.sqrt (δ * LL b lam)).card : ℝ) / ((palSet b lam).card : ℝ))
      atTop (𝓝 (Phi t)) := by
  obtain ⟨ξ, hξ0, hch⟩ := palCritHyps hb
  exact criterion_EK_Omega hch hS (palOmegaHyp hb) t

/-- **Corollary 1.6 for `𝒯_λ`, `ω_S`, uniformly in `t`.** -/
theorem pal_EK_omegaS_uniform (hb : 2 ≤ b) (hS : IsRegular S δ) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ lam : ℕ in atTop, ∀ t : ℝ,
      |(((palSet b lam).filter fun n => (omegaS S n : ℝ) ≤ δ * LL b lam
          + t * Real.sqrt (δ * LL b lam)).card : ℝ) / ((palSet b lam).card : ℝ)
        - Phi t| ≤ ε := by
  obtain ⟨ξ, hξ0, hch⟩ := palCritHyps hb
  exact criterion_EK_omega_uniform hch hS

/-- **Corollary 1.6 for `𝒯_λ`, `Ω_S`, uniformly in `t`.** -/
theorem pal_EK_OmegaS_uniform (hb : 2 ≤ b) (hS : IsRegular S δ) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ lam : ℕ in atTop, ∀ t : ℝ,
      |(((palSet b lam).filter fun n => (bigOmegaS S n : ℝ) ≤ δ * LL b lam
          + t * Real.sqrt (δ * LL b lam)).card : ℝ) / ((palSet b lam).card : ℝ)
        - Phi t| ≤ ε := by
  obtain ⟨ξ, hξ0, hch⟩ := palCritHyps hb
  exact criterion_EK_Omega_uniform hch hS (palOmegaHyp hb)

/-- The set identity specialising `S` to all primes for `ω`. -/
lemma filter_omega_primes_eq (B : Finset ℕ) (x y : ℝ) :
    B.filter (fun n => (omegaS {p : ℕ | p.Prime} n : ℝ) ≤ 1 * x + y * Real.sqrt (1 * x))
      = B.filter (fun n => (smallOmega n : ℝ) ≤ x + y * Real.sqrt x) := by
  refine Finset.filter_congr fun n _ => ?_
  rw [omegaS_primes, one_mul]

/-- The set identity specialising `S` to all primes for `Ω`. -/
lemma filter_Omega_primes_eq (B : Finset ℕ) (x y : ℝ) :
    B.filter (fun n => (bigOmegaS {p : ℕ | p.Prime} n : ℝ) ≤ 1 * x + y * Real.sqrt (1 * x))
      = B.filter (fun n => (bigOmega n : ℝ) ≤ x + y * Real.sqrt x) := by
  refine Finset.filter_congr fun n _ => ?_
  rw [bigOmegaS_primes, one_mul]

/-- **Theorem 1.1, `ω`, pointwise**: the Erdős–Kac law for the number of
distinct prime factors of base-`b` palindromes. -/
theorem pal_EK_omega (hb : 2 ≤ b) (t : ℝ) :
    Tendsto (fun lam : ℕ =>
      (((palSet b lam).filter fun n => (smallOmega n : ℝ) ≤ LL b lam
          + t * Real.sqrt (LL b lam)).card : ℝ) / ((palSet b lam).card : ℝ))
      atTop (𝓝 (Phi t)) := by
  have h := pal_EK_omegaS hb mertens_regular t
  refine h.congr fun lam => ?_
  rw [filter_omega_primes_eq]

/-- **Theorem 1.1, `Ω`, pointwise.** -/
theorem pal_EK_Omega (hb : 2 ≤ b) (t : ℝ) :
    Tendsto (fun lam : ℕ =>
      (((palSet b lam).filter fun n => (bigOmega n : ℝ) ≤ LL b lam
          + t * Real.sqrt (LL b lam)).card : ℝ) / ((palSet b lam).card : ℝ))
      atTop (𝓝 (Phi t)) := by
  have h := pal_EK_OmegaS hb mertens_regular t
  refine h.congr fun lam => ?_
  rw [filter_Omega_primes_eq]

/-- **Theorem 1.1, `ω`, uniformly in `t`.** -/
theorem pal_EK_omega_uniform (hb : 2 ≤ b) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ lam : ℕ in atTop, ∀ t : ℝ,
      |(((palSet b lam).filter fun n => (smallOmega n : ℝ) ≤ LL b lam
          + t * Real.sqrt (LL b lam)).card : ℝ) / ((palSet b lam).card : ℝ)
        - Phi t| ≤ ε := by
  intro ε hε
  filter_upwards [pal_EK_omegaS_uniform hb mertens_regular ε hε] with lam h t
  have := h t
  rwa [filter_omega_primes_eq] at this

/-- **Theorem 1.1, `Ω`, uniformly in `t`.** -/
theorem pal_EK_Omega_uniform (hb : 2 ≤ b) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ lam : ℕ in atTop, ∀ t : ℝ,
      |(((palSet b lam).filter fun n => (bigOmega n : ℝ) ≤ LL b lam
          + t * Real.sqrt (LL b lam)).card : ℝ) / ((palSet b lam).card : ℝ)
        - Phi t| ≤ ε := by
  intro ε hε
  filter_upwards [pal_EK_OmegaS_uniform hb mertens_regular ε hε] with lam h t
  have := h t
  rwa [filter_Omega_primes_eq] at this

/-! ### Theorem 1.2 (localised) / Corollary 1.6 for reversed primes -/

/-- **Corollary 1.6 for `𝒜_{λ,i}`, `ω_S`, pointwise** (the localised law,
stated over the primes `𝒫_{λ,i}` themselves). -/
theorem rev_EK_omegaS_loc (hb : 2 ≤ b) (hi1 : 1 ≤ i) (hi2 : i ≤ b - 1)
    (hS : IsRegular S δ) (t : ℝ) :
    Tendsto (fun lam : ℕ =>
      (((PLamI b lam i).filter fun p =>
          (omegaS S (rev b lam p) : ℝ) ≤ δ * LL b lam
            + t * Real.sqrt (δ * LL b lam)).card : ℝ)
        / ((PLamI b lam i).card : ℝ))
      atTop (𝓝 (Phi t)) := by
  obtain ⟨ξ, hξ0, hch⟩ := revCritHyps hb hi1 hi2
  have h := criterion_EK_omega hch hS t
  refine h.congr' ?_
  filter_upwards [AFam_eventually_eq hb hi1 hi2, eventually_ge_atTop 1]
    with lam hAeq hlam1
  rw [hAeq]
  congr 1
  · exact_mod_cast ALamI_filter_card hb hlam1 (by omega)
      (fun n => (omegaS S n : ℝ) ≤ δ * LL b lam + t * Real.sqrt (δ * LL b lam))
  · exact_mod_cast ALamI_card hb hlam1 (by omega)

/-- **Corollary 1.6 for `𝒜_{λ,i}`, `Ω_S`, pointwise.** -/
theorem rev_EK_OmegaS_loc (hb : 2 ≤ b) (hi1 : 1 ≤ i) (hi2 : i ≤ b - 1)
    (hS : IsRegular S δ) (t : ℝ) :
    Tendsto (fun lam : ℕ =>
      (((PLamI b lam i).filter fun p =>
          (bigOmegaS S (rev b lam p) : ℝ) ≤ δ * LL b lam
            + t * Real.sqrt (δ * LL b lam)).card : ℝ)
        / ((PLamI b lam i).card : ℝ))
      atTop (𝓝 (Phi t)) := by
  obtain ⟨ξ, hξ0, hch⟩ := revCritHyps hb hi1 hi2
  have h := criterion_EK_Omega hch hS (revOmegaHyp hb hi1 hi2) t
  refine h.congr' ?_
  filter_upwards [AFam_eventually_eq hb hi1 hi2, eventually_ge_atTop 1]
    with lam hAeq hlam1
  rw [hAeq]
  congr 1
  · exact_mod_cast ALamI_filter_card hb hlam1 (by omega)
      (fun n => (bigOmegaS S n : ℝ) ≤ δ * LL b lam + t * Real.sqrt (δ * LL b lam))
  · exact_mod_cast ALamI_card hb hlam1 (by omega)

/-- **Corollary 1.6 for `𝒜_{λ,i}`, `ω_S`, uniformly in `t`.** -/
theorem rev_EK_omegaS_loc_uniform (hb : 2 ≤ b) (hi1 : 1 ≤ i) (hi2 : i ≤ b - 1)
    (hS : IsRegular S δ) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ lam : ℕ in atTop, ∀ t : ℝ,
      |(((PLamI b lam i).filter fun p =>
          (omegaS S (rev b lam p) : ℝ) ≤ δ * LL b lam
            + t * Real.sqrt (δ * LL b lam)).card : ℝ)
        / ((PLamI b lam i).card : ℝ) - Phi t| ≤ ε := by
  intro ε hε
  obtain ⟨ξ, hξ0, hch⟩ := revCritHyps hb hi1 hi2
  have h := criterion_EK_omega_uniform hch hS ε hε
  filter_upwards [h, AFam_eventually_eq hb hi1 hi2, eventually_ge_atTop 1]
    with lam h1 hAeq hlam1
  intro t
  have h2 := h1 t
  rw [hAeq] at h2
  have e1 : (((ALamI b lam i).filter fun n => (omegaS S n : ℝ) ≤ δ * LL b lam
      + t * Real.sqrt (δ * LL b lam)).card : ℝ)
      = (((PLamI b lam i).filter fun p =>
          (omegaS S (rev b lam p) : ℝ) ≤ δ * LL b lam
            + t * Real.sqrt (δ * LL b lam)).card : ℝ) := by
    exact_mod_cast ALamI_filter_card hb hlam1 (by omega)
      (fun n => (omegaS S n : ℝ) ≤ δ * LL b lam + t * Real.sqrt (δ * LL b lam))
  have e2 : ((ALamI b lam i).card : ℝ) = ((PLamI b lam i).card : ℝ) := by
    exact_mod_cast ALamI_card hb hlam1 (by omega)
  rw [e1, e2] at h2
  exact h2

/-- **Corollary 1.6 for `𝒜_{λ,i}`, `Ω_S`, uniformly in `t`.** -/
theorem rev_EK_OmegaS_loc_uniform (hb : 2 ≤ b) (hi1 : 1 ≤ i) (hi2 : i ≤ b - 1)
    (hS : IsRegular S δ) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ lam : ℕ in atTop, ∀ t : ℝ,
      |(((PLamI b lam i).filter fun p =>
          (bigOmegaS S (rev b lam p) : ℝ) ≤ δ * LL b lam
            + t * Real.sqrt (δ * LL b lam)).card : ℝ)
        / ((PLamI b lam i).card : ℝ) - Phi t| ≤ ε := by
  intro ε hε
  obtain ⟨ξ, hξ0, hch⟩ := revCritHyps hb hi1 hi2
  have h := criterion_EK_Omega_uniform hch hS (revOmegaHyp hb hi1 hi2) ε hε
  filter_upwards [h, AFam_eventually_eq hb hi1 hi2, eventually_ge_atTop 1]
    with lam h1 hAeq hlam1
  intro t
  have h2 := h1 t
  rw [hAeq] at h2
  have e1 : (((ALamI b lam i).filter fun n => (bigOmegaS S n : ℝ) ≤ δ * LL b lam
      + t * Real.sqrt (δ * LL b lam)).card : ℝ)
      = (((PLamI b lam i).filter fun p =>
          (bigOmegaS S (rev b lam p) : ℝ) ≤ δ * LL b lam
            + t * Real.sqrt (δ * LL b lam)).card : ℝ) := by
    exact_mod_cast ALamI_filter_card hb hlam1 (by omega)
      (fun n => (bigOmegaS S n : ℝ) ≤ δ * LL b lam + t * Real.sqrt (δ * LL b lam))
  have e2 : ((ALamI b lam i).card : ℝ) = ((PLamI b lam i).card : ℝ) := by
    exact_mod_cast ALamI_card hb hlam1 (by omega)
  rw [e1, e2] at h2
  exact h2

/-! ### Theorem 1.2, unlocalised -/

/-- All digit classes are eventually nonempty (Lemma 4.2). -/
lemma PLamI_all_pos (hb : 2 ≤ b) : ∀ᶠ lam : ℕ in atTop,
    ∀ j ∈ Finset.Icc 1 (b - 1), (0:ℝ) < ((PLamI b lam j).card : ℝ) := by
  rw [Filter.eventually_all_finset]
  intro j hj
  rw [Finset.mem_Icc] at hj
  obtain ⟨κ, hκ0, hev⟩ := pilam_lower hb hj.1 hj.2
  filter_upwards [hev, eventually_ge_atTop 1] with lam h1 hlam1
  refine lt_of_lt_of_le ?_ h1
  have hb0R : (0:ℝ) < (b:ℝ) := by exact_mod_cast (by omega : 0 < b)
  have hlamR0 : (0:ℝ) < (lam:ℝ) := by exact_mod_cast (by omega : 0 < lam)
  positivity

/-- **Theorem 1.2 unlocalised, `ω_S`, uniformly in `t`** (general regular
`S`; the convex-combination argument over the leading digit). -/
theorem rev_EK_omegaS_uniform (hb : 2 ≤ b) (hS : IsRegular S δ) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ lam : ℕ in atTop, ∀ t : ℝ,
      |(((PLam b lam).filter fun p =>
          (omegaS S (rev b lam p) : ℝ) ≤ δ * LL b lam
            + t * Real.sqrt (δ * LL b lam)).card : ℝ)
        / ((PLam b lam).card : ℝ) - Phi t| ≤ ε := by
  intro ε hε
  have hloc : ∀ j ∈ Finset.Icc 1 (b - 1), ∀ᶠ lam : ℕ in atTop, ∀ t : ℝ,
      |(((PLamI b lam j).filter fun p =>
          (omegaS S (rev b lam p) : ℝ) ≤ δ * LL b lam
            + t * Real.sqrt (δ * LL b lam)).card : ℝ)
        / ((PLamI b lam j).card : ℝ) - Phi t| ≤ ε := by
    intro j hj
    rw [Finset.mem_Icc] at hj
    exact rev_EK_omegaS_loc_uniform hb hj.1 hj.2 hS ε hε
  rw [← Filter.eventually_all_finset] at hloc
  filter_upwards [hloc, PLamI_all_pos hb, eventually_ge_atTop 1]
    with lam hj hpos hlam1
  intro t
  have hnum : (((PLam b lam).filter fun p =>
      (omegaS S (rev b lam p) : ℝ) ≤ δ * LL b lam
        + t * Real.sqrt (δ * LL b lam)).card : ℝ)
      = ∑ j ∈ Finset.Icc 1 (b - 1),
          (((PLamI b lam j).filter fun p =>
            (omegaS S (rev b lam p) : ℝ) ≤ δ * LL b lam
              + t * Real.sqrt (δ * LL b lam)).card : ℝ) := by
    rw [PLam_filter_card_eq_sum hb hlam1]
    push_cast
    rfl
  have hden : ((PLam b lam).card : ℝ)
      = ∑ j ∈ Finset.Icc 1 (b - 1), ((PLamI b lam j).card : ℝ) := by
    rw [PLam_card_eq_sum hb hlam1]
    push_cast
    rfl
  rw [hnum, hden]
  have hne : (1:ℕ) ∈ Finset.Icc 1 (b - 1) := by
    rw [Finset.mem_Icc]
    omega
  have hdenpos : (0:ℝ) < ∑ j ∈ Finset.Icc 1 (b - 1), ((PLamI b lam j).card : ℝ) :=
    Finset.sum_pos' (fun j hj' => (hpos j hj').le) ⟨1, hne, hpos 1 hne⟩
  exact convex_combination_abs_le (Finset.Icc 1 (b - 1)) _ _ (Phi t) ε
    hpos hdenpos (fun j hj' => hj j hj' t)

/-- **Theorem 1.2 unlocalised, `Ω_S`, uniformly in `t`.** -/
theorem rev_EK_OmegaS_uniform (hb : 2 ≤ b) (hS : IsRegular S δ) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ lam : ℕ in atTop, ∀ t : ℝ,
      |(((PLam b lam).filter fun p =>
          (bigOmegaS S (rev b lam p) : ℝ) ≤ δ * LL b lam
            + t * Real.sqrt (δ * LL b lam)).card : ℝ)
        / ((PLam b lam).card : ℝ) - Phi t| ≤ ε := by
  intro ε hε
  have hloc : ∀ j ∈ Finset.Icc 1 (b - 1), ∀ᶠ lam : ℕ in atTop, ∀ t : ℝ,
      |(((PLamI b lam j).filter fun p =>
          (bigOmegaS S (rev b lam p) : ℝ) ≤ δ * LL b lam
            + t * Real.sqrt (δ * LL b lam)).card : ℝ)
        / ((PLamI b lam j).card : ℝ) - Phi t| ≤ ε := by
    intro j hj
    rw [Finset.mem_Icc] at hj
    exact rev_EK_OmegaS_loc_uniform hb hj.1 hj.2 hS ε hε
  rw [← Filter.eventually_all_finset] at hloc
  filter_upwards [hloc, PLamI_all_pos hb, eventually_ge_atTop 1]
    with lam hj hpos hlam1
  intro t
  have hnum : (((PLam b lam).filter fun p =>
      (bigOmegaS S (rev b lam p) : ℝ) ≤ δ * LL b lam
        + t * Real.sqrt (δ * LL b lam)).card : ℝ)
      = ∑ j ∈ Finset.Icc 1 (b - 1),
          (((PLamI b lam j).filter fun p =>
            (bigOmegaS S (rev b lam p) : ℝ) ≤ δ * LL b lam
              + t * Real.sqrt (δ * LL b lam)).card : ℝ) := by
    rw [PLam_filter_card_eq_sum hb hlam1]
    push_cast
    rfl
  have hden : ((PLam b lam).card : ℝ)
      = ∑ j ∈ Finset.Icc 1 (b - 1), ((PLamI b lam j).card : ℝ) := by
    rw [PLam_card_eq_sum hb hlam1]
    push_cast
    rfl
  rw [hnum, hden]
  have hne : (1:ℕ) ∈ Finset.Icc 1 (b - 1) := by
    rw [Finset.mem_Icc]
    omega
  have hdenpos : (0:ℝ) < ∑ j ∈ Finset.Icc 1 (b - 1), ((PLamI b lam j).card : ℝ) :=
    Finset.sum_pos' (fun j hj' => (hpos j hj').le) ⟨1, hne, hpos 1 hne⟩
  exact convex_combination_abs_le (Finset.Icc 1 (b - 1)) _ _ (Phi t) ε
    hpos hdenpos (fun j hj' => hj j hj' t)

/-! ### Theorem 1.2 with `S` the set of all primes -/

/-- The set identity specialising `S` to all primes, composed with the
reversal, for `ω`. -/
lemma filter_omega_primes_rev_eq (b lam : ℕ) (B : Finset ℕ) (x y : ℝ) :
    B.filter (fun p => (omegaS {q : ℕ | q.Prime} (rev b lam p) : ℝ)
        ≤ 1 * x + y * Real.sqrt (1 * x))
      = B.filter (fun p => (smallOmega (rev b lam p) : ℝ) ≤ x + y * Real.sqrt x) := by
  refine Finset.filter_congr fun p _ => ?_
  rw [omegaS_primes, one_mul]

/-- The same, for `Ω`. -/
lemma filter_Omega_primes_rev_eq (b lam : ℕ) (B : Finset ℕ) (x y : ℝ) :
    B.filter (fun p => (bigOmegaS {q : ℕ | q.Prime} (rev b lam p) : ℝ)
        ≤ 1 * x + y * Real.sqrt (1 * x))
      = B.filter (fun p => (bigOmega (rev b lam p) : ℝ) ≤ x + y * Real.sqrt x) := by
  refine Finset.filter_congr fun p _ => ?_
  rw [bigOmegaS_primes, one_mul]

/-- **Theorem 1.2, localised, `ω`, pointwise.** -/
theorem rev_EK_omega_loc (hb : 2 ≤ b) (hi1 : 1 ≤ i) (hi2 : i ≤ b - 1) (t : ℝ) :
    Tendsto (fun lam : ℕ =>
      (((PLamI b lam i).filter fun p =>
          (smallOmega (rev b lam p) : ℝ) ≤ LL b lam
            + t * Real.sqrt (LL b lam)).card : ℝ)
        / ((PLamI b lam i).card : ℝ))
      atTop (𝓝 (Phi t)) := by
  have h := rev_EK_omegaS_loc hb hi1 hi2 mertens_regular t
  refine h.congr fun lam => ?_
  rw [filter_omega_primes_rev_eq]

/-- **Theorem 1.2, localised, `Ω`, pointwise.** -/
theorem rev_EK_Omega_loc (hb : 2 ≤ b) (hi1 : 1 ≤ i) (hi2 : i ≤ b - 1) (t : ℝ) :
    Tendsto (fun lam : ℕ =>
      (((PLamI b lam i).filter fun p =>
          (bigOmega (rev b lam p) : ℝ) ≤ LL b lam
            + t * Real.sqrt (LL b lam)).card : ℝ)
        / ((PLamI b lam i).card : ℝ))
      atTop (𝓝 (Phi t)) := by
  have h := rev_EK_OmegaS_loc hb hi1 hi2 mertens_regular t
  refine h.congr fun lam => ?_
  rw [filter_Omega_primes_rev_eq]

/-- **Theorem 1.2, unlocalised, `ω`, uniformly in `t`.** -/
theorem rev_EK_omega_uniform (hb : 2 ≤ b) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ lam : ℕ in atTop, ∀ t : ℝ,
      |(((PLam b lam).filter fun p =>
          (smallOmega (rev b lam p) : ℝ) ≤ LL b lam
            + t * Real.sqrt (LL b lam)).card : ℝ)
        / ((PLam b lam).card : ℝ) - Phi t| ≤ ε := by
  intro ε hε
  filter_upwards [rev_EK_omegaS_uniform hb mertens_regular ε hε] with lam h t
  have h2 := h t
  rwa [filter_omega_primes_rev_eq] at h2

/-- **Theorem 1.2, unlocalised, `Ω`, uniformly in `t`.** -/
theorem rev_EK_Omega_uniform (hb : 2 ≤ b) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ lam : ℕ in atTop, ∀ t : ℝ,
      |(((PLam b lam).filter fun p =>
          (bigOmega (rev b lam p) : ℝ) ≤ LL b lam
            + t * Real.sqrt (LL b lam)).card : ℝ)
        / ((PLam b lam).card : ℝ) - Phi t| ≤ ε := by
  intro ε hε
  filter_upwards [rev_EK_OmegaS_uniform hb mertens_regular ε hε] with lam h t
  have h2 := h t
  rwa [filter_Omega_primes_rev_eq] at h2

/-- **Theorem 1.2, unlocalised, `ω`, pointwise.** -/
theorem rev_EK_omega (hb : 2 ≤ b) (t : ℝ) :
    Tendsto (fun lam : ℕ =>
      (((PLam b lam).filter fun p =>
          (smallOmega (rev b lam p) : ℝ) ≤ LL b lam
            + t * Real.sqrt (LL b lam)).card : ℝ)
        / ((PLam b lam).card : ℝ))
      atTop (𝓝 (Phi t)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [rev_EK_omega_uniform hb (ε/2) (by linarith)] with lam h
  rw [Real.dist_eq]
  have := h t
  linarith

/-- **Theorem 1.2, unlocalised, `Ω`, pointwise.** -/
theorem rev_EK_Omega (hb : 2 ≤ b) (t : ℝ) :
    Tendsto (fun lam : ℕ =>
      (((PLam b lam).filter fun p =>
          (bigOmega (rev b lam p) : ℝ) ≤ LL b lam
            + t * Real.sqrt (LL b lam)).card : ℝ)
        / ((PLam b lam).card : ℝ))
      atTop (𝓝 (Phi t)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [rev_EK_Omega_uniform hb (ε/2) (by linarith)] with lam h
  rw [Real.dist_eq]
  have := h t
  linarith

/-! ### Corollary 1.3: the normal order -/

/-- **Corollary 1.3, abstract form**: a uniform Erdős–Kac law forces
concentration, `#{n ∈ B_λ : |g(n) - L_λ| > θL_λ} = o(#B_λ)`. -/
theorem normal_order_of_uniform (BB : ℕ → Finset ℕ) (g : ℕ → ℕ → ℝ)
    (Lf : ℕ → ℝ) (hL : Tendsto Lf atTop atTop)
    (huni : ∀ ε : ℝ, 0 < ε → ∀ᶠ lam : ℕ in atTop, ∀ t : ℝ,
      |(((BB lam).filter fun n => g lam n ≤ Lf lam
          + t * Real.sqrt (Lf lam)).card : ℝ) / ((BB lam).card : ℝ) - Phi t| ≤ ε)
    {θ : ℝ} (hθ : 0 < θ) :
    Tendsto (fun lam => (((BB lam).filter fun n =>
        θ * Lf lam < |g lam n - Lf lam|).card : ℝ) / ((BB lam).card : ℝ))
      atTop (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hsq : Tendsto (fun lam => θ * Real.sqrt (Lf lam)) atTop atTop := by
    have h1 : Tendsto (fun lam : ℕ => Real.sqrt (Lf lam)) atTop atTop :=
      Real.tendsto_sqrt_atTop.comp hL
    exact Tendsto.const_mul_atTop hθ h1
  have hPhiT : Tendsto (fun lam => Phi (θ * Real.sqrt (Lf lam))) atTop (𝓝 1) :=
    tendsto_Phi_atTop.comp hsq
  have hPhiB : Tendsto (fun lam => Phi (-(θ * Real.sqrt (Lf lam)))) atTop (𝓝 0) := by
    refine tendsto_Phi_atBot.comp ?_
    exact Filter.tendsto_neg_atTop_atBot.comp hsq
  filter_upwards [huni (ε/4) (by linarith),
    hL.eventually_ge_atTop 0,
    hPhiT.eventually (Ioi_mem_nhds (by linarith : (1:ℝ) - ε/4 < 1)),
    hPhiB.eventually (Iio_mem_nhds (by linarith : (0:ℝ) < ε/4))]
    with lam huni' hL0 hPT hPB
  rw [Real.dist_eq, sub_zero]
  rcases Nat.eq_zero_or_pos (BB lam).card with hz | hp
  · have hBe : BB lam = ∅ := Finset.card_eq_zero.mp hz
    rw [hBe]
    simpa using hε
  · have hN0 : (0:ℝ) < ((BB lam).card : ℝ) := by exact_mod_cast hp
    have hLL : Real.sqrt (Lf lam) * Real.sqrt (Lf lam) = Lf lam :=
      Real.mul_self_sqrt hL0
    have hsubset : (BB lam).filter (fun n => θ * Lf lam < |g lam n - Lf lam|)
        ⊆ ((BB lam).filter (fun n => ¬ (g lam n ≤ Lf lam
            + θ * Real.sqrt (Lf lam) * Real.sqrt (Lf lam))))
          ∪ (BB lam).filter (fun n => g lam n ≤ Lf lam
            + (-(θ * Real.sqrt (Lf lam))) * Real.sqrt (Lf lam)) := by
      intro n hn
      rw [Finset.mem_filter] at hn
      obtain ⟨hnB, hbad⟩ := hn
      rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
      rcases lt_abs.mp hbad with h | h
      · refine Or.inl ⟨hnB, ?_⟩
        intro hcon
        nlinarith [hLL]
      · refine Or.inr ⟨hnB, ?_⟩
        nlinarith [hLL]
    have h3 := Finset.card_filter_add_card_filter_not
      (s := BB lam) (p := fun n => g lam n ≤ Lf lam
        + θ * Real.sqrt (Lf lam) * Real.sqrt (Lf lam))
    have h4 : ((BB lam).filter (fun n => θ * Lf lam < |g lam n - Lf lam|)).card
        ≤ ((BB lam).filter (fun n => ¬ (g lam n ≤ Lf lam
            + θ * Real.sqrt (Lf lam) * Real.sqrt (Lf lam)))).card
          + ((BB lam).filter (fun n => g lam n ≤ Lf lam
            + (-(θ * Real.sqrt (Lf lam))) * Real.sqrt (Lf lam))).card :=
      le_trans (Finset.card_le_card hsubset) (Finset.card_union_le _ _)
    have h5 : (((BB lam).filter (fun n => ¬ (g lam n ≤ Lf lam
        + θ * Real.sqrt (Lf lam) * Real.sqrt (Lf lam)))).card : ℝ)
        = ((BB lam).card : ℝ)
          - (((BB lam).filter (fun n => g lam n ≤ Lf lam
            + θ * Real.sqrt (Lf lam) * Real.sqrt (Lf lam))).card : ℝ) := by
      have hR := congrArg (fun k : ℕ => (k:ℝ)) h3
      push_cast at hR
      linarith
    have hF1 := huni' (θ * Real.sqrt (Lf lam))
    have hF2 := huni' (-(θ * Real.sqrt (Lf lam)))
    have habs1 := (abs_le.mp hF1).1
    have habs2 := (abs_le.mp hF2).2
    have hPT' : (1:ℝ) - ε/4 < Phi (θ * Real.sqrt (Lf lam)) := hPT
    have hPB' : Phi (-(θ * Real.sqrt (Lf lam))) < ε/4 := hPB
    have hratio0 : (0:ℝ) ≤ (((BB lam).filter (fun n =>
        θ * Lf lam < |g lam n - Lf lam|)).card : ℝ) / ((BB lam).card : ℝ) := by
      positivity
    rw [abs_of_nonneg hratio0]
    have h4R : (((BB lam).filter (fun n => θ * Lf lam < |g lam n - Lf lam|)).card : ℝ)
        ≤ (((BB lam).card : ℝ)
            - (((BB lam).filter (fun n => g lam n ≤ Lf lam
              + θ * Real.sqrt (Lf lam) * Real.sqrt (Lf lam))).card : ℝ))
          + (((BB lam).filter (fun n => g lam n ≤ Lf lam
            + (-(θ * Real.sqrt (Lf lam))) * Real.sqrt (Lf lam))).card : ℝ) := by
      rw [← h5]
      exact_mod_cast h4
    rw [div_lt_iff₀ hN0]
    have e1 : (((BB lam).filter (fun n => g lam n ≤ Lf lam
        + θ * Real.sqrt (Lf lam) * Real.sqrt (Lf lam))).card : ℝ)
        ≥ (Phi (θ * Real.sqrt (Lf lam)) - ε/4) * ((BB lam).card : ℝ) := by
      have h6 := habs1
      rw [ge_iff_le, ← le_div_iff₀ hN0]
      linarith
    have e2 : (((BB lam).filter (fun n => g lam n ≤ Lf lam
        + (-(θ * Real.sqrt (Lf lam))) * Real.sqrt (Lf lam))).card : ℝ)
        ≤ (Phi (-(θ * Real.sqrt (Lf lam))) + ε/4) * ((BB lam).card : ℝ) := by
      have h7 := habs2
      rw [← div_le_iff₀ hN0]
      linarith
    have hfin : ((BB lam).card : ℝ)
          - (((BB lam).filter (fun n => g lam n ≤ Lf lam
            + θ * Real.sqrt (Lf lam) * Real.sqrt (Lf lam))).card : ℝ)
          + (((BB lam).filter (fun n => g lam n ≤ Lf lam
            + (-(θ * Real.sqrt (Lf lam))) * Real.sqrt (Lf lam))).card : ℝ)
        < ε * ((BB lam).card : ℝ) := by
      nlinarith [e1, e2, hPT', hPB', hN0]
    linarith

/-- **Corollary 1.3 for palindromes, `ω`**: `ω` has normal order
`log log n` on `𝒯_λ`. -/
theorem pal_normal_order_omega (hb : 2 ≤ b) {θ : ℝ} (hθ : 0 < θ) :
    Tendsto (fun lam => (((palSet b lam).filter fun n =>
        θ * LL b lam < |(smallOmega n : ℝ) - LL b lam|).card : ℝ)
      / ((palSet b lam).card : ℝ)) atTop (𝓝 0) :=
  normal_order_of_uniform (fun lam => palSet b lam)
    (fun _ n => (smallOmega n : ℝ)) (fun lam => LL b lam)
    (tendsto_LL_atTop hb) (pal_EK_omega_uniform hb) hθ

/-- **Corollary 1.3 for palindromes, `Ω`.** -/
theorem pal_normal_order_Omega (hb : 2 ≤ b) {θ : ℝ} (hθ : 0 < θ) :
    Tendsto (fun lam => (((palSet b lam).filter fun n =>
        θ * LL b lam < |(bigOmega n : ℝ) - LL b lam|).card : ℝ)
      / ((palSet b lam).card : ℝ)) atTop (𝓝 0) :=
  normal_order_of_uniform (fun lam => palSet b lam)
    (fun _ n => (bigOmega n : ℝ)) (fun lam => LL b lam)
    (tendsto_LL_atTop hb) (pal_EK_Omega_uniform hb) hθ

/-- **Corollary 1.3 for reversed primes, `ω`.** -/
theorem rev_normal_order_omega (hb : 2 ≤ b) {θ : ℝ} (hθ : 0 < θ) :
    Tendsto (fun lam => (((PLam b lam).filter fun p =>
        θ * LL b lam < |(smallOmega (rev b lam p) : ℝ) - LL b lam|).card : ℝ)
      / ((PLam b lam).card : ℝ)) atTop (𝓝 0) :=
  normal_order_of_uniform (fun lam => PLam b lam)
    (fun lam p => (smallOmega (rev b lam p) : ℝ)) (fun lam => LL b lam)
    (tendsto_LL_atTop hb) (rev_EK_omega_uniform hb) hθ

/-- **Corollary 1.3 for reversed primes, `Ω`.** -/
theorem rev_normal_order_Omega (hb : 2 ≤ b) {θ : ℝ} (hθ : 0 < θ) :
    Tendsto (fun lam => (((PLam b lam).filter fun p =>
        θ * LL b lam < |(bigOmega (rev b lam p) : ℝ) - LL b lam|).card : ℝ)
      / ((PLam b lam).card : ℝ)) atTop (𝓝 0) :=
  normal_order_of_uniform (fun lam => PLam b lam)
    (fun lam p => (bigOmega (rev b lam p) : ℝ)) (fun lam => LL b lam)
    (tendsto_LL_atTop hb) (rev_EK_Omega_uniform hb) hθ

end EKRev
