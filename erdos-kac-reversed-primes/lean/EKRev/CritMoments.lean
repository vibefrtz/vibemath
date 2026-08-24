/-
EKRev/CritMoments.lean

The moment computation at the heart of Proposition 2.1, in the fixed-order
form: with `W = ω_𝒬 - μ` and the truncation `K` (the proof of the `k`-th
moment uses `K = 2k+1`, so that all products arising from GS stay within the
level `b^{ξλ}`),

* `avg W^m / (√(δL))^m → C_m` (m even) / `0` (m odd)   [`Wc_moment_limit`]
* `avg |W|^m / (√(δL))^m` is eventually bounded         [`Wc_abs_moment_bound`]

both from the GS axiom, Lemma 2.3, and the remainder hypothesis.

Everything here is proved from the axioms of `Cited.lean`; no new axioms.
-/
import Mathlib.Tactic
import EKRev.CritSetup

namespace EKRev

open Finset Filter Real Topology

variable {b : ℕ} {ξ δ : ℝ} {K : ℕ} {S : Set ℕ} {E : Finset ℕ} {BB : ℕ → Finset ℕ}

/-- The centered truncated prime-divisor count `W(n) = ω_𝒬(n) - μ` (§2). -/
noncomputable def Wc (b : ℕ) (ξ : ℝ) (K : ℕ) (S : Set ℕ) (E : Finset ℕ)
    (lam n : ℕ) : ℝ :=
  (omegaR (Qtr b ξ K S E lam) n : ℝ) - muR (Qtr b ξ K S E lam)

/-- The normalizer `√(δL)`. -/
noncomputable def sdl (b : ℕ) (δ : ℝ) (lam : ℕ) : ℝ := Real.sqrt (δ * LL b lam)

lemma tendsto_deltaLL_atTop (hb : 2 ≤ b) (hδ : 0 < δ) :
    Tendsto (fun lam : ℕ => δ * LL b lam) atTop atTop :=
  Tendsto.const_mul_atTop hδ (tendsto_LL_atTop hb)

lemma tendsto_sdl_atTop (hb : 2 ≤ b) (hδ : 0 < δ) :
    Tendsto (fun lam : ℕ => sdl b δ lam) atTop atTop := by
  have h1 : Tendsto Real.sqrt atTop atTop := Real.tendsto_sqrt_atTop
  exact h1.comp (tendsto_deltaLL_atTop hb hδ)

lemma sdl_sq_eventually (hb : 2 ≤ b) (hδ : 0 < δ) :
    ∀ᶠ lam : ℕ in atTop, sdl b δ lam ^ 2 = δ * LL b lam := by
  filter_upwards [(tendsto_deltaLL_atTop hb hδ).eventually_ge_atTop 0] with lam h0
  unfold sdl
  rw [Real.sq_sqrt h0]

/-- `(δL)^j / λ → 0` for any fixed `j` (the remainder term is "smaller than
any fixed power of `L⁻¹`", proof of Prop. 2.1). -/
lemma tendsto_deltaLL_pow_div_atTop (hb : 2 ≤ b) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (j : ℕ) :
    Tendsto (fun lam : ℕ => (δ * LL b lam) ^ j / (lam : ℝ)) atTop (𝓝 0) := by
  have hb1 : (1:ℝ) < (b:ℝ) := by exact_mod_cast (by omega : 1 < b)
  have hlogb : 0 < Real.log b := Real.log_pos hb1
  -- eventually LL ≤ 2 log λ
  have hev : ∀ᶠ lam : ℕ in atTop, 0 ≤ LL b lam ∧ LL b lam ≤ 2 * Real.log lam := by
    have h1 : ∀ᶠ lam : ℕ in atTop, Real.log (Real.log b) ≤ Real.log lam := by
      refine (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop _
    have h2 : ∀ᶠ lam : ℕ in atTop, (0:ℝ) ≤ LL b lam :=
      (tendsto_LL_atTop hb).eventually_ge_atTop 0
    have h3 : ∀ᶠ lam : ℕ in atTop, 1 ≤ lam := eventually_ge_atTop 1
    have h4 : ∀ᶠ lam : ℕ in atTop, (2:ℝ) ≤ (lam:ℝ) := by
      have := eventually_ge_atTop (2:ℕ)
      filter_upwards [this] with lam h
      exact_mod_cast h
    filter_upwards [h1, h2, h3, h4] with lam hl1 hl2 hl3 hl4
    refine ⟨hl2, ?_⟩
    have hlam0 : (0:ℝ) < (lam:ℝ) := by linarith
    have hLL : LL b lam = Real.log ((lam:ℝ) * Real.log b) := LL_eq hb hl3
    rw [hLL, Real.log_mul (by linarith) (by linarith)]
    have h5 : (0:ℝ) < Real.log lam := by
      calc (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
        _ ≤ Real.log lam := Real.log_le_log (by norm_num) hl4
    linarith
  -- compare with (2 log λ)^j / λ → 0
  have hlim : Tendsto (fun lam : ℕ => (2 * Real.log (lam:ℝ)) ^ j / (lam : ℝ))
      atTop (𝓝 0) := by
    have h1 : Tendsto (fun x : ℝ => (Real.log x) ^ j / x) atTop (𝓝 0) :=
      tendsto_pow_log_div_atTop j
    have h2 : Tendsto (fun x : ℝ => 2 ^ j * ((Real.log x) ^ j / x)) atTop (𝓝 (2 ^ j * 0)) :=
      h1.const_mul _
    rw [mul_zero] at h2
    have h3 := h2.comp tendsto_natCast_atTop_atTop
    refine h3.congr fun lam => ?_
    simp only [Function.comp_apply]
    rw [mul_pow]
    ring
  refine squeeze_zero' ?_ ?_ hlim
  · filter_upwards [hev, eventually_ge_atTop 1] with lam h hl
    have hlam0 : (0:ℝ) < (lam:ℝ) := by exact_mod_cast hl
    have h0 : (0:ℝ) ≤ δ * LL b lam := mul_nonneg hδ0.le h.1
    positivity
  · filter_upwards [hev, eventually_ge_atTop 1] with lam h hl
    have hlam0 : (0:ℝ) < (lam:ℝ) := by exact_mod_cast hl
    have hnum : (δ * LL b lam) ^ j ≤ (2 * Real.log (lam:ℝ)) ^ j := by
      refine pow_le_pow_left' (mul_nonneg hδ0.le h.1) ?_ j
      calc δ * LL b lam ≤ 1 * LL b lam := mul_le_mul_of_nonneg_right hδ1 h.1
        _ = LL b lam := one_mul _
        _ ≤ 2 * Real.log (lam:ℝ) := h.2
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right hnum (by positivity)

/-! ### The ratio `√σ²/√(δL) → 1` -/

lemma tendsto_sigSq_ratio (hb : 2 ≤ b) (hδ0 : 0 < δ)
    {c1 : ℝ}
    (hev : ∀ᶠ lam : ℕ in atTop, |sigSq (Qtr b ξ K S E lam) - δ * LL b lam| ≤ c1) :
    Tendsto (fun lam : ℕ => Real.sqrt (sigSq (Qtr b ξ K S E lam)) / sdl b δ lam)
      atTop (𝓝 1) := by
  have hDL := tendsto_deltaLL_atTop hb hδ0
  -- σ²/DL - 1 → 0
  have h1 : Tendsto (fun lam : ℕ => sigSq (Qtr b ξ K S E lam) / (δ * LL b lam) - 1)
      atTop (𝓝 0) := by
    have hg : Tendsto (fun lam : ℕ => c1 / (δ * LL b lam)) atTop (𝓝 0) := by
      have h2 := hDL.inv_tendsto_atTop.const_mul c1
      rw [mul_zero] at h2
      refine h2.congr fun lam => ?_
      rw [div_eq_mul_inv]
      rfl
    refine squeeze_zero_norm' ?_ hg
    filter_upwards [hev, hDL.eventually_ge_atTop 1] with lam h hge
    have hDLpos : (0:ℝ) < δ * LL b lam := by linarith
    have habs : sigSq (Qtr b ξ K S E lam) / (δ * LL b lam) - 1
        = (sigSq (Qtr b ξ K S E lam) - δ * LL b lam) / (δ * LL b lam) := by
      rw [sub_div, div_self (ne_of_gt hDLpos)]
    rw [Real.norm_eq_abs, habs, abs_div, abs_of_pos hDLpos]
    exact div_le_div_of_le' hDLpos h
  -- σ²/DL → 1
  have h2 : Tendsto (fun lam : ℕ => sigSq (Qtr b ξ K S E lam) / (δ * LL b lam))
      atTop (𝓝 1) := by
    have h3 := h1.add_const 1
    rw [zero_add] at h3
    refine h3.congr fun lam => ?_
    ring
  -- take square roots
  have h4 : Tendsto (fun lam : ℕ =>
      Real.sqrt (sigSq (Qtr b ξ K S E lam) / (δ * LL b lam))) atTop (𝓝 1) := by
    have hc : Continuous Real.sqrt := Real.continuous_sqrt
    have := (hc.tendsto 1).comp h2
    rw [show Real.sqrt 1 = 1 from Real.sqrt_one] at this
    exact this
  -- identify with the quotient of square roots, eventually
  refine h4.congr' ?_
  filter_upwards [hDL.eventually_ge_atTop 1] with lam hge
  have hDLpos : (0:ℝ) < δ * LL b lam := by linarith
  unfold sdl
  rw [Real.sqrt_div (sigSq_nonneg _)]

/-! ### Small limit helpers -/

lemma tendsto_const_div_deltaLL (hb : 2 ≤ b) (hδ0 : 0 < δ) (c : ℝ) :
    Tendsto (fun lam : ℕ => c / (δ * LL b lam)) atTop (𝓝 0) := by
  have h2 := (tendsto_deltaLL_atTop hb hδ0).inv_tendsto_atTop.const_mul c
  rw [mul_zero] at h2
  refine h2.congr fun lam => ?_
  rw [div_eq_mul_inv]
  rfl

lemma tendsto_const_div_sdl (hb : 2 ≤ b) (hδ0 : 0 < δ) (c : ℝ) :
    Tendsto (fun lam : ℕ => c / sdl b δ lam) atTop (𝓝 0) := by
  have h2 := (tendsto_sdl_atTop hb hδ0).inv_tendsto_atTop.const_mul c
  rw [mul_zero] at h2
  refine h2.congr fun lam => ?_
  rw [div_eq_mul_inv]
  rfl

lemma tendsto_const_mul_deltaLL_pow_div (hb : 2 ≤ b) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (c : ℝ) (j : ℕ) :
    Tendsto (fun lam : ℕ => c * (δ * LL b lam) ^ j / (lam : ℝ)) atTop (𝓝 0) := by
  have h2 := (tendsto_deltaLL_pow_div_atTop hb hδ0 hδ1 j).const_mul c
  rw [mul_zero] at h2
  refine h2.congr fun lam => ?_
  ring

/-! ### The fixed-order moment limit -/

set_option maxHeartbeats 1600000 in
/-- Proposition 2.1, display (2.4) at fixed order: with `W = ω_𝒬 - μ`,
`avg W^m / (√(δL))^m → C_m` for even `m` and `→ 0` for odd `m`. -/
theorem Wc_moment_limit (h : CritHyps b BB E ξ) (hS : IsRegular S δ) (hK : 1 ≤ K)
    {m : ℕ} (hmK : m ≤ K) :
    Tendsto (fun lam : ℕ =>
        avg (BB lam) (fun n => Wc b ξ K S E lam n ^ m) / sdl b δ lam ^ m)
      atTop (𝓝 (normalMoment m)) := by
  have hb := h.b_ge
  have hδ0 := hS.delta_pos
  have hδ1 := hS.delta_le_one
  rcases Nat.eq_zero_or_pos m with hm0 | hm1
  · -- m = 0 : the average is 1
    subst hm0
    have hev : ∀ᶠ lam : ℕ in atTop,
        (1:ℝ) = avg (BB lam) (fun n => Wc b ξ K S E lam n ^ 0) / sdl b δ lam ^ 0 := by
      filter_upwards [h.nonempty] with lam hne
      have hN : (0:ℝ) < ((BB lam).card : ℝ) := by
        exact_mod_cast Finset.card_pos.mpr hne
      simp only [pow_zero]
      unfold avg
      rw [Finset.sum_const, nsmul_eq_mul, mul_one, div_self (ne_of_gt hN), div_one]
    have h1 : Tendsto (fun _ : ℕ => (1:ℝ)) atTop (𝓝 1) := tendsto_const_nhds
    have h2 := h1.congr' hev
    have h3 : normalMoment 0 = 1 := by
      have he : Even 0 := ⟨0, rfl⟩
      rw [normalMoment, if_pos he, Ck_zero]
    rw [h3]
    exact h2
  · -- m ≥ 1
    obtain ⟨KGS, hKGS1, hgs⟩ := gs_prop3
    obtain ⟨c1, hc10, hc1ev⟩ := setup_mu_sigma (E := E) hb h.xi_pos hK hS
    obtain ⟨CR, hCR0, hCRev⟩ := setup_remainder (S := S) h hK 1 one_pos
    have hDL := tendsto_deltaLL_atTop hb hδ0
    have hratio_pow : Tendsto (fun lam : ℕ =>
        (Real.sqrt (sigSq (Qtr b ξ K S E lam)) / sdl b δ lam) ^ m) atTop (𝓝 1) := by
      have := (tendsto_sigSq_ratio hb hδ0 (hc1ev.mono fun lam hl => hl.2)).pow m
      rwa [one_pow] at this
    have hKGS0 : (0:ℝ) < KGS := by linarith
    have hCk := Ck_pos m
    have hmR : (0:ℝ) < (m:ℝ) := by exact_mod_cast hm1
    have hmain : ∀ᶠ lam : ℕ in atTop,
        (Even m →
          |avg (BB lam) (fun n => Wc b ξ K S E lam n ^ m) / sdl b δ lam ^ m
            - Ck m * (Real.sqrt (sigSq (Qtr b ξ K S E lam)) / sdl b δ lam) ^ m|
          ≤ KGS * (Ck m * 2 ^ m * (m:ℝ) ^ 3 * 2 / (δ * LL b lam))
            + KGS * (2 ^ m * (δ * LL b lam) ^ m * CR / (lam : ℝ))) ∧
        (¬ Even m →
          |avg (BB lam) (fun n => Wc b ξ K S E lam n ^ m) / sdl b δ lam ^ m|
          ≤ KGS * (Ck m * 2 ^ m * (m:ℝ) ^ ((3:ℝ)/2) * 2 / sdl b δ lam)
            + KGS * (2 ^ m * (δ * LL b lam) ^ m * CR / (lam : ℝ))) := by
      filter_upwards [hc1ev, hCRev, h.nonempty,
        hDL.eventually_ge_atTop (2 * (m:ℝ) ^ 3 + 2 * c1 + 2 * c1 + 1),
        eventually_ge_atTop 1] with lam hμσ hrem hne hDLbig hlam1
      set σ2 := sigSq (Qtr b ξ K S E lam) with hσ2def
      set μv := muR (Qtr b ξ K S E lam) with hμdef
      set DL := δ * LL b lam with hDLdef
      set SD := sdl b δ lam with hSDdef
      have hN : (0:ℝ) < ((BB lam).card : ℝ) := by
        exact_mod_cast Finset.card_pos.mpr hne
      have hσ2DL : |σ2 - DL| ≤ c1 := hμσ.2
      have hμDL : |μv - DL| ≤ c1 := hμσ.1
      rw [abs_le] at hσ2DL hμDL
      have hm30 : (0:ℝ) ≤ (m:ℝ) ^ 3 := by positivity
      have hDL1 : (1:ℝ) ≤ DL := by linarith
      have hσ2low : DL / 2 ≤ σ2 := by linarith
      have hσ2hi : σ2 ≤ 2 * DL := by linarith
      have hσ2pos : (0:ℝ) < σ2 := by linarith
      have hμhi : μv ≤ 2 * DL := by linarith
      have hμ0 : (0:ℝ) ≤ μv := muR_nonneg _
      have hm3 : ((m:ℝ)) ^ 3 ≤ σ2 := by nlinarith [hσ2low, hDLbig]
      have hSDsq : SD ^ 2 = DL := by
        rw [hSDdef, hDLdef]
        unfold sdl
        rw [Real.sq_sqrt (by rw [← hDLdef]; linarith : (0:ℝ) ≤ δ * LL b lam)]
      have hSD1 : (1:ℝ) ≤ SD := by
        rw [hSDdef]
        unfold sdl
        rw [show (1:ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
        refine Real.sqrt_le_sqrt ?_
        rw [← hDLdef]
        linarith
      have hSDpos : (0:ℝ) < SD := by linarith
      have hSDm : (1:ℝ) ≤ SD ^ m := one_le_pow₀ hSD1
      have hSDmpos : (0:ℝ) < SD ^ m := by positivity
      have hGS := hgs (BB lam) (Qtr b ξ K S E lam) hne (h.mem_pos lam)
        (Qtr_prime hb) m hm1 (by rw [← hσ2def]; exact hm3)
      have hrw1 : sigSq (Qtr b ξ K S E lam) ^ ((m : ℝ) / 2) = Real.sqrt σ2 ^ m := by
        rw [rpow_natCast_div_two (sigSq_nonneg _), hσ2def]
      have hrw2 : sigSq (Qtr b ξ K S E lam) ^ ((1 : ℝ) / 2) = Real.sqrt σ2 := by
        rw [show ((1:ℝ)/2) = ((1:ℕ):ℝ)/2 by norm_num,
          rpow_natCast_div_two (sigSq_nonneg _), pow_one, hσ2def]
      have hremN : (∑ d ∈ piProds (Qtr b ξ K S E lam) m, |rem (BB lam) d|)
          ≤ CR * ((BB lam).card : ℝ) / (lam:ℝ) := by
        have h5 := hrem m hmK
        calc (∑ d ∈ piProds (Qtr b ξ K S E lam) m, |rem (BB lam) d|)
            ≤ CR * ((BB lam).card : ℝ) / (lam : ℝ) ^ (1:ℝ) := h5
          _ = CR * ((BB lam).card : ℝ) / (lam : ℝ) := by
              rw [Real.rpow_one]
      have hremsum0 : (0:ℝ) ≤ ∑ d ∈ piProds (Qtr b ξ K S E lam) m, |rem (BB lam) d| :=
        Finset.sum_nonneg fun d _ => abs_nonneg _
      have hsq2 : Real.sqrt σ2 ≤ 2 * SD := by
        calc Real.sqrt σ2 ≤ Real.sqrt (2 * DL) := Real.sqrt_le_sqrt hσ2hi
          _ ≤ Real.sqrt (4 * DL) := by
              refine Real.sqrt_le_sqrt ?_
              linarith
          _ = 2 * SD := by
              rw [show (4:ℝ) * DL = (2*SD)^2 by rw [mul_pow, hSDsq]; ring]
              rw [Real.sqrt_sq (by linarith)]
      have hratio2 : (Real.sqrt σ2 / SD) ^ m ≤ 2 ^ m := by
        refine pow_le_pow_left' (by positivity) ?_ m
        rw [div_le_iff₀ hSDpos]
        linarith
      have havg : avg (BB lam) (fun n => Wc b ξ K S E lam n ^ m) / SD ^ m
          = (∑ n ∈ BB lam, Wc b ξ K S E lam n ^ m) / (((BB lam).card : ℝ) * SD ^ m) := by
        unfold avg
        rw [div_div]
      constructor
      · intro hme
        have hGSe := hGS.1 hme
        rw [hrw1] at hGSe
        have hNSD : (0:ℝ) < ((BB lam).card : ℝ) * SD ^ m := by positivity
        have hXeq : Ck m * (Real.sqrt σ2 / SD) ^ m
            = Ck m * ((BB lam).card : ℝ) * Real.sqrt σ2 ^ m
              / (((BB lam).card : ℝ) * SD ^ m) := by
          have hSDm0 : SD ^ m ≠ 0 := by positivity
          have hSD0 : SD ≠ 0 := ne_of_gt hSDpos
          have hN0 : ((BB lam).card : ℝ) ≠ 0 := ne_of_gt hN
          field_simp [hSDm0, hN0]
          rw [div_pow, div_mul_cancel₀ _ hSDm0]
        rw [havg, hXeq, div_sub_div_same, abs_div, abs_of_pos hNSD, div_le_iff₀ hNSD]
        refine le_trans hGSe ?_
        have hterm1 : Ck m * ((BB lam).card : ℝ) * Real.sqrt σ2 ^ m * (m:ℝ) ^ 3 / σ2
            ≤ (Ck m * 2 ^ m * (m:ℝ) ^ 3 * 2 / DL) * (((BB lam).card : ℝ) * SD ^ m) := by
          have e1 : Real.sqrt σ2 ^ m ≤ 2 ^ m * SD ^ m := by
            have h6 := hratio2
            rw [div_pow, div_le_iff₀ (by positivity : (0:ℝ) < SD ^ m)] at h6
            exact h6
          have e2 : (1:ℝ) / σ2 ≤ 2 / DL := by
            have h7 := one_div_le_one_div_of_le (by linarith : (0:ℝ) < DL / 2) hσ2low
            have h8 : (1:ℝ) / (DL / 2) = 2 / DL := one_div_div DL 2
            rw [h8] at h7
            exact h7
          calc Ck m * ((BB lam).card : ℝ) * Real.sqrt σ2 ^ m * (m:ℝ) ^ 3 / σ2
              = (Ck m * (m:ℝ) ^ 3 * ((BB lam).card : ℝ)) * (Real.sqrt σ2 ^ m) * (1 / σ2) := by
                ring
            _ ≤ (Ck m * (m:ℝ) ^ 3 * ((BB lam).card : ℝ)) * (2 ^ m * SD ^ m) * (2 / DL) := by
                refine mul_le_mul ?_ e2 (by positivity) (by positivity)
                refine mul_le_mul_of_nonneg_left e1 (by positivity)
            _ = (Ck m * 2 ^ m * (m:ℝ) ^ 3 * 2 / DL) * (((BB lam).card : ℝ) * SD ^ m) := by
                field_simp
                try ring
        have hterm2 : μv ^ m * ∑ d ∈ piProds (Qtr b ξ K S E lam) m, |rem (BB lam) d|
            ≤ (2 ^ m * DL ^ m * CR / (lam : ℝ)) * (((BB lam).card : ℝ) * SD ^ m) := by
          have e3 : μv ^ m ≤ (2 * DL) ^ m := pow_le_pow_left' hμ0 hμhi m
          have hlamR : (0:ℝ) < (lam:ℝ) := by exact_mod_cast hlam1
          have e4 : (0:ℝ) ≤ (2 * DL) ^ m * (CR * ((BB lam).card : ℝ) / (lam:ℝ)) := by
            positivity
          calc μv ^ m * ∑ d ∈ piProds (Qtr b ξ K S E lam) m, |rem (BB lam) d|
              ≤ (2 * DL) ^ m * (CR * ((BB lam).card : ℝ) / (lam:ℝ)) := by
                refine mul_le_mul e3 hremN hremsum0 (by positivity)
            _ ≤ ((2 * DL) ^ m * (CR * ((BB lam).card : ℝ) / (lam:ℝ))) * SD ^ m := by
                nlinarith [hSDm, e4]
            _ = (2 ^ m * DL ^ m * CR / (lam : ℝ)) * (((BB lam).card : ℝ) * SD ^ m) := by
                rw [mul_pow]
                ring
        calc KGS * (Ck m * ((BB lam).card : ℝ) * Real.sqrt σ2 ^ m * (m:ℝ) ^ 3 / σ2
              + μv ^ m * ∑ d ∈ piProds (Qtr b ξ K S E lam) m, |rem (BB lam) d|)
            ≤ KGS * ((Ck m * 2 ^ m * (m:ℝ) ^ 3 * 2 / DL) * (((BB lam).card : ℝ) * SD ^ m)
              + (2 ^ m * DL ^ m * CR / (lam : ℝ)) * (((BB lam).card : ℝ) * SD ^ m)) := by
              refine mul_le_mul_of_nonneg_left (by linarith [hterm1, hterm2]) (by linarith)
          _ = (KGS * (Ck m * 2 ^ m * (m:ℝ) ^ 3 * 2 / DL)
              + KGS * (2 ^ m * DL ^ m * CR / (lam : ℝ))) * (((BB lam).card : ℝ) * SD ^ m) := by
              ring
      · intro hmo
        have hGSo := hGS.2 hmo
        rw [hrw1, hrw2] at hGSo
        have hNSD : (0:ℝ) < ((BB lam).card : ℝ) * SD ^ m := by positivity
        rw [havg, abs_div, abs_of_pos hNSD, div_le_iff₀ hNSD]
        refine le_trans hGSo ?_
        have hsqσ2pos : (0:ℝ) < Real.sqrt σ2 := Real.sqrt_pos.mpr hσ2pos
        have hterm1 : Ck m * ((BB lam).card : ℝ) * Real.sqrt σ2 ^ m
              * (m:ℝ) ^ ((3:ℝ)/2) / Real.sqrt σ2
            ≤ (Ck m * 2 ^ m * (m:ℝ) ^ ((3:ℝ)/2) * 2 / SD)
              * (((BB lam).card : ℝ) * SD ^ m) := by
          have e1 : Real.sqrt σ2 ^ m ≤ 2 ^ m * SD ^ m := by
            have h6 := hratio2
            rw [div_pow, div_le_iff₀ (by positivity : (0:ℝ) < SD ^ m)] at h6
            exact h6
          have e3 : SD ≤ 2 * Real.sqrt σ2 := by
            calc SD ≤ Real.sqrt (4 * σ2) := by
                  rw [hSDdef]
                  unfold sdl
                  refine Real.sqrt_le_sqrt ?_
                  rw [← hDLdef]
                  linarith
              _ = 2 * Real.sqrt σ2 := by
                  rw [show (4:ℝ) * σ2 = (2 * Real.sqrt σ2)^2 by
                    rw [mul_pow, Real.sq_sqrt hσ2pos.le]; ring]
                  rw [Real.sqrt_sq (by positivity)]
          have e2 : (1:ℝ) / Real.sqrt σ2 ≤ 2 / SD := by
            have h7 := one_div_le_one_div_of_le (by linarith : (0:ℝ) < SD / 2)
              (by linarith : SD / 2 ≤ Real.sqrt σ2)
            have h8 : (1:ℝ) / (SD / 2) = 2 / SD := one_div_div SD 2
            rw [h8] at h7
            exact h7
          have hm32 : (0:ℝ) ≤ (m:ℝ) ^ ((3:ℝ)/2) := Real.rpow_nonneg hmR.le _
          calc Ck m * ((BB lam).card : ℝ) * Real.sqrt σ2 ^ m
                * (m:ℝ) ^ ((3:ℝ)/2) / Real.sqrt σ2
              = (Ck m * (m:ℝ) ^ ((3:ℝ)/2) * ((BB lam).card : ℝ))
                  * (Real.sqrt σ2 ^ m) * (1 / Real.sqrt σ2) := by
                ring
            _ ≤ (Ck m * (m:ℝ) ^ ((3:ℝ)/2) * ((BB lam).card : ℝ))
                  * (2 ^ m * SD ^ m) * (2 / SD) := by
                refine mul_le_mul ?_ e2 (by positivity) (by positivity)
                refine mul_le_mul_of_nonneg_left e1 (by positivity)
            _ = (Ck m * 2 ^ m * (m:ℝ) ^ ((3:ℝ)/2) * 2 / SD)
                  * (((BB lam).card : ℝ) * SD ^ m) := by
                field_simp
                try ring
        have hterm2 : μv ^ m * ∑ d ∈ piProds (Qtr b ξ K S E lam) m, |rem (BB lam) d|
            ≤ (2 ^ m * DL ^ m * CR / (lam : ℝ)) * (((BB lam).card : ℝ) * SD ^ m) := by
          have e3 : μv ^ m ≤ (2 * DL) ^ m := pow_le_pow_left' hμ0 hμhi m
          have hlamR : (0:ℝ) < (lam:ℝ) := by exact_mod_cast hlam1
          have e4 : (0:ℝ) ≤ (2 * DL) ^ m * (CR * ((BB lam).card : ℝ) / (lam:ℝ)) := by
            positivity
          calc μv ^ m * ∑ d ∈ piProds (Qtr b ξ K S E lam) m, |rem (BB lam) d|
              ≤ (2 * DL) ^ m * (CR * ((BB lam).card : ℝ) / (lam:ℝ)) := by
                refine mul_le_mul e3 hremN hremsum0 (by positivity)
            _ ≤ ((2 * DL) ^ m * (CR * ((BB lam).card : ℝ) / (lam:ℝ))) * SD ^ m := by
                nlinarith [hSDm, e4]
            _ = (2 ^ m * DL ^ m * CR / (lam : ℝ)) * (((BB lam).card : ℝ) * SD ^ m) := by
                rw [mul_pow]
                ring
        calc KGS * (Ck m * ((BB lam).card : ℝ) * Real.sqrt σ2 ^ m
              * (m:ℝ) ^ ((3:ℝ)/2) / Real.sqrt σ2
              + μv ^ m * ∑ d ∈ piProds (Qtr b ξ K S E lam) m, |rem (BB lam) d|)
            ≤ KGS * ((Ck m * 2 ^ m * (m:ℝ) ^ ((3:ℝ)/2) * 2 / SD)
                * (((BB lam).card : ℝ) * SD ^ m)
              + (2 ^ m * DL ^ m * CR / (lam : ℝ)) * (((BB lam).card : ℝ) * SD ^ m)) := by
              refine mul_le_mul_of_nonneg_left (by linarith [hterm1, hterm2]) (by linarith)
          _ = (KGS * (Ck m * 2 ^ m * (m:ℝ) ^ ((3:ℝ)/2) * 2 / SD)
              + KGS * (2 ^ m * DL ^ m * CR / (lam : ℝ)))
                * (((BB lam).card : ℝ) * SD ^ m) := by
              ring
    have hg12 : Tendsto (fun lam : ℕ =>
        KGS * (Ck m * 2 ^ m * (m:ℝ) ^ 3 * 2 / (δ * LL b lam))
          + KGS * (2 ^ m * (δ * LL b lam) ^ m * CR / (lam : ℝ))) atTop (𝓝 0) := by
      have h1 : Tendsto (fun lam : ℕ =>
          KGS * (Ck m * 2 ^ m * (m:ℝ) ^ 3 * 2 / (δ * LL b lam))) atTop (𝓝 0) := by
        have h5 := (tendsto_const_div_deltaLL hb hδ0
          (Ck m * 2 ^ m * (m:ℝ) ^ 3 * 2)).const_mul KGS
        rwa [mul_zero] at h5
      have h2 : Tendsto (fun lam : ℕ =>
          KGS * (2 ^ m * (δ * LL b lam) ^ m * CR / (lam : ℝ))) atTop (𝓝 0) := by
        have h3 := tendsto_const_mul_deltaLL_pow_div hb hδ0 hδ1 (KGS * 2 ^ m * CR) m
        refine h3.congr fun lam => ?_
        ring
      have h4 := h1.add h2
      rwa [add_zero] at h4
    have hg32 : Tendsto (fun lam : ℕ =>
        KGS * (Ck m * 2 ^ m * (m:ℝ) ^ ((3:ℝ)/2) * 2 / sdl b δ lam)
          + KGS * (2 ^ m * (δ * LL b lam) ^ m * CR / (lam : ℝ))) atTop (𝓝 0) := by
      have h1 : Tendsto (fun lam : ℕ =>
          KGS * (Ck m * 2 ^ m * (m:ℝ) ^ ((3:ℝ)/2) * 2 / sdl b δ lam)) atTop (𝓝 0) := by
        have h5 := (tendsto_const_div_sdl hb hδ0
          (Ck m * 2 ^ m * (m:ℝ) ^ ((3:ℝ)/2) * 2)).const_mul KGS
        rwa [mul_zero] at h5
      have h2 : Tendsto (fun lam : ℕ =>
          KGS * (2 ^ m * (δ * LL b lam) ^ m * CR / (lam : ℝ))) atTop (𝓝 0) := by
        have h3 := tendsto_const_mul_deltaLL_pow_div hb hδ0 hδ1 (KGS * 2 ^ m * CR) m
        refine h3.congr fun lam => ?_
        ring
      have h4 := h1.add h2
      rwa [add_zero] at h4
    by_cases hme : Even m
    · have hdiff : Tendsto (fun lam : ℕ =>
          avg (BB lam) (fun n => Wc b ξ K S E lam n ^ m) / sdl b δ lam ^ m
            - Ck m * (Real.sqrt (sigSq (Qtr b ξ K S E lam)) / sdl b δ lam) ^ m)
          atTop (𝓝 0) := by
        refine squeeze_zero_norm' ?_ hg12
        filter_upwards [hmain] with lam hl
        rw [Real.norm_eq_abs]
        exact hl.1 hme
      have hX : Tendsto (fun lam : ℕ =>
          Ck m * (Real.sqrt (sigSq (Qtr b ξ K S E lam)) / sdl b δ lam) ^ m)
          atTop (𝓝 (Ck m)) := by
        have h5 := hratio_pow.const_mul (Ck m)
        rwa [mul_one] at h5
      have hsum := hX.add hdiff
      rw [add_zero] at hsum
      have hNM : normalMoment m = Ck m := by rw [normalMoment, if_pos hme]
      rw [hNM]
      refine hsum.congr fun lam => ?_
      ring
    · have hT : Tendsto (fun lam : ℕ =>
          avg (BB lam) (fun n => Wc b ξ K S E lam n ^ m) / sdl b δ lam ^ m)
          atTop (𝓝 0) := by
        refine squeeze_zero_norm' ?_ hg32
        filter_upwards [hmain] with lam hl
        rw [Real.norm_eq_abs]
        exact hl.2 hme
      have hNM : normalMoment m = 0 := by rw [normalMoment, if_neg hme]
      rw [hNM]
      exact hT

/-! ### Absolute moments via Cauchy–Schwarz -/

/-- The fixed-order substitute for the Lyapunov step (eq. (2.5) context):
`avg |W|^m / (√(δL))^m` is eventually bounded, via Cauchy–Schwarz and the
even moment of order `2m`. -/
theorem Wc_abs_moment_bound (h : CritHyps b BB E ξ) (hS : IsRegular S δ)
    (hK : 1 ≤ K) {m : ℕ} (hm2K : 2 * m ≤ K) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ᶠ lam : ℕ in atTop,
      avg (BB lam) (fun n => |Wc b ξ K S E lam n| ^ m) / sdl b δ lam ^ m ≤ D := by
  have h2m := Wc_moment_limit h hS hK (m := 2 * m) hm2K
  refine ⟨Real.sqrt (normalMoment (2*m) + 1), Real.sqrt_nonneg _, ?_⟩
  have hev := h2m.eventually_le_const (lt_add_one (normalMoment (2*m)))
  filter_upwards [hev, h.nonempty,
    (tendsto_deltaLL_atTop h.b_ge hS.delta_pos).eventually_ge_atTop 1]
    with lam h2mle hne hDL1
  have hN : (0:ℝ) < ((BB lam).card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hne
  have hSD1 : (1:ℝ) ≤ sdl b δ lam := by
    unfold sdl
    rw [show (1:ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_le_sqrt (by linarith)
  have hSDpos : (0:ℝ) < sdl b δ lam := by linarith
  set SD := sdl b δ lam
  set T := avg (BB lam) (fun n => |Wc b ξ K S E lam n| ^ m) / SD ^ m with hT
  have hT0 : 0 ≤ T := by
    rw [hT]
    unfold avg
    positivity
  have hTsq : T ^ 2 ≤ avg (BB lam) (fun n => Wc b ξ K S E lam n ^ (2*m)) / SD ^ (2*m) := by
    have hCS := sq_sum_abs_pow_le (BB lam) (Wc b ξ K S E lam) m
    have e1 : T ^ 2 = (∑ n ∈ BB lam, |Wc b ξ K S E lam n| ^ m) ^ 2
        / (((BB lam).card : ℝ) ^ 2 * (SD ^ m) ^ 2) := by
      rw [hT]
      unfold avg
      rw [div_div, div_pow, mul_pow]
    have e2 : avg (BB lam) (fun n => Wc b ξ K S E lam n ^ (2*m)) / SD ^ (2*m)
        = (∑ n ∈ BB lam, Wc b ξ K S E lam n ^ (2*m))
          / (((BB lam).card : ℝ) * SD ^ (2*m)) := by
      unfold avg
      rw [div_div]
    rw [e1, e2, div_le_div_iff₀ (by positivity) (by positivity)]
    have e3 : (SD ^ m) ^ 2 = SD ^ (2*m) := by
      rw [← pow_mul, mul_comm]
    calc (∑ n ∈ BB lam, |Wc b ξ K S E lam n| ^ m) ^ 2
          * (((BB lam).card : ℝ) * SD ^ (2*m))
        ≤ (((BB lam).card : ℝ) * ∑ n ∈ BB lam, Wc b ξ K S E lam n ^ (2*m))
          * (((BB lam).card : ℝ) * SD ^ (2*m)) :=
          mul_le_mul_of_nonneg_right hCS (by positivity)
      _ = (∑ n ∈ BB lam, Wc b ξ K S E lam n ^ (2*m))
          * (((BB lam).card : ℝ) ^ 2 * (SD ^ m) ^ 2) := by
          rw [e3]
          ring
  have hfinal : T ^ 2 ≤ normalMoment (2*m) + 1 := le_trans hTsq h2mle
  calc T ≤ Real.sqrt (T ^ 2) := by
        rw [Real.sqrt_sq hT0]
    _ ≤ Real.sqrt (normalMoment (2*m) + 1) := Real.sqrt_le_sqrt hfinal

/-! ### The full moment convergence (Prop. 2.1, moments part, fixed order) -/

set_option maxHeartbeats 1600000 in
/-- Proposition 2.1, fixed-order moments: with `K = 2k+1` internally,
`avg ((ω_S - δL)/√(δL))^k → C_k` for even `k`, `0` for odd `k`. -/
theorem criterion_moments (h : CritHyps b BB E ξ) (hS : IsRegular S δ) (k : ℕ) :
    Tendsto (fun lam : ℕ => avg (BB lam)
        (fun n => (((omegaS S n : ℝ) - δ * LL b lam) / sdl b δ lam) ^ k))
      atTop (𝓝 (normalMoment k)) := by
  have hb := h.b_ge
  have hδ0 := hS.delta_pos
  set K := 2 * k + 1 with hKdef
  have hK : 1 ≤ K := by omega
  -- the deviation Δ and its bound
  obtain ⟨c1, hc10, hc1ev⟩ := setup_mu_sigma (E := E) hb h.xi_pos hK hS
  have hlarge := setup_large_primes hb h.xi_pos h.xi_le_one hK
  set c2 : ℝ := (E.card : ℝ) + 2 * (K:ℝ) / ξ + c1 with hc2def
  have hc20 : 0 ≤ c2 := by
    rw [hc2def]
    have h1 : (0:ℝ) ≤ 2 * (K:ℝ) / ξ := div_nonneg (by positivity) h.xi_pos.le
    have h2 : (0:ℝ) ≤ (E.card : ℝ) := by positivity
    linarith
  have hΔbound : ∀ᶠ lam : ℕ in atTop, ∀ n ∈ BB lam,
      |((omegaS S n : ℝ) - δ * LL b lam) - Wc b ξ K S E lam n| ≤ c2 := by
    filter_upwards [hc1ev, hlarge] with lam hμσ hbig
    intro n hn
    have hn1 : 1 ≤ n := h.mem_pos lam n hn
    have hnb : n ≤ b ^ lam := h.mem_le lam n hn
    have hy0 : (0:ℝ) ≤ ytr b ξ K lam := ytr_nonneg hb
    obtain ⟨hlo, hhi⟩ := omegaS_sub_omegaR_bound (n := n) hn1
      (Qtr b ξ K S E lam) (fun ℓ => mem_Qset_iff hy0)
    have hcount := hbig n hn1 hnb
    have hμDL := hμσ.1
    rw [abs_le] at hμDL
    have hdecomp : ((omegaS S n : ℝ) - δ * LL b lam) - Wc b ξ K S E lam n
        = ((omegaS S n : ℝ) - (omegaR (Qtr b ξ K S E lam) n : ℝ))
          + (muR (Qtr b ξ K S E lam) - δ * LL b lam) := by
      unfold Wc
      ring
    rw [hdecomp]
    have hcast1 : (omegaR (Qtr b ξ K S E lam) n : ℝ) ≤ (omegaS S n : ℝ) := by
      exact_mod_cast hlo
    have hcast2 : (omegaS S n : ℝ) ≤ (omegaR (Qtr b ξ K S E lam) n : ℝ)
        + (E.card : ℝ)
        + ((n.primeFactors.filter fun ℓ : ℕ => ytr b ξ K lam < (ℓ:ℝ)).card : ℝ) := by
      exact_mod_cast hhi
    rw [abs_le]
    constructor
    · have h2 : (0:ℝ) ≤ 2 * (K:ℝ) / ξ := div_nonneg (by positivity) h.xi_pos.le
      rw [hc2def]
      linarith
    · rw [hc2def]
      linarith
  -- expansion of the average via the binomial theorem
  have hexp : ∀ lam : ℕ,
      avg (BB lam) (fun n => (((omegaS S n : ℝ) - δ * LL b lam) / sdl b δ lam) ^ k)
      = ∑ j ∈ Finset.range (k+1),
          (avg (BB lam) (fun n => Wc b ξ K S E lam n ^ j
            * (((omegaS S n : ℝ) - δ * LL b lam) - Wc b ξ K S E lam n) ^ (k - j)
            * (Nat.choose k j : ℝ)) / sdl b δ lam ^ k) := by
    intro lam
    have hpt : ∀ n : ℕ, (((omegaS S n : ℝ) - δ * LL b lam) / sdl b δ lam) ^ k
        = (∑ j ∈ Finset.range (k+1), Wc b ξ K S E lam n ^ j
            * (((omegaS S n : ℝ) - δ * LL b lam) - Wc b ξ K S E lam n) ^ (k - j)
            * (Nat.choose k j : ℝ)) / sdl b δ lam ^ k := by
      intro n
      rw [div_pow]
      congr 1
      have hbin := add_pow (Wc b ξ K S E lam n)
        (((omegaS S n : ℝ) - δ * LL b lam) - Wc b ξ K S E lam n) k
      rw [show Wc b ξ K S E lam n
          + (((omegaS S n : ℝ) - δ * LL b lam) - Wc b ξ K S E lam n)
          = ((omegaS S n : ℝ) - δ * LL b lam) by ring] at hbin
      exact hbin
    calc avg (BB lam) (fun n => (((omegaS S n : ℝ) - δ * LL b lam) / sdl b δ lam) ^ k)
        = (∑ n ∈ BB lam, (∑ j ∈ Finset.range (k+1), Wc b ξ K S E lam n ^ j
            * (((omegaS S n : ℝ) - δ * LL b lam) - Wc b ξ K S E lam n) ^ (k - j)
            * (Nat.choose k j : ℝ)) / sdl b δ lam ^ k) / ((BB lam).card : ℝ) := by
          unfold avg
          congr 1
          exact Finset.sum_congr rfl fun n _ => hpt n
      _ = (∑ j ∈ Finset.range (k+1), ∑ n ∈ BB lam, Wc b ξ K S E lam n ^ j
            * (((omegaS S n : ℝ) - δ * LL b lam) - Wc b ξ K S E lam n) ^ (k - j)
            * (Nat.choose k j : ℝ)) / sdl b δ lam ^ k / ((BB lam).card : ℝ) := by
          rw [← Finset.sum_div, Finset.sum_comm]
      _ = ∑ j ∈ Finset.range (k+1),
          (avg (BB lam) (fun n => Wc b ξ K S E lam n ^ j
            * (((omegaS S n : ℝ) - δ * LL b lam) - Wc b ξ K S E lam n) ^ (k - j)
            * (Nat.choose k j : ℝ)) / sdl b δ lam ^ k) := by
          unfold avg
          rw [Finset.sum_div, Finset.sum_div]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [div_div, div_div, mul_comm (sdl b δ lam ^ k) (((BB lam).card : ℝ))]
  -- limit of each binomial term
  have hterm : ∀ j ∈ Finset.range (k+1),
      Tendsto (fun lam : ℕ =>
        avg (BB lam) (fun n => Wc b ξ K S E lam n ^ j
          * (((omegaS S n : ℝ) - δ * LL b lam) - Wc b ξ K S E lam n) ^ (k - j)
          * (Nat.choose k j : ℝ)) / sdl b δ lam ^ k)
        atTop (𝓝 (if j = k then normalMoment k else 0)) := by
    intro j hj
    rw [Finset.mem_range] at hj
    by_cases hjk : j = k
    · subst hjk
      simp only [Nat.sub_self, pow_zero, Nat.choose_self, Nat.cast_one, mul_one, if_pos rfl]
      exact Wc_moment_limit h hS hK (by omega : j ≤ K)
    · rw [if_neg hjk]
      have hjk' : j < k := by omega
      -- bound: |term| ≤ C(k,j)·c2^{k-j}·(avg|W|^j/SD^j)·(1/SD)^{k-j}
      obtain ⟨D, hD0, hDev⟩ := Wc_abs_moment_bound h hS hK
        (m := j) (by omega : 2 * j ≤ K)
      have hg : Tendsto (fun lam : ℕ =>
          (Nat.choose k j : ℝ) * c2 ^ (k-j) * D * (1 / sdl b δ lam) ^ (k-j))
          atTop (𝓝 0) := by
        have h1 : Tendsto (fun lam : ℕ => (1 / sdl b δ lam) ^ (k-j)) atTop (𝓝 0) := by
          have h2 := (tendsto_const_div_sdl hb hδ0 1).pow (k-j)
          rwa [zero_pow (by omega : k - j ≠ 0)] at h2
        have h3 := h1.const_mul ((Nat.choose k j : ℝ) * c2 ^ (k-j) * D)
        rw [mul_zero] at h3
        refine h3.congr fun lam => ?_
        ring
      refine squeeze_zero_norm' ?_ hg
      filter_upwards [hΔbound, hDev, h.nonempty,
        (tendsto_deltaLL_atTop hb hδ0).eventually_ge_atTop 1] with lam hΔ hD hne hDL1
      have hN : (0:ℝ) < ((BB lam).card : ℝ) := by
        exact_mod_cast Finset.card_pos.mpr hne
      have hSD1 : (1:ℝ) ≤ sdl b δ lam := by
        unfold sdl
        rw [show (1:ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
        exact Real.sqrt_le_sqrt (by linarith)
      have hSDpos : (0:ℝ) < sdl b δ lam := by linarith
      rw [Real.norm_eq_abs]
      -- pointwise bound on the average
      have hptw : |avg (BB lam) (fun n => Wc b ξ K S E lam n ^ j
          * (((omegaS S n : ℝ) - δ * LL b lam) - Wc b ξ K S E lam n) ^ (k - j)
          * (Nat.choose k j : ℝ))|
          ≤ (Nat.choose k j : ℝ) * c2 ^ (k-j)
            * avg (BB lam) (fun n => |Wc b ξ K S E lam n| ^ j) := by
        unfold avg
        rw [abs_div, abs_of_pos hN, div_le_iff₀ hN]
        have h6 : (Nat.choose k j : ℝ) * c2 ^ (k-j)
            * ((∑ n ∈ BB lam, |Wc b ξ K S E lam n| ^ j) / ((BB lam).card : ℝ))
            * ((BB lam).card : ℝ)
            = (Nat.choose k j : ℝ) * c2 ^ (k-j)
              * ∑ n ∈ BB lam, |Wc b ξ K S E lam n| ^ j := by
          field_simp
        rw [h6]
        calc |∑ n ∈ BB lam, Wc b ξ K S E lam n ^ j
              * (((omegaS S n : ℝ) - δ * LL b lam) - Wc b ξ K S E lam n) ^ (k - j)
              * (Nat.choose k j : ℝ)|
            ≤ ∑ n ∈ BB lam, |Wc b ξ K S E lam n ^ j
              * (((omegaS S n : ℝ) - δ * LL b lam) - Wc b ξ K S E lam n) ^ (k - j)
              * (Nat.choose k j : ℝ)| := Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ n ∈ BB lam, |Wc b ξ K S E lam n| ^ j * c2 ^ (k-j)
              * (Nat.choose k j : ℝ) := by
              refine Finset.sum_le_sum fun n hn => ?_
              rw [abs_mul, abs_mul, abs_pow, abs_pow]
              have h4 : |((omegaS S n : ℝ) - δ * LL b lam) - Wc b ξ K S E lam n| ^ (k-j)
                  ≤ c2 ^ (k-j) :=
                pow_le_pow_left' (abs_nonneg _) (hΔ n hn) (k-j)
              have h5 : |(Nat.choose k j : ℝ)| = (Nat.choose k j : ℝ) :=
                abs_of_nonneg (by positivity)
              rw [h5]
              refine mul_le_mul_of_nonneg_right ?_ (by positivity)
              exact mul_le_mul_of_nonneg_left h4 (by positivity)
          _ = (Nat.choose k j : ℝ) * c2 ^ (k-j)
              * ∑ n ∈ BB lam, |Wc b ξ K S E lam n| ^ j := by
              rw [← Finset.sum_mul, ← Finset.sum_mul]
              ring
      -- divide by SD^k and compare with the vanishing bound
      have hSDk : sdl b δ lam ^ k = sdl b δ lam ^ j * sdl b δ lam ^ (k-j) := by
        rw [← pow_add]
        congr 1
        omega
      have hSDkpos : (0:ℝ) < sdl b δ lam ^ k := by positivity
      rw [abs_div, abs_of_pos hSDkpos]
      calc |avg (BB lam) (fun n => Wc b ξ K S E lam n ^ j
            * (((omegaS S n : ℝ) - δ * LL b lam) - Wc b ξ K S E lam n) ^ (k - j)
            * (Nat.choose k j : ℝ))| / sdl b δ lam ^ k
          ≤ ((Nat.choose k j : ℝ) * c2 ^ (k-j)
              * avg (BB lam) (fun n => |Wc b ξ K S E lam n| ^ j)) / sdl b δ lam ^ k :=
            div_le_div_of_le' hSDkpos hptw
        _ = (Nat.choose k j : ℝ) * c2 ^ (k-j)
            * (avg (BB lam) (fun n => |Wc b ξ K S E lam n| ^ j) / sdl b δ lam ^ j)
            * (1 / sdl b δ lam) ^ (k-j) := by
            rw [hSDk, one_div_pow]
            ring
        _ ≤ (Nat.choose k j : ℝ) * c2 ^ (k-j) * D * (1 / sdl b δ lam) ^ (k-j) := by
            refine mul_le_mul_of_nonneg_right ?_ (by positivity)
            exact mul_le_mul_of_nonneg_left hD (by positivity)
  -- assemble the sum of limits
  have hsum := tendsto_finset_sum (Finset.range (k+1)) hterm
  have hval : (∑ j ∈ Finset.range (k+1), if j = k then normalMoment k else 0)
      = normalMoment k := by
    rw [Finset.sum_ite_eq' (Finset.range (k+1)) k (fun _ => normalMoment k)]
    rw [if_pos (Finset.mem_range.mpr (by omega))]
  rw [← hval]
  refine hsum.congr fun lam => ?_
  exact (hexp lam).symm

end EKRev
