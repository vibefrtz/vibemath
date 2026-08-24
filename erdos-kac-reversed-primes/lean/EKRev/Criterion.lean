/-
EKRev/Criterion.lean

The conclusions of Proposition 2.1:

* `criterion_EK_omega`  — display (2.5) for `ω_S`, pointwise in `t`
  (method of moments, [Bil, Thm. 30.2]);
* `criterion_EK_Omega`  — display (2.5) for `Ω_S`, under hypothesis (iii)
  (the sandwich argument at the end of the proof of Prop. 2.1, with
  Markov's inequality and the Lipschitz bound `Φ' ≤ (2π)^{-1/2}`);
* `tendsto_uniform_of_mono` — the Pólya-type upgrade to uniformity in `t`
  ("uniformly in t because Φ is continuous");
* uniform versions of both conclusions.

Everything here is proved from the axioms of `Cited.lean`; no new axioms.
-/
import Mathlib.Tactic
import EKRev.CritMoments

namespace EKRev

open Finset Filter Real Topology

variable {b : ℕ} {ξ δ : ℝ} {S : Set ℕ} {E : Finset ℕ} {BB : ℕ → Finset ℕ}

/-! ### The conclusion for `ω_S` -/

/-- Proposition 2.1, conclusion (2.5) for `ω_S`, pointwise in `t`. -/
theorem criterion_EK_omega (h : CritHyps b BB E ξ) (hS : IsRegular S δ) (t : ℝ) :
    Tendsto (fun lam : ℕ =>
      (((BB lam).filter fun n => (omegaS S n : ℝ) ≤ δ * LL b lam
          + t * Real.sqrt (δ * LL b lam)).card : ℝ) / ((BB lam).card : ℝ))
      atTop (𝓝 (Phi t)) := by
  set K := 2 * 0 + 1 with hKdef  -- any K works for the moments; they use their own
  have hMM := method_of_moments BB
    (fun lam n => ((omegaS S n : ℝ) - δ * LL b lam) / sdl b δ lam)
    h.nonempty (fun k => criterion_moments h hS k) t
  refine hMM.congr' ?_
  filter_upwards [(tendsto_sdl_atTop h.b_ge hS.delta_pos).eventually_gt_atTop 0]
    with lam hSD
  have hset : (BB lam).filter
      (fun n => ((omegaS S n : ℝ) - δ * LL b lam) / sdl b δ lam ≤ t)
      = (BB lam).filter (fun n => (omegaS S n : ℝ) ≤ δ * LL b lam
          + t * Real.sqrt (δ * LL b lam)) := by
    refine Finset.filter_congr fun n _ => ?_
    rw [div_le_iff₀ hSD]
    unfold sdl
    constructor <;> intro h1 <;> linarith
  unfold edf
  rw [hset]

/-! ### The sandwich for `Ω_S` -/

private lemma bigOmegaS_sub_omegaS_le (S : Set ℕ) (n : ℕ) :
    (bigOmegaS S n : ℝ) - (omegaS S n : ℝ) ≤ (bigOmega n : ℝ) - (smallOmega n : ℝ) := by
  have h1 := bigOmegaS_eq S n
  have h2 := bigOmegaS_eq Set.univ n
  have h3 := excessS_le S n
  have h4 := excessS_univ n
  have h5 : omegaS Set.univ n = smallOmega n := by
    unfold omegaS smallOmega
    congr 1
    ext ℓ
    simp only [Finset.mem_filter, Set.mem_univ, and_true]
  have h6 : bigOmegaS Set.univ n = bigOmega n := by
    unfold bigOmegaS bigOmega
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext ℓ
    simp only [Finset.mem_filter, Set.mem_univ, and_true]
  have h7 : (bigOmegaS S n : ℝ) - (omegaS S n : ℝ) = (excessS S n : ℝ) := by
    rw [h1]
    push_cast
    ring
  have h8 : (bigOmega n : ℝ) - (smallOmega n : ℝ) = (excessS Set.univ n : ℝ) := by
    rw [← h6, ← h5, h2]
    push_cast
    ring
  rw [h7, h8]
  exact_mod_cast h3

private lemma omegaS_le_bigOmegaS (S : Set ℕ) (n : ℕ) :
    omegaS S n ≤ bigOmegaS S n := by
  rw [bigOmegaS_eq S n]
  omega

set_option maxHeartbeats 1000000 in
/-- Proposition 2.1, conclusion (2.5) for `Ω_S`, under hypothesis (iii)
(the sandwich at the end of the proof of Prop. 2.1). -/
theorem criterion_EK_Omega (h : CritHyps b BB E ξ) (hS : IsRegular S δ)
    (hΩ : OmegaHyp BB) (t : ℝ) :
    Tendsto (fun lam : ℕ =>
      (((BB lam).filter fun n => (bigOmegaS S n : ℝ) ≤ δ * LL b lam
          + t * Real.sqrt (δ * LL b lam)).card : ℝ) / ((BB lam).card : ℝ))
      atTop (𝓝 (Phi t)) := by
  obtain ⟨CΩ, hCΩ0, hCΩ⟩ := hΩ
  rw [Metric.tendsto_nhds]
  intro ε hε
  set τ : ℝ := ε * Real.sqrt (2 * Real.pi) / 4 with hτdef
  have h2π := sqrt_two_pi_pos
  have hτ0 : 0 < τ := by
    rw [hτdef]
    positivity
  have hPhiτ : Phi t - Phi (t - τ) ≤ ε / 4 := by
    have h1 := Phi_sub_Phi_le (by linarith : t - τ ≤ t)
    have h2 : (t - (t - τ)) / Real.sqrt (2 * Real.pi) = ε / 4 := by
      rw [hτdef]
      field_simp
      ring
    linarith [h1, h2.le, h2.ge]
  have hω1 := (Metric.tendsto_nhds.mp (criterion_EK_omega h hS t)) (ε/4) (by linarith)
  have hω2 := (Metric.tendsto_nhds.mp (criterion_EK_omega h hS (t - τ))) (ε/4)
    (by linarith)
  have hηlim : Tendsto (fun lam : ℕ => (CΩ / τ) / sdl b δ lam) atTop (𝓝 0) :=
    tendsto_const_div_sdl h.b_ge hS.delta_pos (CΩ / τ)
  have hη := hηlim.eventually_le_const (by linarith : (0:ℝ) < ε/4)
  filter_upwards [hω1, hω2, hη, h.nonempty,
    (tendsto_sdl_atTop h.b_ge hS.delta_pos).eventually_gt_atTop 0, hCΩ]
    with lam hd1 hd2 hηb hne hSD hsum
  rw [Real.dist_eq] at hd1 hd2 ⊢
  have hN : (0:ℝ) < ((BB lam).card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hne
  set SD := Real.sqrt (δ * LL b lam) with hSDdef
  have hSD' : sdl b δ lam = SD := rfl
  rw [hSD'] at hSD hηb
  set c : ℝ := δ * LL b lam + t * SD with hcdef
  set AΩ := (BB lam).filter (fun n => (bigOmegaS S n : ℝ) ≤ c) with hAΩ
  set Aω := (BB lam).filter (fun n => (omegaS S n : ℝ) ≤ c) with hAω
  set Aω' := (BB lam).filter (fun n => (omegaS S n : ℝ) ≤ δ * LL b lam + (t - τ) * SD)
    with hAω'
  set Exc := (BB lam).filter
    (fun n => τ * SD < (bigOmegaS S n : ℝ) - (omegaS S n : ℝ)) with hExc
  -- (i) upper: AΩ ⊆ Aω
  have hup : AΩ ⊆ Aω := by
    intro n hn
    rw [hAΩ, Finset.mem_filter] at hn
    rw [hAω, Finset.mem_filter]
    refine ⟨hn.1, ?_⟩
    have := omegaS_le_bigOmegaS S n
    have hcast : (omegaS S n : ℝ) ≤ (bigOmegaS S n : ℝ) := by exact_mod_cast this
    linarith [hn.2]
  -- (ii) lower: Aω' ⊆ AΩ ∪ Exc
  have hlow : Aω' ⊆ AΩ ∪ Exc := by
    intro n hn
    rw [hAω', Finset.mem_filter] at hn
    by_cases hcase : (bigOmegaS S n : ℝ) - (omegaS S n : ℝ) ≤ τ * SD
    · refine Finset.mem_union_left _ ?_
      rw [hAΩ, Finset.mem_filter]
      refine ⟨hn.1, ?_⟩
      rw [hcdef]
      have := hn.2
      nlinarith [this, hcase]
    · refine Finset.mem_union_right _ ?_
      rw [hExc, Finset.mem_filter]
      push_neg at hcase
      exact ⟨hn.1, hcase⟩
  -- (iii) the exceptional set is small: #Exc · τ·SD ≤ CΩ · N
  have hexc : (Exc.card : ℝ) * (τ * SD) ≤ CΩ * ((BB lam).card : ℝ) := by
    have h1 : ∀ n ∈ Exc, τ * SD ≤ (bigOmegaS S n : ℝ) - (omegaS S n : ℝ) := by
      intro n hn
      rw [hExc, Finset.mem_filter] at hn
      exact hn.2.le
    have h2 : (Exc.card : ℝ) * (τ * SD)
        ≤ ∑ n ∈ Exc, ((bigOmegaS S n : ℝ) - (omegaS S n : ℝ)) := by
      have h3 := Finset.card_nsmul_le_sum Exc
        (fun n => (bigOmegaS S n : ℝ) - (omegaS S n : ℝ)) (τ * SD) h1
      rwa [nsmul_eq_mul] at h3
    have h4 : ∑ n ∈ Exc, ((bigOmegaS S n : ℝ) - (omegaS S n : ℝ))
        ≤ ∑ n ∈ BB lam, ((bigOmegaS S n : ℝ) - (omegaS S n : ℝ)) := by
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
      · rw [hExc]
        exact Finset.filter_subset _ _
      · intro n _ _
        have := omegaS_le_bigOmegaS S n
        have hcast : (omegaS S n : ℝ) ≤ (bigOmegaS S n : ℝ) := by exact_mod_cast this
        linarith
    have h5 : ∑ n ∈ BB lam, ((bigOmegaS S n : ℝ) - (omegaS S n : ℝ))
        ≤ ∑ n ∈ BB lam, ((bigOmega n : ℝ) - (smallOmega n : ℝ)) :=
      Finset.sum_le_sum fun n _ => bigOmegaS_sub_omegaS_le S n
    linarith [hsum]
  have hexcN : (Exc.card : ℝ) / ((BB lam).card : ℝ) ≤ ε / 4 := by
    have hτSD : (0:ℝ) < τ * SD := by positivity
    have h6 : (Exc.card : ℝ) ≤ CΩ * ((BB lam).card : ℝ) / (τ * SD) := by
      rw [le_div_iff₀ hτSD]
      exact hexc
    have h7 : (Exc.card : ℝ) / ((BB lam).card : ℝ) ≤ CΩ / (τ * SD) := by
      rw [div_le_div_iff₀ hN hτSD]
      calc (Exc.card : ℝ) * (τ * SD) ≤ CΩ * ((BB lam).card : ℝ) := hexc
        _ = CΩ * ((BB lam).card : ℝ) := rfl
    refine le_trans h7 ?_
    calc CΩ / (τ * SD) = (CΩ / τ) / SD := by rw [div_div]
      _ ≤ ε / 4 := hηb
  -- combine
  set FΩ := (AΩ.card : ℝ) / ((BB lam).card : ℝ) with hFΩ
  set Fω := (Aω.card : ℝ) / ((BB lam).card : ℝ) with hFω
  set Fω' := (Aω'.card : ℝ) / ((BB lam).card : ℝ) with hFω'
  have hupF : FΩ ≤ Fω := by
    rw [hFΩ, hFω]
    exact div_le_div_of_le' hN (by exact_mod_cast Finset.card_le_card hup)
  have hlowF : Fω' ≤ FΩ + (Exc.card : ℝ) / ((BB lam).card : ℝ) := by
    rw [hFω', hFΩ, ← add_div]
    refine div_le_div_of_le' hN ?_
    have h8 := Finset.card_le_card hlow
    have h9 := Finset.card_union_le AΩ Exc
    have : (Aω'.card : ℝ) ≤ ((AΩ ∪ Exc).card : ℝ) := by exact_mod_cast h8
    have h10 : ((AΩ ∪ Exc).card : ℝ) ≤ (AΩ.card : ℝ) + (Exc.card : ℝ) := by
      exact_mod_cast h9
    linarith
  -- hd1 : |Fω − Φ t| < ε/4 ; hd2 : |Fω' − Φ(t−τ)| < ε/4
  have hd1' : |Fω - Phi t| < ε/4 := hd1
  have hd2' : |Fω' - Phi (t - τ)| < ε/4 := hd2
  rw [abs_lt] at hd1' hd2' ⊢
  constructor
  · -- Φ t − FΩ < ε: FΩ ≥ Fω' − Exc/N > Φ(t−τ) − ε/4 − ε/4 ≥ Φ t − 3ε/4
    have := hPhiτ
    nlinarith [hlowF, hd2'.1, hexcN]
  · -- FΩ − Φ t < ε
    nlinarith [hupF, hd1'.2]

/-! ### Uniformity in `t` (Pólya) -/

set_option maxHeartbeats 1600000 in
/-- Pólya-type uniformity: monotone functions `F_λ` with values in `[0,1]`
converging pointwise to `Φ` converge uniformly ("uniformly in `t` because `Φ`
is continuous", end of the proof of Prop. 2.1). -/
theorem tendsto_uniform_of_mono (F : ℕ → ℝ → ℝ)
    (hmono : ∀ lam, Monotone (F lam))
    (h0 : ∀ lam t, 0 ≤ F lam t) (h1 : ∀ lam t, F lam t ≤ 1)
    (hpt : ∀ t : ℝ, Tendsto (fun lam => F lam t) atTop (𝓝 (Phi t))) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ lam : ℕ in atTop, ∀ t : ℝ, |F lam t - Phi t| ≤ ε := by
  intro ε hε
  have h2π := sqrt_two_pi_pos
  obtain ⟨T1, hT1⟩ := (Filter.eventually_atBot).mp
    (tendsto_Phi_atBot.eventually_le_const (by linarith : (0:ℝ) < ε/4))
  obtain ⟨T2', hT2⟩ := (Filter.eventually_atTop).mp
    (tendsto_Phi_atTop.eventually_const_le (by linarith : 1 - ε/4 < 1))
  set step : ℝ := ε * Real.sqrt (2 * Real.pi) / 4 with hstep
  have hstep0 : 0 < step := by
    rw [hstep]
    positivity
  set T2 := max T2' (T1 + step) with hT2def
  have hT2ge : T2' ≤ T2 := le_max_left _ _
  have hT12 : T1 + step ≤ T2 := le_max_right _ _
  set M := ⌈(T2 - T1) / step⌉₊ with hM
  have hM1 : 1 ≤ M := by
    rw [hM]
    refine Nat.one_le_ceil_iff.mpr ?_
    have hnum : step ≤ T2 - T1 := by linarith
    exact div_pos (by linarith) hstep0
  have hgrid : T2 ≤ T1 + M * step := by
    have hce := Nat.le_ceil ((T2 - T1) / step)
    rw [← hM] at hce
    rw [div_le_iff₀ hstep0] at hce
    linarith
  have hev : ∀ᶠ lam : ℕ in atTop, ∀ i ∈ Finset.range (M+1),
      |F lam (T1 + (i:ℝ) * step) - Phi (T1 + (i:ℝ) * step)| ≤ ε/4 := by
    rw [Filter.eventually_all_finset]
    intro i _
    have h4 := Metric.tendsto_nhds.mp (hpt (T1 + (i:ℝ) * step)) (ε/4) (by linarith)
    filter_upwards [h4] with lam h5
    rw [Real.dist_eq] at h5
    linarith
  filter_upwards [hev] with lam hg
  intro t
  rcases lt_or_ge t T1 with hcase | hcase
  · -- t < T1 : both F and Φ are ≤ ε/2 here
    have hF : F lam t ≤ F lam T1 := hmono lam hcase.le
    have hg0 := hg 0 (Finset.mem_range.mpr (by omega))
    simp only [Nat.cast_zero, zero_mul, add_zero] at hg0
    have hΦT1 : Phi T1 ≤ ε/4 := hT1 T1 le_rfl
    have hΦt : Phi t ≤ ε/4 := le_trans (Phi_mono hcase.le) hΦT1
    rw [abs_le] at hg0 ⊢
    constructor
    · linarith [h0 lam t, hΦt]
    · linarith [Phi_nonneg t, hΦT1, hF, hg0.2]
  · rcases le_or_gt t (T1 + M * step) with hcase2 | hcase2
    · -- grid range
      set i := min ⌊(t - T1) / step⌋₊ (M - 1) with hi
      have hiM : i + 1 ≤ M := by
        rw [hi]
        have := min_le_right ⌊(t - T1) / step⌋₊ (M - 1)
        omega
      have hile : (i : ℝ) ≤ (t - T1)/step := by
        have h7 : ((min ⌊(t - T1) / step⌋₊ (M-1) : ℕ) : ℝ)
            ≤ ((⌊(t - T1) / step⌋₊ : ℕ) : ℝ) := by
          exact_mod_cast min_le_left _ _
        rw [hi]
        refine le_trans h7 ?_
        exact Nat.floor_le (div_nonneg (by linarith) hstep0.le)
      have hlow : T1 + (i:ℝ) * step ≤ t := by
        have h8 : (i:ℝ) * step ≤ t - T1 := by
          calc (i:ℝ) * step ≤ ((t - T1)/step) * step :=
                mul_le_mul_of_nonneg_right hile hstep0.le
            _ = t - T1 := div_mul_cancel₀ _ (ne_of_gt hstep0)
        linarith
      have hhigh : t ≤ T1 + ((i:ℝ)+1) * step := by
        rcases le_or_gt (M-1 : ℕ) ⌊(t - T1)/step⌋₊ with hmin | hmin
        · have hieq : i = M - 1 := by
            rw [hi, min_eq_right hmin]
          have hcast : ((i:ℝ)+1) = (M:ℝ) := by
            rw [hieq]
            have h9 : ((M - 1 : ℕ) : ℝ) = (M:ℝ) - 1 := by
              have : (1:ℕ) ≤ M := hM1
              push_cast [Nat.cast_sub this]
              ring
            rw [h9]
            ring
          rw [hcast]
          exact hcase2
        · have hieq : i = ⌊(t - T1)/step⌋₊ := by
            rw [hi, min_eq_left hmin.le]
          have h9 : (t - T1)/step < (⌊(t - T1)/step⌋₊ : ℝ) + 1 :=
            Nat.lt_floor_add_one _
          have h10 : t - T1 < ((⌊(t-T1)/step⌋₊ : ℝ) + 1) * step := by
            rw [← div_lt_iff₀ hstep0]
            exact h9
          rw [hieq]
          linarith
      have hgi := hg i (Finset.mem_range.mpr (by omega))
      have hgi1 := hg (i+1) (Finset.mem_range.mpr (by omega))
      have hcast1 : ((i+1 : ℕ) : ℝ) = (i:ℝ) + 1 := by push_cast; ring
      rw [hcast1] at hgi1
      rw [abs_le] at hgi hgi1 ⊢
      have hile2 : T1 + (i:ℝ) * step ≤ T1 + ((i:ℝ)+1) * step := by nlinarith [hstep0.le]
      have hΦgap : Phi (T1 + ((i:ℝ)+1)*step) - Phi (T1 + (i:ℝ)*step) ≤ ε/4 := by
        have h11 := Phi_sub_Phi_le hile2
        have h12 : ((T1 + ((i:ℝ)+1)*step) - (T1 + (i:ℝ)*step)) / Real.sqrt (2*Real.pi)
            = ε/4 := by
          rw [hstep]
          field_simp
          ring
        linarith [h12.le, h12.ge]
      constructor
      · have hFmono := hmono lam hlow
        have hΦmono := Phi_mono hhigh
        linarith [hgi.1, hΦgap, hFmono, hΦmono]
      · have hFmono := hmono lam hhigh
        have hΦmono := Phi_mono hlow
        linarith [hgi1.2, hΦgap, hFmono, hΦmono]
    · -- t beyond the grid: both F and Φ are ≥ 1 − 3ε/4
      have ht2 : T2 ≤ t := le_trans hgrid hcase2.le
      have hΦT : 1 - ε/4 ≤ Phi T2 := hT2 T2 hT2ge
      have hΦt : 1 - ε/4 ≤ Phi t := le_trans hΦT (Phi_mono ht2)
      have hgM := hg M (Finset.mem_range.mpr (by omega))
      rw [abs_le] at hgM ⊢
      have hΦM : 1 - ε/2 ≤ Phi (T1 + (M:ℝ)*step) := by
        have h13 := Phi_mono hgrid
        linarith [hΦT, hgM.1]
      have hFt : 1 - 3*ε/4 ≤ F lam t := by
        have h14 := hmono lam hcase2.le
        linarith [hgM.1, hΦM]
      constructor
      · linarith [Phi_le_one t, hFt]
      · linarith [h1 lam t, hΦt]

/-! ### Uniform conclusions -/

/-- Proposition 2.1, conclusion for `ω_S`, uniformly in `t`. -/
theorem criterion_EK_omega_uniform (h : CritHyps b BB E ξ) (hS : IsRegular S δ) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ lam : ℕ in atTop, ∀ t : ℝ,
      |(((BB lam).filter fun n => (omegaS S n : ℝ) ≤ δ * LL b lam
          + t * Real.sqrt (δ * LL b lam)).card : ℝ) / ((BB lam).card : ℝ)
        - Phi t| ≤ ε := by
  refine tendsto_uniform_of_mono _ ?_ ?_ ?_ (fun t => criterion_EK_omega h hS t)
  · intro lam s t hst
    rcases Nat.eq_zero_or_pos (BB lam).card with hz | hp
    · simp [hz]
    · have hN : (0:ℝ) < ((BB lam).card : ℝ) := by exact_mod_cast hp
      refine div_le_div_of_le' hN ?_
      have hsub : (BB lam).filter (fun n => (omegaS S n : ℝ) ≤ δ * LL b lam
          + s * Real.sqrt (δ * LL b lam))
          ⊆ (BB lam).filter (fun n => (omegaS S n : ℝ) ≤ δ * LL b lam
          + t * Real.sqrt (δ * LL b lam)) := by
        intro n hn
        rw [Finset.mem_filter] at hn ⊢
        refine ⟨hn.1, ?_⟩
        have hs2 : s * Real.sqrt (δ * LL b lam) ≤ t * Real.sqrt (δ * LL b lam) :=
          mul_le_mul_of_nonneg_right hst (Real.sqrt_nonneg _)
        linarith [hn.2]
      exact_mod_cast Finset.card_le_card hsub
  · intro lam t
    positivity
  · intro lam t
    rcases Nat.eq_zero_or_pos (BB lam).card with hz | hp
    · simp [hz]
    · have hN : (0:ℝ) < ((BB lam).card : ℝ) := by exact_mod_cast hp
      rw [div_le_one hN]
      exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)

/-- Proposition 2.1, conclusion for `Ω_S`, uniformly in `t`. -/
theorem criterion_EK_Omega_uniform (h : CritHyps b BB E ξ) (hS : IsRegular S δ)
    (hΩ : OmegaHyp BB) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ lam : ℕ in atTop, ∀ t : ℝ,
      |(((BB lam).filter fun n => (bigOmegaS S n : ℝ) ≤ δ * LL b lam
          + t * Real.sqrt (δ * LL b lam)).card : ℝ) / ((BB lam).card : ℝ)
        - Phi t| ≤ ε := by
  refine tendsto_uniform_of_mono _ ?_ ?_ ?_ (fun t => criterion_EK_Omega h hS hΩ t)
  · intro lam s t hst
    rcases Nat.eq_zero_or_pos (BB lam).card with hz | hp
    · simp [hz]
    · have hN : (0:ℝ) < ((BB lam).card : ℝ) := by exact_mod_cast hp
      refine div_le_div_of_le' hN ?_
      have hsub : (BB lam).filter (fun n => (bigOmegaS S n : ℝ) ≤ δ * LL b lam
          + s * Real.sqrt (δ * LL b lam))
          ⊆ (BB lam).filter (fun n => (bigOmegaS S n : ℝ) ≤ δ * LL b lam
          + t * Real.sqrt (δ * LL b lam)) := by
        intro n hn
        rw [Finset.mem_filter] at hn ⊢
        refine ⟨hn.1, ?_⟩
        have hs2 : s * Real.sqrt (δ * LL b lam) ≤ t * Real.sqrt (δ * LL b lam) :=
          mul_le_mul_of_nonneg_right hst (Real.sqrt_nonneg _)
        linarith [hn.2]
      exact_mod_cast Finset.card_le_card hsub
  · intro lam t
    positivity
  · intro lam t
    rcases Nat.eq_zero_or_pos (BB lam).card with hz | hp
    · simp [hz]
    · have hN : (0:ℝ) < ((BB lam).card : ℝ) := by exact_mod_cast hp
      rw [div_le_one hN]
      exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)

end EKRev
