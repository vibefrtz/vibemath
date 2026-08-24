/-
EKRev/RevHyp.lean

Verification of hypotheses (i)–(ii) of Proposition 2.1 for the reversed
primes `𝒜_{λ,i}` (§4 of the paper):

* `pilam_lower` / `pilam_upper` — Lemma 4.2, first part: from the prime
  number theorem, `π_{λ,i} ≍ b^λ/λ` (lower bound for each fixed leading
  digit `i`; upper bound for `π_λ` from Brun–Titchmarsh);
* `AFam` — the family fed to the criterion, patched to `{1}` at the
  finitely many `λ` where `𝒜_{λ,i}` is empty (the paper's footnote in the
  proof of Theorem 1.2);
* `rev_rem_le` / `rev_drs_package` — Lemma 4.4': the remainder bound from
  [DRS, Thm. 1.3] (`drs_thm13`), for all admissible moduli;
* `revCritHyps` — hypotheses (i)–(ii) of Proposition 2.1 for `AFam`.

Fully proved from the axioms of `Cited.lean`.
-/
import Mathlib.Tactic
import EKRev.PalHyp
import EKRev.PrimeBlocks

namespace EKRev

open Finset Filter Real Topology

variable {b i lam : ℕ}

/-! ### The prime number theorem input (Lemma 4.2, first part) -/

/-- `i·b^{λ-1} → ∞` for `i ≥ 1`, `b ≥ 2`. -/
lemma tendsto_mul_pow_pred (hb : 2 ≤ b) (hi1 : 1 ≤ i) :
    Tendsto (fun lam : ℕ => i * b ^ (lam - 1)) atTop atTop := by
  have hmono : ∀ lam : ℕ, lam ≤ i * b ^ (lam - 1) := by
    intro lam
    rcases Nat.eq_zero_or_pos lam with h | h
    · simp [h]
    · have h1 : lam - 1 < 2 ^ (lam - 1) := Nat.lt_two_pow_self
      have h2 : 2 ^ (lam - 1) ≤ b ^ (lam - 1) := Nat.pow_le_pow_left hb _
      have h3 : b ^ (lam - 1) ≤ i * b ^ (lam - 1) :=
        Nat.le_mul_of_pos_left _ (by omega)
      omega
  exact tendsto_atTop_mono hmono tendsto_id

set_option maxHeartbeats 1000000 in
/-- Lemma 4.2 (lower bound): `π_{λ,i} ≥ κ b^λ/λ` eventually, with
`κ = κ(b) > 0`, for each fixed leading digit `1 ≤ i ≤ b-1`. -/
theorem pilam_lower (hb : 2 ≤ b) (hi1 : 1 ≤ i) (hi2 : i ≤ b - 1) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ᶠ lam : ℕ in atTop,
      κ * (b:ℝ) ^ lam / (lam:ℝ) ≤ ((PLamI b lam i).card : ℝ) := by
  have hbR : (1:ℝ) < (b:ℝ) := by exact_mod_cast (by omega : 1 < b)
  have hb0R : (0:ℝ) < (b:ℝ) := by linarith
  have hlogb : 0 < Real.log b := Real.log_pos hbR
  set ε : ℝ := 1 / (8 * (b:ℝ)) with hεdef
  have hε0 : 0 < ε := by positivity
  have hb2R : (2:ℝ) ≤ (b:ℝ) := by exact_mod_cast hb
  have hε1 : ε ≤ 1 / 16 := by
    rw [hεdef]
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]
    linarith
  refine ⟨1 / (2 * (b:ℝ) * Real.log b), by positivity, ?_⟩
  -- PNT along the two endpoint sequences
  have hx := pnt.comp (tendsto_mul_pow_pred hb hi1)
  have hy := pnt.comp (tendsto_mul_pow_pred hb (show 1 ≤ i + 1 by omega))
  rw [Metric.tendsto_nhds] at hx hy
  have hxe := hx ε hε0
  have hye := hy ε hε0
  -- the logarithm of the lower endpoint grows
  have hlogx : Tendsto (fun lam : ℕ => Real.log ((i * b ^ (lam - 1) : ℕ) : ℝ))
      atTop atTop := by
    refine Real.tendsto_log_atTop.comp ?_
    have := tendsto_mul_pow_pred hb hi1
    exact tendsto_natCast_atTop_atTop.comp this
  filter_upwards [hxe, hye, eventually_ge_atTop 2,
    hlogx.eventually_ge_atTop (1/ε)] with lam hxl hyl hlam2 hlogxl
  simp only [Function.comp] at hxl hyl
  rw [Real.dist_eq] at hxl hyl
  set B : ℕ := b ^ (lam - 1) with hBdef
  have hB1 : 1 ≤ B := Nat.one_le_pow _ _ (by omega)
  set x : ℝ := ((i * B : ℕ) : ℝ) with hxdef
  set y : ℝ := (((i + 1) * B : ℕ) : ℝ) with hydef
  have hx1 : (1:ℝ) ≤ x := by
    rw [hxdef]
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hy2 : (2:ℝ) ≤ y := by
    rw [hydef]
    have : 2 ≤ (i + 1) * B := by nlinarith
    exact_mod_cast this
  have hxy : x ≤ y := by
    rw [hxdef, hydef]
    have : i * B ≤ (i + 1) * B := Nat.mul_le_mul_right _ (by omega)
    exact_mod_cast this
  set Lx : ℝ := Real.log x with hLxdef
  set Ly : ℝ := Real.log y with hLydef
  have hLx0 : 0 < Lx ∨ Lx = 0 := by
    rcases lt_or_eq_of_le (Real.log_nonneg hx1) with h | h
    · exact Or.inl h
    · exact Or.inr h.symm
  have hLxbig : 1/ε ≤ Lx := hlogxl
  have hLxpos : 0 < Lx := lt_of_lt_of_le (by positivity) hLxbig
  have hLypos : 0 < Ly := lt_of_lt_of_le hLxpos (Real.log_le_log (by linarith) hxy)
  have hx0 : (0:ℝ) < x := by linarith
  have hy0 : (0:ℝ) < y := by linarith
  -- the PNT estimates, rearranged
  have hpy : ((pic ((i + 1) * B) : ℕ) : ℝ) ≥ (1 - ε) * y / Ly := by
    have h1 : |((pic ((i+1) * B) : ℕ) : ℝ) * Ly / y - 1| < ε := hyl
    have h2 := (abs_lt.mp h1).1
    have h3 : (1 - ε) ≤ ((pic ((i+1) * B) : ℕ) : ℝ) * Ly / y := by linarith
    rw [ge_iff_le, div_le_iff₀ hLypos]
    have h4 := mul_le_mul_of_nonneg_right h3 hy0.le
    rw [div_mul_cancel₀ _ (ne_of_gt hy0)] at h4
    linarith
  have hpx : ((pic (i * B) : ℕ) : ℝ) ≤ (1 + ε) * x / Lx := by
    have h1 : |((pic (i * B) : ℕ) : ℝ) * Lx / x - 1| < ε := hxl
    have h2 := (abs_lt.mp h1).2
    have h3 : ((pic (i * B) : ℕ) : ℝ) * Lx / x ≤ 1 + ε := by linarith
    rw [div_le_iff₀ hx0] at h3
    rw [le_div_iff₀ hLxpos]
    linarith
  -- Ly ≤ (1+ε) Lx
  have hLyLx : Ly ≤ (1 + ε) * Lx := by
    have h1 : Ly - Lx ≤ 1 := by
      have e1 : y = 2 * x * ((i+1:ℝ) / (2*i)) := by
        rw [hxdef, hydef]
        push_cast
        have hi0 : (0:ℝ) < (i:ℝ) := by exact_mod_cast hi1
        field_simp
        try ring
      have h2 : y ≤ 2 * x := by
        rw [e1]
        have hi0 : (0:ℝ) < (i:ℝ) := by exact_mod_cast hi1
        have h3 : (i+1:ℝ) / (2*i) ≤ 1 := by
          rw [div_le_one (by linarith)]
          have : (1:ℝ) ≤ (i:ℝ) := by exact_mod_cast hi1
          linarith
        nlinarith [hx0]
      have h4 : Ly ≤ Real.log 2 + Lx := by
        rw [hLydef, hLxdef]
        calc Real.log y ≤ Real.log (2 * x) := Real.log_le_log hy0 h2
          _ = Real.log 2 + Real.log x := Real.log_mul (by norm_num) (ne_of_gt hx0)
      have h5 : Real.log 2 ≤ 1 := by
        have h6 := Real.exp_one_gt_two -- hmm name check below
        calc Real.log 2 ≤ Real.log (Real.exp 1) :=
              Real.log_le_log (by norm_num) (by linarith)
          _ = 1 := Real.log_exp 1
      linarith
    have h7 : 1 ≤ ε * Lx := by
      have h8 := mul_le_mul_of_nonneg_left hLxbig hε0.le
      rwa [mul_one_div, div_self (ne_of_gt hε0)] at h8
    linarith
  -- the count of the block
  have hblock : ((PLamI b lam i).card : ℝ)
      = ((pic ((i + 1) * B) : ℕ) : ℝ) - ((pic (i * B) : ℕ) : ℝ) := by
    have h1 := pic_add_primesIn_card
      (show i * B ≤ (i+1) * B from Nat.mul_le_mul_right _ (by omega))
    have h2 : PLamI b lam i = primesIn (i * B) ((i+1) * B) := rfl
    rw [h2]
    have hR := congrArg (fun k : ℕ => (k : ℝ)) h1
    push_cast at hR
    linarith
  rw [hblock]
  -- assemble: pic y − pic x ≥ [(1−ε)y − (1+ε)² x]/Ly ≥ B/(2 Ly) ≥ κ b^λ/λ
  have hpx2 : ((pic (i * B) : ℕ) : ℝ) ≤ (1 + ε) * (1 + ε) * x / Ly := by
    calc ((pic (i * B) : ℕ) : ℝ) ≤ (1 + ε) * x / Lx := hpx
      _ ≤ (1 + ε) * (1 + ε) * x / Ly := by
          rw [div_le_div_iff₀ hLxpos hLypos]
          calc (1 + ε) * x * Ly ≤ (1 + ε) * x * ((1 + ε) * Lx) := by
                refine mul_le_mul_of_nonneg_left hLyLx ?_
                have : (0:ℝ) ≤ x := hx0.le
                nlinarith [hε0]
            _ = (1 + ε) * (1 + ε) * x * Lx := by ring
  have hmain : ((pic ((i + 1) * B) : ℕ) : ℝ) - ((pic (i * B) : ℕ) : ℝ)
      ≥ ((B:ℝ) / 2) / Ly := by
    have hix : x = (i:ℝ) * (B:ℝ) := by
      rw [hxdef]
      push_cast
      ring
    have hiy : y = ((i:ℝ) + 1) * (B:ℝ) := by
      rw [hydef]
      push_cast
      ring
    have hnum : (1 - ε) * y - (1 + ε) * (1 + ε) * x ≥ (B:ℝ) / 2 := by
      rw [hix, hiy]
      have hiR : (1:ℝ) ≤ (i:ℝ) := by exact_mod_cast hi1
      have hiRb : (i:ℝ) ≤ (b:ℝ) - 1 := by
        have h1 : (i:ℝ) ≤ ((b - 1 : ℕ):ℝ) := by exact_mod_cast hi2
        have hcast : ((b - 1 : ℕ):ℝ) = (b:ℝ) - 1 := by
          have h1b : (1:ℕ) ≤ b := by omega
          rw [Nat.cast_sub h1b]
          norm_num
        linarith [hcast ▸ h1]
      have hB0R : (0:ℝ) < (B:ℝ) := by
        have : 0 < B := by omega
        exact_mod_cast this
      -- (1−ε)(i+1) − (1+ε)²i = 1 − ε(3i+1+εi) ≥ 1/2 for ε ≤ 1/(8b), i ≤ b−1
      have hεb : ε * (b:ℝ) ≤ 1/8 := by
        rw [hεdef]
        rw [div_mul_eq_mul_div, div_le_div_iff₀ (by linarith) (by norm_num)]
        linarith
      have hεi : ε * (i:ℝ) ≤ 1/8 := by
        have h1 : ε * (i:ℝ) ≤ ε * (b:ℝ) := by
          refine mul_le_mul_of_nonneg_left ?_ hε0.le
          linarith [hiRb]
        linarith
      have hkey : (1 - ε) * ((i:ℝ) + 1) - (1 + ε) * (1 + ε) * (i:ℝ) ≥ 1/2 := by
        have e3 : (1 - ε) * ((i:ℝ) + 1) - (1 + ε) * (1 + ε) * (i:ℝ)
            = 1 - ε * (3 * (i:ℝ) + 1 + ε * (i:ℝ)) := by ring
        have h1 : 3 * (i:ℝ) + 1 + ε * (i:ℝ) ≤ 4 * (b:ℝ) := by
          have : ε * (i:ℝ) ≤ 1 := by linarith
          linarith [hiRb, hb2R]
        have h2 : ε * (3 * (i:ℝ) + 1 + ε * (i:ℝ)) ≤ 1/2 := by
          calc ε * (3 * (i:ℝ) + 1 + ε * (i:ℝ)) ≤ ε * (4 * (b:ℝ)) := by
                refine mul_le_mul_of_nonneg_left h1 hε0.le
            _ = 4 * (ε * (b:ℝ)) := by ring
            _ ≤ 4 * (1/8) := by linarith
            _ = 1/2 := by norm_num
        rw [e3]
        linarith
      have e4 : (1 - ε) * (((i:ℝ) + 1) * (B:ℝ))
            - (1 + ε) * (1 + ε) * ((i:ℝ) * (B:ℝ))
          = ((1 - ε) * ((i:ℝ) + 1) - (1 + ε) * (1 + ε) * (i:ℝ)) * (B:ℝ) := by
        ring
      have h5 := mul_le_mul_of_nonneg_right hkey hB0R.le
      linarith [e4 ▸ h5]
    have h8 : ((pic ((i + 1) * B) : ℕ) : ℝ) - ((pic (i * B) : ℕ) : ℝ)
        ≥ ((1 - ε) * y - (1 + ε) * (1 + ε) * x) / Ly := by
      have h9 : ((1 - ε) * y - (1 + ε) * (1 + ε) * x) / Ly
          = (1 - ε) * y / Ly - (1 + ε) * (1 + ε) * x / Ly := by
        ring
      rw [h9]
      have := hpy
      have := hpx2
      linarith
    calc ((pic ((i + 1) * B) : ℕ) : ℝ) - ((pic (i * B) : ℕ) : ℝ)
        ≥ ((1 - ε) * y - (1 + ε) * (1 + ε) * x) / Ly := h8
      _ ≥ ((B:ℝ) / 2) / Ly := by
          exact div_le_div_of_le' hLypos hnum
  -- Ly ≤ λ log b and B = b^λ / b
  have hLyle : Ly ≤ (lam:ℝ) * Real.log b := by
    rw [hLydef, hydef]
    have h1 : ((i + 1) * B : ℕ) ≤ b ^ lam := by
      rw [hBdef]
      calc (i + 1) * b ^ (lam - 1) ≤ b * b ^ (lam - 1) :=
            Nat.mul_le_mul_right _ (by omega)
        _ = b ^ lam := by
            rw [← pow_succ']
            congr 1
            omega
    calc Real.log (((i + 1) * B : ℕ) : ℝ)
        ≤ Real.log (((b ^ lam : ℕ)) : ℝ) := by
          refine Real.log_le_log (by positivity) ?_
          exact_mod_cast h1
      _ = (lam:ℝ) * Real.log b := by
          push_cast
          exact Real.log_pow (b:ℝ) lam
  have hBval : (B:ℝ) = (b:ℝ) ^ lam / (b:ℝ) := by
    rw [hBdef]
    push_cast
    rw [eq_div_iff (ne_of_gt hb0R), ← pow_succ]
    congr 1
    omega
  have hlamR0 : (0:ℝ) < (lam:ℝ) := by
    have : (0:ℕ) < lam := by omega
    exact_mod_cast this
  calc 1 / (2 * (b:ℝ) * Real.log b) * (b:ℝ) ^ lam / (lam:ℝ)
      ≤ ((B:ℝ) / 2) / Ly := by
        rw [hBval]
        rw [div_le_div_iff₀ hlamR0 hLypos]
        have hpow0 : (0:ℝ) < (b:ℝ) ^ lam := by positivity
        calc 1 / (2 * (b:ℝ) * Real.log b) * (b:ℝ) ^ lam * Ly
            ≤ 1 / (2 * (b:ℝ) * Real.log b) * (b:ℝ) ^ lam
                * ((lam:ℝ) * Real.log b) := by
              refine mul_le_mul_of_nonneg_left hLyle (by positivity)
          _ = (b:ℝ) ^ lam / (b:ℝ) / 2 * (lam:ℝ) := by
              field_simp
              try ring
      _ ≤ ((pic ((i + 1) * B) : ℕ) : ℝ) - ((pic (i * B) : ℕ) : ℝ) := hmain

/-- Chebyshev-type upper bound from Brun–Titchmarsh:
`π_λ ≤ C_u b^λ/λ` eventually. -/
theorem pilam_upper (hb : 2 ≤ b) :
    ∃ Cu : ℝ, 0 ≤ Cu ∧ ∀ᶠ lam : ℕ in atTop,
      ((PLam b lam).card : ℝ) ≤ Cu * (b:ℝ) ^ lam / (lam:ℝ) := by
  obtain ⟨C, hC0, hBT⟩ := brun_titchmarsh
  have hbR : (1:ℝ) < (b:ℝ) := by exact_mod_cast (by omega : 1 < b)
  have hlogb : 0 < Real.log b := Real.log_pos hbR
  refine ⟨2 * C / Real.log b, by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop 2] with lam hlam2
  set B : ℕ := b ^ (lam - 1) with hBdef
  set y : ℕ := b ^ lam - B with hydef
  have hBle : B ≤ b ^ lam := Nat.pow_le_pow_right (by omega) (by omega)
  have h2B : 2 * B ≤ b ^ lam := by
    rw [hBdef]
    calc 2 * b ^ (lam - 1) ≤ b * b ^ (lam - 1) := Nat.mul_le_mul_right _ hb
      _ = b ^ lam := by
          rw [← pow_succ']
          congr 1
          omega
  have hy2 : 2 ≤ y := by
    have hB2 : 2 ≤ B := by
      rw [hBdef]
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (lam - 1) := Nat.pow_le_pow_right (by omega) (by omega)
        _ ≤ b ^ (lam - 1) := Nat.pow_le_pow_left hb _
    omega
  have hsum : B + y = b ^ lam := by omega
  have h1 : ((primesIn B (B + y)).card : ℝ) ≤ C * (y:ℝ) / Real.log (y:ℝ) :=
    hBT B y hy2
  have hPLam : (PLam b lam).card = (primesIn B (B + y)).card := by
    unfold PLam
    rw [hsum]
  rw [hPLam]
  have hyR2 : (2:ℝ) ≤ (y:ℝ) := by exact_mod_cast hy2
  have hlogy0 : 0 < Real.log (y:ℝ) := Real.log_pos (by linarith)
  have hyB : (B:ℝ) ≤ (y:ℝ) := by
    have : B ≤ y := by omega
    exact_mod_cast this
  have hlogyge : ((lam:ℝ) - 1) * Real.log b ≤ Real.log (y:ℝ) := by
    have h2 : Real.log ((B:ℕ):ℝ) ≤ Real.log (y:ℝ) :=
      Real.log_le_log (by positivity) hyB
    have h3 : Real.log ((B:ℕ):ℝ) = ((lam:ℝ) - 1) * Real.log b := by
      rw [hBdef]
      push_cast
      rw [Real.log_pow]
      have hc1 : ((lam - 1 : ℕ):ℝ) = (lam:ℝ) - 1 := by
        have h1l : (1:ℕ) ≤ lam := by omega
        rw [Nat.cast_sub h1l]
        norm_num
      rw [hc1]
    linarith [h3 ▸ h2]
  have hlamR : (2:ℝ) ≤ (lam:ℝ) := by exact_mod_cast hlam2
  have hhalf : (lam:ℝ) / 2 * Real.log b ≤ Real.log (y:ℝ) := by
    have : (lam:ℝ) / 2 ≤ (lam:ℝ) - 1 := by linarith
    nlinarith [hlogb]
  have hyle : (y:ℝ) ≤ (b:ℝ) ^ lam := by
    have : y ≤ b ^ lam := by omega
    calc (y:ℝ) ≤ ((b ^ lam : ℕ):ℝ) := by exact_mod_cast this
      _ = (b:ℝ) ^ lam := by push_cast; rfl
  calc ((primesIn B (B + y)).card : ℝ) ≤ C * (y:ℝ) / Real.log (y:ℝ) := h1
    _ ≤ C * (b:ℝ) ^ lam / ((lam:ℝ) / 2 * Real.log b) := by
        have hd0 : (0:ℝ) < (lam:ℝ) / 2 * Real.log b := by
          have : (0:ℝ) < (lam:ℝ) := by linarith
          positivity
        rw [div_le_div_iff₀ hlogy0 hd0]
        have hnum : C * (y:ℝ) ≤ C * (b:ℝ) ^ lam :=
          mul_le_mul_of_nonneg_left hyle hC0
        have hCy0 : (0:ℝ) ≤ C * (y:ℝ) := mul_nonneg hC0 (by positivity)
        nlinarith [hhalf, hlogy0, hnum, hCy0]
    _ = 2 * C / Real.log b * (b:ℝ) ^ lam / (lam:ℝ) := by
        have hlne : (lam:ℝ) ≠ 0 := by
          have : (0:ℝ) < (lam:ℝ) := by linarith
          linarith
        field_simp
        try ring

/-! ### The patched family `AFam` (the paper's footnote) -/

/-- `𝒜_{λ,i}`, patched to `{1}` at the finitely many `λ` where the set is
empty or `λ = 0`.  Only the eventual behaviour enters the theorems. -/
def AFam (b i : ℕ) (lam : ℕ) : Finset ℕ :=
  if 1 ≤ lam ∧ (ALamI b lam i).Nonempty then ALamI b lam i else {1}

lemma AFam_eventually_eq (hb : 2 ≤ b) (hi1 : 1 ≤ i) (hi2 : i ≤ b - 1) :
    ∀ᶠ lam : ℕ in atTop, AFam b i lam = ALamI b lam i := by
  obtain ⟨κ, hκ0, hev⟩ := pilam_lower hb hi1 hi2
  filter_upwards [hev, eventually_ge_atTop 1] with lam h1 h2
  have hlam0 : (0:ℝ) < (lam:ℝ) := by
    have : (0:ℕ) < lam := by omega
    exact_mod_cast this
  have hpos : (0:ℝ) < ((PLamI b lam i).card : ℝ) := by
    refine lt_of_lt_of_le ?_ h1
    have hb0R : (0:ℝ) < (b:ℝ) := by
      have : (0:ℕ) < b := by omega
      exact_mod_cast this
    positivity
  have hPne : (PLamI b lam i).Nonempty := by
    rw [← Finset.card_pos]
    exact_mod_cast hpos
  have hAne : (ALamI b lam i).Nonempty := hPne.image _
  unfold AFam
  rw [if_pos ⟨h2, hAne⟩]

lemma AFam_card_eventually (hb : 2 ≤ b) (hi1 : 1 ≤ i) (hi2 : i ≤ b - 1) :
    ∀ᶠ lam : ℕ in atTop, (AFam b i lam).card = (PLamI b lam i).card := by
  filter_upwards [AFam_eventually_eq hb hi1 hi2, eventually_ge_atTop 1]
    with lam h1 h2
  rw [h1]
  exact ALamI_card hb h2 (by omega)

/-! ### Lemma 4.4': the remainder bound from [DRS, Thm. 1.3] -/

/-- Two-endpoint estimate: `|r_d(λ)| ≤ 2 sup_z |π̄_λ(z,d,d) - π_λ(z)/d|`
(proof of Lemma 4.4). -/
lemma rev_rem_le (hb : 2 ≤ b) (hlam : 1 ≤ lam) (hi1 : 1 ≤ i) (hi2 : i ≤ b - 1)
    {d : ℕ} (hd : 1 ≤ d) {Bd : ℝ}
    (h1 : |((revCount b lam ((i + 1) * b ^ (lam - 1)) d d : ℕ) : ℝ)
        - ((picLam b lam ((i + 1) * b ^ (lam - 1)) : ℕ) : ℝ) / d| ≤ Bd)
    (h2 : |((revCount b lam (i * b ^ (lam - 1)) d d : ℕ) : ℝ)
        - ((picLam b lam (i * b ^ (lam - 1)) : ℕ) : ℝ) / d| ≤ Bd) :
    |rem (ALamI b lam i) d| ≤ 2 * Bd := by
  have hib : i + 1 ≤ b := by omega
  -- the divisor count over 𝒜_{λ,i} as a difference of revCounts
  have hAcount : (((ALamI b lam i).filter fun n => d ∣ n).card : ℝ)
      = ((revCount b lam ((i + 1) * b ^ (lam - 1)) d d : ℕ) : ℝ)
        - ((revCount b lam (i * b ^ (lam - 1)) d d : ℕ) : ℝ) := by
    have e1 := ALamI_filter_dvd_card hb hlam hib d
    have e2 : ((PLamI b lam i).filter fun p => d ∣ rev b lam p)
        = (PLamI b lam i).filter fun p => rev b lam p % d = d % d := by
      refine Finset.filter_congr fun p _ => ?_
      rw [Nat.mod_self]
      constructor
      · rintro ⟨c, hc⟩
        rw [hc]
        exact Nat.mul_mod_right d c
      · intro h
        exact Nat.dvd_of_mod_eq_zero h
    have e3 := revCount_block hb hlam hi1 hi2 d d
    rw [e1, e2]
    have hR := congrArg (fun k : ℕ => (k : ℝ)) e3
    push_cast at hR
    linarith
  have hAcard : ((ALamI b lam i).card : ℝ)
      = ((picLam b lam ((i + 1) * b ^ (lam - 1)) : ℕ) : ℝ)
        - ((picLam b lam (i * b ^ (lam - 1)) : ℕ) : ℝ) := by
    have e4 := picLam_block hb hlam hi1
    have e5 : (ALamI b lam i).card = (PLamI b lam i).card := ALamI_card hb hlam hib
    rw [e5]
    have hR := congrArg (fun k : ℕ => (k : ℝ)) e4
    push_cast at hR
    linarith
  unfold rem
  rw [hAcount, hAcard]
  have e6 : ((revCount b lam ((i + 1) * b ^ (lam - 1)) d d : ℕ) : ℝ)
        - ((revCount b lam (i * b ^ (lam - 1)) d d : ℕ) : ℝ)
        - (((picLam b lam ((i + 1) * b ^ (lam - 1)) : ℕ) : ℝ)
            - ((picLam b lam (i * b ^ (lam - 1)) : ℕ) : ℝ)) / d
      = (((revCount b lam ((i + 1) * b ^ (lam - 1)) d d : ℕ) : ℝ)
          - ((picLam b lam ((i + 1) * b ^ (lam - 1)) : ℕ) : ℝ) / d)
        - (((revCount b lam (i * b ^ (lam - 1)) d d : ℕ) : ℝ)
          - ((picLam b lam (i * b ^ (lam - 1)) : ℕ) : ℝ) / d) := by
    ring
  rw [e6]
  calc |_ - _| ≤ |((revCount b lam ((i + 1) * b ^ (lam - 1)) d d : ℕ) : ℝ)
          - ((picLam b lam ((i + 1) * b ^ (lam - 1)) : ℕ) : ℝ) / d|
        + |((revCount b lam (i * b ^ (lam - 1)) d d : ℕ) : ℝ)
          - ((picLam b lam (i * b ^ (lam - 1)) : ℕ) : ℝ) / d| := abs_sub _ _
    _ ≤ Bd + Bd := add_le_add h1 h2
    _ = 2 * Bd := by ring

/-- Lemma 4.4', packaged: a level `0 < ξ ≤ 1/2` and constants `c > 0`,
`C ≥ 0` with, eventually in `λ`, a bound function `Bnd` dominating
`|r_d(λ)|` at all admissible moduli, whose sum over admissible moduli is
`≤ C·b^{λ-c√λ}`. -/
theorem rev_drs_package (hb : 2 ≤ b) (hi1 : 1 ≤ i) (hi2 : i ≤ b - 1) :
    ∃ ξ : ℝ, 0 < ξ ∧ ξ ≤ 1/2 ∧
      ∃ c C : ℝ, 0 < c ∧ 0 ≤ C ∧
        ∀ᶠ lam : ℕ in atTop,
          ∃ Bnd : ℕ → ℝ,
            (∀ d, 0 ≤ Bnd d) ∧
            (∀ d, 1 ≤ d → Nat.Coprime d (b ^ 3 - b) →
              (d : ℝ) ≤ (b : ℝ) ^ (ξ * (lam : ℝ)) →
              |rem (ALamI b lam i) d| ≤ 2 * Bnd d) ∧
            ((∑ d ∈ (Finset.Icc 1 (b ^ lam)).filter
                (fun d => Nat.Coprime d (b ^ 3 - b)
                  ∧ (d : ℝ) ≤ (b : ℝ) ^ (ξ * (lam : ℝ))), Bnd d)
              ≤ C * (b:ℝ) ^ ((lam:ℝ) - c * Real.sqrt (lam:ℝ))) := by
  obtain ⟨ξ0, hξ00, hdrs⟩ := drs_thm13 b hb
  set ξ : ℝ := min (ξ0/2) (1/2) with hξdef
  have hξ0 : 0 < ξ := lt_min (by linarith) (by norm_num)
  have hξξ0 : ξ < ξ0 := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  obtain ⟨c, C, hc0, hC0, lam0, hlam0⟩ := hdrs ξ hξ0 hξξ0
  refine ⟨ξ, hξ0, min_le_right _ _, c, C, hc0, hC0, ?_⟩
  rw [Filter.eventually_atTop]
  refine ⟨max lam0 1, fun lam hlam => ?_⟩
  have hlamlam0 : lam0 ≤ lam := le_trans (le_max_left _ _) hlam
  have hlam1 : 1 ≤ lam := le_trans (le_max_right _ _) hlam
  obtain ⟨Bnd, hB0, hBptw, hBsum⟩ := hlam0 lam hlamlam0
  have hbmul : b * (b ^ 2 - 1) = b ^ 3 - b := b_mul_sq_sub_one (by omega)
  refine ⟨Bnd, hB0, ?_, ?_⟩
  · intro d hd hcop hdle
    have hcop' : Nat.Coprime d (b * (b ^ 2 - 1)) := by
      rw [hbmul]
      exact hcop
    have hB : 0 < b ^ (lam - 1) := Nat.pos_pow_of_pos _ (by omega)
    have hz1 : b ^ (lam - 1) ≤ (i + 1) * b ^ (lam - 1) :=
      Nat.le_mul_of_pos_left _ (by omega)
    have hz2 : (i + 1) * b ^ (lam - 1) ≤ b ^ lam := by
      calc (i + 1) * b ^ (lam - 1) ≤ b * b ^ (lam - 1) :=
            Nat.mul_le_mul_right _ (by omega)
        _ = b ^ lam := by
            rw [← pow_succ']
            congr 1
            omega
    have hz3 : b ^ (lam - 1) ≤ i * b ^ (lam - 1) :=
      Nat.le_mul_of_pos_left _ (by omega)
    have hz4 : i * b ^ (lam - 1) ≤ b ^ lam :=
      le_trans (Nat.mul_le_mul_right _ (by omega)) hz2
    have h1 := hBptw d hd hcop' hdle ((i + 1) * b ^ (lam - 1)) hz1 hz2 d
    have h2 := hBptw d hd hcop' hdle (i * b ^ (lam - 1)) hz3 hz4 d
    exact rev_rem_le hb hlam1 hi1 hi2 hd h1 h2
  · have hb0R : (0:ℝ) < (b:ℝ) := by
      have : (0:ℕ) < b := by omega
      exact_mod_cast this
    have hsub : (Finset.Icc 1 (b ^ lam)).filter
        (fun d => Nat.Coprime d (b ^ 3 - b)
          ∧ (d : ℝ) ≤ (b : ℝ) ^ (ξ * (lam : ℝ)))
        ⊆ (Finset.Icc 1 (⌈(b : ℝ) ^ (ξ * (lam : ℝ))⌉₊)).filter
            (fun d => Nat.Coprime d (b * (b ^ 2 - 1))
              ∧ (d : ℝ) ≤ (b : ℝ) ^ (ξ * (lam : ℝ))) := by
      intro d hd
      simp only [Finset.mem_filter, Finset.mem_Icc] at hd ⊢
      obtain ⟨⟨hd1, _⟩, hdc, hdle⟩ := hd
      refine ⟨⟨hd1, ?_⟩, ?_, hdle⟩
      · have hle2 : (d:ℝ) ≤ (⌈(b : ℝ) ^ (ξ * (lam : ℝ))⌉₊ : ℝ) :=
          le_trans hdle (Nat.le_ceil _)
        exact_mod_cast hle2
      · rw [hbmul]
        exact hdc
    calc (∑ d ∈ (Finset.Icc 1 (b ^ lam)).filter
          (fun d => Nat.Coprime d (b ^ 3 - b)
            ∧ (d : ℝ) ≤ (b : ℝ) ^ (ξ * (lam : ℝ))), Bnd d)
        ≤ ∑ d ∈ (Finset.Icc 1 (⌈(b : ℝ) ^ (ξ * (lam : ℝ))⌉₊)).filter
            (fun d => Nat.Coprime d (b * (b ^ 2 - 1))
              ∧ (d : ℝ) ≤ (b : ℝ) ^ (ξ * (lam : ℝ))), Bnd d :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun d _ _ => hB0 d)
      _ ≤ C * (b:ℝ) ^ ((lam:ℝ) - c * Real.sqrt (lam:ℝ)) := hBsum

/-! ### Decay of `λ^P b^{-c√λ}` -/

lemma tendsto_rpow_mul_rpow_neg_sqrt (hb : 2 ≤ b) {c : ℝ} (hc : 0 < c) (P : ℝ) :
    Tendsto (fun lam : ℕ => (lam:ℝ) ^ P * (b:ℝ) ^ (-(c * Real.sqrt (lam:ℝ))))
      atTop (𝓝 0) := by
  have hbR : (1:ℝ) < (b:ℝ) := by exact_mod_cast (by omega : 1 < b)
  have hb0R : (0:ℝ) < (b:ℝ) := by linarith
  have hlogb : 0 < Real.log b := Real.log_pos hbR
  set c' : ℝ := c * Real.log b with hc'def
  have hc' : 0 < c' := mul_pos hc hlogb
  have hg := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (2*P) c' hc'
  have hsqrt : Tendsto (fun lam : ℕ => Real.sqrt ((lam:ℝ))) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hcomp := hg.comp hsqrt
  refine hcomp.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with lam hlam
  have hlam0 : (0:ℝ) < (lam:ℝ) := by
    have : (0:ℕ) < lam := by omega
    exact_mod_cast this
  simp only [Function.comp]
  have h1 : (Real.sqrt ((lam:ℝ))) ^ (2*P) = (lam:ℝ) ^ P := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hlam0.le]
    congr 1
    ring
  have h2 : Real.exp (-c' * Real.sqrt ((lam:ℝ)))
      = (b:ℝ) ^ (-(c * Real.sqrt ((lam:ℝ)))) := by
    rw [Real.rpow_def_of_pos hb0R]
    congr 1
    rw [hc'def]
    ring
  rw [h1, h2]

/-! ### Hypotheses (i)–(ii) for reversed primes -/

/-- Reversed primes with fixed leading digit satisfy hypotheses (i)–(ii) of
Proposition 2.1 for the family `AFam b i` and the exceptional set `ℰ_b`
(Lemma 4.4'). -/
theorem revCritHyps (hb : 2 ≤ b) (hi1 : 1 ≤ i) (hi2 : i ≤ b - 1) :
    ∃ ξ : ℝ, 0 < ξ ∧ CritHyps b (AFam b i) (Eb b) ξ := by
  obtain ⟨ξ, hξ0, hξh, c, C, hc0, hC0, hpkg⟩ := rev_drs_package hb hi1 hi2
  obtain ⟨κ, hκ0, hκev⟩ := pilam_lower hb hi1 hi2
  have hbR : (1:ℝ) < (b:ℝ) := by exact_mod_cast (by omega : 1 < b)
  have hb0R : (0:ℝ) < (b:ℝ) := by linarith
  refine ⟨ξ, hξ0, ⟨hb, hξ0, by linarith, ?_, ?_, ?_, ?_⟩⟩
  · refine Filter.Eventually.of_forall fun lam => ?_
    unfold AFam
    split_ifs with h
    · exact h.2
    · exact Finset.singleton_nonempty 1
  · intro lam n hn
    unfold AFam at hn
    split_ifs at hn with h
    · obtain ⟨hlam1, _⟩ := h
      unfold ALamI at hn
      rw [Finset.mem_image] at hn
      obtain ⟨p, hp, rfl⟩ := hn
      rw [mem_PLamI_iff] at hp
      have hplt : p < b ^ lam := by
        calc p < (i + 1) * b ^ (lam - 1) := hp.2.1
          _ ≤ b * b ^ (lam - 1) := Nat.mul_le_mul_right _ (by omega)
          _ = b ^ lam := by
              rw [← pow_succ']
              congr 1
              omega
      have hp1 : 1 ≤ p := by
        have hB : 0 < b ^ (lam - 1) := Nat.pos_pow_of_pos _ (by omega)
        have := hp.1
        nlinarith
      exact rev_pos (by omega) hplt hp1
    · rw [Finset.mem_singleton] at hn
      omega
  · intro lam n hn
    unfold AFam at hn
    split_ifs at hn with h
    · unfold ALamI at hn
      rw [Finset.mem_image] at hn
      obtain ⟨p, hp, rfl⟩ := hn
      exact le_of_lt (rev_lt (by omega) lam p)
    · rw [Finset.mem_singleton] at hn
      have : 1 ≤ b ^ lam := Nat.one_le_pow _ _ (by omega)
      omega
  · intro A hA
    refine ⟨1, by norm_num, ?_⟩
    have hdecay := tendsto_rpow_mul_rpow_neg_sqrt hb hc0 (A + 1)
    have hκ2C : (0:ℝ) < κ / (2 * C + 1) := by positivity
    have hev2 : ∀ᶠ lam : ℕ in atTop,
        (lam:ℝ) ^ (A+1) * (b:ℝ) ^ (-(c * Real.sqrt (lam:ℝ))) ≤ κ / (2 * C + 1) := by
      have h1 := hdecay.eventually (Iio_mem_nhds hκ2C)
      exact h1.mono (fun lam h => le_of_lt h)
    filter_upwards [hpkg, hκev, hev2, AFam_eventually_eq hb hi1 hi2,
      AFam_card_eventually hb hi1 hi2, eventually_ge_atTop 1]
      with lam hBndpkg hκlam hsmall hAeq hAcard hlam1
    obtain ⟨Bnd, hB0, hBrem, hBsum⟩ := hBndpkg
    have hlamR0 : (0:ℝ) < (lam:ℝ) := by
      have : (0:ℕ) < lam := by omega
      exact_mod_cast this
    have hlamA : (0:ℝ) < (lam:ℝ) ^ A := Real.rpow_pos_of_pos hlamR0 _
    have hlamA1 : (0:ℝ) < (lam:ℝ) ^ (A+1) := Real.rpow_pos_of_pos hlamR0 _
    have hpow0 : (0:ℝ) < (b:ℝ) ^ lam := by positivity
    -- pointwise |rem| ≤ 2 Bnd, restricted-sum comparison
    have hptw : ∀ d ∈ (Finset.Icc 1 (b ^ lam)).filter
        (fun d => Squarefree d ∧ noFactorIn (Eb b) d
          ∧ (d:ℝ) ≤ (b:ℝ) ^ (ξ * (lam:ℝ))),
        |rem (AFam b i lam) d| ≤ 2 * Bnd d := by
      intro d hd
      simp only [Finset.mem_filter, Finset.mem_Icc] at hd
      obtain ⟨⟨hd1, _⟩, _, hdE, hdle⟩ := hd
      rw [hAeq]
      exact hBrem d hd1 ((noFactorIn_Eb_iff hb hd1).mp hdE) hdle
    have hsub : (Finset.Icc 1 (b ^ lam)).filter
        (fun d => Squarefree d ∧ noFactorIn (Eb b) d
          ∧ (d:ℝ) ≤ (b:ℝ) ^ (ξ * (lam:ℝ)))
        ⊆ (Finset.Icc 1 (b ^ lam)).filter
          (fun d => Nat.Coprime d (b ^ 3 - b)
            ∧ (d : ℝ) ≤ (b : ℝ) ^ (ξ * (lam : ℝ))) := by
      intro d hd
      simp only [Finset.mem_filter, Finset.mem_Icc] at hd ⊢
      obtain ⟨⟨hd1, hd2⟩, _, hdE, hdle⟩ := hd
      exact ⟨⟨hd1, hd2⟩, (noFactorIn_Eb_iff hb hd1).mp hdE, hdle⟩
    -- the exponential factorisation of the DRS bound
    have hconv : (b:ℝ) ^ ((lam:ℝ) - c * Real.sqrt (lam:ℝ))
        = (b:ℝ) ^ lam * (b:ℝ) ^ (-(c * Real.sqrt (lam:ℝ))) := by
      rw [← Real.rpow_natCast (b:ℝ) lam, ← Real.rpow_add hb0R]
      congr 1
      try ring
    have hX0 : (0:ℝ) ≤ (b:ℝ) ^ (-(c * Real.sqrt (lam:ℝ))) :=
      Real.rpow_nonneg hb0R.le _
    -- λ^{A+1} = λ^A · λ
    have hsplitpow : (lam:ℝ) ^ (A+1) = (lam:ℝ) ^ A * (lam:ℝ) := by
      rw [Real.rpow_add_one (ne_of_gt hlamR0)]
    calc ∑ d ∈ (Finset.Icc 1 (b ^ lam)).filter
          (fun d => Squarefree d ∧ noFactorIn (Eb b) d
            ∧ (d:ℝ) ≤ (b:ℝ) ^ (ξ * (lam:ℝ))),
          |rem (AFam b i lam) d|
        ≤ ∑ d ∈ (Finset.Icc 1 (b ^ lam)).filter
            (fun d => Squarefree d ∧ noFactorIn (Eb b) d
              ∧ (d:ℝ) ≤ (b:ℝ) ^ (ξ * (lam:ℝ))), 2 * Bnd d :=
          Finset.sum_le_sum hptw
      _ ≤ ∑ d ∈ (Finset.Icc 1 (b ^ lam)).filter
            (fun d => Nat.Coprime d (b ^ 3 - b)
              ∧ (d : ℝ) ≤ (b : ℝ) ^ (ξ * (lam : ℝ))), 2 * Bnd d :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub
            (fun d _ _ => by linarith [hB0 d])
      _ = 2 * ∑ d ∈ (Finset.Icc 1 (b ^ lam)).filter
            (fun d => Nat.Coprime d (b ^ 3 - b)
              ∧ (d : ℝ) ≤ (b : ℝ) ^ (ξ * (lam : ℝ))), Bnd d := by
          rw [Finset.mul_sum]
      _ ≤ 2 * (C * (b:ℝ) ^ ((lam:ℝ) - c * Real.sqrt (lam:ℝ))) := by
          linarith [hBsum]
      _ = 2 * C * ((b:ℝ) ^ lam * (b:ℝ) ^ (-(c * Real.sqrt (lam:ℝ)))) := by
          rw [hconv]
          ring
      _ ≤ κ * (b:ℝ) ^ lam / (lam:ℝ) ^ (A+1) := by
          rw [le_div_iff₀ hlamA1]
          have hkey : 2 * C * ((lam:ℝ) ^ (A+1)
              * (b:ℝ) ^ (-(c * Real.sqrt (lam:ℝ)))) ≤ κ := by
            have h3 := mul_le_mul_of_nonneg_left hsmall
              (by linarith : (0:ℝ) ≤ 2 * C)
            have h4 : 2 * C * (κ / (2 * C + 1)) ≤ κ := by
              have h5 : 2 * C * (κ / (2 * C + 1)) = κ * (2 * C / (2 * C + 1)) := by
                ring
              have h6 : 2 * C / (2 * C + 1) ≤ 1 := by
                rw [div_le_one (by linarith)]
                linarith
              calc 2 * C * (κ / (2 * C + 1)) = κ * (2 * C / (2 * C + 1)) := h5
                _ ≤ κ * 1 := mul_le_mul_of_nonneg_left h6 hκ0.le
                _ = κ := mul_one κ
            linarith
          calc 2 * C * ((b:ℝ) ^ lam * (b:ℝ) ^ (-(c * Real.sqrt (lam:ℝ))))
                * (lam:ℝ) ^ (A+1)
              = (2 * C * ((lam:ℝ) ^ (A+1)
                  * (b:ℝ) ^ (-(c * Real.sqrt (lam:ℝ))))) * (b:ℝ) ^ lam := by
                ring
            _ ≤ κ * (b:ℝ) ^ lam := mul_le_mul_of_nonneg_right hkey hpow0.le
      _ = (κ * (b:ℝ) ^ lam / (lam:ℝ)) / (lam:ℝ) ^ A := by
          rw [hsplitpow]
          ring
      _ ≤ ((AFam b i lam).card : ℝ) / (lam:ℝ) ^ A := by
          rw [hAcard]
          exact div_le_div_of_le' hlamA hκlam
      _ = 1 * ((AFam b i lam).card : ℝ) / (lam:ℝ) ^ A := by
          ring

end EKRev
