/-
DSS/P2.lean

**Corollary 1.3 of the paper**: for `g` with `μ_g > 0` and `d_g = 1`,

  `#{p ≤ x : g(p) is a P₂}  ≫  π(x) / log log x`.

The proof is the paper's targeting argument.  The window `(y, y + H/2]` with
`y = μ_g·L`, `H = √L`, `L = log_b x` is partitioned by the points
`z_i = y + Δ(i+1)`, `Δ = (2y)^{0.455}`; the short-interval theorem of
Halberstam–Heath-Brown–Richert (`hhbr`, an axiom transcribed in
`DSS/Cited.lean`) puts `≫ y^{0.455}/log y` almost-primes `P₂` in each of the
`≫ H/Δ` intervals `(z_i − z_i^{0.455}, z_i]`, giving `≫ √L/log L` distinct
targets `k` in the window.  Each target is hit by `≳ π(x)/√L` primes, by the
local limit theorem (`mmr`) — since `d_g = 1` the factor `π(x)` is common to
main and error terms, so no prime number theorem is needed — and the
accumulated error `O(π(x)·√L·(log x)^{−3/4})` is absorbed.

Axioms used: `mmr` and `hhbr`, and nothing else.
-/
import DSS.Cited
import DSS.FWeight
import DSS.Examples

namespace DSS

open Finset

/-! ### Elementary real preliminaries (no axioms) -/

/-- `log L ≤ 8·L^{1/8}` for `L ≥ 1`. -/
lemma log_le_eight_rpow {L : ℝ} (hL : 1 ≤ L) :
    Real.log L ≤ 8 * L ^ (8⁻¹ : ℝ) := by
  have hL0 : 0 < L := by linarith
  have h1 : Real.log (L ^ (8⁻¹ : ℝ)) = (8⁻¹ : ℝ) * Real.log L :=
    Real.log_rpow hL0 _
  have h2 : Real.log (L ^ (8⁻¹ : ℝ)) ≤ L ^ (8⁻¹ : ℝ) - 1 :=
    Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hL0 _)
  have h3 : 0 < L ^ (8⁻¹ : ℝ) := Real.rpow_pos_of_pos hL0 _
  rw [h1] at h2
  linarith

/-- Explicit threshold past which `c ≤ L^e`, for a fixed exponent `e > 0`. -/
lemma exists_rpow_threshold (c : ℝ) {e : ℝ} (he : 0 < e) :
    ∃ L₀ : ℝ, 1 ≤ L₀ ∧ ∀ L : ℝ, L₀ ≤ L → c ≤ L ^ e := by
  refine ⟨max 1 ((max c 1) ^ (e⁻¹ : ℝ)), le_max_left _ _, ?_⟩
  intro L hL
  have hc1 : (1 : ℝ) ≤ max c 1 := le_max_right _ _
  have h0 : (0 : ℝ) ≤ max c 1 := by linarith
  have h2 : (max c 1) ^ (e⁻¹ : ℝ) ≤ L := le_trans (le_max_right _ _) hL
  have h3 : ((max c 1) ^ (e⁻¹ : ℝ)) ^ e ≤ L ^ e :=
    Real.rpow_le_rpow (Real.rpow_nonneg h0 _) h2 he.le
  have h4 : ((max c 1) ^ (e⁻¹ : ℝ)) ^ e = max c 1 := by
    rw [← Real.rpow_mul h0, inv_mul_cancel₀ (ne_of_gt he), Real.rpow_one]
  rw [h4] at h3
  exact le_trans (le_max_left _ _) h3

/-- The pointwise Gaussian lower bound on the half-window: if `u² ≤ L/4` then
the Gaussian weight at displacement `u` is at least `exp(−1/(8s))` times the
peak value `1/√(2πsL)`. -/
lemma gaussian_lower {s L u : ℝ} (hs : 0 < s) (hL : 0 < L) (hu : u ^ 2 ≤ L / 4) :
    Real.exp (-(1 / (8 * s))) / (Real.sqrt (2 * Real.pi * s) * Real.sqrt L)
      ≤ Real.exp (-u ^ 2 / (2 * s * L)) / Real.sqrt (2 * Real.pi * s * L) := by
  have hpi := Real.pi_pos
  have hden : Real.sqrt (2 * Real.pi * s * L)
      = Real.sqrt (2 * Real.pi * s) * Real.sqrt L := Real.sqrt_mul (by positivity) L
  rw [hden]
  have hdpos : 0 < Real.sqrt (2 * Real.pi * s) * Real.sqrt L := by positivity
  have harg : -(1 / (8 * s)) ≤ -u ^ 2 / (2 * s * L) := by
    rw [neg_div, neg_le_neg_iff]
    have h1 : u ^ 2 / (2 * s * L) ≤ (L / 4) / (2 * s * L) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      exact mul_le_mul_of_nonneg_right hu (by positivity)
    have h2 : (L / 4) / (2 * s * L) = 1 / (8 * s) := by
      field_simp
      ring
    linarith
  rw [div_le_div_iff₀ hdpos hdpos]
  exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr harg) (le_of_lt hdpos)

open Classical in
/-- The primes `p ≤ x` whose value `g(p)` is a `P₂`. -/
noncomputable def p2Primes {b : ℕ} (g : Weight b) (x : ℝ) : Finset ℕ :=
  (primesLE x).filter (fun p => ∃ n : ℕ, IsP2 n ∧ g.eval p = (n : ℤ))

open Classical in
lemma mem_p2Primes {b : ℕ} {g : Weight b} {x : ℝ} {p : ℕ} :
    p ∈ p2Primes g x ↔ p ∈ primesLE x ∧ ∃ n : ℕ, IsP2 n ∧ g.eval p = (n : ℤ) := by
  unfold p2Primes
  exact Finset.mem_filter

/-! ### The main theorem -/

/-- **Corollary 1.3**: for `μ_g > 0` and `d_g = 1` there is `c > 0` with

`#{p ≤ x : g(p) is a P₂} ≥ c · π(x) / log log x`

for all large `x`.  Axioms: `mmr` and `hhbr`. -/
theorem p2_count {b : ℕ} (g : Weight b) (hg : g.Coprime₁) (hdg : g.dg = 1)
    (hmu : 0 < g.mu) :
    ∃ c : ℝ, 0 < c ∧ ∃ x₀ : ℝ, 3 ≤ x₀ ∧ ∀ x : ℝ, x₀ ≤ x →
      c * (picount x : ℝ) / Real.log (Real.log x) ≤ ((p2Primes g x).card : ℝ) := by
  obtain ⟨c₁, z₀, hc₁, hz₀3, hhbr'⟩ := hhbr
  obtain ⟨C, hC0, hmmr⟩ := mmr g hg (ε := (1 : ℝ) / 4) (by norm_num) (by norm_num)
  have hσ : 0 < g.sigSq := Weight.sigSq_pos hg
  have hb1 : (1 : ℝ) < (b : ℝ) := by exact_mod_cast g.one_lt_b
  have hb0 : (0 : ℝ) < (b : ℝ) := by linarith
  have hlogb : 0 < Real.log b := Real.log_pos hb1
  obtain ⟨θ, hθdef⟩ : ∃ t : ℝ, t = 0.455 := ⟨_, rfl⟩
  set c₃ : ℝ := Real.exp (-(1 / (8 * g.sigSq))) / Real.sqrt (2 * Real.pi * g.sigSq)
    with hc₃def
  have hc₃ : 0 < c₃ := by
    apply div_pos (Real.exp_pos _)
    apply Real.sqrt_pos.mpr
    have := Real.pi_pos
    positivity
  set c₆ : ℝ := c₁ * c₃ / 16 with hc₆def
  have hc₆ : 0 < c₆ := by positivity
  refine ⟨c₆ / 4, by positivity, ?_⟩
  -- the thresholds, all on `L = log_b x`
  obtain ⟨LD, hLD1, hLD⟩ :=
    exists_rpow_threshold (4 * (2 * g.mu) ^ θ) (e := 0.045) (by norm_num)
  obtain ⟨LC, hLC1, hLC⟩ :=
    exists_rpow_threshold (1 / g.mu) (e := (1 : ℝ) / 2) (by norm_num)
  obtain ⟨LF, hLF1, hLF⟩ :=
    exists_rpow_threshold (16 * C / (c₆ * (Real.log b) ^ ((3 : ℝ) / 4)))
      (e := 8⁻¹) (by norm_num)
  obtain ⟨LF2, hLF21, hLF2⟩ :=
    exists_rpow_threshold (C / (c₃ * (Real.log b) ^ ((3 : ℝ) / 4)))
      (e := (1 : ℝ) / 4) (by norm_num)
  set LH : ℝ := Real.exp (max 1 (-(2 * Real.log (Real.log b)))) with hLHdef
  set Lmax : ℝ := max (max (max 4 ((z₀ + 1) / g.mu)) (max LC LD))
      (max (max LF LF2) (max (2 * g.mu) LH)) with hLmaxdef
  refine ⟨max 3 ((b : ℝ) ^ Lmax), le_max_left _ _, ?_⟩
  intro x hx
  -- unpacking the threshold
  obtain ⟨L, hLdef⟩ : ∃ t : ℝ, t = Real.logb b x := ⟨_, rfl⟩
  have hxb : (b : ℝ) ^ Lmax ≤ x := le_trans (le_max_right _ _) hx
  have hx3 : (3 : ℝ) ≤ x := le_trans (le_max_left _ _) hx
  have hx0 : (0 : ℝ) < x := by linarith
  have hL : Lmax ≤ L := by
    rw [hLdef]
    have h1 : Real.logb b ((b : ℝ) ^ Lmax) ≤ Real.logb b x :=
      (Real.logb_le_logb hb1 (Real.rpow_pos_of_pos hb0 _) hx0).mpr hxb
    rwa [Real.logb_rpow hb0 (ne_of_gt hb1)] at h1
  -- the individual threshold consequences
  have hT1 : max 4 ((z₀ + 1) / g.mu) ≤ L :=
    le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hL
  have hT2 : max LC LD ≤ L :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hL
  have hT3 : max LF LF2 ≤ L :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hL
  have hT4 : max (2 * g.mu) LH ≤ L :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hL
  have hL4 : (4 : ℝ) ≤ L := le_trans (le_max_left _ _) hT1
  have hL0 : (0 : ℝ) < L := by linarith
  have hL1 : (1 : ℝ) ≤ L := by linarith
  have hlogL : (0 : ℝ) < Real.log L := Real.log_pos (by linarith)
  -- the window quantities
  obtain ⟨y, hydef⟩ : ∃ t : ℝ, t = g.mu * L := ⟨_, rfl⟩
  obtain ⟨H, hHdef⟩ : ∃ t : ℝ, t = Real.sqrt L := ⟨_, rfl⟩
  obtain ⟨Δ, hΔdef⟩ : ∃ t : ℝ, t = (2 * y) ^ θ := ⟨_, rfl⟩
  have hy0 : 0 < y := by rw [hydef]; positivity
  have hH0 : 0 < H := by rw [hHdef]; exact Real.sqrt_pos.mpr hL0
  have hHL : H * H = L := by rw [hHdef]; exact Real.mul_self_sqrt (le_of_lt hL0)
  have hH2 : 2 ≤ H := by
    rw [hHdef]
    rw [show (2:ℝ) = Real.sqrt 4 by
      rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)]]
    exact Real.sqrt_le_sqrt hL4
  have hΔ0 : 0 < Δ := by rw [hΔdef]; exact Real.rpow_pos_of_pos (by linarith) θ
  have hθpos : (0 : ℝ) < θ := by rw [hθdef]; norm_num
  have hθle1 : θ ≤ 1 := by rw [hθdef]; norm_num
  -- threshold consequences
  have hyz₀ : z₀ + 1 ≤ y := by
    have h1 : (z₀ + 1) / g.mu ≤ L := le_trans (le_max_right _ _) hT1
    calc z₀ + 1 = g.mu * ((z₀ + 1) / g.mu) := by field_simp
      _ ≤ g.mu * L := by gcongr
      _ = y := hydef.symm
  have hy3 : (3 : ℝ) ≤ y := by linarith
  have hHy : H ≤ y := by
    have h1 : 1 / g.mu ≤ L ^ ((1 : ℝ) / 2) := hLC L (le_trans (le_max_left _ _) hT2)
    have h3 : L ^ ((1 : ℝ) / 2) = H := by rw [hHdef, Real.sqrt_eq_rpow]
    rw [h3] at h1
    have h4 : g.mu * (1 / g.mu) ≤ g.mu * H := by gcongr
    rw [mul_one_div, div_self (ne_of_gt hmu)] at h4
    calc H = 1 * H := (one_mul H).symm
      _ ≤ (g.mu * H) * H := mul_le_mul_of_nonneg_right h4 (le_of_lt hH0)
      _ = g.mu * (H * H) := by ring
      _ = g.mu * L := by rw [hHL]
      _ = y := hydef.symm
  have h4Δ : 4 * Δ ≤ H := by
    have h1 : 4 * (2 * g.mu) ^ θ ≤ L ^ (0.045 : ℝ) :=
      hLD L (le_trans (le_max_right _ _) hT2)
    have h3 : Δ = (2 * g.mu) ^ θ * L ^ θ := by
      rw [hΔdef, hydef, show (2 : ℝ) * (g.mu * L) = (2 * g.mu) * L by ring,
        Real.mul_rpow (by positivity) (le_of_lt hL0)]
    have h5 : L ^ (0.045 : ℝ) * L ^ θ = L ^ ((1 : ℝ) / 2) := by
      rw [hθdef, ← Real.rpow_add hL0]
      norm_num
    have h6 : L ^ ((1 : ℝ) / 2) = H := by rw [hHdef, Real.sqrt_eq_rpow]
    calc 4 * Δ = (4 * (2 * g.mu) ^ θ) * L ^ θ := by rw [h3]; ring
      _ ≤ L ^ (0.045 : ℝ) * L ^ θ := by
          gcongr
      _ = H := by rw [h5, h6]
  -- ### the target points and their intervals
  obtain ⟨I, hIdef⟩ : ∃ n : ℕ, n = ⌊H / (2 * Δ)⌋₊ := ⟨_, rfl⟩
  obtain ⟨z, hzdef⟩ : ∃ f : ℕ → ℝ, f = fun i : ℕ => y + Δ * ((i : ℝ) + 1) := ⟨_, rfl⟩
  have hu2 : 2 ≤ H / (2 * Δ) := by
    rw [le_div_iff₀ (by positivity)]
    linarith
  have hIle : (I : ℝ) ≤ H / (2 * Δ) := by
    rw [hIdef]
    exact Nat.floor_le (by positivity)
  have hIge : H / (4 * Δ) ≤ (I : ℝ) := by
    have h1 : H / (2 * Δ) < (I : ℝ) + 1 := by
      rw [hIdef]
      exact Nat.lt_floor_add_one _
    have h2 : H / (4 * Δ) = (H / (2 * Δ)) / 2 := by
      rw [div_div]
      ring_nf
    linarith
  have hzy : ∀ i : ℕ, y < z i := by
    intro i
    have h1 : (0 : ℝ) < Δ * ((i : ℝ) + 1) := by positivity
    simp only [hzdef]
    linarith
  have hzle : ∀ i : ℕ, i < I → z i ≤ y + H / 2 := by
    intro i hi
    have h1 : ((i : ℝ) + 1) ≤ (I : ℝ) := by exact_mod_cast hi
    have h3 : Δ * ((i : ℝ) + 1) ≤ Δ * (H / (2 * Δ)) := by
      calc Δ * ((i : ℝ) + 1) ≤ Δ * (I : ℝ) := by gcongr
        _ ≤ Δ * (H / (2 * Δ)) := by gcongr
    have h4 : Δ * (H / (2 * Δ)) = H / 2 := by
      field_simp
    simp only [hzdef]
    linarith
  have hz2y : ∀ i : ℕ, i < I → z i ≤ 2 * y := by
    intro i hi
    have := hzle i hi
    linarith
  have hzθΔ : ∀ i : ℕ, i < I → (z i) ^ θ ≤ Δ := by
    intro i hi
    rw [hΔdef]
    exact Real.rpow_le_rpow (by linarith [hzy i]) (hz2y i hi) (le_of_lt hθpos)
  -- ### the target set `K`
  obtain ⟨K, hKdef⟩ : ∃ s : Finset ℕ,
      s = (range I).biUnion (fun i => p2InInterval (z i)) := ⟨_, rfl⟩
  have hmemInt : ∀ i : ℕ, ∀ k ∈ p2InInterval (z i),
      IsP2 k ∧ z i - (z i) ^ θ < (k : ℝ) ∧ (k : ℝ) ≤ z i := by
    intro i k hk
    rw [p2InInterval, mem_filter] at hk
    rw [hθdef]
    exact hk.2
  have hdisj : ∀ i ∈ range I, ∀ j ∈ range I, i ≠ j →
      Disjoint (p2InInterval (z i)) (p2InInterval (z j)) := by
    have key : ∀ i j : ℕ, j ∈ range I → i < j →
        Disjoint (p2InInterval (z i)) (p2InInterval (z j)) := by
      intro i j hj hij
      rw [Finset.disjoint_left]
      intro k hki hkj
      obtain ⟨_, _, hk2⟩ := hmemInt i k hki
      obtain ⟨_, hk3, _⟩ := hmemInt j k hkj
      have h1 : (z j) ^ θ ≤ Δ := hzθΔ j (mem_range.mp hj)
      have h2 : z i ≤ z j - Δ := by
        rw [hzdef]
        show y + Δ * ((i : ℝ) + 1) ≤ y + Δ * ((j : ℝ) + 1) - Δ
        have h3 : (i : ℝ) + 1 + 1 ≤ (j : ℝ) + 1 := by
          have h3' : (i : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast hij
          linarith
        have h4 : Δ * ((i : ℝ) + 1 + 1) ≤ Δ * ((j : ℝ) + 1) :=
          mul_le_mul_of_nonneg_left h3 (le_of_lt hΔ0)
        have h5 : Δ * ((i : ℝ) + 1 + 1) = Δ * ((i : ℝ) + 1) + Δ := by ring
        linarith
      linarith
    intro i hi j hj hij
    rcases Nat.lt_or_ge i j with h | h
    · exact key i j hj h
    · exact (key j i hi (by omega)).symm
  have hKcard : (K.card : ℝ) = ∑ i ∈ range I, ((p2InInterval (z i)).card : ℝ) := by
    rw [hKdef, Finset.card_biUnion hdisj]
    push_cast
    rfl
  -- ### the lower bound on `#K`
  have hlog2y : (0 : ℝ) < Real.log (2 * y) := Real.log_pos (by linarith)
  have hIntLower : ∀ i : ℕ, i < I →
      c₁ * y ^ θ / Real.log (2 * y) ≤ ((p2InInterval (z i)).card : ℝ) := by
    intro i hi
    have h1 : z₀ ≤ z i := by linarith [hzy i]
    refine le_trans ?_ (hhbr' (z i) h1)
    have hzi3 : (3 : ℝ) ≤ z i := by linarith [hzy i]
    have hlogzi : 0 < Real.log (z i) := Real.log_pos (by linarith)
    have h3 : y ^ θ ≤ (z i) ^ θ :=
      Real.rpow_le_rpow (le_of_lt hy0) (le_of_lt (hzy i)) (le_of_lt hθpos)
    have h4 : Real.log (z i) ≤ Real.log (2 * y) :=
      Real.log_le_log (by linarith) (hz2y i hi)
    rw [hθdef] at h3 ⊢
    gcongr
  have hyθ0 : (0 : ℝ) < y ^ θ := Real.rpow_pos_of_pos hy0 θ
  have hyθΔ : Δ ≤ 2 * y ^ θ := by
    have h3 : Δ = (2 : ℝ) ^ θ * y ^ θ := by
      rw [hΔdef, Real.mul_rpow (by norm_num) (le_of_lt hy0)]
    have h4 : (2 : ℝ) ^ θ ≤ 2 := by
      calc (2 : ℝ) ^ θ ≤ (2 : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) hθle1
        _ = 2 := Real.rpow_one 2
    rw [h3]
    exact mul_le_mul_of_nonneg_right h4 (le_of_lt hyθ0)
  have hlog2yL : Real.log (2 * y) ≤ 2 * Real.log L := by
    have h6 : 2 * g.mu ≤ L := le_trans (le_max_left _ _) hT4
    have h8 : (2 * g.mu) * L ≤ L * L := by gcongr
    have h9 : Real.log (2 * y) ≤ Real.log (L * L) := by
      rw [hydef, show (2:ℝ) * (g.mu * L) = (2 * g.mu) * L by ring]
      exact Real.log_le_log (by positivity) h8
    have h10 : Real.log (L * L) = Real.log L + Real.log L :=
      Real.log_mul (ne_of_gt hL0) (ne_of_gt hL0)
    linarith
  have hKlower : c₁ * H / (16 * Real.log L) ≤ (K.card : ℝ) := by
    have h1 : (I : ℝ) * (c₁ * y ^ θ / Real.log (2 * y)) ≤ (K.card : ℝ) := by
      rw [hKcard]
      have h2 := Finset.card_nsmul_le_sum (range I)
        (fun i => ((p2InInterval (z i)).card : ℝ))
        (c₁ * y ^ θ / Real.log (2 * y))
        (fun i hi => hIntLower i (mem_range.mp hi))
      rwa [card_range, nsmul_eq_mul] at h2
    refine le_trans ?_ h1
    have hstep : c₁ * H / (16 * Real.log L)
        ≤ (H / (4 * Δ)) * (c₁ * y ^ θ / Real.log (2 * y)) := by
      have e1 : (H / (4 * Δ)) * (c₁ * y ^ θ / Real.log (2 * y))
          = c₁ * (H * y ^ θ) / ((4 * Δ) * Real.log (2 * y)) := by
        ring
      rw [e1, div_le_div_iff₀ (by positivity) (by positivity)]
      have h11 : (4 * Δ) * Real.log (2 * y)
          ≤ (4 * (2 * y ^ θ)) * (2 * Real.log L) := by
        have := mul_le_mul (by linarith : 4 * Δ ≤ 4 * (2 * y ^ θ)) hlog2yL
          (le_of_lt hlog2y) (by positivity)
        linarith
      calc c₁ * H * ((4 * Δ) * Real.log (2 * y))
          ≤ c₁ * H * ((4 * (2 * y ^ θ)) * (2 * Real.log L)) := by
            gcongr
        _ = c₁ * (H * y ^ θ) * (16 * Real.log L) := by ring
    refine le_trans hstep ?_
    have hfac : 0 ≤ c₁ * y ^ θ / Real.log (2 * y) :=
      div_nonneg (by positivity) (le_of_lt hlog2y)
    exact mul_le_mul_of_nonneg_right hIge hfac
  -- ### the membership facts and the upper bound on `#K`
  have hKmem : ∀ k ∈ K, IsP2 k ∧ y < (k : ℝ) ∧ (k : ℝ) ≤ y + H / 2 := by
    intro k hk
    rw [hKdef, Finset.mem_biUnion] at hk
    obtain ⟨i, hi, hki⟩ := hk
    obtain ⟨h1, h2, h3⟩ := hmemInt i k hki
    have h4 : (z i) ^ θ ≤ Δ := hzθΔ i (mem_range.mp hi)
    have h5 : z i ≤ y + H / 2 := hzle i (mem_range.mp hi)
    refine ⟨h1, ?_, by linarith⟩
    have h7 : y ≤ z i - Δ := by
      rw [hzdef]
      show y ≤ y + Δ * ((i : ℝ) + 1) - Δ
      have h9 : (0 : ℝ) ≤ Δ * (i : ℝ) := by positivity
      have h10 : Δ * ((i : ℝ) + 1) = Δ * (i : ℝ) + Δ := by ring
      linarith
    linarith
  have hKupper : (K.card : ℝ) ≤ H := by
    have hsub : K ⊆ Finset.Ioc ⌊y⌋₊ ⌊y + H / 2⌋₊ := by
      intro k hk
      obtain ⟨_, h1, h2⟩ := hKmem k hk
      rw [Finset.mem_Ioc]
      exact ⟨(Nat.floor_lt (le_of_lt hy0)).mpr h1, Nat.le_floor h2⟩
    have hmono : ⌊y⌋₊ ≤ ⌊y + H / 2⌋₊ := Nat.floor_le_floor (by linarith)
    have h1 : K.card ≤ ⌊y + H / 2⌋₊ - ⌊y⌋₊ := by
      have := Finset.card_le_card hsub
      rwa [Nat.card_Ioc] at this
    have h3 : ((⌊y + H / 2⌋₊ - ⌊y⌋₊ : ℕ) : ℝ)
        = (⌊y + H / 2⌋₊ : ℝ) - (⌊y⌋₊ : ℝ) := by
      rw [Nat.cast_sub hmono]
    have h4 : (⌊y + H / 2⌋₊ : ℝ) ≤ y + H / 2 := Nat.floor_le (by linarith)
    have h5 : y - 1 < (⌊y⌋₊ : ℝ) := Nat.sub_one_lt_floor y
    calc (K.card : ℝ) ≤ ((⌊y + H / 2⌋₊ - ⌊y⌋₊ : ℕ) : ℝ) := by exact_mod_cast h1
      _ = (⌊y + H / 2⌋₊ : ℝ) - (⌊y⌋₊ : ℝ) := h3
      _ ≤ (y + H / 2) - (y - 1) := by linarith
      _ = H / 2 + 1 := by ring
      _ ≤ H := by linarith
  -- ### the local limit theorem on each target
  have hx2 : (2 : ℝ) < x := by linarith
  have hlogx0 : (0 : ℝ) < Real.log x := Real.log_pos (by linarith)
  have hlogxL : Real.log x = L * Real.log b := by
    rw [hLdef, Real.logb, div_mul_cancel₀ _ (ne_of_gt hlogb)]
  have hlogx34 : (0 : ℝ) < (Real.log x) ^ ((3 : ℝ) / 4) :=
    Real.rpow_pos_of_pos hlogx0 _
  obtain ⟨A, hAdef⟩ : ∃ t : ℝ, t = (picount x : ℝ) * (c₃ / H) := ⟨_, rfl⟩
  obtain ⟨B, hBdef⟩ : ∃ t : ℝ, t = C * (picount x : ℝ) / (Real.log x) ^ ((3 : ℝ) / 4) :=
    ⟨_, rfl⟩
  have hπ0 : (0 : ℝ) ≤ (picount x : ℝ) := by positivity
  have hHne : H ≠ 0 := ne_of_gt hH0
  have hlogLne : Real.log L ≠ 0 := ne_of_gt hlogL
  have hA0 : 0 ≤ A := by
    rw [hAdef]
    positivity
  have hB0 : 0 ≤ B := by
    rw [hBdef]
    positivity
  have hΓ : ∀ k ∈ K, A - B ≤ (countEq g x (k : ℤ) : ℝ) := by
    intro k hk
    obtain ⟨_, hk1, hk2⟩ := hKmem k hk
    -- the main term dominates `A`
    have hmain : A ≤ mmrMain g x (k : ℤ) := by
      rw [mmrMain_def, piCong_of_dg_eq_one g hdg, hdg]
      have hcast : (((k : ℤ) : ℝ)) = (k : ℝ) := by push_cast; rfl
      have hLb : Real.logb (b : ℝ) x = L := hLdef.symm
      rw [hLb, hcast]
      have hu2 : ((k : ℝ) - g.mu * L) ^ 2 ≤ L / 4 := by
        have h3 : (0 : ℝ) < (k : ℝ) - y := by linarith
        have h4 : (k : ℝ) - y ≤ H / 2 := by linarith
        have h6 : (H / 2) ^ 2 = L / 4 := by
          rw [div_pow, hHdef, Real.sq_sqrt (le_of_lt hL0)]
          norm_num
        have h7 : ((k : ℝ) - y) ^ 2 ≤ (H / 2) ^ 2 := sq_le_sq' (by linarith) h4
        have h8 : (k : ℝ) - g.mu * L = (k : ℝ) - y := by rw [hydef]
        rw [h8]
        linarith
      have hgl := gaussian_lower hσ hL0 hu2
      have e1 : A = (picount x : ℝ)
          * (Real.exp (-(1 / (8 * g.sigSq)))
             / (Real.sqrt (2 * Real.pi * g.sigSq) * Real.sqrt L)) := by
        rw [hAdef, hc₃def, hHdef]
        rw [div_div]
      calc A ≤ (picount x : ℝ)
            * (Real.exp (-((k : ℝ) - g.mu * L) ^ 2 / (2 * g.sigSq * L))
               / Real.sqrt (2 * Real.pi * g.sigSq * L)) := by
            rw [e1]
            exact mul_le_mul_of_nonneg_left hgl (by positivity)
        _ = (1 : ℕ) * (picount x : ℝ) / Real.sqrt (2 * Real.pi * g.sigSq * L)
            * Real.exp (-((k : ℝ) - g.mu * L) ^ 2 / (2 * g.sigSq * L)) := by
            push_cast
            ring
    have herr := hmmr x hx2 (k : ℤ)
    have h34 : (1 : ℝ) - 1 / 4 = 3 / 4 := by norm_num
    rw [h34] at herr
    have h5 := (abs_le.mp herr).1
    linarith [hmain, hBdef]
  -- ### summing over the targets
  have hsum1 : (K.card : ℝ) * (A - B) ≤ ∑ k ∈ K, (countEq g x (k : ℤ) : ℝ) := by
    have h := Finset.card_nsmul_le_sum K
      (fun k => (countEq g x (k : ℤ) : ℝ)) (A - B) hΓ
    rwa [nsmul_eq_mul] at h
  have hsum2 : ∑ k ∈ K, (countEq g x (k : ℤ) : ℝ) ≤ ((p2Primes g x).card : ℝ) := by
    have hfibdisj : ∀ k ∈ K, ∀ k' ∈ K, k ≠ k' →
        Disjoint ((primesLE x).filter (fun p => g.eval p = ((k : ℕ) : ℤ)))
          ((primesLE x).filter (fun p => g.eval p = ((k' : ℕ) : ℤ))) := by
      intro k _ k' _ hkk'
      rw [Finset.disjoint_left]
      intro p hp hp'
      rw [mem_filter] at hp hp'
      have : ((k : ℕ) : ℤ) = ((k' : ℕ) : ℤ) := by rw [← hp.2, hp'.2]
      exact hkk' (by exact_mod_cast this)
    have hfibsub : K.biUnion
        (fun k => (primesLE x).filter (fun p => g.eval p = ((k : ℕ) : ℤ)))
        ⊆ p2Primes g x := by
      intro p hp
      rw [Finset.mem_biUnion] at hp
      obtain ⟨k, hkK, hpk⟩ := hp
      rw [mem_filter] at hpk
      rw [mem_p2Primes]
      exact ⟨hpk.1, k, (hKmem k hkK).1, hpk.2⟩
    calc ∑ k ∈ K, (countEq g x (k : ℤ) : ℝ)
        = ((K.biUnion (fun k => (primesLE x).filter
            (fun p => g.eval p = ((k : ℕ) : ℤ)))).card : ℝ) := by
          rw [Finset.card_biUnion hfibdisj]
          push_cast
          rfl
      _ ≤ ((p2Primes g x).card : ℝ) := by
          exact_mod_cast Finset.card_le_card hfibsub
  -- ### the error absorption and the final chain
  have hsqrtL : H = L ^ ((1 : ℝ) / 2) := by rw [hHdef]; exact Real.sqrt_eq_rpow L
  have hlogx34e : (Real.log x) ^ ((3 : ℝ) / 4)
      = L ^ ((3 : ℝ) / 4) * (Real.log b) ^ ((3 : ℝ) / 4) := by
    rw [hlogxL, Real.mul_rpow (le_of_lt hL0) (le_of_lt hlogb)]
  -- `B ≤ A`, so the per-target bound is nonnegative
  have hBA : B ≤ A := by
    have h1 : C / (c₃ * (Real.log b) ^ ((3 : ℝ) / 4)) ≤ L ^ ((1 : ℝ) / 4) :=
      hLF2 L (le_trans (le_max_right _ _) hT3)
    have h2 : C * H ≤ c₃ * (Real.log x) ^ ((3 : ℝ) / 4) := by
      have h3 : C ≤ L ^ ((1 : ℝ) / 4) * (c₃ * (Real.log b) ^ ((3 : ℝ) / 4)) := by
        have h4 : 0 < c₃ * (Real.log b) ^ ((3 : ℝ) / 4) := by positivity
        calc C = (C / (c₃ * (Real.log b) ^ ((3 : ℝ) / 4)))
              * (c₃ * (Real.log b) ^ ((3 : ℝ) / 4)) := by field_simp
          _ ≤ L ^ ((1 : ℝ) / 4) * (c₃ * (Real.log b) ^ ((3 : ℝ) / 4)) := by gcongr
      calc C * H ≤ (L ^ ((1 : ℝ) / 4) * (c₃ * (Real.log b) ^ ((3 : ℝ) / 4))) * H := by
            gcongr
        _ = c₃ * (L ^ ((1 : ℝ) / 4) * L ^ ((1 : ℝ) / 2))
            * (Real.log b) ^ ((3 : ℝ) / 4) := by rw [hsqrtL]; ring
        _ = c₃ * L ^ ((3 : ℝ) / 4) * (Real.log b) ^ ((3 : ℝ) / 4) := by
            rw [← Real.rpow_add hL0]
            norm_num
        _ = c₃ * (Real.log x) ^ ((3 : ℝ) / 4) := by rw [hlogx34e]; ring
    rw [hAdef, hBdef, div_le_iff₀ hlogx34]
    have h9 : C ≤ c₃ / H * (Real.log x) ^ ((3 : ℝ) / 4) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hH0]
      exact h2
    calc C * (picount x : ℝ) = (picount x : ℝ) * C := by ring
      _ ≤ (picount x : ℝ) * (c₃ / H * (Real.log x) ^ ((3 : ℝ) / 4)) :=
          mul_le_mul_of_nonneg_left h9 hπ0
      _ = (picount x : ℝ) * (c₃ / H) * (Real.log x) ^ ((3 : ℝ) / 4) := by ring
  -- the two main quantities
  have hKA : c₆ * (picount x : ℝ) / Real.log L ≤ (c₁ * H / (16 * Real.log L)) * A := by
    have e1 : (c₁ * H / (16 * Real.log L)) * A
        = (c₁ * c₃ / 16) * (picount x : ℝ) / Real.log L := by
      rw [hAdef]
      field_simp
    rw [e1, hc₆def]
  have hHB : H * B ≤ (c₆ / 2) * (picount x : ℝ) / Real.log L := by
    have h1 : 16 * C / (c₆ * (Real.log b) ^ ((3 : ℝ) / 4)) ≤ L ^ (8⁻¹ : ℝ) :=
      hLF L (le_trans (le_max_left _ _) hT3)
    -- `C·√L·log L ≤ (c₆/2)·(log x)^{3/4}`
    have h2 : C * H * Real.log L ≤ (c₆ / 2) * (Real.log x) ^ ((3 : ℝ) / 4) := by
      have h3 : Real.log L ≤ 8 * L ^ (8⁻¹ : ℝ) := log_le_eight_rpow hL1
      have h4 : 0 < c₆ * (Real.log b) ^ ((3 : ℝ) / 4) := by positivity
      have h5 : 16 * C ≤ L ^ (8⁻¹ : ℝ) * (c₆ * (Real.log b) ^ ((3 : ℝ) / 4)) := by
        calc 16 * C = (16 * C / (c₆ * (Real.log b) ^ ((3 : ℝ) / 4)))
              * (c₆ * (Real.log b) ^ ((3 : ℝ) / 4)) := by field_simp
          _ ≤ L ^ (8⁻¹ : ℝ) * (c₆ * (Real.log b) ^ ((3 : ℝ) / 4)) := by gcongr
      have h6 : C * H * Real.log L ≤ C * L ^ ((1 : ℝ) / 2) * (8 * L ^ (8⁻¹ : ℝ)) := by
        rw [hsqrtL]
        gcongr
      have h7 : C * L ^ ((1 : ℝ) / 2) * (8 * L ^ (8⁻¹ : ℝ))
          = (16 * C) * (L ^ ((1 : ℝ) / 2) * L ^ (8⁻¹ : ℝ)) / 2 := by ring
      have h8 : L ^ ((1 : ℝ) / 2) * L ^ (8⁻¹ : ℝ) = L ^ ((5 : ℝ) / 8) := by
        rw [← Real.rpow_add hL0]
        norm_num
      have h9 : (16 * C) * L ^ ((5 : ℝ) / 8)
          ≤ (L ^ (8⁻¹ : ℝ) * (c₆ * (Real.log b) ^ ((3 : ℝ) / 4))) * L ^ ((5 : ℝ) / 8) :=
        mul_le_mul_of_nonneg_right h5 (Real.rpow_nonneg (le_of_lt hL0) _)
      have h10 : (L ^ (8⁻¹ : ℝ) * (c₆ * (Real.log b) ^ ((3 : ℝ) / 4))) * L ^ ((5 : ℝ) / 8)
          = c₆ * L ^ ((3 : ℝ) / 4) * (Real.log b) ^ ((3 : ℝ) / 4) := by
        have h11 : L ^ (8⁻¹ : ℝ) * L ^ ((5 : ℝ) / 8) = L ^ ((3 : ℝ) / 4) := by
          rw [← Real.rpow_add hL0]
          norm_num
        calc (L ^ (8⁻¹ : ℝ) * (c₆ * (Real.log b) ^ ((3 : ℝ) / 4))) * L ^ ((5 : ℝ) / 8)
            = (L ^ (8⁻¹ : ℝ) * L ^ ((5 : ℝ) / 8))
              * (c₆ * (Real.log b) ^ ((3 : ℝ) / 4)) := by ring
          _ = L ^ ((3 : ℝ) / 4) * (c₆ * (Real.log b) ^ ((3 : ℝ) / 4)) := by rw [h11]
          _ = c₆ * L ^ ((3 : ℝ) / 4) * (Real.log b) ^ ((3 : ℝ) / 4) := by ring
      calc C * H * Real.log L ≤ C * L ^ ((1 : ℝ) / 2) * (8 * L ^ (8⁻¹ : ℝ)) := h6
        _ = (16 * C) * (L ^ ((1 : ℝ) / 2) * L ^ (8⁻¹ : ℝ)) / 2 := h7
        _ = (16 * C) * L ^ ((5 : ℝ) / 8) / 2 := by rw [h8]
        _ ≤ (L ^ (8⁻¹ : ℝ) * (c₆ * (Real.log b) ^ ((3 : ℝ) / 4)))
            * L ^ ((5 : ℝ) / 8) / 2 := by linarith
        _ = c₆ * L ^ ((3 : ℝ) / 4) * (Real.log b) ^ ((3 : ℝ) / 4) / 2 := by rw [h10]
        _ = (c₆ / 2) * (Real.log x) ^ ((3 : ℝ) / 4) := by rw [hlogx34e]; ring
    rw [hBdef]
    have e2 : H * (C * (picount x : ℝ) / (Real.log x) ^ ((3 : ℝ) / 4))
        = (H * C * (picount x : ℝ)) / (Real.log x) ^ ((3 : ℝ) / 4) := by ring
    rw [e2, div_le_div_iff₀ hlogx34 hlogL]
    calc H * C * (picount x : ℝ) * Real.log L
        = (C * H * Real.log L) * (picount x : ℝ) := by ring
      _ ≤ ((c₆ / 2) * (Real.log x) ^ ((3 : ℝ) / 4)) * (picount x : ℝ) :=
          mul_le_mul_of_nonneg_right h2 hπ0
      _ = (c₆ / 2) * (picount x : ℝ) * (Real.log x) ^ ((3 : ℝ) / 4) := by ring
  -- putting the count together
  have hcount : (c₆ / 2) * (picount x : ℝ) / Real.log L ≤ ((p2Primes g x).card : ℝ) := by
    have h1 : (c₁ * H / (16 * Real.log L)) * A - H * B ≤ (K.card : ℝ) * (A - B) := by
      have h2 : (K.card : ℝ) * (A - B) = (K.card : ℝ) * A - (K.card : ℝ) * B := by
        ring
      rw [h2]
      have h3 : (c₁ * H / (16 * Real.log L)) * A ≤ (K.card : ℝ) * A := by
        gcongr
      have h4 : (K.card : ℝ) * B ≤ H * B := by gcongr
      linarith
    have h5 : (c₆ / 2) * (picount x : ℝ) / Real.log L
        ≤ (c₁ * H / (16 * Real.log L)) * A - H * B := by
      have h6 := hKA
      have h7 := hHB
      have e1 : (c₆ / 2) * (picount x : ℝ) / Real.log L
          = c₆ * (picount x : ℝ) / Real.log L
            - (c₆ / 2) * (picount x : ℝ) / Real.log L := by
        field_simp
        ring
      rw [e1]
      linarith
    linarith [hsum1, hsum2]
  -- converting `log L` into `log log x`
  have hloglogx : Real.log (Real.log x) = Real.log L + Real.log (Real.log b) := by
    rw [hlogxL]
    exact Real.log_mul (ne_of_gt hL0) (ne_of_gt hlogb)
  have hLH : LH ≤ L := le_trans (le_max_right _ _) hT4
  have hlogL1 : max 1 (-(2 * Real.log (Real.log b))) ≤ Real.log L := by
    have h1 : Real.log LH ≤ Real.log L := Real.log_le_log (by
      rw [hLHdef]; positivity) hLH
    rwa [hLHdef, Real.log_exp] at h1
  have hloglogpos : 0 < Real.log (Real.log x) := by
    have h1 : (1 : ℝ) ≤ Real.log L := le_trans (le_max_left _ _) hlogL1
    have h2 : -(2 * Real.log (Real.log b)) ≤ Real.log L :=
      le_trans (le_max_right _ _) hlogL1
    rw [hloglogx]
    linarith
  have hfinal : Real.log L ≤ 2 * Real.log (Real.log x) := by
    have h2 : -(2 * Real.log (Real.log b)) ≤ Real.log L :=
      le_trans (le_max_right _ _) hlogL1
    rw [hloglogx]
    linarith
  refine le_trans ?_ hcount
  rw [div_le_div_iff₀ hloglogpos hlogL]
  calc c₆ / 4 * (picount x : ℝ) * Real.log L
      ≤ c₆ / 4 * (picount x : ℝ) * (2 * Real.log (Real.log x)) := by
        gcongr
    _ = c₆ / 2 * (picount x : ℝ) * Real.log (Real.log x) := by ring

/-! ### The concrete instances -/

/-- **The sum of the squares of the decimal digits of a prime is a `P₂` for
`≫ π(x)/log log x` primes**: the `S`-instance of Corollary 1.3, the
unconditional companion of the A052034 theorem of the predecessor paper. -/
theorem p2_count_S :
    ∃ c : ℝ, 0 < c ∧ ∃ x₀ : ℝ, 3 ≤ x₀ ∧ ∀ x : ℝ, x₀ ≤ x →
      c * (picount x : ℝ) / Real.log (Real.log x)
        ≤ (((primesLE x).filter (fun p => IsP2 (S p))).card : ℝ) := by
  classical
  obtain ⟨c, hc, x₀, hx₀, h⟩ := p2_count wS wS_coprime₁ dg_wS mu_wS_pos
  refine ⟨c, hc, x₀, hx₀, fun x hx => ?_⟩
  refine le_trans (h x hx) ?_
  have heq : p2Primes wS x = (primesLE x).filter (fun p => IsP2 (S p)) := by
    refine Finset.ext fun p => ?_
    rw [mem_p2Primes, Finset.mem_filter]
    constructor
    · rintro ⟨hp, n, hn, hev⟩
      rw [eval_wS] at hev
      have h2 : S p = n := by exact_mod_cast hev
      exact ⟨hp, h2 ▸ hn⟩
    · rintro ⟨hp, h2⟩
      exact ⟨hp, S p, h2, by rw [eval_wS]⟩
  rw [heq]

/-- **The binary digit sum of a prime is a `P₂` for `≫ π(x)/log log x`
primes**: the `s_2`-instance of Corollary 1.3. -/
theorem p2_count_binary :
    ∃ c : ℝ, 0 < c ∧ ∃ x₀ : ℝ, 3 ≤ x₀ ∧ ∀ x : ℝ, x₀ ≤ x →
      c * (picount x : ℝ) / Real.log (Real.log x)
        ≤ (((primesLE x).filter (fun p => IsP2 (sb 2 p))).card : ℝ) := by
  classical
  obtain ⟨c, hc, x₀, hx₀, h⟩ := p2_count (sbWeight 2 (le_refl 2))
    (sbWeight_coprime₁ 2 (le_refl 2)) sbWeight_two_dg
    (by rw [sbWeight_two_mu]; norm_num)
  refine ⟨c, hc, x₀, hx₀, fun x hx => ?_⟩
  refine le_trans (h x hx) ?_
  have heq : p2Primes (sbWeight 2 (le_refl 2)) x
      = (primesLE x).filter (fun p => IsP2 (sb 2 p)) := by
    refine Finset.ext fun p => ?_
    rw [mem_p2Primes, Finset.mem_filter]
    constructor
    · rintro ⟨hp, n, hn, hev⟩
      rw [eval_sbWeight] at hev
      have h2 : sb 2 p = n := by exact_mod_cast hev
      exact ⟨hp, h2 ▸ hn⟩
    · rintro ⟨hp, h2⟩
      exact ⟨hp, sb 2 p, h2, by rw [eval_sbWeight]⟩
  rw [heq]

end DSS
