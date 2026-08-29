/-
DSS/SquareAssembly.lean

**The Fourier assembly of Theorem 1.1 (the paper's §2.4), machine-checked as
an implication.**

The proof of Theorem 1.1 has three analytic inputs — the integrated minor-arc
estimate (Corollary 2.7), the shrinking major-arc Gaussian expansion
(Proposition 2.8), and the Gaussian-scale tail (Proposition 2.10) — and one
assembly step: Fourier inversion on `ℝ/ℤ`, the evaluation of the Gaussian
Fourier transform, and the collection of the arc-centre coefficients into the
lattice density via the finite Fourier identity (37).  Under the discipline of
this development the analytic inputs are transcribed as *definitions*
(`SquareMinor`, `SquareMajor` — never axioms), and this file proves the
assembly step:

  `squareLLT_of_arcs :  SquareMinor g → SquareMajor g → SquareLLT g`,

so that the derivation of the local limit theorem (5) from the two named
square-method estimates is certified by the kernel.  (The tail clause (6) of
Theorem 1.1 is the transcription `SquareTail` of Proposition 2.10 itself, so
there is nothing to assemble on that side.)

## Encoding notes

* `sqPhi g x θ = ∑_{1 ≤ n ≤ x} e(θ·g(n²))` is the **unnormalised** exponential
  sum: `sqPhi = x · Φ_x` in the paper's notation.  The bounds in `SquareMinor`
  and `SquareMajor` carry the factor `x` accordingly.
* The arc radius is the paper's `T/√L` with `T = log L`, `L = log_b x`
  (`arcRad`).  The circle `ℝ/ℤ` is realised as the fundamental window
  `(−1/(2d_g), 1 − 1/(2d_g)]`: every lattice point `j/d_g`, `0 ≤ j < d_g`,
  is interior to it once `arcRad < 1/(2d_g)`, so no arc wraps around.
* `SquareMinor` transcribes Corollary 2.7 on this window: for every `B > 0`
  the integral of `‖sqPhi‖` over the window minus the arcs is
  `≤ C·x·L^{−B}` for large `L`.  On the window, the removed set
  `⋃_j (j/d − T/√L, j/d + T/√L]` differs from the paper's
  `{θ : dist(θ, d⁻¹ℤ) ≤ T/√L}` only by endpoints, a set of measure zero.
* `SquareMajor` transcribes Proposition 2.8 with the remainder eliminated:
  the pointwise decomposition `Φ = η_j·e(2μLu)·exp(−4π²σ²Lu²) + R_{j,x}(u)`
  together with `∑_j ∫|R_{j,x}| ≪ (log L)^{5+ε}/L` is exactly the statement
  that the integrated distance from `Φ` to the Gaussian model is
  `≪ (log L)^{5+ε}/L`.  The arc-centre coefficients are the `etaSq` of
  `DSS/RhoFourier.lean`, and (37) (`rhoSq_fourier`) closes the circle.
* Quantifier order in both transcriptions is `∀ (B or ε), ∃ C, ∃ L₀, ∀ x`,
  matching the paper's fixed-`ε` uniformity in `x` and `k`, as for `mmr`.

Nothing in this file is conditional: it imports no axioms; `SquareMinor` and
`SquareMajor` are definitions, and `squareLLT_of_arcs` is proved.
-/
import DSS.SquareLLT
import DSS.RhoFourier

namespace DSS

open Finset MeasureTheory intervalIntegral

variable {b : ℕ}

/-! ### The exponential sum, the arcs, and the two transcriptions -/

/-- The unnormalised exponential sum `∑_{1 ≤ n ≤ x} e(θ·g(n²))`
(the paper's `x·Φ_x(θ)`). -/
noncomputable def sqPhi (g : Weight b) (x θ : ℝ) : ℂ :=
  ∑ n ∈ intsLE x, ee (θ * ((g.eval (n ^ 2) : ℤ) : ℝ))

/-- The arc radius `T/√L`, `T = log L`, `L = log_b x`. -/
noncomputable def arcRad (b : ℕ) (x : ℝ) : ℝ :=
  Real.log (Real.logb b x) / Real.sqrt (Real.logb b x)

/-- The left endpoint `−1/(2d_g)` of the fundamental window. -/
noncomputable def sqWin (g : Weight b) : ℝ := -(1 / (2 * (g.dg : ℝ)))

/-- The major arc `(j/d_g − T/√L, j/d_g + T/√L]` about the `j`-th lattice
point. -/
def arcIoc (g : Weight b) (x : ℝ) (j : ℕ) : Set ℝ :=
  Set.Ioc ((j : ℝ) / (g.dg : ℝ) - arcRad b x) ((j : ℝ) / (g.dg : ℝ) + arcRad b x)

/-- The minor arcs: the fundamental window minus the major arcs. -/
def minorSet (g : Weight b) (x : ℝ) : Set ℝ :=
  Set.Ioc (sqWin g) (sqWin g + 1) \ ⋃ j ∈ range g.dg, arcIoc g x j

/-- The Gaussian model on the `j`-th arc: `x·η_j·e(2μ_gLu)·exp(−4π²σ_g²Lu²)`
(the paper's main term in Proposition 2.8, times `x` since `sqPhi` is
unnormalised). -/
noncomputable def arcMain (g : Weight b) (x : ℝ) (j : ℕ) (u : ℝ) : ℂ :=
  (x : ℂ) * (etaSq g j * ee (2 * g.mu * Real.logb b x * u)
    * ((Real.exp (-(4 * Real.pi ^ 2 * g.sigSq * Real.logb b x * u ^ 2)) : ℝ) : ℂ))

/-- **`SquareMinor g`: the conclusion of Corollary 2.7 for `g`** (the
integrated minor-arc estimate), transcribed on the fundamental window.  A
definition, not an axiom. -/
def SquareMinor (g : Weight b) : Prop :=
  ∀ B : ℝ, 0 < B → ∃ C : ℝ, 0 ≤ C ∧ ∃ L₀ : ℝ, ∀ x : ℝ,
    L₀ ≤ Real.logb b x →
      ∫ θ in minorSet g x, ‖sqPhi g x θ‖ ≤ C * x * Real.logb b x ^ (-B)

/-- **`SquareMajor g`: the conclusion of Proposition 2.8 for `g`** (the
shrinking major-arc Gaussian expansion), transcribed with the remainder
`R_{j,x}` eliminated: the integrated distance of `sqPhi` from the Gaussian
model over the `d_g` arcs is `≤ C·x·(log L)^{5+ε}/L`.  A definition, not an
axiom. -/
def SquareMajor (g : Weight b) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∃ L₀ : ℝ, ∀ x : ℝ,
    L₀ ≤ Real.logb b x →
      ∑ j ∈ range g.dg, ∫ u in (-(arcRad b x))..(arcRad b x),
          ‖sqPhi g x ((j : ℝ) / (g.dg : ℝ) + u) - arcMain g x j u‖
        ≤ C * x * Real.log (Real.logb b x) ^ (5 + ε) / Real.logb b x

/-! ### Continuity -/

lemma continuous_ee_lin (c : ℝ) : Continuous fun θ : ℝ => ee (θ * c) := by
  unfold ee
  fun_prop

lemma continuous_sqPhi (g : Weight b) (x : ℝ) : Continuous (sqPhi g x) := by
  unfold sqPhi
  exact continuous_finsetSum _ fun n _ => continuous_ee_lin _

/-! ### Orthogonality and Fourier inversion on the window -/

/-- `∫_a^{a+1} e(θm) dθ = [m = 0]` for `m ∈ ℤ`: orthogonality of characters
over any length-one window. -/
lemma integral_ee_mul_int (m : ℤ) (a : ℝ) :
    ∫ θ in a..(a + 1), ee (θ * (m : ℝ)) = if m = 0 then 1 else 0 := by
  rcases eq_or_ne m 0 with rfl | hm
  · simp only [Int.cast_zero, mul_zero]
    have h1 : ∀ θ : ℝ, ee (0 : ℝ) = (1 : ℂ) := by
      intro θ
      unfold ee
      simp
    rw [show (fun _ : ℝ => ee (0 : ℝ)) = fun _ : ℝ => (1 : ℂ) from funext h1]
    simp
  · rw [if_neg hm]
    have hc : (2 * (Real.pi : ℂ) * Complex.I * (m : ℂ)) ≠ 0 := by
      apply mul_ne_zero
      apply mul_ne_zero
      apply mul_ne_zero
      · norm_num
      · exact_mod_cast Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
      · exact Complex.I_ne_zero
      · exact_mod_cast Int.cast_ne_zero.mpr hm
    have hrw : ∀ θ : ℝ, ee (θ * (m : ℝ))
        = Complex.exp ((2 * (Real.pi : ℂ) * Complex.I * (m : ℂ)) * (θ : ℂ)) := by
      intro θ
      unfold ee
      congr 1
      push_cast
      ring
    calc ∫ θ in a..(a + 1), ee (θ * (m : ℝ))
        = ∫ θ in a..(a + 1),
            Complex.exp ((2 * (Real.pi : ℂ) * Complex.I * (m : ℂ)) * (θ : ℂ)) :=
          intervalIntegral.integral_congr fun θ _ => hrw θ
      _ = (Complex.exp ((2 * (Real.pi : ℂ) * Complex.I * (m : ℂ)) * ((a + 1 : ℝ) : ℂ))
            - Complex.exp ((2 * (Real.pi : ℂ) * Complex.I * (m : ℂ)) * ((a : ℝ) : ℂ)))
            / (2 * (Real.pi : ℂ) * Complex.I * (m : ℂ)) := integral_exp_mul_complex hc
      _ = 0 := by
          have h1 : (2 * (Real.pi : ℂ) * Complex.I * (m : ℂ)) * ((a + 1 : ℝ) : ℂ)
              = (2 * (Real.pi : ℂ) * Complex.I * (m : ℂ)) * ((a : ℝ) : ℂ)
                + (m : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
            push_cast
            ring
          rw [h1, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one,
            sub_self, zero_div]

/-- **Fourier inversion:** integrating `sqPhi(θ)·e(−θk)` over the fundamental
window counts the solutions of `g(n²) = k`. -/
lemma sqPhi_inversion (g : Weight b) (x : ℝ) (k : ℤ) :
    ∫ θ in (sqWin g)..(sqWin g + 1), sqPhi g x θ * ee (-(θ * (k : ℝ)))
      = (sqCountEq g x k : ℂ) := by
  have hcong : ∀ θ : ℝ, sqPhi g x θ * ee (-(θ * (k : ℝ)))
      = ∑ n ∈ intsLE x, ee (θ * ((g.eval (n ^ 2) - k : ℤ) : ℝ)) := by
    intro θ
    unfold sqPhi
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [← ee_add]
    congr 1
    push_cast
    ring
  rw [intervalIntegral.integral_congr (fun θ _ => hcong θ),
    intervalIntegral.integral_finsetSum
      (fun n _ => (continuous_ee_lin _).intervalIntegrable _ _)]
  have hval : ∀ n ∈ intsLE x,
      (∫ θ in (sqWin g)..(sqWin g + 1), ee (θ * ((g.eval (n ^ 2) - k : ℤ) : ℝ)))
        = if g.eval (n ^ 2) = k then (1 : ℂ) else 0 := by
    intro n _
    rw [integral_ee_mul_int (g.eval (n ^ 2) - k) (sqWin g)]
    congr 1
    simp [sub_eq_zero]
  rw [Finset.sum_congr rfl hval]
  unfold sqCountEq
  rw [Finset.sum_boole]

/-! ### Splitting the window into arcs and minor set -/

lemma arc_subset_window (g : Weight b) (x : ℝ)
    (hδ : arcRad b x < 1 / (2 * (g.dg : ℝ))) {j : ℕ} (hj : j ∈ range g.dg) :
    arcIoc g x j ⊆ Set.Ioc (sqWin g) (sqWin g + 1) := by
  have hd0 : (0 : ℝ) < (g.dg : ℝ) := by exact_mod_cast g.dg_pos
  have hjd : (j : ℝ) ≤ (g.dg : ℝ) - 1 := by
    have h1 : j + 1 ≤ g.dg := mem_range.mp hj
    have h2 : ((j + 1 : ℕ) : ℝ) ≤ ((g.dg : ℕ) : ℝ) := by exact_mod_cast h1
    push_cast at h2
    linarith
  have hj0 : (0 : ℝ) ≤ (j : ℝ) := by positivity
  apply Set.Ioc_subset_Ioc
  · unfold sqWin
    have h1 : (0 : ℝ) ≤ (j : ℝ) / (g.dg : ℝ) := by positivity
    linarith
  · unfold sqWin
    have hdne : (g.dg : ℝ) ≠ 0 := ne_of_gt hd0
    have h2 : (j : ℝ) / (g.dg : ℝ) ≤ ((g.dg : ℝ) - 1) / (g.dg : ℝ) := by gcongr
    have h3 : ((g.dg : ℝ) - 1) / (g.dg : ℝ) = 1 - 1 / (g.dg : ℝ) := by
      field_simp
    have h4 : 1 / (2 * (g.dg : ℝ)) = 1 / (g.dg : ℝ) / 2 := by ring
    rw [h4] at hδ
    linarith

lemma arc_pairwise_disjoint (g : Weight b) (x : ℝ)
    (hδ : arcRad b x < 1 / (2 * (g.dg : ℝ))) :
    Set.Pairwise (↑(range g.dg) : Set ℕ) (Function.onFun Disjoint (arcIoc g x)) := by
  have hd0 : (0 : ℝ) < (g.dg : ℝ) := by exact_mod_cast g.dg_pos
  have h4 : 1 / (2 * (g.dg : ℝ)) = 1 / (g.dg : ℝ) / 2 := by ring
  rw [h4] at hδ
  have key : ∀ i j : ℕ, i < j →
      Disjoint (arcIoc g x i) (arcIoc g x j) := by
    intro i j h
    have hij1 : (i : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast h
    have h1 : 1 / (g.dg : ℝ) ≤ ((j : ℝ) - (i : ℝ)) / (g.dg : ℝ) := by
      gcongr
      linarith
    have h2 : ((j : ℝ) - (i : ℝ)) / (g.dg : ℝ)
        = (j : ℝ) / (g.dg : ℝ) - (i : ℝ) / (g.dg : ℝ) := by ring
    exact Set.Ioc_disjoint_Ioc_of_le (by linarith)
  intro i hi j hj hij
  unfold Function.onFun
  rcases lt_or_gt_of_ne hij with h | h
  · exact key i j h
  · exact (key j i h).symm

/-- The window integral of a continuous function splits into the `d_g` arc
integrals plus the minor-set integral. -/
lemma window_split (g : Weight b) (x : ℝ)
    (hδ : arcRad b x < 1 / (2 * (g.dg : ℝ))) (F : ℝ → ℂ) (hF : Continuous F) :
    ∫ θ in Set.Ioc (sqWin g) (sqWin g + 1), F θ
      = (∑ j ∈ range g.dg, ∫ θ in arcIoc g x j, F θ) + ∫ θ in minorSet g x, F θ := by
  have hwin : IntegrableOn F (Set.Ioc (sqWin g) (sqWin g + 1)) := by
    have h1 : IntervalIntegrable F volume (sqWin g) (sqWin g + 1) :=
      hF.intervalIntegrable _ _
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)).mp h1
  have hsubU : (⋃ j ∈ range g.dg, arcIoc g x j) ⊆ Set.Ioc (sqWin g) (sqWin g + 1) :=
    Set.iUnion₂_subset fun j hj => arc_subset_window g x hδ hj
  have hmeasU : MeasurableSet (⋃ j ∈ range g.dg, arcIoc g x j) :=
    (range g.dg).measurableSet_biUnion fun j _ => measurableSet_Ioc
  have hintU : IntegrableOn F (⋃ j ∈ range g.dg, arcIoc g x j) := hwin.mono_set hsubU
  have hintM : IntegrableOn F (minorSet g x) := hwin.mono_set Set.sdiff_subset
  have hcover : (⋃ j ∈ range g.dg, arcIoc g x j) ∪ minorSet g x
      = Set.Ioc (sqWin g) (sqWin g + 1) := Set.union_sdiff_cancel hsubU
  calc ∫ θ in Set.Ioc (sqWin g) (sqWin g + 1), F θ
      = ∫ θ in (⋃ j ∈ range g.dg, arcIoc g x j) ∪ minorSet g x, F θ := by
        rw [hcover]
    _ = (∫ θ in ⋃ j ∈ range g.dg, arcIoc g x j, F θ) + ∫ θ in minorSet g x, F θ :=
        setIntegral_union disjoint_sdiff_self_right (measurableSet_Ioc.diff hmeasU)
          hintU hintM
    _ = (∑ j ∈ range g.dg, ∫ θ in arcIoc g x j, F θ) + ∫ θ in minorSet g x, F θ := by
        congr 1
        exact integral_biUnion_finset (range g.dg) (fun j _ => measurableSet_Ioc)
          (arc_pairwise_disjoint g x hδ)
          (fun j hj => hwin.mono_set (arc_subset_window g x hδ hj))

/-! ### Reducing an arc to a centred interval -/

/-- The `j`-th arc integral, translated to the centred interval and with the
arc-centre character pulled out. -/
lemma arc_integral_eq (g : Weight b) (x : ℝ) (k : ℤ) (j : ℕ)
    (hδ0 : 0 ≤ arcRad b x) :
    ∫ θ in arcIoc g x j, sqPhi g x θ * ee (-(θ * (k : ℝ)))
      = ee (-((j : ℝ) / (g.dg : ℝ) * (k : ℝ)))
        * ∫ u in (-(arcRad b x))..(arcRad b x),
            sqPhi g x ((j : ℝ) / (g.dg : ℝ) + u) * ee (-(u * (k : ℝ))) := by
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = (j : ℝ) / (g.dg : ℝ) := ⟨_, rfl⟩
  obtain ⟨δ, hδeq⟩ : ∃ δ : ℝ, δ = arcRad b x := ⟨_, rfl⟩
  rw [← hδeq] at hδ0
  rw [← hc, ← hδeq]
  have h1 : (∫ θ in (c - δ)..(c + δ), sqPhi g x θ * ee (-(θ * (k : ℝ))))
      = ∫ θ in arcIoc g x j, sqPhi g x θ * ee (-(θ * (k : ℝ))) := by
    rw [intervalIntegral.integral_of_le (by linarith)]
    rw [hc, hδeq]
    rfl
  have h2 := intervalIntegral.integral_comp_add_right
    (a := -δ) (b := δ) (f := fun θ => sqPhi g x θ * ee (-(θ * (k : ℝ)))) c
  rw [show -δ + c = c - δ by ring, show δ + c = c + δ by ring] at h2
  have h3 : (∫ u in (-δ)..δ,
        (fun θ => sqPhi g x θ * ee (-(θ * (k : ℝ)))) (u + c))
      = ee (-(c * (k : ℝ))) * ∫ u in (-δ)..δ,
          sqPhi g x (c + u) * ee (-(u * (k : ℝ))) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun u _ => ?_
    show sqPhi g x (u + c) * ee (-((u + c) * (k : ℝ)))
      = ee (-(c * (k : ℝ))) * (sqPhi g x (c + u) * ee (-(u * (k : ℝ))))
    rw [show u + c = c + u from add_comm u c,
      show -((c + u) * (k : ℝ)) = -(c * (k : ℝ)) + -(u * (k : ℝ)) by ring,
      ee_add]
    ring
  rw [← h1, ← h2, h3]

/-! ### The Gaussian Fourier transform and its tail -/

lemma norm_ee (t : ℝ) : ‖ee t‖ = 1 := by
  unfold ee
  rw [show 2 * (Real.pi : ℂ) * Complex.I * ((t : ℝ) : ℂ)
      = ((2 * Real.pi * t : ℝ) : ℂ) * Complex.I from by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

lemma norm_etaSq_le_one (g : Weight b) (j : ℕ) : ‖etaSq g j‖ ≤ 1 := by
  unfold etaSq
  have hd0 : (0 : ℝ) < (g.dg : ℝ) := by exact_mod_cast g.dg_pos
  rw [norm_mul]
  have h1 : ‖((g.dg : ℕ) : ℂ)⁻¹‖ = 1 / (g.dg : ℝ) := by
    rw [norm_inv]
    have hbc : ((g.dg : ℕ) : ℂ) = (((g.dg : ℕ) : ℝ) : ℂ) := by push_cast; ring
    rw [hbc, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hd0, one_div]
  have h2 : ‖∑ r ∈ range g.dg,
      ee ((j : ℝ) * (((g.w 1 * (r : ℤ) ^ 2 : ℤ) : ℝ) / (g.dg : ℝ)))‖ ≤ (g.dg : ℝ) := by
    calc ‖∑ r ∈ range g.dg,
        ee ((j : ℝ) * (((g.w 1 * (r : ℤ) ^ 2 : ℤ) : ℝ) / (g.dg : ℝ)))‖
        ≤ ∑ r ∈ range g.dg,
            ‖ee ((j : ℝ) * (((g.w 1 * (r : ℤ) ^ 2 : ℤ) : ℝ) / (g.dg : ℝ)))‖ :=
          norm_sum_le _ _
      _ = ∑ _r ∈ range g.dg, (1 : ℝ) :=
          Finset.sum_congr rfl fun r _ => norm_ee _
      _ = (g.dg : ℝ) := by simp
  calc ‖((g.dg : ℕ) : ℂ)⁻¹‖ * ‖∑ r ∈ range g.dg,
      ee ((j : ℝ) * (((g.w 1 * (r : ℤ) ^ 2 : ℤ) : ℝ) / (g.dg : ℝ)))‖
      ≤ 1 / (g.dg : ℝ) * (g.dg : ℝ) := by
        rw [h1]
        exact mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = 1 := by field_simp

/-- **The Gaussian Fourier transform**: for `α > 0` and `β ∈ ℝ`,
`∫_ℝ e(βu)·exp(−αu²) du = √(π/α)·exp(−π²β²/α)`. -/
lemma integral_ee_gaussian {α : ℝ} (hα : 0 < α) (β : ℝ) :
    ∫ u : ℝ, ee (β * u) * ((Real.exp (-(α * u ^ 2)) : ℝ) : ℂ)
      = ((Real.sqrt (Real.pi / α) * Real.exp (-(Real.pi ^ 2 * β ^ 2 / α)) : ℝ) : ℂ) := by
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = -(Real.pi * β / α) := ⟨_, rfl⟩
  have hαne : α ≠ 0 := ne_of_gt hα
  have hαc : α * c = -(Real.pi * β) := by rw [hc]; field_simp
  have hαc2 : α * c ^ 2 = Real.pi ^ 2 * β ^ 2 / α := by
    rw [hc]; field_simp; try ring
  have hbre : (0 : ℝ) < ((α : ℂ)).re := by simpa using hα
  have hFT := GaussianFourier.integral_cexp_neg_mul_sq_add_real_mul_I (b := (α : ℂ)) hbre c
  have hpt : ∀ u : ℝ, ee (β * u) * ((Real.exp (-(α * u ^ 2)) : ℝ) : ℂ)
      = ((Real.exp (-(α * c ^ 2)) : ℝ) : ℂ)
          * Complex.exp (-(α : ℂ) * (((u : ℝ) : ℂ) + (c : ℂ) * Complex.I) ^ 2) := by
    intro u
    unfold ee
    rw [Complex.ofReal_exp, Complex.ofReal_exp, ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    have expand : (-(α : ℂ) * (((u : ℝ) : ℂ) + (c : ℂ) * Complex.I) ^ 2)
        = -(α : ℂ) * ((u : ℝ) : ℂ) ^ 2
          - 2 * ((α * c : ℝ) : ℂ) * ((u : ℝ) : ℂ) * Complex.I
          - ((α * c ^ 2 : ℝ) : ℂ) * Complex.I ^ 2 := by
      push_cast
      ring
    rw [expand, Complex.I_sq,
      show ((α * c : ℝ) : ℂ) = ((-(Real.pi * β) : ℝ) : ℂ) from by rw [hαc]]
    push_cast
    ring
  calc ∫ u : ℝ, ee (β * u) * ((Real.exp (-(α * u ^ 2)) : ℝ) : ℂ)
      = ∫ u : ℝ, ((Real.exp (-(α * c ^ 2)) : ℝ) : ℂ)
          * Complex.exp (-(α : ℂ) * (((u : ℝ) : ℂ) + (c : ℂ) * Complex.I) ^ 2) := by
        simp only [hpt]
    _ = ((Real.exp (-(α * c ^ 2)) : ℝ) : ℂ)
          * ∫ u : ℝ, Complex.exp (-(α : ℂ) * (((u : ℝ) : ℂ) + (c : ℂ) * Complex.I) ^ 2) :=
        MeasureTheory.integral_const_mul _ _
    _ = ((Real.exp (-(α * c ^ 2)) : ℝ) : ℂ) * ((Real.pi : ℂ) / (α : ℂ)) ^ (1 / 2 : ℂ) := by
        rw [hFT]
    _ = ((Real.sqrt (Real.pi / α) * Real.exp (-(Real.pi ^ 2 * β ^ 2 / α)) : ℝ) : ℂ) := by
        have h1 : ((Real.pi : ℂ) / (α : ℂ)) = (((Real.pi / α : ℝ)) : ℂ) := by
          push_cast; ring
        have h2 : (0 : ℝ) ≤ Real.pi / α := le_of_lt (div_pos Real.pi_pos hα)
        rw [h1, show (1 / 2 : ℂ) = (((1 / 2 : ℝ)) : ℂ) from by norm_num,
          ← Complex.ofReal_cpow h2, ← Real.sqrt_eq_rpow,
          show -(α * c ^ 2) = -(Real.pi ^ 2 * β ^ 2 / α) from by rw [hαc2]]
        push_cast
        ring

/-- **The Gaussian tail**: cutting the Fourier integral at `±δ` costs at most
`exp(−αδ²/2)·√(π/(α/2))`. -/
lemma gaussian_tail_bound {α : ℝ} (hα : 0 < α) (β δ : ℝ) (hδ : 0 ≤ δ) :
    ‖(∫ u : ℝ, ee (β * u) * ((Real.exp (-(α * u ^ 2)) : ℝ) : ℂ))
        - ∫ u in (-δ)..δ, ee (β * u) * ((Real.exp (-(α * u ^ 2)) : ℝ) : ℂ)‖
      ≤ Real.exp (-(α * δ ^ 2 / 2)) * Real.sqrt (Real.pi / (α / 2)) := by
  obtain ⟨G, hGdef⟩ : ∃ G : ℝ → ℂ,
      G = fun u => ee (β * u) * ((Real.exp (-(α * u ^ 2)) : ℝ) : ℂ) := ⟨_, rfl⟩
  have hGnorm : ∀ u : ℝ, ‖G u‖ = Real.exp (-(α * u ^ 2)) := by
    intro u
    rw [hGdef]
    simp only [norm_mul, norm_ee, one_mul, Complex.norm_real, Real.norm_eq_abs]
    exact abs_of_pos (Real.exp_pos _)
  have hGcont : Continuous G := by
    rw [hGdef]
    apply Continuous.mul
    · have h2 := continuous_ee_lin β
      have h3 : (fun u : ℝ => ee (u * β)) = fun u : ℝ => ee (β * u) := by
        funext u; rw [mul_comm]
      rw [h3] at h2
      exact h2
    · fun_prop
  have hintα : Integrable fun u : ℝ => Real.exp (-(α * u ^ 2)) := by
    have h1 := integrable_exp_neg_mul_sq hα
    have h2 : (fun u : ℝ => Real.exp (-α * u ^ 2))
        = fun u : ℝ => Real.exp (-(α * u ^ 2)) := by
      funext u; rw [neg_mul]
    rw [h2] at h1
    exact h1
  have hGint : Integrable G :=
    Integrable.mono' hintα hGcont.aestronglyMeasurable
      (Filter.Eventually.of_forall fun u => le_of_eq (hGnorm u))
  have hsplit : (∫ u : ℝ, G u) - (∫ u in Set.Ioc (-δ) δ, G u)
      = ∫ u in (Set.Ioc (-δ) δ)ᶜ, G u := by
    have h : (∫ u in Set.Ioc (-δ) δ, G u) + ∫ u in (Set.Ioc (-δ) δ)ᶜ, G u
        = ∫ u : ℝ, G u :=
      MeasureTheory.integral_add_compl measurableSet_Ioc hGint
    linear_combination h.symm
  rw [← hGdef, intervalIntegral.integral_of_le (by linarith : -δ ≤ δ), hsplit]
  have hint2 : Integrable fun u : ℝ => Real.exp (-(α / 2 * u ^ 2)) := by
    have h1 := integrable_exp_neg_mul_sq (by positivity : (0 : ℝ) < α / 2)
    have h2 : (fun u : ℝ => Real.exp (-(α / 2) * u ^ 2))
        = fun u : ℝ => Real.exp (-(α / 2 * u ^ 2)) := by
      funext u; rw [neg_mul]
    rw [h2] at h1
    exact h1
  calc ‖∫ u in (Set.Ioc (-δ) δ)ᶜ, G u‖
      ≤ ∫ u in (Set.Ioc (-δ) δ)ᶜ, ‖G u‖ := norm_integral_le_integral_norm _
    _ = ∫ u in (Set.Ioc (-δ) δ)ᶜ, Real.exp (-(α * u ^ 2)) := by
        simp only [hGnorm]
    _ ≤ ∫ u in (Set.Ioc (-δ) δ)ᶜ,
          Real.exp (-(α * δ ^ 2 / 2)) * Real.exp (-(α / 2 * u ^ 2)) := by
        apply setIntegral_mono_on
        · exact hintα.integrableOn
        · exact (hint2.const_mul _).integrableOn
        · exact measurableSet_Ioc.compl
        · intro u hu
          have hu2 : δ ^ 2 ≤ u ^ 2 := by
            simp only [Set.mem_compl_iff, Set.mem_Ioc, not_and, not_le] at hu
            by_cases h : u ≤ -δ
            · nlinarith
            · have h' : -δ < u := not_le.mp h
              have h2 := hu h'
              nlinarith
          rw [show -(α * u ^ 2) = (-(α * δ ^ 2 / 2) + -(α / 2 * u ^ 2))
                + (-(α / 2) * (u ^ 2 - δ ^ 2)) by ring,
            Real.exp_add]
          calc Real.exp (-(α * δ ^ 2 / 2) + -(α / 2 * u ^ 2))
                * Real.exp (-(α / 2) * (u ^ 2 - δ ^ 2))
              ≤ Real.exp (-(α * δ ^ 2 / 2) + -(α / 2 * u ^ 2)) * 1 := by
                apply mul_le_mul_of_nonneg_left _ (le_of_lt (Real.exp_pos _))
                rw [← Real.exp_zero]
                apply Real.exp_le_exp.mpr
                nlinarith
            _ = Real.exp (-(α * δ ^ 2 / 2)) * Real.exp (-(α / 2 * u ^ 2)) := by
                rw [mul_one, Real.exp_add]
    _ = Real.exp (-(α * δ ^ 2 / 2)) * ∫ u in (Set.Ioc (-δ) δ)ᶜ,
          Real.exp (-(α / 2 * u ^ 2)) := MeasureTheory.integral_const_mul _ _
    _ ≤ Real.exp (-(α * δ ^ 2 / 2)) * Real.sqrt (Real.pi / (α / 2)) := by
        apply mul_le_mul_of_nonneg_left _ (le_of_lt (Real.exp_pos _))
        calc ∫ u in (Set.Ioc (-δ) δ)ᶜ, Real.exp (-(α / 2 * u ^ 2))
            ≤ ∫ u : ℝ, Real.exp (-(α / 2 * u ^ 2)) :=
              setIntegral_le_integral hint2
                (Filter.Eventually.of_forall fun u => le_of_lt (Real.exp_pos _))
          _ = Real.sqrt (Real.pi / (α / 2)) := by
              have h1 := integral_gaussian (α / 2)
              have h2 : (fun u : ℝ => Real.exp (-(α / 2) * u ^ 2))
                  = fun u : ℝ => Real.exp (-(α / 2 * u ^ 2)) := by
                funext u; rw [neg_mul]
              rw [h2] at h1
              exact h1

private lemma rhoSq_le_dg (g : Weight b) (k : ℤ) : (rhoSq g k : ℝ) ≤ (g.dg : ℝ) := by
  have h1 : rhoSq g k ≤ g.dg := by
    calc rhoSq g k ≤ (range g.dg).card := Finset.card_filter_le _ _
      _ = g.dg := Finset.card_range _
  exact_mod_cast h1

/-! ### Small `x`: the trivial bound -/

/-- On any bounded range `2 < x`, `L ≤ L₀` the count and the main term are
each `O(x/L)`, so a large constant absorbs them (the encoding note of
`SquareLLT`). -/
lemma small_x_bound (g : Weight b) (hg : g.Coprime₁) {ε : ℝ} (hε : 0 < ε) (L₀ : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 2 < x → Real.logb b x ≤ L₀ → ∀ k : ℤ,
      |(sqCountEq g x k : ℝ) - sqMain g x k|
        ≤ C * x * (max 1 (Real.log (Real.logb (b : ℝ) x))) ^ (5 + ε)
            / Real.logb (b : ℝ) x := by
  have hσ := Weight.sigSq_pos hg
  have hb1 : (1 : ℝ) < (b : ℝ) := by
    have h1 : 1 < b := by have := g.hb; omega
    exact_mod_cast h1
  have hd0 : (0 : ℝ) < (g.dg : ℝ) := by exact_mod_cast g.dg_pos
  obtain ⟨Lm, hLm⟩ : ∃ Lm : ℝ, Lm = Real.logb b 2 := ⟨_, rfl⟩
  have hLm0 : 0 < Lm := by
    rw [hLm]
    exact Real.logb_pos hb1 (by norm_num)
  obtain ⟨L₁, hL₁⟩ : ∃ L₁ : ℝ, L₁ = max L₀ (Lm + 1) := ⟨_, rfl⟩
  have hL₁0 : 0 < L₁ := by
    rw [hL₁]
    have := le_max_right L₀ (Lm + 1)
    linarith
  refine ⟨L₁ * (1 + (g.dg : ℝ) / Real.sqrt (4 * Real.pi * g.sigSq * Lm)), ?_, ?_⟩
  · positivity
  intro x hx2 hxL k
  obtain ⟨L, hLdef⟩ : ∃ L : ℝ, L = Real.logb b x := ⟨_, rfl⟩
  rw [← hLdef] at hxL ⊢
  have hLlow : Lm < L := by
    rw [hLm, hLdef]
    exact Real.logb_lt_logb hb1 (by norm_num) hx2
  have hL0 : 0 < L := lt_trans hLm0 hLlow
  have hLL₁ : L ≤ L₁ := by
    rw [hL₁]
    exact le_trans hxL (le_max_left _ _)
  have hx0 : (0 : ℝ) < x := by linarith
  -- the count is at most `x`
  have hcount : (sqCountEq g x k : ℝ) ≤ x := by
    have h1 : sqCountEq g x k ≤ (intsLE x).card := Finset.card_filter_le _ _
    have h2 : (intsLE x).card = ⌊x⌋₊ := by
      unfold intsLE
      rw [Nat.card_Icc]
      omega
    have h3 : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le (le_of_lt hx0)
    calc (sqCountEq g x k : ℝ) ≤ ((intsLE x).card : ℝ) := by exact_mod_cast h1
      _ = (⌊x⌋₊ : ℝ) := by exact_mod_cast h2
      _ ≤ x := h3
  have hcount0 : (0 : ℝ) ≤ (sqCountEq g x k : ℝ) := by positivity
  -- the main term is at most `d·x/√(4πσ²L)`
  have hmain0 : 0 ≤ sqMain g x k := by
    unfold sqMain
    rw [← hLdef]
    positivity
  have hmain : sqMain g x k ≤ (g.dg : ℝ) * x / Real.sqrt (4 * Real.pi * g.sigSq * L) := by
    unfold sqMain
    rw [← hLdef]
    have hexp : Real.exp (-(((k : ℝ) - 2 * g.mu * L) ^ 2) / (4 * g.sigSq * L)) ≤ 1 := by
      rw [show (1 : ℝ) = Real.exp 0 from (Real.exp_zero).symm]
      apply Real.exp_le_exp.mpr
      have h3 : 0 ≤ (((k : ℝ) - 2 * g.mu * L) ^ 2) / (4 * g.sigSq * L) := by positivity
      rw [neg_div]
      linarith
    have hsq0 : 0 < Real.sqrt (4 * Real.pi * g.sigSq * L) := by
      apply Real.sqrt_pos.mpr
      positivity
    calc (rhoSq g k : ℝ) * x / Real.sqrt (4 * Real.pi * g.sigSq * L)
          * Real.exp (-(((k : ℝ) - 2 * g.mu * L) ^ 2) / (4 * g.sigSq * L))
        ≤ (rhoSq g k : ℝ) * x / Real.sqrt (4 * Real.pi * g.sigSq * L) * 1 := by
          apply mul_le_mul_of_nonneg_left hexp
          positivity
      _ = (rhoSq g k : ℝ) * x / Real.sqrt (4 * Real.pi * g.sigSq * L) := mul_one _
      _ ≤ (g.dg : ℝ) * x / Real.sqrt (4 * Real.pi * g.sigSq * L) := by
          gcongr
          exact_mod_cast rhoSq_le_dg g k
  -- assemble the trivial bound
  have hsqm0 : 0 < Real.sqrt (4 * Real.pi * g.sigSq * Lm) := by
    apply Real.sqrt_pos.mpr
    positivity
  have hmono : (g.dg : ℝ) / Real.sqrt (4 * Real.pi * g.sigSq * L)
      ≤ (g.dg : ℝ) / Real.sqrt (4 * Real.pi * g.sigSq * Lm) := by
    have hs : Real.sqrt (4 * Real.pi * g.sigSq * Lm)
        ≤ Real.sqrt (4 * Real.pi * g.sigSq * L) :=
      Real.sqrt_le_sqrt (by
        nlinarith [mul_pos (mul_pos (mul_pos (by norm_num : (0:ℝ) < 4) Real.pi_pos) hσ)
          (sub_pos.mpr hLlow)])
    gcongr
  have habs : |(sqCountEq g x k : ℝ) - sqMain g x k|
      ≤ x * (1 + (g.dg : ℝ) / Real.sqrt (4 * Real.pi * g.sigSq * Lm)) := by
    have h1 : |(sqCountEq g x k : ℝ) - sqMain g x k|
        ≤ (sqCountEq g x k : ℝ) + sqMain g x k := by
      rcases abs_cases ((sqCountEq g x k : ℝ) - sqMain g x k) with h | h <;>
        rw [h.1] <;> linarith
    have h2 : sqMain g x k ≤ x * ((g.dg : ℝ) / Real.sqrt (4 * Real.pi * g.sigSq * Lm)) := by
      calc sqMain g x k
          ≤ (g.dg : ℝ) * x / Real.sqrt (4 * Real.pi * g.sigSq * L) := hmain
        _ = x * ((g.dg : ℝ) / Real.sqrt (4 * Real.pi * g.sigSq * L)) := by ring
        _ ≤ x * ((g.dg : ℝ) / Real.sqrt (4 * Real.pi * g.sigSq * Lm)) := by
            apply mul_le_mul_of_nonneg_left hmono (le_of_lt hx0)
    have h3 : x * (1 + (g.dg : ℝ) / Real.sqrt (4 * Real.pi * g.sigSq * Lm))
        = x + x * ((g.dg : ℝ) / Real.sqrt (4 * Real.pi * g.sigSq * Lm)) := by ring
    linarith
  have hM5 : (1 : ℝ) ≤ (max 1 (Real.log L)) ^ (5 + ε) := by
    calc (1 : ℝ) = (1 : ℝ) ^ (5 + ε) := (Real.one_rpow _).symm
      _ ≤ (max 1 (Real.log L)) ^ (5 + ε) := by
          apply Real.rpow_le_rpow (by norm_num) (le_max_left _ _)
          linarith
  obtain ⟨D, hDdef⟩ : ∃ D : ℝ, D = 1 + (g.dg : ℝ) / Real.sqrt (4 * Real.pi * g.sigSq * Lm) :=
    ⟨_, rfl⟩
  have hD0 : 0 < D := by
    rw [hDdef]
    positivity
  rw [← hDdef] at habs ⊢
  have hL₁ne : L₁ ≠ 0 := ne_of_gt hL₁0
  calc |(sqCountEq g x k : ℝ) - sqMain g x k|
      ≤ x * D := habs
    _ = L₁ * D * x / L₁ := by field_simp
    _ ≤ L₁ * D * x / L := by
        gcongr
    _ = L₁ * D * x * 1 / L := by ring
    _ ≤ L₁ * D * x * (max 1 (Real.log L)) ^ (5 + ε) / L := by
        gcongr

/-! ### The assembly -/

private lemma log_le_four_sqrt_sqrt {L : ℝ} (hL : 1 ≤ L) :
    Real.log L ≤ 4 * Real.sqrt (Real.sqrt L) := by
  have h0 : (0 : ℝ) < L := by linarith
  have h1 : (0 : ℝ) < Real.sqrt L := Real.sqrt_pos.mpr h0
  have h2 : (0 : ℝ) < Real.sqrt (Real.sqrt L) := Real.sqrt_pos.mpr h1
  have h3 : Real.log L = 2 * Real.log (Real.sqrt L) := by
    rw [Real.log_sqrt (le_of_lt h0)]; ring
  have h4 : Real.log (Real.sqrt L) = 2 * Real.log (Real.sqrt (Real.sqrt L)) := by
    rw [Real.log_sqrt (le_of_lt h1)]; ring
  have h5 : Real.log (Real.sqrt (Real.sqrt L)) ≤ Real.sqrt (Real.sqrt L) - 1 :=
    Real.log_le_sub_one_of_pos h2
  rw [h3, h4]
  linarith

set_option maxHeartbeats 2000000 in
/-- **The Fourier assembly of Theorem 1.1 (the paper's §2.4):** the square
local limit theorem follows from the integrated minor-arc estimate and the
shrinking major-arc Gaussian expansion.  Proved — no axioms. -/
theorem squareLLT_of_arcs (g : Weight b) (hg : g.Coprime₁)
    (hminor : SquareMinor g) (hmajor : SquareMajor g) : SquareLLT g := by
  intro ε hε
  obtain ⟨C₁, hC₁0, L₁, hmin⟩ := hminor 2 (by norm_num)
  obtain ⟨C₂, hC₂0, L₂, hmaj⟩ := hmajor ε hε
  have hσ := Weight.sigSq_pos hg
  have hd0 : (0 : ℝ) < (g.dg : ℝ) := by exact_mod_cast g.dg_pos
  have hb1 : (1 : ℝ) < (b : ℝ) := by
    have h1 : 1 < b := by have := g.hb; omega
    exact_mod_cast h1
  have hπ := Real.pi_pos
  obtain ⟨L₀, hL₀def⟩ : ∃ L₀ : ℝ, L₀ = max (max L₁ L₂)
      (max (max (Real.exp 1) ((8 * (g.dg : ℝ)) ^ 4 + 1))
        (max (Real.exp (1 / (2 * Real.pi ^ 2 * g.sigSq) + 1))
          (1 / (2 * Real.pi * g.sigSq) + 1))) := ⟨_, rfl⟩
  obtain ⟨Cs, hCs0, hsmall⟩ := small_x_bound g hg hε L₀
  refine ⟨max Cs (C₁ + C₂ + (g.dg : ℝ)), le_trans hCs0 (le_max_left _ _), fun x hx2 k => ?_⟩
  have hx0 : (0 : ℝ) < x := by linarith
  have hLx0 : (0 : ℝ) < Real.logb (b : ℝ) x :=
    Real.logb_pos hb1 (by linarith)
  by_cases hbig : L₀ ≤ Real.logb (b : ℝ) x
  case neg =>
    have hsm := hsmall x hx2 (not_le.mp hbig).le k
    calc |(sqCountEq g x k : ℝ) - sqMain g x k|
        ≤ Cs * x * (max 1 (Real.log (Real.logb (b : ℝ) x))) ^ (5 + ε)
            / Real.logb (b : ℝ) x := hsm
      _ ≤ max Cs (C₁ + C₂ + (g.dg : ℝ)) * x
            * (max 1 (Real.log (Real.logb (b : ℝ) x))) ^ (5 + ε)
            / Real.logb (b : ℝ) x := by
          gcongr
          exact le_max_left _ _
  case pos =>
  -- names for the running quantities
  obtain ⟨L, hLdef⟩ : ∃ L : ℝ, L = Real.logb (b : ℝ) x := ⟨_, rfl⟩
  obtain ⟨T, hTdef⟩ : ∃ T : ℝ, T = Real.log L := ⟨_, rfl⟩
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ, δ = arcRad b x := ⟨_, rfl⟩
  obtain ⟨α, hαdef⟩ : ∃ α : ℝ, α = 4 * Real.pi ^ 2 * g.sigSq * L := ⟨_, rfl⟩
  obtain ⟨β, hβdef⟩ : ∃ β : ℝ, β = 2 * g.mu * L - (k : ℝ) := ⟨_, rfl⟩
  rw [← hLdef] at hbig hLx0
  -- threshold components
  have hcomp1 : L₁ ≤ L := le_trans (by
    rw [hL₀def]; exact le_trans (le_max_left _ _) (le_max_left _ _)) hbig
  have hcomp2 : L₂ ≤ L := le_trans (by
    rw [hL₀def]; exact le_trans (le_max_right _ _) (le_max_left _ _)) hbig
  have hcomp3 : Real.exp 1 ≤ L := le_trans (by
    rw [hL₀def]; exact le_trans (le_trans (le_max_left _ _) (le_max_left _ _))
      (le_max_right _ _)) hbig
  have hcomp4 : (8 * (g.dg : ℝ)) ^ 4 + 1 ≤ L := le_trans (by
    rw [hL₀def]; exact le_trans (le_trans (le_max_right _ _) (le_max_left _ _))
      (le_max_right _ _)) hbig
  have hcomp5 : Real.exp (1 / (2 * Real.pi ^ 2 * g.sigSq) + 1) ≤ L := le_trans (by
    rw [hL₀def]; exact le_trans (le_trans (le_max_left _ _) (le_max_right _ _))
      (le_max_right _ _)) hbig
  have hcomp6 : 1 / (2 * Real.pi * g.sigSq) + 1 ≤ L := le_trans (by
    rw [hL₀def]; exact le_trans (le_trans (le_max_right _ _) (le_max_right _ _))
      (le_max_right _ _)) hbig
  -- derived facts
  have hexp1 : (1 : ℝ) < Real.exp 1 := by
    have := Real.add_one_le_exp 1
    linarith
  have hL1 : (1 : ℝ) < L := lt_of_lt_of_le hexp1 hcomp3
  have hL0 : (0 : ℝ) < L := by linarith
  have hLne : L ≠ 0 := ne_of_gt hL0
  have hσne : g.sigSq ≠ 0 := ne_of_gt hσ
  have hπne : Real.pi ≠ 0 := Real.pi_ne_zero
  have hT1 : (1 : ℝ) ≤ T := by
    rw [hTdef, Real.le_log_iff_exp_le hL0]
    exact hcomp3
  have hT0 : (0 : ℝ) < T := by linarith
  have hδT : δ = T / Real.sqrt L := by
    rw [hδdef]
    unfold arcRad
    rw [← hLdef, ← hTdef]
  have hsqL0 : (0 : ℝ) < Real.sqrt L := Real.sqrt_pos.mpr hL0
  have hδ0 : (0 : ℝ) < δ := by
    rw [hδT]
    positivity
  have hα0 : (0 : ℝ) < α := by rw [hαdef]; positivity
  have hσL1 : (1 : ℝ) ≤ 2 * Real.pi * g.sigSq * L := by
    have h1 : 0 < 2 * Real.pi * g.sigSq := by positivity
    have hinv : (2 * Real.pi * g.sigSq) * (1 / (2 * Real.pi * g.sigSq)) = 1 := by
      field_simp
    have h3 := mul_le_mul_of_nonneg_left hcomp6 (le_of_lt h1)
    nlinarith
  have hTσ : (1 : ℝ) ≤ 2 * Real.pi ^ 2 * g.sigSq * T := by
    have h1 : 1 / (2 * Real.pi ^ 2 * g.sigSq) + 1 ≤ T := by
      rw [hTdef, Real.le_log_iff_exp_le hL0]
      exact hcomp5
    have h2 : 0 < 2 * Real.pi ^ 2 * g.sigSq := by positivity
    have h3 : (2 * Real.pi ^ 2 * g.sigSq) * (1 / (2 * Real.pi ^ 2 * g.sigSq)) = 1 := by
      field_simp
    have h4 := mul_le_mul_of_nonneg_left h1 (le_of_lt h2)
    nlinarith
  -- the geometric constraint `δ < 1/(2d)`
  have hss0 : (0 : ℝ) < Real.sqrt (Real.sqrt L) := Real.sqrt_pos.mpr hsqL0
  have hδsmall : δ < 1 / (2 * (g.dg : ℝ)) := by
    obtain ⟨s, hsdef⟩ : ∃ s : ℝ, s = Real.sqrt (Real.sqrt L) := ⟨_, rfl⟩
    have hs0 : (0 : ℝ) < s := by rw [hsdef]; exact hss0
    have hsne : s ≠ 0 := ne_of_gt hs0
    have hlog : Real.log L ≤ 4 * s := by
      rw [hsdef]
      exact log_le_four_sqrt_sqrt (le_of_lt hL1)
    have hs4 : (8 * (g.dg : ℝ)) ^ 2 < Real.sqrt L := by
      have h1 : Real.sqrt ((8 * (g.dg : ℝ)) ^ 4) < Real.sqrt L := by
        apply Real.sqrt_lt_sqrt (by positivity)
        linarith
      have h2 : ((8 * (g.dg : ℝ)) ^ 2) ^ 2 = (8 * (g.dg : ℝ)) ^ 4 := by ring
      rw [← h2, Real.sqrt_sq (by positivity)] at h1
      exact h1
    have hss : 8 * (g.dg : ℝ) < s := by
      rw [hsdef]
      have h1 : Real.sqrt ((8 * (g.dg : ℝ)) ^ 2) < Real.sqrt (Real.sqrt L) :=
        Real.sqrt_lt_sqrt (by positivity) hs4
      rw [Real.sqrt_sq (by positivity)] at h1
      exact h1
    have hmulself : s * s = Real.sqrt L := by
      rw [hsdef]
      exact Real.mul_self_sqrt (Real.sqrt_nonneg L)
    rw [hδT, ← hmulself]
    have hss2 : (0 : ℝ) < s * s := by positivity
    calc T / (s * s) ≤ (4 * s) / (s * s) := by
          gcongr
          rw [hTdef]
          exact hlog
      _ = 4 / s := by
          field_simp
          try ring
      _ < 1 / (2 * (g.dg : ℝ)) := by
          rw [div_lt_div_iff₀ hs0 (by positivity)]
          nlinarith
  -- the two inputs at this `x`
  have hLcomp1 : L₁ ≤ Real.logb (b : ℝ) x := by rw [← hLdef]; exact hcomp1
  have hLcomp2 : L₂ ≤ Real.logb (b : ℝ) x := by rw [← hLdef]; exact hcomp2
  have hminor' := hmin x hLcomp1
  have hmajor' := hmaj x hLcomp2
  rw [← hLdef] at hminor'
  rw [← hLdef, ← hTdef, ← hδdef] at hmajor'
  -- continuity packages
  have heeK : Continuous fun u : ℝ => ee (-(u * (k : ℝ))) := by
    have h2 := continuous_ee_lin (-(k : ℝ))
    have h3 : (fun u : ℝ => ee (u * -(k : ℝ))) = fun u : ℝ => ee (-(u * (k : ℝ))) := by
      funext u
      congr 1
      ring
    rw [h3] at h2
    exact h2
  have hFcont : Continuous fun θ : ℝ => sqPhi g x θ * ee (-(θ * (k : ℝ))) :=
    (continuous_sqPhi g x).mul heeK
  have hee2μ : Continuous fun u : ℝ => ee (2 * g.mu * Real.logb (b : ℝ) x * u) := by
    have h2 := continuous_ee_lin (2 * g.mu * Real.logb (b : ℝ) x)
    have h3 : (fun u : ℝ => ee (u * (2 * g.mu * Real.logb (b : ℝ) x)))
        = fun u : ℝ => ee (2 * g.mu * Real.logb (b : ℝ) x * u) := by
      funext u
      congr 1
      ring
    rw [h3] at h2
    exact h2
  have harcCont : ∀ j : ℕ, Continuous (arcMain g x j) := by
    intro j
    unfold arcMain
    apply continuous_const.mul
    apply Continuous.mul
    · exact continuous_const.mul hee2μ
    · fun_prop
  have heeβ : Continuous fun u : ℝ => ee (β * u) := by
    have h2 := continuous_ee_lin β
    have h3 : (fun u : ℝ => ee (u * β)) = fun u : ℝ => ee (β * u) := by
      funext u
      congr 1
      ring
    rw [h3] at h2
    exact h2
  have hGcont : Continuous fun u : ℝ => ee (β * u) * ((Real.exp (-(α * u ^ 2)) : ℝ) : ℂ) := by
    apply heeβ.mul
    fun_prop
  -- the centred Gaussian integrals and arc remainders
  obtain ⟨Gδ, hGδdef⟩ : ∃ z : ℂ,
      z = ∫ u in (-δ)..δ, ee (β * u) * ((Real.exp (-(α * u ^ 2)) : ℝ) : ℂ) := ⟨_, rfl⟩
  obtain ⟨GR, hGRdef⟩ : ∃ z : ℂ,
      z = ∫ u : ℝ, ee (β * u) * ((Real.exp (-(α * u ^ 2)) : ℝ) : ℂ) := ⟨_, rfl⟩
  obtain ⟨Rj, hRjdef⟩ : ∃ R : ℕ → ℂ, R = fun j : ℕ =>
      ∫ u in (-δ)..δ, (sqPhi g x ((j : ℝ) / (g.dg : ℝ) + u) - arcMain g x j u)
        * ee (-(u * (k : ℝ))) := ⟨_, rfl⟩
  -- the arc decomposition
  have hdec : ∀ j : ℕ,
      (∫ u in (-δ)..δ, sqPhi g x ((j : ℝ) / (g.dg : ℝ) + u) * ee (-(u * (k : ℝ))))
      = Rj j + ((x : ℂ) * etaSq g j) * Gδ := by
    intro j
    simp only [hRjdef, hGδdef]
    have hptw : ∀ u : ℝ, sqPhi g x ((j : ℝ) / (g.dg : ℝ) + u) * ee (-(u * (k : ℝ)))
        = (sqPhi g x ((j : ℝ) / (g.dg : ℝ) + u) - arcMain g x j u) * ee (-(u * (k : ℝ)))
          + ((x : ℂ) * etaSq g j)
              * (ee (β * u) * ((Real.exp (-(α * u ^ 2)) : ℝ) : ℂ)) := by
      intro u
      have he : ee (2 * g.mu * Real.logb (b : ℝ) x * u) * ee (-(u * (k : ℝ)))
          = ee (β * u) := by
        rw [← ee_add]
        congr 1
        rw [hβdef, hLdef]
        ring
      have hexp : ((Real.exp (-(4 * Real.pi ^ 2 * g.sigSq * Real.logb (b : ℝ) x * u ^ 2)) : ℝ) : ℂ)
          = ((Real.exp (-(α * u ^ 2)) : ℝ) : ℂ) := by
        rw [hαdef, hLdef]
      have harc : arcMain g x j u * ee (-(u * (k : ℝ)))
          = ((x : ℂ) * etaSq g j)
              * (ee (β * u) * ((Real.exp (-(α * u ^ 2)) : ℝ) : ℂ)) := by
        unfold arcMain
        calc (x : ℂ) * (etaSq g j * ee (2 * g.mu * Real.logb (b : ℝ) x * u)
              * ((Real.exp (-(4 * Real.pi ^ 2 * g.sigSq * Real.logb (b : ℝ) x * u ^ 2)) : ℝ) : ℂ))
              * ee (-(u * (k : ℝ)))
            = ((x : ℂ) * etaSq g j)
                * ((ee (2 * g.mu * Real.logb (b : ℝ) x * u) * ee (-(u * (k : ℝ))))
                  * ((Real.exp (-(4 * Real.pi ^ 2 * g.sigSq * Real.logb (b : ℝ) x * u ^ 2)) : ℝ) : ℂ)) := by
              ring
          _ = ((x : ℂ) * etaSq g j)
                * (ee (β * u) * ((Real.exp (-(α * u ^ 2)) : ℝ) : ℂ)) := by
              rw [he, hexp]
      calc sqPhi g x ((j : ℝ) / (g.dg : ℝ) + u) * ee (-(u * (k : ℝ)))
          = (sqPhi g x ((j : ℝ) / (g.dg : ℝ) + u) - arcMain g x j u) * ee (-(u * (k : ℝ)))
            + arcMain g x j u * ee (-(u * (k : ℝ))) := by ring
        _ = _ := by rw [harc]
    have hint1 : IntervalIntegrable (fun u =>
        (sqPhi g x ((j : ℝ) / (g.dg : ℝ) + u) - arcMain g x j u) * ee (-(u * (k : ℝ))))
        MeasureTheory.volume (-δ) δ := by
      apply Continuous.intervalIntegrable
      exact (((continuous_sqPhi g x).comp (continuous_const.add continuous_id)).sub
        (harcCont j)).mul heeK
    have hint2 : IntervalIntegrable (fun u =>
        ((x : ℂ) * etaSq g j) * (ee (β * u) * ((Real.exp (-(α * u ^ 2)) : ℝ) : ℂ)))
        MeasureTheory.volume (-δ) δ :=
      (continuous_const.mul hGcont).intervalIntegrable _ _
    rw [intervalIntegral.integral_congr fun u _ => hptw u,
      intervalIntegral.integral_add hint1 hint2,
      intervalIntegral.integral_const_mul]
  -- Fourier inversion, split, and per-arc reduction
  have hwinle : sqWin g ≤ sqWin g + 1 := by linarith
  have hδsmall' : arcRad b x < 1 / (2 * (g.dg : ℝ)) := by rw [← hδdef]; exact hδsmall
  have hcount : (sqCountEq g x k : ℂ)
      = (∑ j ∈ range g.dg, ee (-((j : ℝ) / (g.dg : ℝ) * (k : ℝ)))
          * (Rj j + ((x : ℂ) * etaSq g j) * Gδ))
        + ∫ θ in minorSet g x, sqPhi g x θ * ee (-(θ * (k : ℝ))) := by
    calc (sqCountEq g x k : ℂ)
        = ∫ θ in (sqWin g)..(sqWin g + 1), sqPhi g x θ * ee (-(θ * (k : ℝ))) :=
          (sqPhi_inversion g x k).symm
      _ = ∫ θ in Set.Ioc (sqWin g) (sqWin g + 1), sqPhi g x θ * ee (-(θ * (k : ℝ))) :=
          intervalIntegral.integral_of_le hwinle
      _ = (∑ j ∈ range g.dg, ∫ θ in arcIoc g x j, sqPhi g x θ * ee (-(θ * (k : ℝ))))
            + ∫ θ in minorSet g x, sqPhi g x θ * ee (-(θ * (k : ℝ))) :=
          window_split g x hδsmall' _ hFcont
      _ = _ := by
          congr 1
          refine Finset.sum_congr rfl fun j hj => ?_
          rw [arc_integral_eq g x k j (by rw [← hδdef]; exact le_of_lt hδ0)]
          rw [← hδdef, hdec j]
  -- the Fourier identity (37) with matched argument
  have h37' : ∑ j ∈ range g.dg, etaSq g j * ee (-((j : ℝ) / (g.dg : ℝ) * (k : ℝ)))
      = ((rhoSq g k : ℕ) : ℂ) := by
    rw [← rhoSq_fourier g k]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [show -((j : ℝ) / (g.dg : ℝ) * (k : ℝ)) = -((j : ℝ) * ((k : ℝ) / (g.dg : ℝ))) by ring]
  have hsplit2 : (∑ j ∈ range g.dg, ee (-((j : ℝ) / (g.dg : ℝ) * (k : ℝ)))
        * (Rj j + ((x : ℂ) * etaSq g j) * Gδ))
      = (∑ j ∈ range g.dg, ee (-((j : ℝ) / (g.dg : ℝ) * (k : ℝ))) * Rj j)
        + ((x : ℂ) * ((rhoSq g k : ℕ) : ℂ)) * Gδ := by
    rw [show (∑ j ∈ range g.dg, ee (-((j : ℝ) / (g.dg : ℝ) * (k : ℝ)))
          * (Rj j + ((x : ℂ) * etaSq g j) * Gδ))
        = ∑ j ∈ range g.dg, (ee (-((j : ℝ) / (g.dg : ℝ) * (k : ℝ))) * Rj j
          + ((x : ℂ) * (etaSq g j * ee (-((j : ℝ) / (g.dg : ℝ) * (k : ℝ))))) * Gδ) from
      Finset.sum_congr rfl fun j _ => by ring]
    rw [Finset.sum_add_distrib]
    congr 1
    rw [← Finset.sum_mul, ← Finset.mul_sum, h37']
  -- the Gaussian value and the main term
  have hGRval : GR = ((Real.sqrt (Real.pi / α)
      * Real.exp (-(Real.pi ^ 2 * β ^ 2 / α)) : ℝ) : ℂ) := by
    rw [hGRdef]
    exact integral_ee_gaussian hα0 β
  have hmainC : ((sqMain g x k : ℝ) : ℂ) = ((x : ℂ) * ((rhoSq g k : ℕ) : ℂ)) * GR := by
    rw [hGRval]
    have hsqrtv : Real.sqrt (Real.pi / α) = 1 / Real.sqrt (4 * Real.pi * g.sigSq * L) := by
      rw [hαdef]
      rw [show Real.pi / (4 * Real.pi ^ 2 * g.sigSq * L)
          = (4 * Real.pi * g.sigSq * L)⁻¹ from by
        field_simp
        try ring]
      rw [Real.sqrt_inv, one_div]
    have hargs : -(Real.pi ^ 2 * β ^ 2 / α)
        = -(((k : ℝ) - 2 * g.mu * L) ^ 2) / (4 * g.sigSq * L) := by
      rw [hαdef, hβdef, neg_div]
      congr 1
      field_simp
      ring
    unfold sqMain
    rw [← hLdef, hsqrtv, hargs]
    push_cast
    ring
  -- norms of the error pieces
  have hρnorm : ‖((rhoSq g k : ℕ) : ℂ)‖ = (rhoSq g k : ℝ) := by
    rw [show ((rhoSq g k : ℕ) : ℂ) = (((rhoSq g k : ℕ) : ℝ) : ℂ) from by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs]
    exact abs_of_nonneg (by positivity)
  have hxnorm : ‖((x : ℝ) : ℂ)‖ = x := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact abs_of_pos hx0
  have hT5 : (1 : ℝ) ≤ T ^ (5 + ε) := by
    calc (1 : ℝ) = (1 : ℝ) ^ (5 + ε) := (Real.one_rpow _).symm
      _ ≤ T ^ (5 + ε) := Real.rpow_le_rpow (by norm_num) hT1 (by linarith)
  have htail : ‖Gδ - GR‖ ≤ Real.exp (-(α * δ ^ 2 / 2)) * Real.sqrt (Real.pi / (α / 2)) := by
    rw [hGδdef, hGRdef, norm_sub_rev]
    exact gaussian_tail_bound hα0 β δ (le_of_lt hδ0)
  have htail2 : Real.exp (-(α * δ ^ 2 / 2)) * Real.sqrt (Real.pi / (α / 2))
      ≤ T ^ (5 + ε) / L := by
    have hδ2 : δ ^ 2 = T ^ 2 / L := by
      rw [hδT, div_pow, Real.sq_sqrt (le_of_lt hL0)]
    have hαδ : α * δ ^ 2 / 2 = 2 * Real.pi ^ 2 * g.sigSq * T ^ 2 := by
      rw [hαdef, hδ2]
      rw [show 4 * Real.pi ^ 2 * g.sigSq * L * (T ^ 2 / L) / 2
          = 2 * Real.pi ^ 2 * g.sigSq * (L / L) * T ^ 2 from by ring,
        div_self hLne, mul_one]
    have he1 : Real.exp (-(α * δ ^ 2 / 2)) ≤ 1 / L := by
      rw [hαδ]
      have h1 : T ≤ 2 * Real.pi ^ 2 * g.sigSq * T ^ 2 := by
        nlinarith [hTσ, hT0]
      calc Real.exp (-(2 * Real.pi ^ 2 * g.sigSq * T ^ 2)) ≤ Real.exp (-T) := by
            apply Real.exp_le_exp.mpr
            linarith
        _ = 1 / L := by
            rw [hTdef, Real.exp_neg, Real.exp_log hL0, one_div]
    have hs1 : Real.sqrt (Real.pi / (α / 2)) ≤ 1 := by
      apply Real.sqrt_le_one.mpr
      rw [hαdef, div_le_one (by positivity)]
      nlinarith [mul_le_mul_of_nonneg_left hσL1 (le_of_lt hπ)]
    calc Real.exp (-(α * δ ^ 2 / 2)) * Real.sqrt (Real.pi / (α / 2))
        ≤ (1 / L) * 1 :=
          mul_le_mul he1 hs1 (Real.sqrt_nonneg _) (by positivity)
      _ = 1 / L := mul_one _
      _ ≤ T ^ (5 + ε) / L := by gcongr
  have hL2le : L ^ (-2 : ℝ) ≤ T ^ (5 + ε) / L := by
    have h1 : L ^ (-2 : ℝ) = (L ^ (2 : ℕ))⁻¹ := by
      rw [Real.rpow_neg (le_of_lt hL0)]
      congr 1
      rw [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) from by norm_num, Real.rpow_natCast]
    have h2 : (L ^ (2 : ℕ))⁻¹ ≤ 1 / L := by
      rw [one_div]
      gcongr
      nlinarith
    calc L ^ (-2 : ℝ) = (L ^ (2 : ℕ))⁻¹ := h1
      _ ≤ 1 / L := h2
      _ ≤ T ^ (5 + ε) / L := by gcongr
  have hE1 : ‖∫ θ in minorSet g x, sqPhi g x θ * ee (-(θ * (k : ℝ)))‖
      ≤ C₁ * x * (T ^ (5 + ε) / L) := by
    calc ‖∫ θ in minorSet g x, sqPhi g x θ * ee (-(θ * (k : ℝ)))‖
        ≤ ∫ θ in minorSet g x, ‖sqPhi g x θ * ee (-(θ * (k : ℝ)))‖ :=
          norm_integral_le_integral_norm _
      _ = ∫ θ in minorSet g x, ‖sqPhi g x θ‖ := by
          simp only [norm_mul, norm_ee, mul_one]
      _ ≤ C₁ * x * L ^ (-2 : ℝ) := hminor'
      _ ≤ C₁ * x * (T ^ (5 + ε) / L) := by
          apply mul_le_mul_of_nonneg_left hL2le (by positivity)
  have hnormRj : ∀ j ∈ range g.dg,
      ‖Rj j‖ ≤ ∫ u in (-δ)..δ, ‖sqPhi g x ((j : ℝ) / (g.dg : ℝ) + u) - arcMain g x j u‖ := by
    intro j _
    simp only [hRjdef]
    calc ‖∫ u in (-δ)..δ, (sqPhi g x ((j : ℝ) / (g.dg : ℝ) + u) - arcMain g x j u)
          * ee (-(u * (k : ℝ)))‖
        ≤ ∫ u in (-δ)..δ, ‖(sqPhi g x ((j : ℝ) / (g.dg : ℝ) + u) - arcMain g x j u)
            * ee (-(u * (k : ℝ)))‖ :=
          intervalIntegral.norm_integral_le_integral_norm (by linarith)
      _ = ∫ u in (-δ)..δ, ‖sqPhi g x ((j : ℝ) / (g.dg : ℝ) + u) - arcMain g x j u‖ := by
          refine intervalIntegral.integral_congr fun u _ => ?_
          rw [norm_mul, norm_ee, mul_one]
  have hE2 : ‖∑ j ∈ range g.dg, ee (-((j : ℝ) / (g.dg : ℝ) * (k : ℝ))) * Rj j‖
      ≤ C₂ * x * T ^ (5 + ε) / L := by
    calc ‖∑ j ∈ range g.dg, ee (-((j : ℝ) / (g.dg : ℝ) * (k : ℝ))) * Rj j‖
        ≤ ∑ j ∈ range g.dg, ‖ee (-((j : ℝ) / (g.dg : ℝ) * (k : ℝ))) * Rj j‖ :=
          norm_sum_le _ _
      _ = ∑ j ∈ range g.dg, ‖Rj j‖ := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [norm_mul, norm_ee, one_mul]
      _ ≤ ∑ j ∈ range g.dg, ∫ u in (-δ)..δ,
            ‖sqPhi g x ((j : ℝ) / (g.dg : ℝ) + u) - arcMain g x j u‖ :=
          Finset.sum_le_sum hnormRj
      _ ≤ C₂ * x * T ^ (5 + ε) / L := hmajor'
  have hE3 : ‖((x : ℂ) * ((rhoSq g k : ℕ) : ℂ)) * (Gδ - GR)‖
      ≤ (g.dg : ℝ) * x * (T ^ (5 + ε) / L) := by
    rw [norm_mul, norm_mul, hxnorm, hρnorm]
    calc x * (rhoSq g k : ℝ) * ‖Gδ - GR‖
        ≤ x * (g.dg : ℝ) * (T ^ (5 + ε) / L) := by
          apply mul_le_mul ?_ (le_trans htail htail2) (norm_nonneg _) (by positivity)
          exact mul_le_mul_of_nonneg_left (rhoSq_le_dg g k) (le_of_lt hx0)
      _ = (g.dg : ℝ) * x * (T ^ (5 + ε) / L) := by ring
  -- assemble
  have hdiffeq : (sqCountEq g x k : ℂ) - ((sqMain g x k : ℝ) : ℂ)
      = ((∑ j ∈ range g.dg, ee (-((j : ℝ) / (g.dg : ℝ) * (k : ℝ))) * Rj j)
          + ((x : ℂ) * ((rhoSq g k : ℕ) : ℂ)) * (Gδ - GR))
        + ∫ θ in minorSet g x, sqPhi g x θ * ee (-(θ * (k : ℝ))) := by
    rw [hcount, hsplit2, hmainC]
    ring
  have hcast : |(sqCountEq g x k : ℝ) - sqMain g x k|
      = ‖(sqCountEq g x k : ℂ) - ((sqMain g x k : ℝ) : ℂ)‖ := by
    rw [show (sqCountEq g x k : ℂ) - ((sqMain g x k : ℝ) : ℂ)
        = (((sqCountEq g x k : ℝ) - sqMain g x k : ℝ) : ℂ) from by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs]
  have htotal : ‖(sqCountEq g x k : ℂ) - ((sqMain g x k : ℝ) : ℂ)‖
      ≤ (C₁ + C₂ + (g.dg : ℝ)) * x * T ^ (5 + ε) / L := by
    rw [hdiffeq]
    calc ‖((∑ j ∈ range g.dg, ee (-((j : ℝ) / (g.dg : ℝ) * (k : ℝ))) * Rj j)
            + ((x : ℂ) * ((rhoSq g k : ℕ) : ℂ)) * (Gδ - GR))
          + ∫ θ in minorSet g x, sqPhi g x θ * ee (-(θ * (k : ℝ)))‖
        ≤ ‖(∑ j ∈ range g.dg, ee (-((j : ℝ) / (g.dg : ℝ) * (k : ℝ))) * Rj j)
            + ((x : ℂ) * ((rhoSq g k : ℕ) : ℂ)) * (Gδ - GR)‖
          + ‖∫ θ in minorSet g x, sqPhi g x θ * ee (-(θ * (k : ℝ)))‖ := norm_add_le _ _
      _ ≤ (‖∑ j ∈ range g.dg, ee (-((j : ℝ) / (g.dg : ℝ) * (k : ℝ))) * Rj j‖
            + ‖((x : ℂ) * ((rhoSq g k : ℕ) : ℂ)) * (Gδ - GR)‖)
          + ‖∫ θ in minorSet g x, sqPhi g x θ * ee (-(θ * (k : ℝ)))‖ := by
          have := norm_add_le (∑ j ∈ range g.dg, ee (-((j : ℝ) / (g.dg : ℝ) * (k : ℝ))) * Rj j)
            (((x : ℂ) * ((rhoSq g k : ℕ) : ℂ)) * (Gδ - GR))
          linarith
      _ ≤ (C₂ * x * T ^ (5 + ε) / L + (g.dg : ℝ) * x * (T ^ (5 + ε) / L))
          + C₁ * x * (T ^ (5 + ε) / L) := by
          have h1 := hE2
          have h2 := hE3
          have h3 := hE1
          linarith
      _ = (C₁ + C₂ + (g.dg : ℝ)) * x * T ^ (5 + ε) / L := by ring
  rw [hcast, ← hLdef, ← hTdef, max_eq_right hT1]
  calc ‖(sqCountEq g x k : ℂ) - ((sqMain g x k : ℝ) : ℂ)‖
      ≤ (C₁ + C₂ + (g.dg : ℝ)) * x * T ^ (5 + ε) / L := htotal
    _ ≤ max Cs (C₁ + C₂ + (g.dg : ℝ)) * x * T ^ (5 + ε) / L := by
        gcongr
        exact le_max_right _ _

end DSS