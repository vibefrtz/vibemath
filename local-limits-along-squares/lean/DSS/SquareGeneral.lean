/-
DSS/SquareGeneral.lean

**Theorem 2.1 (the general square local theorem) reduced to Theorem 1.1.**

Theorem 1.1 is stated for a *primitive* weight, `g ∈ ℱ_b`.  Section 2 of the
paper removes the primitivity assumption: for a general nonconstant integer
valued strongly `b`-additive `g`, with

  `h_g = gcd(g(1), …, g(b−1)) > 0`,  `g̃ = g/h_g ∈ ℱ_b`,

the same formula holds with the periodic factor (13),

  `ρ_{g,□}(k) = h_g · #{r mod d_{g̃} : g̃(1)r² ≡ k/h_g (mod d_{g̃})}` if `h_g ∣ k`,
  `ρ_{g,□}(k) = 0` otherwise,

and the paper's proof is the scaling computation `μ_g = h μ_{g̃}`,
`σ_g² = h² σ_{g̃}²`, `ρ_{g,□}(k)/σ_g = ρ_{g̃,□}(k/h)/σ_{g̃}`.

This file verifies that reduction as an **implication**, in the discipline of
`DSS/SquareLLT.lean`: `SquareLLT g̃` (a definition, never an axiom) implies
`SquareLLTGen h g̃`, the transcription of Theorem 2.1 for `g = h·g̃`.  Nothing
analytic is assumed or proved here — only that the two statements are the same
statement after the substitution `k = hℓ`.

Nothing in this file is conditional: it imports no axioms.
-/
import DSS.SquareLLT

namespace DSS

open Finset

namespace Weight

variable {b : ℕ}

/-- The rescaled digit weight `h·g`; the paper's `g = h_g·g̃` read backwards. -/
def smulW (h : ℤ) (g : Weight b) : Weight b where
  w := fun a => h * g.w a
  hb := g.hb
  w_zero := by simp [g.w_zero]

@[simp] lemma smulW_w (h : ℤ) (g : Weight b) (a : ℕ) : (g.smulW h).w a = h * g.w a := rfl

/-- Strong additivity is linear in the weight: `(h·g)(n) = h·g(n)`. -/
@[simp] theorem eval_smulW (h : ℤ) (g : Weight b) (n : ℕ) :
    (g.smulW h).eval n = h * g.eval n := by
  unfold Weight.eval
  induction (Nat.digits b n) with
  | nil => simp
  | cons d tl ih =>
      simp only [List.map_cons, List.sum_cons, smulW_w, ih]
      ring

/-- `μ_{h·g} = h·μ_g`. -/
theorem mu_smulW (h : ℤ) (g : Weight b) : (g.smulW h).mu = (h : ℝ) * g.mu := by
  have hsum : (∑ a ∈ range b, ((g.smulW h).w a : ℝ))
      = (h : ℝ) * ∑ a ∈ range b, (g.w a : ℝ) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun a _ => by simp only [smulW_w]; push_cast; ring)
  unfold Weight.mu
  rw [hsum, mul_div_assoc]

/-- `σ²_{h·g} = h²·σ²_g`. -/
theorem sigSq_smulW (h : ℤ) (g : Weight b) :
    (g.smulW h).sigSq = (h : ℝ) ^ 2 * g.sigSq := by
  have hsum : (∑ a ∈ range b, (((g.smulW h).w a : ℝ) - (g.smulW h).mu) ^ 2)
      = (h : ℝ) ^ 2 * ∑ a ∈ range b, ((g.w a : ℝ) - g.mu) ^ 2 := by
    rw [mu_smulW, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun a _ => by simp only [smulW_w]; push_cast; ring)
  unfold Weight.sigSq
  rw [hsum, mul_div_assoc]

end Weight

variable {b : ℕ}

/-- **The general lattice density, eq. (13):** for `g = h·g̃`,
`ρ_{g,□}(k) = h·ρ_{g̃,□}(k/h)` when `h ∣ k`, and `0` otherwise. -/
noncomputable def rhoSqGen (h : ℤ) (g : Weight b) (k : ℤ) : ℕ :=
  if h ∣ k then h.toNat * rhoSq g (k / h) else 0

/-- The main term of (14), the general square local theorem, for `g = h·g̃`. -/
noncomputable def sqMainGen (h : ℤ) (g : Weight b) (x : ℝ) (k : ℤ) : ℝ :=
  (rhoSqGen h g k : ℝ) * x
      / Real.sqrt (4 * Real.pi * (g.smulW h).sigSq * Real.logb (b : ℝ) x)
    * Real.exp (-(((k : ℝ) - 2 * (g.smulW h).mu * Real.logb (b : ℝ) x) ^ 2)
                  / (4 * (g.smulW h).sigSq * Real.logb (b : ℝ) x))

/-- **`SquareLLTGen h g̃`: the conclusion of Theorem 2.1 for `g = h·g̃`.**
Same encoding as `SquareLLT`; a definition, not an axiom. -/
def SquareLLTGen (h : ℤ) (g : Weight b) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 2 < x → ∀ k : ℤ,
      |(sqCountEq (g.smulW h) x k : ℝ) - sqMainGen h g x k|
        ≤ C * x * (max 1 (Real.log (Real.logb (b : ℝ) x))) ^ (5 + ε)
            / Real.logb (b : ℝ) x

/-- Off the lattice `h ∣ k` there is nothing to count: every value of `h·g` is
a multiple of `h`. -/
lemma sqCountEq_smulW_of_not_dvd {h : ℤ} (g : Weight b) (x : ℝ) {k : ℤ} (hk : ¬ h ∣ k) :
    sqCountEq (g.smulW h) x k = 0 := by
  unfold sqCountEq
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro n _
  rw [Weight.eval_smulW]
  intro hcon
  exact hk ⟨g.eval (n ^ 2), hcon.symm⟩

/-- On the lattice the count is literally the primitive count at `k/h`. -/
lemma sqCountEq_smulW {h : ℤ} (hh : h ≠ 0) (g : Weight b) (x : ℝ) (l : ℤ) :
    sqCountEq (g.smulW h) x (h * l) = sqCountEq g x l := by
  unfold sqCountEq
  congr 1
  refine Finset.filter_congr (fun n _ => ?_)
  rw [Weight.eval_smulW]
  exact ⟨fun hcon => mul_left_cancel₀ hh hcon, fun hcon => by rw [hcon]⟩

/-- The main terms agree after the substitution `k = hℓ`: this is the paper's
`ρ_{g̃,□}(ℓ)/σ_{g̃} = h·ρ_{g̃,□}(k/h)/σ_g`. -/
lemma sqMainGen_eq {h : ℤ} (hh : 0 < h) (g : Weight b) (x : ℝ) (l : ℤ) :
    sqMainGen h g x (h * l) = sqMain g x l := by
  have hhR : (0 : ℝ) < (h : ℝ) := by exact_mod_cast hh
  have hhne : ((h : ℝ)) ≠ 0 := ne_of_gt hhR
  have hsq : ((h : ℝ)) ^ 2 ≠ 0 := pow_ne_zero 2 hhne
  have hrho : (rhoSqGen h g (h * l) : ℝ) = (h : ℝ) * (rhoSq g l : ℝ) := by
    unfold rhoSqGen
    rw [if_pos ⟨l, rfl⟩, Int.mul_ediv_cancel_left _ (ne_of_gt hh)]
    have htn : ((h.toNat : ℕ) : ℝ) = (h : ℝ) := by
      exact_mod_cast congrArg (fun t : ℤ => (t : ℝ)) (Int.toNat_of_nonneg hh.le)
    push_cast
    rw [htn]
  unfold sqMainGen sqMain
  rw [hrho, Weight.sigSq_smulW, Weight.mu_smulW]
  -- the square root scales by `h`
  have hroot : Real.sqrt (4 * Real.pi * ((h : ℝ) ^ 2 * g.sigSq) * Real.logb (b : ℝ) x)
      = (h : ℝ) * Real.sqrt (4 * Real.pi * g.sigSq * Real.logb (b : ℝ) x) := by
    have hrw : 4 * Real.pi * ((h : ℝ) ^ 2 * g.sigSq) * Real.logb (b : ℝ) x
        = (h : ℝ) ^ 2 * (4 * Real.pi * g.sigSq * Real.logb (b : ℝ) x) := by ring
    rw [hrw, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hhR.le]
  -- the exponent is unchanged
  have hexp : -((((h * l : ℤ) : ℝ) - 2 * ((h : ℝ) * g.mu) * Real.logb (b : ℝ) x) ^ 2)
      / (4 * ((h : ℝ) ^ 2 * g.sigSq) * Real.logb (b : ℝ) x)
      = -(((l : ℝ) - 2 * g.mu * Real.logb (b : ℝ) x) ^ 2)
        / (4 * g.sigSq * Real.logb (b : ℝ) x) := by
    have hnum : -((((h * l : ℤ) : ℝ) - 2 * ((h : ℝ) * g.mu) * Real.logb (b : ℝ) x) ^ 2)
        = (h : ℝ) ^ 2 * (-(((l : ℝ) - 2 * g.mu * Real.logb (b : ℝ) x) ^ 2)) := by
      push_cast
      ring
    have hden : 4 * ((h : ℝ) ^ 2 * g.sigSq) * Real.logb (b : ℝ) x
        = (h : ℝ) ^ 2 * (4 * g.sigSq * Real.logb (b : ℝ) x) := by ring
    rw [hnum, hden, mul_div_mul_left _ _ hsq]
  rw [hroot, hexp]
  congr 1
  rw [mul_assoc, mul_div_mul_left _ _ hhne]

/-- **Theorem 2.1 from Theorem 1.1** (the `h_g`-scaling), as an implication:
if the primitive weight `g̃` satisfies the conclusion of Theorem 1.1, then
`h·g̃` satisfies the conclusion of Theorem 2.1, with the same constants. -/
theorem squareLLT_general {h : ℤ} (hh : 0 < h) (g : Weight b) (hllt : SquareLLT g) :
    SquareLLTGen h g := by
  intro ε hε
  obtain ⟨C, hC0, hC⟩ := hllt ε hε
  refine ⟨C, hC0, fun x hx k => ?_⟩
  have hb1 : (1 : ℝ) < (b : ℝ) := by exact_mod_cast g.one_lt_b
  have hlog : 0 < Real.logb (b : ℝ) x := Real.logb_pos hb1 (by linarith)
  by_cases hdvd : h ∣ k
  · obtain ⟨l, rfl⟩ := hdvd
    rw [sqCountEq_smulW (ne_of_gt hh), sqMainGen_eq hh]
    exact hC x hx l
  · rw [sqCountEq_smulW_of_not_dvd g x hdvd]
    have hmain : sqMainGen h g x k = 0 := by
      unfold sqMainGen rhoSqGen
      rw [if_neg hdvd]
      simp
    rw [hmain]
    simp only [Nat.cast_zero, sub_zero, abs_zero]
    have hpow : (0 : ℝ) ≤ (max 1 (Real.log (Real.logb (b : ℝ) x))) ^ (5 + ε) :=
      Real.rpow_nonneg (le_trans zero_le_one (le_max_left _ _)) _
    positivity

end DSS
