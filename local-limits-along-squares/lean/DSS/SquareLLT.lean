/-
DSS/SquareLLT.lean

**The statement of Theorem 1.1 (the square local limit theorem), as a
hypothesis.**

Theorem 1.1 is the paper's own new analytic result.  Under the axiom
discipline of this development (axioms transcribe *literature* results only,
in `DSS/Cited.lean`), the paper's own theorems are never axiomatised; and its
proof adapts the internals of Mauduit–Rivat and Morgenbesser rather than
quoting black-box statements, so those engines cannot be transcribed
faithfully either.  Instead this file *defines* the property

  `SquareLLT g`  —  "`g` satisfies the conclusion of Theorem 1.1"

as a `Prop`, transcribing the statement with the same conventions as the
`mmr` axiom (quantifier order `∀ ε, ∃ C, ∀ x, ∀ k`; real cut-offs; the
congruence encoded by `Int.emod` inside `rhoSq`), and the sieve consequences
are proved as **implications** from it (`DSS/SquareP2.lean`).  The axiom base
of the development is unchanged.

Encoding notes:

* The count is over `1 ≤ n ≤ x` (`intsLE`), the paper's `#{n ≤ x : …}`.
* The main term is eq. (5) verbatim:
  `ρ_{g,□}(k) · x / √(4π σ_g² L) · exp(−(k − 2μ_g L)²/(4 σ_g² L))`,
  `L = log_b x`.
* The error is `C · x · (max 1 (log L))^{5+ε} / L`.  For fixed `g` and `ε`
  this is equivalent to the paper's `O_{b,g,ε}(x (log L)^{5+ε}/L)` as
  `x → ∞`: for `L ≥ e` the two agree, while on any range `2 < x`, `L ≤ e`
  the count and the main term are each `O_{b,g}(x/L)`, so a larger `C`
  absorbs them.  (Without the `max` the statement would be *false* near
  `x = b`, where `log L → 0` while the left side does not.)
* `∀ ε > 0`, matching "for every ε > 0" in the paper.

Nothing in this file is conditional: it imports no axioms; `SquareLLT` is a
definition.
-/
import DSS.RhoSquare

namespace DSS

open Finset

/-- The integers `1 ≤ n ≤ x`, for a real cut-off `x`. -/
noncomputable def intsLE (x : ℝ) : Finset ℕ := Icc 1 ⌊x⌋₊

lemma mem_intsLE {x : ℝ} (hx : 0 ≤ x) {n : ℕ} :
    n ∈ intsLE x ↔ 1 ≤ n ∧ (n : ℝ) ≤ x := by
  simp only [intsLE, mem_Icc]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, (Nat.le_floor_iff hx).mp h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, Nat.le_floor h2⟩

/-- `x - 1 ≤ #{1 ≤ n ≤ x}`: the integer count fills the real length. -/
lemma card_intsLE {x : ℝ} (hx : 1 ≤ x) : x - 1 ≤ ((intsLE x).card : ℝ) := by
  have h0 : (0 : ℝ) ≤ x := by linarith
  have hfl : 1 ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx)
  have hcard : (intsLE x).card = ⌊x⌋₊ := by
    unfold intsLE
    rw [Nat.card_Icc]
    omega
  have h2 : x - 1 < (⌊x⌋₊ : ℝ) := by
    have := Nat.lt_floor_add_one x
    have h3 := Nat.floor_le h0
    linarith [Nat.sub_one_lt_floor x]
  rw [hcard]
  linarith

variable {b : ℕ}

/-- `#{1 ≤ n ≤ x : g(n²) = k}`. -/
noncomputable def sqCountEq (g : Weight b) (x : ℝ) (k : ℤ) : ℕ :=
  ((intsLE x).filter (fun n : ℕ => g.eval (n ^ 2) = k)).card

/-- The integers up to `x` are partitioned by the value of `g` on their
squares; summing `sqCountEq` over the values actually taken recovers the full
count.  The encoding check, as for `countEq`. -/
theorem sum_sqCountEq (g : Weight b) (x : ℝ) :
    ∑ k ∈ (intsLE x).image (fun n => g.eval (n ^ 2)), sqCountEq g x k
      = (intsLE x).card := by
  unfold sqCountEq
  refine (Finset.card_eq_sum_card_fiberwise ?_).symm
  intro n hn
  exact Finset.mem_image_of_mem _ hn

/-- The main term of eq. (5):

`ρ_{g,□}(k) · x / √(4π σ_g² log_b x) · exp(−(k − 2 μ_g log_b x)² / (4 σ_g² log_b x))`. -/
noncomputable def sqMain (g : Weight b) (x : ℝ) (k : ℤ) : ℝ :=
  (rhoSq g k : ℝ) * x
      / Real.sqrt (4 * Real.pi * g.sigSq * Real.logb (b : ℝ) x)
    * Real.exp (-(((k : ℝ) - 2 * g.mu * Real.logb (b : ℝ) x) ^ 2)
                  / (4 * g.sigSq * Real.logb (b : ℝ) x))

lemma sqMain_def (g : Weight b) (x : ℝ) (k : ℤ) :
    sqMain g x k =
      (rhoSq g k : ℝ) * x
          / Real.sqrt (4 * Real.pi * g.sigSq * Real.logb (b : ℝ) x)
        * Real.exp (-(((k : ℝ) - 2 * g.mu * Real.logb (b : ℝ) x) ^ 2)
                      / (4 * g.sigSq * Real.logb (b : ℝ) x)) := rfl

/-- For `d_g = 1`, the main term in the doubled-variance normal form
`s = 2σ_g²` consumed by `gaussian_lower`. -/
lemma sqMain_dg_one (g : Weight b) (hdg : g.dg = 1) (x : ℝ) (k : ℤ) :
    sqMain g x k =
      x / Real.sqrt (2 * Real.pi * (2 * g.sigSq) * Real.logb (b : ℝ) x)
        * Real.exp (-(((k : ℝ) - 2 * g.mu * Real.logb (b : ℝ) x) ^ 2)
                      / (2 * (2 * g.sigSq) * Real.logb (b : ℝ) x)) := by
  unfold sqMain
  rw [rhoSq_dg_one g hdg]
  have h1 : 4 * Real.pi * g.sigSq * Real.logb (b : ℝ) x
      = 2 * Real.pi * (2 * g.sigSq) * Real.logb (b : ℝ) x := by ring
  have h2 : 4 * g.sigSq * Real.logb (b : ℝ) x
      = 2 * (2 * g.sigSq) * Real.logb (b : ℝ) x := by ring
  rw [h1, h2]
  norm_num

/-- **`SquareLLT g`: the conclusion of Theorem 1.1 for `g`.**

For each fixed `ε > 0` there is `C = C(b, g, ε)` with

`| #{1 ≤ n ≤ x : g(n²) = k} − sqMain g x k |
   ≤ C · x · (max 1 (log log_b x))^{5+ε} / log_b x`

uniformly for real `x > 2` and all `k ∈ ℤ`.  A definition, not an axiom. -/
def SquareLLT (g : Weight b) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 2 < x → ∀ k : ℤ,
      |(sqCountEq g x k : ℝ) - sqMain g x k|
        ≤ C * x * (max 1 (Real.log (Real.logb (b : ℝ) x))) ^ (5 + ε)
            / Real.logb (b : ℝ) x

end DSS
