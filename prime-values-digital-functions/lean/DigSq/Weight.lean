/-
DigSq/Weight.lean

Digit weights, their strongly `b`-additive extension, the constants `μ_g`,
`σ_g²`, `d_g` of the paper, and Lemma 2.2.

Nothing in this file is conditional: it imports no axioms.
-/
import DigSq.Imports

namespace DigSq

open Finset

/-- A **digit weight** in base `b`.

The paper's `g` is determined by its values `g(0) = 0, g(1), …, g(b-1)` on the
digits; we carry a function `ℕ → ℤ` and only ever use it on `{0, …, b-1}`. -/
structure Weight (b : ℕ) where
  /-- the value of the weight on a digit -/
  w : ℕ → ℤ
  /-- the base is at least two -/
  hb : 2 ≤ b
  /-- `g(0) = 0` -/
  w_zero : w 0 = 0

namespace Weight

variable {b : ℕ} (g : Weight b)

lemma one_lt_b (g : Weight b) : 1 < b := g.hb

lemma b_pos (g : Weight b) : 0 < b := lt_trans one_pos g.one_lt_b

/-- The **strongly `b`-additive extension** of the digit weight:
`g(∑_j ε_j b^j) = ∑_j g(ε_j)`. -/
def eval (n : ℕ) : ℤ := ((Nat.digits b n).map g.w).sum

lemma eval_def (n : ℕ) : g.eval n = ((Nat.digits b n).map g.w).sum := rfl

@[simp] lemma eval_zero : g.eval 0 = 0 := by rw [g.eval_def]; simp

/-- The recursion that expresses strong `b`-additivity: appending a digit `d`
adds `g(d)`. -/
theorem eval_add_mul (d m : ℕ) (hd : d < b) :
    g.eval (d + b * m) = g.w d + g.eval m := by
  rcases Nat.eq_zero_or_pos (d + b * m) with h | h
  · have hbm : b * m = 0 := by omega
    have hd0 : d = 0 := by omega
    have hm0 : m = 0 := by
      have hbp := g.b_pos
      rcases Nat.mul_eq_zero.mp hbm with hb | hm
      · omega
      · exact hm
    subst hd0; subst hm0; simp [g.w_zero]
  · have hmod : (d + b * m) % b = d := by
      rw [Nat.add_mul_mod_self_left]; exact Nat.mod_eq_of_lt hd
    have hdiv : (d + b * m) / b = m := by
      rw [Nat.add_mul_div_left _ _ g.b_pos, Nat.div_eq_of_lt hd]; simp
    rw [g.eval_def, Nat.digits_def' g.one_lt_b h, hmod, hdiv, g.eval_def]
    simp

/-- Strong `b`-additivity in the form used by the paper: for a list of digits,
`g` of the number they encode is the sum of `g` over the digits. -/
theorem eval_ofDigits : ∀ L : List ℕ, (∀ d ∈ L, d < b) →
    g.eval (Nat.ofDigits b L) = (L.map g.w).sum := by
  intro L
  induction L with
  | nil => intro _; simp
  | cons d tl ih =>
      intro h
      have hd : d < b := h d (by simp)
      have htl : ∀ e ∈ tl, e < b := fun e he => h e (by simp [he])
      have hcons : Nat.ofDigits b (d :: tl) = d + b * Nat.ofDigits b tl := Nat.ofDigits_cons
      rw [hcons, g.eval_add_mul d _ hd, ih htl]
      simp

section Constants

/-- `μ_g`, the mean of `g` over the digits. -/
noncomputable def mu : ℝ := (∑ a ∈ range b, (g.w a : ℝ)) / b

/-- `σ_g²`, the variance of `g` over the digits. -/
noncomputable def sigSq : ℝ := (∑ a ∈ range b, ((g.w a : ℝ) - g.mu) ^ 2) / b

/-- `d_g` of eq. (4):
`gcd(g(2) - 2g(1), …, g(b-1) - (b-1)g(1), b-1)`.
Including `a = 0` and `a = 1` in the `gcd` is harmless, since both contribute `0`. -/
def dg : ℕ := Nat.gcd (b - 1) ((range b).gcd fun a => (g.w a - (a : ℤ) * g.w 1).natAbs)

/-- The coprimality hypothesis (3): `gcd(g(1), …, g(b-1)) = 1`. -/
def Coprime₁ : Prop := ((Ico 1 b).gcd fun a => (g.w a).natAbs) = 1

lemma mu_def : g.mu = (∑ a ∈ range b, (g.w a : ℝ)) / b := rfl

lemma sigSq_def : g.sigSq = (∑ a ∈ range b, ((g.w a : ℝ) - g.mu) ^ 2) / b := rfl

lemma dg_def :
    g.dg = Nat.gcd (b - 1) ((range b).gcd fun a => (g.w a - (a : ℤ) * g.w 1).natAbs) := rfl

lemma coprime₁_def : g.Coprime₁ ↔ ((Ico 1 b).gcd fun a => (g.w a).natAbs) = 1 := Iff.rfl

/-- `d_g` divides `b - 1`. -/
theorem dg_dvd_sub_one : g.dg ∣ b - 1 := Nat.gcd_dvd_left _ _

/-- `d_g ≥ 1`.  It divides `b - 1 ≥ 1`, so it is never `0`; this is what makes
the encoding of the congruence `g(1)·p ≡ k (mod d_g)` by `Int.emod` in
`DigSq.piCong` meaningful. -/
theorem dg_pos : 0 < g.dg := by
  have hb1 : 0 < b - 1 := by have := g.hb; omega
  rw [g.dg_def]
  exact Nat.gcd_pos_of_pos_left _ hb1

/-- `d_g` divides each `g(a) - a·g(1)`. -/
theorem dg_dvd_sub (a : ℕ) (ha : a < b) :
    (g.dg : ℤ) ∣ g.w a - (a : ℤ) * g.w 1 := by
  have h : g.dg ∣ (g.w a - (a : ℤ) * g.w 1).natAbs :=
    dvd_trans (Nat.gcd_dvd_right _ _) (Finset.gcd_dvd (mem_range.mpr ha))
  exact Int.dvd_natAbs.mp (Int.natCast_dvd_natCast.mpr h)

/-- **The congruence of §2 of the paper:** `d_g` divides `g(n) - g(1)·n`, so the
value of `g` at `n` is determined modulo `d_g` by `n` itself.

The proof is an induction on the digits: `b ≡ 1 (mod d_g)` because `d_g ∣ b - 1`,
and `g(a) ≡ a·g(1) (mod d_g)` on each digit by `dg_dvd_sub`. -/
theorem dg_dvd_eval_sub : ∀ n : ℕ, (g.dg : ℤ) ∣ g.eval n - g.w 1 * n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; simp
    · have hdb : n % b < b := Nat.mod_lt n g.b_pos
      have hnm : n = n % b + b * (n / b) := (Nat.mod_add_div n b).symm
      have hmlt : n / b < n := Nat.div_lt_self hn g.one_lt_b
      have hev : g.eval n = g.w (n % b) + g.eval (n / b) := by
        conv_lhs => rw [hnm]
        exact g.eval_add_mul (n % b) (n / b) hdb
      have h1 : (g.dg : ℤ) ∣ g.w (n % b) - ((n % b : ℕ) : ℤ) * g.w 1 :=
        g.dg_dvd_sub (n % b) hdb
      have h2 : (g.dg : ℤ) ∣ g.eval (n / b) - g.w 1 * ((n / b : ℕ) : ℤ) := ih (n / b) hmlt
      have h3 : (g.dg : ℤ) ∣ ((b : ℤ) - 1) := by
        have hb : (1 : ℕ) ≤ b := le_of_lt g.one_lt_b
        have hd : ((g.dg : ℕ) : ℤ) ∣ ((b - 1 : ℕ) : ℤ) :=
          Int.natCast_dvd_natCast.mpr g.dg_dvd_sub_one
        rwa [Nat.cast_sub hb, Nat.cast_one] at hd
      have hcast : ((n : ℕ) : ℤ) = ((n % b : ℕ) : ℤ) + (b : ℤ) * ((n / b : ℕ) : ℤ) := by
        exact_mod_cast hnm
      have hkey : g.eval n - g.w 1 * (n : ℤ)
          = (g.w (n % b) - ((n % b : ℕ) : ℤ) * g.w 1)
            + (g.eval (n / b) - g.w 1 * ((n / b : ℕ) : ℤ))
            - g.w 1 * ((n / b : ℕ) : ℤ) * ((b : ℤ) - 1) := by
        rw [hev, hcast]; ring
      rw [hkey]
      exact dvd_sub (dvd_add h1 h2) (Dvd.dvd.mul_left h3 _)

lemma sigSq_nonneg : 0 ≤ g.sigSq := by
  rw [g.sigSq_def]
  apply div_nonneg _ (by positivity)
  exact sum_nonneg fun a _ => sq_nonneg _

end Constants

section LemmaTwoTwo

variable {g}

/-- **Lemma 2.2, first part.** Under (3) the weight is not constant on the
digits, so `σ_g > 0`. -/
theorem sigSq_pos (hg : g.Coprime₁) : 0 < g.sigSq := by
  rcases lt_or_eq_of_le g.sigSq_nonneg with h | h
  · exact h
  · exfalso
    -- `σ_g² = 0` forces every digit value to equal `μ_g`
    have hb0 : (0 : ℝ) < b := by exact_mod_cast g.b_pos
    have hsum : ∑ a ∈ range b, ((g.w a : ℝ) - g.mu) ^ 2 = 0 := by
      have h' : (∑ a ∈ range b, ((g.w a : ℝ) - g.mu) ^ 2) / (b : ℝ) = 0 := by
        rw [← g.sigSq_def]; exact h.symm
      exact (div_eq_zero_iff.mp h').resolve_right (ne_of_gt hb0)
    have hall : ∀ a ∈ range b, ((g.w a : ℝ) - g.mu) ^ 2 = 0 :=
      (sum_eq_zero_iff_of_nonneg fun a _ => sq_nonneg _).mp hsum
    have heq : ∀ a ∈ range b, (g.w a : ℝ) = g.mu := by
      intro a ha
      have := hall a ha
      have : (g.w a : ℝ) - g.mu = 0 := by nlinarith [this]
      linarith
    -- `g(0) = 0` pins `μ_g = 0`, hence every digit value is `0`
    have h0 : g.mu = 0 := by
      have := heq 0 (mem_range.mpr g.b_pos)
      rw [g.w_zero] at this; simpa using this.symm
    have hzero : ∀ a ∈ Ico 1 b, (g.w a).natAbs = 0 := by
      intro a ha
      have ha' : a ∈ range b := mem_range.mpr (mem_Ico.mp ha).2
      have : (g.w a : ℝ) = 0 := by rw [heq a ha', h0]
      have : g.w a = 0 := by exact_mod_cast this
      simp [this]
    -- so the `gcd` of (3) is `0`, not `1`
    have hg' : ((Ico 1 b).gcd fun a => (g.w a).natAbs) = 1 := hg
    have hz0 : ((Ico 1 b).gcd fun a => (g.w a).natAbs) = 0 :=
      Finset.gcd_eq_zero_iff.mpr hzero
    rw [hg'] at hz0
    exact one_ne_zero hz0

/-- **Lemma 2.2, second part.** Under (3), `gcd(g(1), d_g) = 1`. -/
theorem coprime_w_one_dg (hg : g.Coprime₁) :
    Nat.Coprime (g.w 1).natAbs g.dg := by
  set d := Nat.gcd (g.w 1).natAbs g.dg with hd
  have hw1 : (d : ℤ) ∣ g.w 1 :=
    Int.dvd_natAbs.mp (Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_left _ _))
  -- `d` divides every `g(a)`, hence divides the `gcd` of (3), which is `1`
  have hdvd : ∀ a ∈ Ico 1 b, d ∣ (g.w a).natAbs := by
    intro a ha
    have hab : a < b := (mem_Ico.mp ha).2
    have hdg : (d : ℤ) ∣ (g.dg : ℤ) := Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_right _ _)
    have h1 : (d : ℤ) ∣ g.w a - (a : ℤ) * g.w 1 := dvd_trans hdg (g.dg_dvd_sub a hab)
    have h2 : (d : ℤ) ∣ (a : ℤ) * g.w 1 := Dvd.dvd.mul_left hw1 _
    have h3 : (d : ℤ) ∣ g.w a := by
      have h4 := dvd_add h1 h2
      simpa using h4
    exact Int.natCast_dvd_natCast.mp (Int.dvd_natAbs.mpr h3)
  have hg' : ((Ico 1 b).gcd fun a => (g.w a).natAbs) = 1 := hg
  have hfin : d ∣ ((Ico 1 b).gcd fun a => (g.w a).natAbs) := Finset.dvd_gcd hdvd
  rw [hg'] at hfin
  exact Nat.eq_one_of_dvd_one hfin

end LemmaTwoTwo

end Weight

end DigSq
