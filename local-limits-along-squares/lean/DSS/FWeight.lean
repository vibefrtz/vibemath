/-
DSS/FWeight.lean

Weights that see the length (§5 of the paper).  For a tuple of integer weights
`w₀, …, w_{b−1}`, the function `F_w(n) = ∑_{j<ℓ_b(n)} w_{ε_j(n)}` splits as

  `F_w(n) = w₀·ℓ_b(n) + g_w(n)`,     `g_w(a) = w_a − w₀`  (eq. (52)),

with `g_w` strongly `b`-additive.  This file formalises:

* the split (52), and the zero-digit counter `Z_b = F_{(1,0,…,0)}`;
* the parameters of Corollaries 5.5/5.9: the strongly additive part of `Z_b` has
  `μ = −(b−1)/b`, `σ² = (b−1)/b²`, `d_g = 1`, and the target `Z_b(p) = r` on
  the shell of `br`-digit primes sits at the exact centre of the window;
* **Example 5.13** (base 3, weights `(1,2,−3)`): on odd shells the only prime
  value of `F_w` is `2` — the congruence forcing behind the numerics of §5.5;
* a base-4 mean-zero example with `d_g = 3`;
* the digit sum itself as a weight, with `d_g = 1` and `μ = 1/2` in base `2`.

Nothing in this file is conditional: it imports no axioms.
-/
import DSS.Weight
import DSS.Digits

namespace DSS

open Finset

/-! ### The length and the split -/

/-- `ℓ_b(n)`, the number of base-`b` digits of `n`. -/
def lb (b n : ℕ) : ℕ := (Nat.digits b n).length

/-- `F_w(n) = ∑_{j<ℓ_b(n)} w_{ε_j(n)}`: every digit weighted, zeros included. -/
def Fw (b : ℕ) (w : ℕ → ℤ) (n : ℕ) : ℤ := ((Nat.digits b n).map w).sum

lemma Fw_def (b : ℕ) (w : ℕ → ℤ) (n : ℕ) :
    Fw b w n = ((Nat.digits b n).map w).sum := rfl

/-- The strongly `b`-additive part of `F_w`: the weight `a ↦ w_a − w₀`. -/
def gw (b : ℕ) (w : ℕ → ℤ) (hb : 2 ≤ b) : Weight b where
  w := fun a => w a - w 0
  hb := hb
  w_zero := by ring

/-- **The split (14)**: `F_w(n) = w₀·ℓ_b(n) + g_w(n)`. -/
theorem Fw_eq_split (b : ℕ) (w : ℕ → ℤ) (hb : 2 ≤ b) (n : ℕ) :
    Fw b w n = w 0 * (lb b n : ℤ) + (gw b w hb).eval n := by
  rw [Fw_def, lb, Weight.eval]
  induction Nat.digits b n with
  | nil => simp
  | cons d l ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons, ih]
      push_cast
      show w d + (w 0 * l.length + ((l.map fun a => w a - w 0)).sum)
          = w 0 * ((l.length : ℤ) + 1) + (w d - w 0 + ((l.map fun a => w a - w 0)).sum)
      ring

/-- The zero-digit counter `Z_b(n)`. -/
def Zb (b n : ℕ) : ℕ := (Nat.digits b n).count 0

/-- `Z_b` is `F_w` for the weight `(1, 0, …, 0)`. -/
theorem Zb_eq_Fw (b n : ℕ) :
    (Zb b n : ℤ) = Fw b (fun a => if a = 0 then 1 else 0) n := by
  rw [Zb, Fw_def]
  induction Nat.digits b n with
  | nil => simp
  | cons d l ih =>
      rw [List.map_cons, List.sum_cons]
      by_cases hd : d = 0
      · subst hd
        rw [List.count_cons_self]
        push_cast
        rw [← ih]
        omega
      · rw [List.count_cons_of_ne hd]
        rw [← ih]
        simp [hd]

/-! ### The parameters of Corollaries 5.5/5.9 -/

/-- The strongly additive part of `Z_b`: the weight `a ↦ −1` on nonzero
digits. -/
def zeroWeight (b : ℕ) (hb : 2 ≤ b) : Weight b where
  w := fun a => if a = 0 then 0 else -1
  hb := hb
  w_zero := by simp

lemma zeroWeight_w (b : ℕ) (hb : 2 ≤ b) (a : ℕ) :
    (zeroWeight b hb).w a = if a = 0 then 0 else -1 := rfl

/-- Hypothesis (3) for the zero counter. -/
theorem zeroWeight_coprime₁ (b : ℕ) (hb : 2 ≤ b) : (zeroWeight b hb).Coprime₁ := by
  have h1 : (1 : ℕ) ∈ Ico 1 b := by
    rw [mem_Ico]
    omega
  have h2 : ((Ico 1 b).gcd fun a => ((zeroWeight b hb).w a).natAbs)
      ∣ ((zeroWeight b hb).w 1).natAbs := Finset.gcd_dvd h1
  have h3 : ((zeroWeight b hb).w 1).natAbs = 1 := by
    rw [zeroWeight_w]
    norm_num
  rw [h3] at h2
  exact Nat.dvd_one.mp h2

/-- `d_g = 1` for the zero counter: for `b ≥ 3` the list (4) contains
`|g(2) − 2g(1)| = 1`; for `b = 2` the modulus divides `b − 1 = 1`. -/
theorem zeroWeight_dg (b : ℕ) (hb : 2 ≤ b) : (zeroWeight b hb).dg = 1 := by
  rcases Nat.lt_or_ge b 3 with h3 | h3
  · -- `b = 2`
    have h1 : (zeroWeight b hb).dg ∣ b - 1 := (zeroWeight b hb).dg_dvd_sub_one
    have h2 : b - 1 = 1 := by omega
    rw [h2] at h1
    exact Nat.dvd_one.mp h1
  · -- `b ≥ 3`: the entry at `a = 2`
    have h4 : ((zeroWeight b hb).dg : ℤ)
        ∣ (zeroWeight b hb).w 2 - (2 : ℤ) * (zeroWeight b hb).w 1 :=
      (zeroWeight b hb).dg_dvd_sub 2 (by omega)
    have h5 : (zeroWeight b hb).w 2 - (2 : ℤ) * (zeroWeight b hb).w 1 = 1 := by
      rw [zeroWeight_w, zeroWeight_w]
      norm_num
    rw [h5] at h4
    have h7 : (zeroWeight b hb).dg ∣ 1 := by exact_mod_cast h4
    exact Nat.dvd_one.mp h7

/-- `μ = (1−b)/b = −(b−1)/b` for the zero counter (so `λ = w₀ + μ = 1/b`). -/
theorem zeroWeight_mu (b : ℕ) (hb : 2 ≤ b) :
    (zeroWeight b hb).mu = (1 - (b : ℝ)) / (b : ℝ) := by
  rw [Weight.mu]
  congr 1
  have h1 : ∀ a ∈ range b, ((zeroWeight b hb).w a : ℝ)
      = (if a = 0 then (1 : ℝ) else 0) - 1 := by
    intro a _
    rw [zeroWeight_w]
    by_cases h : a = 0 <;> simp [h]
  rw [Finset.sum_congr rfl h1, Finset.sum_sub_distrib,
    Finset.sum_ite_eq' (range b) 0 (fun _ => (1 : ℝ))]
  simp [mem_range, show 0 < b by omega]

/-- `σ² = (b−1)/b²` for the zero counter. -/
theorem zeroWeight_sigSq (b : ℕ) (hb : 2 ≤ b) :
    (zeroWeight b hb).sigSq = ((b : ℝ) - 1) / (b : ℝ) ^ 2 := by
  have hb0 : (b : ℝ) ≠ 0 := by
    have h : (0 : ℝ) < b := by
      have : 0 < b := by omega
      exact_mod_cast this
    linarith
  rw [Weight.sigSq, zeroWeight_mu b hb]
  have h1 : ∀ a ∈ range b, (((zeroWeight b hb).w a : ℝ) - (1 - (b : ℝ)) / (b : ℝ)) ^ 2
      = (if a = 0 then (((b : ℝ) - 1) / (b : ℝ)) ^ 2 else (1 / (b : ℝ)) ^ 2) := by
    intro a _
    rw [zeroWeight_w]
    by_cases h : a = 0
    · rw [if_pos h, if_pos h]
      have h3 : ((0 : ℤ) : ℝ) - (1 - (b : ℝ)) / (b : ℝ) = ((b : ℝ) - 1) / (b : ℝ) := by
        push_cast
        rw [zero_sub, ← neg_div]
        congr 1
        ring
      rw [h3]
    · rw [if_neg h, if_neg h]
      have h3 : ((-1 : ℤ) : ℝ) - (1 - (b : ℝ)) / (b : ℝ) = -(1 / (b : ℝ)) := by
        push_cast
        field_simp
        ring
      rw [h3, neg_sq]
  rw [Finset.sum_congr rfl h1]
  have h2 : ∑ a ∈ range b,
      (if a = 0 then (((b : ℝ) - 1) / (b : ℝ)) ^ 2 else (1 / (b : ℝ)) ^ 2)
      = (((b : ℝ) - 1) / (b : ℝ)) ^ 2 + ((b : ℝ) - 1) * (1 / (b : ℝ)) ^ 2 := by
    have h3 : ∀ a ∈ range b,
        (if a = 0 then (((b : ℝ) - 1) / (b : ℝ)) ^ 2 else (1 / (b : ℝ)) ^ 2)
        = (if a = 0 then (((b : ℝ) - 1) / (b : ℝ)) ^ 2 - (1 / (b : ℝ)) ^ 2 else 0)
          + (1 / (b : ℝ)) ^ 2 := by
      intro a _
      by_cases h : a = 0 <;> simp [h]
    rw [Finset.sum_congr rfl h3, Finset.sum_add_distrib,
      Finset.sum_ite_eq' (range b) 0
        (fun _ => (((b : ℝ) - 1) / (b : ℝ)) ^ 2 - (1 / (b : ℝ)) ^ 2),
      Finset.sum_const]
    simp only [show (0 : ℕ) ∈ range b from mem_range.mpr (by omega), if_pos,
      card_range, nsmul_eq_mul]
    ring
  rw [h2]
  field_simp
  ring

/-- **The admissible shell is exact** (Corollaries 5.5/5.9): for the target
`Z_b(p) = r` on the shell of `m = br`-digit primes, the value `k = r − m` of
the additive part sits at the exact centre `μ·m` of the window. -/
theorem zeroWeight_shell_centre (b r : ℕ) (hb : 2 ≤ b) :
    ((r : ℝ) - ((b * r : ℕ) : ℝ)) - ((1 - (b : ℝ)) / (b : ℝ)) * ((b * r : ℕ) : ℝ)
      = 0 := by
  have hb0 : (b : ℝ) ≠ 0 := by
    have h : (0 : ℝ) < b := by
      have : 0 < b := by omega
      exact_mod_cast this
    linarith
  push_cast
  field_simp
  ring

/-! ### Example 5.13: base 3, weights `(1, 2, −3)` -/

/-- The strongly additive part `(0, 1, −4)` of the base-3 example. -/
def exWeight3 : Weight 3 where
  w := fun a => if a = 0 then 0 else if a = 1 then 1 else -4
  hb := by norm_num
  w_zero := by simp

theorem exWeight3_coprime₁ : exWeight3.Coprime₁ := by
  rw [Weight.coprime₁_def]
  decide

theorem exWeight3_dg : exWeight3.dg = 2 := by decide

/-- **Example 5.13, the forcing**: on an odd shell every prime value of
`F_w = ℓ_3 + g` is `2`.  For `p ≠ 2` prime, `g(p) ≡ p ≡ 1 (mod 2)`, so on an
odd shell `F_w(p)` is even. -/
theorem base3_odd_shell_forcing {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {q : ℕ} (hq : q.Prime) (hodd : Odd (lb 3 p))
    (hF : (lb 3 p : ℤ) + exWeight3.eval p = (q : ℤ)) :
    q = 2 := by
  -- the congruence `g(p) ≡ p (mod 2)` from `d_g = 2`
  have h1 : ((2 : ℕ) : ℤ) ∣ exWeight3.eval p - exWeight3.w 1 * p := by
    rw [← exWeight3_dg]
    exact exWeight3.dg_dvd_eval_sub p
  have h2 : exWeight3.w 1 = 1 := by decide
  rw [h2, one_mul] at h1
  -- `p` is odd
  have h3 : p % 2 = 1 := hp.eq_two_or_odd.resolve_left hp2
  obtain ⟨j, hj⟩ := hodd
  -- `q` is even, hence `2`
  rcases hq.eq_two_or_odd with h | h
  · exact h
  · exfalso
    omega

/-! ### The base-4 mean-zero example -/

/-- The weight `(0, 1, 2, −3)` in base `4` of the introduction: mean zero,
satisfying (3), with `d_g = 3` — the example showing `c_g = 3/2 ≠ 1`. -/
def exWeight4 : Weight 4 where
  w := fun a => if a = 0 then 0 else if a = 1 then 1 else if a = 2 then 2 else -3
  hb := by norm_num
  w_zero := by simp

theorem exWeight4_coprime₁ : exWeight4.Coprime₁ := by
  rw [Weight.coprime₁_def]
  decide

theorem exWeight4_dg : exWeight4.dg = 3 := by decide

theorem exWeight4_mu : exWeight4.mu = 0 := by
  have h : ∑ a ∈ range 4, exWeight4.w a = 0 := by decide
  have h2 : ∑ a ∈ range 4, ((exWeight4.w a : ℤ) : ℝ) = ((0 : ℤ) : ℝ) := by
    rw [← h]
    exact (Int.cast_sum _ _).symm
  rw [Weight.mu, h2]
  norm_num

/-! ### The digit sum itself, as a weight -/

/-- The digit-sum weight `a ↦ a`. -/
def sbWeight (b : ℕ) (hb : 2 ≤ b) : Weight b where
  w := fun a => (a : ℤ)
  hb := hb
  w_zero := by simp

theorem eval_sbWeight (b : ℕ) (hb : 2 ≤ b) (n : ℕ) :
    (sbWeight b hb).eval n = (sb b n : ℤ) := by
  rw [Weight.eval, sb]
  rw [Nat.cast_list_sum]
  rfl

theorem sbWeight_coprime₁ (b : ℕ) (hb : 2 ≤ b) : (sbWeight b hb).Coprime₁ := by
  have h1 : (1 : ℕ) ∈ Ico 1 b := by
    rw [mem_Ico]
    omega
  have h2 : ((Ico 1 b).gcd fun a => ((sbWeight b hb).w a).natAbs)
      ∣ ((sbWeight b hb).w 1).natAbs := Finset.gcd_dvd h1
  have h3 : ((sbWeight b hb).w 1).natAbs = 1 := by
    show ((1 : ℕ) : ℤ).natAbs = 1
    norm_num
  rw [h3] at h2
  exact Nat.dvd_one.mp h2

/-- In base `2` the binary digit sum has `d_g = 1`. -/
theorem sbWeight_two_dg : (sbWeight 2 (le_refl 2)).dg = 1 := by
  have h1 : (sbWeight 2 (le_refl 2)).dg ∣ 2 - 1 :=
    (sbWeight 2 (le_refl 2)).dg_dvd_sub_one
  exact Nat.dvd_one.mp h1

/-- In base `2` the binary digit sum has `μ = 1/2 > 0`. -/
theorem sbWeight_two_mu : (sbWeight 2 (le_refl 2)).mu = 1 / 2 := by
  have h : ∑ a ∈ range 2, (sbWeight 2 (le_refl 2)).w a = 1 := by decide
  have h2 : ∑ a ∈ range 2, (((sbWeight 2 (le_refl 2)).w a : ℤ) : ℝ)
      = ((1 : ℤ) : ℝ) := by
    rw [← h]
    exact (Int.cast_sum _ _).symm
  rw [Weight.mu, h2]
  norm_num

end DSS
