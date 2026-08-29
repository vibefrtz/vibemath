/-
DSS/SpectralGap.lean

**Lemma 2.4 of the paper (the two-digit spectral gap): the verified parts.**

The lemma is the engine of the square local limit theorem: with

  `A_θ(t) = (1/b) ∑_{a<b} e(θ g(a) + a t)`,

it asserts `|A_θ(t) A_θ(bt)| ≤ exp(−c_g‖d_gθ‖²)`, with modulus `1` attained
exactly on the lattice `d_gθ ∈ ℤ`.  This file verifies:

1. **The gcd identity (17)** behind the Bezout step, for every `b ≥ 2`:
   `gcd((b−1)g(1), g(2)−2g(1), …, g(b−1)−(b−1)g(1)) = d_g`  (`gcd_bezout`).
2. **The lattice direction**: if `d_gθ ∈ ℤ` then at `t ≡ −θg(1)` both digital
   factors are literally `1`, so the product has modulus one
   (`lattice_abs_one`) — the "⟸" of the equality clause.
3. **The scalar gap inequality** `1 − cos(2πx) ≥ 8‖x‖²`, `‖·‖` the distance
   to the nearest integer (`one_sub_cos_ge`) — the analytic heart, proved
   from Jordan's inequality.
4. **The full quantitative gap in the binary case**, the case the paper's
   Remark 2.3 audits: for `b = 2` and `g` primitive,
   `‖A_θ(t) A_θ(2t)‖ ≤ exp(−(2/5)‖θ‖²)`  (`two_digit_gap_two`),
   with the explicit admissible constant `c_g = 2/5`.
5. **The full quantitative gap in every base `b ≥ 2`** (`two_digit_gap`):
   for primitive `g` there is `c_g > 0` with
   `‖A_θ(t) A_θ(bt)‖ ≤ exp(−c_g‖d_gθ‖²)` uniformly in `θ, t` — via a finset
   Bezout lemma (`finset_gcd_bezout`, `dg_combination`), the distance
   estimate (18) (`dist01_dg_le`), and a one-pair factor bound
   (`norm_digitalFactor_le_pair`).

Not formalised here: the "⟹" direction of the equality clause.

Nothing in this file is conditional: it imports no axioms.
-/
import DSS.Weight

namespace DSS

open Finset

/-! ### The distance to the nearest integer -/

/-- `‖x‖`, the distance from `x` to the nearest integer. -/
noncomputable def dist01 (x : ℝ) : ℝ := |x - round x|

lemma dist01_nonneg (x : ℝ) : 0 ≤ dist01 x := abs_nonneg _

lemma dist01_le_half (x : ℝ) : dist01 x ≤ 1 / 2 := abs_sub_round x

private lemma abs_sub' (a c : ℝ) : |a - c| ≤ |a| + |c| := by
  calc |a - c| = |a + -c| := by ring_nf
    _ ≤ |a| + |-c| := abs_add_le _ _
    _ = |a| + |c| := by rw [abs_neg]

/-- `round` minimises the distance to the integers. -/
lemma dist01_le_abs_sub (x : ℝ) (n : ℤ) : dist01 x ≤ |x - n| := by
  rcases eq_or_ne n (round x) with h | h
  · rw [h]; exact le_refl _
  · have h2 : (1 : ℤ) ≤ |n - round x| := Int.one_le_abs (sub_ne_zero.mpr h)
    have h1 : (1 : ℝ) ≤ |(n : ℝ) - round x| := by
      calc (1 : ℝ) = ((1 : ℤ) : ℝ) := by norm_num
        _ ≤ ((|n - round x| : ℤ) : ℝ) := by exact_mod_cast h2
        _ = |(n : ℝ) - (round x : ℝ)| := by push_cast; rfl
    have h3 : |(n : ℝ) - round x| ≤ |x - n| + |x - round x| := by
      calc |(n : ℝ) - round x| = |(x - round x) - (x - n)| := by ring_nf
        _ ≤ |x - round x| + |x - n| := abs_sub' _ _
        _ = |x - n| + |x - round x| := by ring
    have h4 := abs_sub_round x
    unfold dist01
    linarith

lemma dist01_neg (x : ℝ) : dist01 (-x) = dist01 x := by
  have h1 : dist01 (-x) ≤ dist01 x := by
    calc dist01 (-x) ≤ |(-x) - ((-round x : ℤ) : ℝ)| := dist01_le_abs_sub (-x) (-round x)
      _ = |x - round x| := by push_cast; rw [abs_sub_comm]; ring_nf
      _ = dist01 x := rfl
  have h2 : dist01 x ≤ dist01 (-x) := by
    calc dist01 x ≤ |x - ((-round (-x) : ℤ) : ℝ)| := dist01_le_abs_sub x (-round (-x))
      _ = |(-x) - round (-x)| := by push_cast; rw [abs_sub_comm]; ring_nf
      _ = dist01 (-x) := rfl
  linarith

lemma dist01_sub_le (a c : ℝ) : dist01 (a - c) ≤ dist01 a + dist01 c := by
  calc dist01 (a - c) ≤ |(a - c) - (((round a - round c : ℤ)) : ℝ)| :=
        dist01_le_abs_sub (a - c) (round a - round c)
    _ = |(a - round a) - (c - round c)| := by push_cast; ring_nf
    _ ≤ |a - round a| + |c - round c| := abs_sub' _ _
    _ = dist01 a + dist01 c := rfl

lemma dist01_two_mul_le (a : ℝ) : dist01 (2 * a) ≤ 2 * dist01 a := by
  calc dist01 (2 * a) ≤ |2 * a - ((2 * round a : ℤ) : ℝ)| :=
        dist01_le_abs_sub (2 * a) (2 * round a)
    _ = |2 * (a - round a)| := by push_cast; ring_nf
    _ = 2 * |a - round a| := by rw [abs_mul]; norm_num
    _ = 2 * dist01 a := rfl

/-! ### The scalar gap inequality -/

/-- `sin(πδ) ≥ 2δ` for `0 ≤ δ ≤ 1/2` (Jordan's inequality). -/
lemma sin_pi_mul_ge {δ : ℝ} (h0 : 0 ≤ δ) (h1 : δ ≤ 1 / 2) :
    2 * δ ≤ Real.sin (Real.pi * δ) := by
  have hπ := Real.pi_pos
  have hx0 : 0 ≤ Real.pi * δ := by positivity
  have hx1 : Real.pi * δ ≤ Real.pi / 2 := by nlinarith
  have h := Real.mul_le_sin hx0 hx1
  calc 2 * δ = 2 / Real.pi * (Real.pi * δ) := by field_simp
    _ ≤ Real.sin (Real.pi * δ) := h

/-- **The scalar spectral gap:** `1 − cos(2πx) ≥ 8‖x‖²`. -/
theorem one_sub_cos_ge (x : ℝ) :
    8 * dist01 x ^ 2 ≤ 1 - Real.cos (2 * Real.pi * x) := by
  obtain ⟨δ, hδdef⟩ : ∃ t : ℝ, t = x - round x := ⟨_, rfl⟩
  -- `1 − cos(2πx) = 2 sin²(πx)`, and `sin²(πx) = sin²(πδ)` by periodicity
  have hcos : Real.cos (2 * Real.pi * x) = 1 - 2 * Real.sin (Real.pi * x) ^ 2 := by
    have h1 := Real.cos_two_mul (Real.pi * x)
    have h2 := Real.sin_sq_add_cos_sq (Real.pi * x)
    have h3 : 2 * Real.pi * x = 2 * (Real.pi * x) := by ring
    rw [h3, h1]
    nlinarith
  have hper : Real.sin (Real.pi * x) ^ 2 = Real.sin (Real.pi * δ) ^ 2 := by
    have hx : Real.pi * x = Real.pi * δ + (round x : ℤ) * Real.pi := by
      rw [hδdef]; ring
    rw [hx, Real.sin_add_int_mul_pi]
    rcases Int.even_or_odd (round x) with he | ho
    · rw [he.neg_one_zpow]
      ring
    · rw [ho.neg_one_zpow]
      ring
  -- Jordan on `|δ| ≤ 1/2`
  have hδabs : |δ| ≤ 1 / 2 := by rw [hδdef]; exact abs_sub_round x
  have hsin : 2 * |δ| ≤ |Real.sin (Real.pi * δ)| := by
    rcases abs_cases δ with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1] at hδabs ⊢
      have := sin_pi_mul_ge h2 hδabs
      calc 2 * δ ≤ Real.sin (Real.pi * δ) := this
        _ ≤ |Real.sin (Real.pi * δ)| := le_abs_self _
    · rw [h1] at hδabs ⊢
      have hneg : 0 ≤ -δ := by linarith
      have := sin_pi_mul_ge hneg hδabs
      have hodd : Real.sin (Real.pi * (-δ)) = -Real.sin (Real.pi * δ) := by
        rw [show Real.pi * (-δ) = -(Real.pi * δ) by ring, Real.sin_neg]
      rw [hodd] at this
      calc 2 * -δ ≤ -Real.sin (Real.pi * δ) := this
        _ ≤ |Real.sin (Real.pi * δ)| := neg_le_abs _
  have hd : dist01 x = |δ| := by rw [dist01, hδdef]
  have hsq : 4 * dist01 x ^ 2 ≤ Real.sin (Real.pi * δ) ^ 2 := by
    rw [hd]
    have h1 : (2 * |δ|) ^ 2 ≤ |Real.sin (Real.pi * δ)| ^ 2 := by
      apply sq_le_sq' _ hsin
      have : 0 ≤ 2 * |δ| := by positivity
      linarith [abs_nonneg (Real.sin (Real.pi * δ))]
    have h2 : |Real.sin (Real.pi * δ)| ^ 2 = Real.sin (Real.pi * δ) ^ 2 := sq_abs _
    nlinarith
  rw [hcos]
  nlinarith [hsq, hper]

/-! ### The gcd identity (17) -/

/-- **Equation (17) of the paper:** under (1),

`gcd((b−1)·g(1), g(2)−2g(1), …, g(b−1)−(b−1)g(1)) = d_g`.

The left side is `gcd((b−1)|g(1)|, G)` with `G` the gcd of eq. (2); the
content is that primitivity lets the factor `|g(1)|` be removed. -/
theorem gcd_bezout {b : ℕ} (g : Weight b) (hg : g.Coprime₁) :
    Nat.gcd ((b - 1) * (g.w 1).natAbs)
      ((range b).gcd fun a => (g.w a - (a : ℤ) * g.w 1).natAbs) = g.dg := by
  set G : ℕ := (range b).gcd fun a => (g.w a - (a : ℤ) * g.w 1).natAbs with hGdef
  set D : ℕ := Nat.gcd ((b - 1) * (g.w 1).natAbs) G with hDdef
  have hdg : g.dg = Nat.gcd (b - 1) G := g.dg_def
  -- `D` is coprime to `|g(1)|`
  have hcop : Nat.Coprime D (g.w 1).natAbs := by
    set e : ℕ := Nat.gcd D (g.w 1).natAbs with hedef
    have he1 : (e : ℤ) ∣ g.w 1 :=
      Int.dvd_natAbs.mp (Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_right _ _))
    have heG : e ∣ G := dvd_trans (Nat.gcd_dvd_left _ _) (Nat.gcd_dvd_right _ _)
    have hall : ∀ a ∈ Ico 1 b, e ∣ (g.w a).natAbs := by
      intro a ha
      have hab : a < b := (mem_Ico.mp ha).2
      have h1 : e ∣ (g.w a - (a : ℤ) * g.w 1).natAbs :=
        dvd_trans heG (Finset.gcd_dvd (mem_range.mpr hab))
      have h2 : (e : ℤ) ∣ g.w a - (a : ℤ) * g.w 1 :=
        Int.dvd_natAbs.mp (Int.natCast_dvd_natCast.mpr h1)
      have h3 : (e : ℤ) ∣ (a : ℤ) * g.w 1 := Dvd.dvd.mul_left he1 _
      have h4 : (e : ℤ) ∣ g.w a := by
        have := dvd_add h2 h3
        simpa using this
      exact Int.natCast_dvd_natCast.mp (Int.dvd_natAbs.mpr h4)
    have h5 : e ∣ ((Ico 1 b).gcd fun a => (g.w a).natAbs) := Finset.dvd_gcd hall
    rw [hg] at h5
    exact Nat.eq_one_of_dvd_one h5
  -- `D ∣ b − 1`
  have hDb : D ∣ b - 1 := by
    have h1 : D ∣ (b - 1) * (g.w 1).natAbs := Nat.gcd_dvd_left _ _
    exact (Nat.Coprime.dvd_of_dvd_mul_right hcop) h1
  -- `D ∣ d_g`
  have hDdg : D ∣ g.dg := by
    rw [hdg]
    exact Nat.dvd_gcd hDb (Nat.gcd_dvd_right _ _)
  -- `d_g ∣ D`
  have hdgD : g.dg ∣ D := by
    have h1 : g.dg ∣ b - 1 := g.dg_dvd_sub_one
    have h2 : g.dg ∣ (b - 1) * (g.w 1).natAbs := Dvd.dvd.mul_right h1 _
    have h3 : g.dg ∣ G := by
      rw [hdg]
      exact Nat.gcd_dvd_right _ _
    exact Nat.dvd_gcd h2 h3
  exact Nat.dvd_antisymm hDdg hdgD

/-! ### The digital factor and the lattice direction -/

/-- The one-digit factor `A_θ(t) = (1/b) ∑_{a<b} e(θ g(a) + a t)` of (15). -/
noncomputable def digitalFactor {b : ℕ} (g : Weight b) (θ t : ℝ) : ℂ :=
  (b : ℂ)⁻¹ * ∑ a ∈ range b,
    Complex.exp (2 * Real.pi * Complex.I * ((θ * g.w a + a * t : ℝ) : ℂ))

private lemma exp_two_pi_int (n : ℤ) :
    Complex.exp (2 * Real.pi * Complex.I * ((n : ℝ) : ℂ)) = 1 := by
  have h := Complex.exp_int_mul_two_pi_mul_I n
  rw [← h]
  congr 1
  push_cast
  ring

/-- **The lattice direction of Lemma 2.4**: if `d_gθ ∈ ℤ`, then at
`t = −θ·g(1)` both digital factors equal `1`, so
`‖A_θ(t)A_θ(bt)‖ = 1`.  (Together with the gap inequality this is the "⟸"
of the equality clause.) -/
theorem lattice_abs_one {b : ℕ} (g : Weight b) {θ : ℝ} (z : ℤ)
    (hz : (g.dg : ℝ) * θ = z) :
    ‖digitalFactor g θ (-(θ * g.w 1))
      * digitalFactor g θ ((b : ℝ) * (-(θ * g.w 1)))‖ = 1 := by
  -- every phase in either factor is an integer
  have hphase1 : ∀ a : ℕ, a < b → ∃ n : ℤ,
      θ * g.w a + a * (-(θ * g.w 1)) = (n : ℝ) := by
    intro a ha
    obtain ⟨q, hq⟩ := g.dg_dvd_sub a ha
    refine ⟨z * q, ?_⟩
    calc θ * g.w a + a * (-(θ * g.w 1))
        = θ * (((g.w a - (a : ℤ) * g.w 1) : ℤ) : ℝ) := by push_cast; ring
      _ = θ * (((g.dg : ℤ) * q : ℤ) : ℝ) := by rw [hq]
      _ = ((g.dg : ℝ) * θ) * (q : ℝ) := by push_cast; ring
      _ = (z : ℝ) * (q : ℝ) := by rw [hz]
      _ = ((z * q : ℤ) : ℝ) := by push_cast; ring
  have hphase2 : ∀ a : ℕ, a < b → ∃ n : ℤ,
      θ * g.w a + a * ((b : ℝ) * (-(θ * g.w 1))) = (n : ℝ) := by
    intro a ha
    obtain ⟨q, hq⟩ := g.dg_dvd_sub a ha
    obtain ⟨e, he⟩ := g.dg_dvd_sub_one
    have hb1 : (1 : ℕ) ≤ b := le_of_lt g.one_lt_b
    have hbe : ((b : ℤ) - 1) = (g.dg : ℤ) * e := by
      have h0 : b - 1 = g.dg * e := he
      omega
    refine ⟨z * q - a * (z * (e * g.w 1)), ?_⟩
    have key : θ * g.w a + a * ((b : ℝ) * (-(θ * g.w 1)))
        = θ * (((g.w a - (a : ℤ) * g.w 1) : ℤ) : ℝ)
          - (a : ℝ) * (θ * (((((b : ℤ) - 1)) * g.w 1 : ℤ) : ℝ)) := by
      push_cast
      ring
    rw [key, hq, hbe]
    have h1 : θ * (((g.dg : ℤ) * q : ℤ) : ℝ) = ((z * q : ℤ) : ℝ) := by
      push_cast
      calc θ * ((g.dg : ℝ) * (q : ℝ)) = ((g.dg : ℝ) * θ) * (q : ℝ) := by ring
        _ = (z : ℝ) * (q : ℝ) := by rw [hz]
    have h2 : θ * ((((g.dg : ℤ) * e) * g.w 1 : ℤ) : ℝ)
        = ((z * (e * g.w 1) : ℤ) : ℝ) := by
      push_cast
      calc θ * ((g.dg : ℝ) * (e : ℝ) * ((g.w 1 : ℤ) : ℝ))
          = ((g.dg : ℝ) * θ) * ((e : ℝ) * ((g.w 1 : ℤ) : ℝ)) := by ring
        _ = (z : ℝ) * ((e : ℝ) * ((g.w 1 : ℤ) : ℝ)) := by rw [hz]
    rw [h1, h2]
    push_cast
    ring
  -- a factor with all phases integral equals `1`
  have hfactor : ∀ t : ℝ, (∀ a : ℕ, a < b → ∃ n : ℤ,
      θ * g.w a + a * t = (n : ℝ)) → digitalFactor g θ t = 1 := by
    intro t ht
    unfold digitalFactor
    have hsum : ∑ a ∈ range b,
        Complex.exp (2 * Real.pi * Complex.I * ((θ * g.w a + a * t : ℝ) : ℂ))
        = (b : ℂ) := by
      have hone : ∀ a ∈ range b,
          Complex.exp (2 * Real.pi * Complex.I * ((θ * g.w a + a * t : ℝ) : ℂ))
            = 1 := by
        intro a ha
        obtain ⟨n, hn⟩ := ht a (mem_range.mp ha)
        rw [hn]
        exact exp_two_pi_int n
      rw [Finset.sum_congr rfl hone]
      simp
    rw [hsum]
    have hbne : (b : ℂ) ≠ 0 := by
      have hb : b ≠ 0 := Nat.pos_iff_ne_zero.mp g.b_pos
      exact_mod_cast hb
    field_simp
  rw [hfactor _ hphase1, hfactor _ hphase2]
  simp

/-! ### The full gap in the binary case -/

private lemma normSq_one_add_exp (ψ : ℝ) :
    Complex.normSq (1 + Complex.exp (2 * Real.pi * Complex.I * (ψ : ℂ)))
      = 2 + 2 * Real.cos (2 * Real.pi * ψ) := by
  have h1 : 2 * Real.pi * Complex.I * (ψ : ℂ)
      = ((2 * Real.pi * ψ : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [h1, Complex.exp_mul_I]
  have hc : Complex.cos ((2 * Real.pi * ψ : ℝ) : ℂ)
      = ((Real.cos (2 * Real.pi * ψ) : ℝ) : ℂ) := (Complex.ofReal_cos _).symm
  have hs : Complex.sin ((2 * Real.pi * ψ : ℝ) : ℂ)
      = ((Real.sin (2 * Real.pi * ψ) : ℝ) : ℂ) := (Complex.ofReal_sin _).symm
  rw [hc, hs]
  have h2 : (1 : ℂ) + (((Real.cos (2 * Real.pi * ψ) : ℝ) : ℂ)
      + ((Real.sin (2 * Real.pi * ψ) : ℝ) : ℂ) * Complex.I)
      = (((1 + Real.cos (2 * Real.pi * ψ) : ℝ) : ℂ)
        + ((Real.sin (2 * Real.pi * ψ) : ℝ) : ℂ) * Complex.I) := by
    push_cast
    ring
  rw [h2, Complex.normSq_add_mul_I]
  have hpy := Real.sin_sq_add_cos_sq (2 * Real.pi * ψ)
  nlinarith

/-- `‖A_θ(t)‖² = (1 + cos 2πφ)/2` in base `2`, where `φ = θ·g(1) + t` is the
only nontrivial phase. -/
private lemma normSq_digitalFactor_two (g : Weight 2) (θ t : ℝ) :
    Complex.normSq (digitalFactor g θ t)
      = (1 + Real.cos (2 * Real.pi * (θ * g.w 1 + t))) / 2 := by
  have hexp : digitalFactor g θ t
      = (2 : ℂ)⁻¹ * (1 + Complex.exp
          (2 * Real.pi * Complex.I * ((θ * g.w 1 + t : ℝ) : ℂ))) := by
    unfold digitalFactor
    rw [Finset.sum_range_succ, Finset.sum_range_one]
    have h0 : ((θ * g.w 0 + (0 : ℕ) * t : ℝ) : ℂ) = 0 := by
      rw [g.w_zero]
      push_cast
      ring
    have h1 : ((θ * g.w 1 + (1 : ℕ) * t : ℝ) : ℂ) = ((θ * g.w 1 + t : ℝ) : ℂ) := by
      push_cast
      ring
    rw [h0, h1, mul_zero, Complex.exp_zero]
    norm_num
  rw [hexp, Complex.normSq_mul, normSq_one_add_exp]
  have h2 : Complex.normSq ((2 : ℂ)⁻¹) = 1 / 4 := by
    rw [Complex.normSq_inv]
    norm_num
  rw [h2]
  ring

/-- **The two-digit spectral gap in base `2` (Lemma 2.4, case `b = 2`),
with the explicit constant `2/5`:**

`‖A_θ(t) · A_θ(2t)‖ ≤ exp(−(2/5)·‖θ‖²)`, uniformly in `θ, t`. -/
theorem two_digit_gap_two (g : Weight 2) (hg : g.Coprime₁) (θ t : ℝ) :
    ‖digitalFactor g θ t * digitalFactor g θ (2 * t)‖
      ≤ Real.exp (-(2 / 5) * dist01 θ ^ 2) := by
  -- primitivity in base 2: `g(1) = ±1`
  have hw1 : g.w 1 = 1 ∨ g.w 1 = -1 := by
    have h1 : ((Ico 1 2).gcd fun a => (g.w a).natAbs) = 1 := hg
    have h2 : Ico 1 2 = {1} := by decide
    rw [h2] at h1
    have h3 : (g.w 1).natAbs = 1 := by simpa using h1
    rcases Int.natAbs_eq_iff.mp h3 with h | h
    · left; exact_mod_cast h
    · right; exact_mod_cast h
  obtain ⟨x, hxdef⟩ : ∃ u : ℝ, u = dist01 (θ * g.w 1 + t) := ⟨_, rfl⟩
  obtain ⟨y, hydef⟩ : ∃ u : ℝ, u = dist01 (θ * g.w 1 + 2 * t) := ⟨_, rfl⟩
  have hx0 : 0 ≤ x := by rw [hxdef]; exact dist01_nonneg _
  have hy0 : 0 ≤ y := by rw [hydef]; exact dist01_nonneg _
  -- the triangle chain: `‖θ‖ = ‖θ·g(1)‖ ≤ 2x + y`
  have htri : dist01 θ ≤ 2 * x + y := by
    have hsub : dist01 (θ * g.w 1)
        ≤ dist01 (2 * (θ * g.w 1 + t)) + dist01 (θ * g.w 1 + 2 * t) := by
      have hidn : θ * g.w 1 = 2 * (θ * g.w 1 + t) - (θ * g.w 1 + 2 * t) := by ring
      calc dist01 (θ * g.w 1)
          = dist01 (2 * (θ * g.w 1 + t) - (θ * g.w 1 + 2 * t)) := by rw [← hidn]
        _ ≤ dist01 (2 * (θ * g.w 1 + t)) + dist01 (θ * g.w 1 + 2 * t) :=
            dist01_sub_le _ _
    have h2x : dist01 (2 * (θ * g.w 1 + t)) ≤ 2 * x := by
      rw [hxdef]
      exact dist01_two_mul_le _
    have hw : dist01 (θ * (g.w 1 : ℝ)) = dist01 θ := by
      rcases hw1 with h | h
      · rw [h]; norm_num
      · rw [h]
        push_cast
        rw [show θ * (-1 : ℝ) = -θ by ring, dist01_neg]
    rw [hw] at hsub
    rw [hydef]
    linarith
  -- each factor: `‖A‖² ≤ 1 − 4·dist² ≤ exp(−4·dist²)`
  have hfac : ∀ u : ℝ, Complex.normSq (digitalFactor g θ u)
      ≤ Real.exp (-(4 * dist01 (θ * g.w 1 + u) ^ 2)) := by
    intro u
    rw [normSq_digitalFactor_two]
    have h1 := one_sub_cos_ge (θ * g.w 1 + u)
    have h3 : 1 - 4 * dist01 (θ * g.w 1 + u) ^ 2
        ≤ Real.exp (-(4 * dist01 (θ * g.w 1 + u) ^ 2)) := by
      have := Real.add_one_le_exp (-(4 * dist01 (θ * g.w 1 + u) ^ 2))
      linarith
    linarith
  -- assemble
  have hxfac := hfac t
  have hyfac := hfac (2 * t)
  rw [← hxdef] at hxfac
  rw [← hydef] at hyfac
  have hnormSq : ∀ z : ℂ, Complex.normSq z = ‖z‖ ^ 2 := fun z =>
    Complex.normSq_eq_norm_sq z
  have habs2 : ‖digitalFactor g θ t * digitalFactor g θ (2 * t)‖ ^ 2
      ≤ Real.exp (-(4 * x ^ 2)) * Real.exp (-(4 * y ^ 2)) := by
    rw [norm_mul, mul_pow, ← hnormSq, ← hnormSq]
    exact mul_le_mul hxfac hyfac (Complex.normSq_nonneg _)
      (le_of_lt (Real.exp_pos _))
  have hexp2 : Real.exp (-(4 * x ^ 2)) * Real.exp (-(4 * y ^ 2))
      = Real.exp (-(2 * (x ^ 2 + y ^ 2))) ^ 2 := by
    rw [← Real.exp_add, ← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hroot : ‖digitalFactor g θ t * digitalFactor g θ (2 * t)‖
      ≤ Real.exp (-(2 * (x ^ 2 + y ^ 2))) := by
    have h1 : ‖digitalFactor g θ t * digitalFactor g θ (2 * t)‖ ^ 2
        ≤ Real.exp (-(2 * (x ^ 2 + y ^ 2))) ^ 2 := by
      rw [← hexp2]
      exact habs2
    have h2 : (0 : ℝ) ≤ ‖digitalFactor g θ t * digitalFactor g θ (2 * t)‖ :=
      norm_nonneg _
    have h3 : (0 : ℝ) ≤ Real.exp (-(2 * (x ^ 2 + y ^ 2))) := le_of_lt (Real.exp_pos _)
    nlinarith
  refine le_trans hroot ?_
  -- `(2x+y)² ≤ 5(x²+y²)`, so `2(x²+y²) ≥ (2/5)‖θ‖²`
  apply Real.exp_le_exp.mpr
  have hCS : (2 * x + y) ^ 2 ≤ 5 * (x ^ 2 + y ^ 2) := by nlinarith [sq_nonneg (x - 2 * y)]
  have hθ2 : dist01 θ ^ 2 ≤ (2 * x + y) ^ 2 := by
    apply sq_le_sq' _ htri
    have := dist01_nonneg θ
    linarith
  nlinarith

/-! ### The full gap in every base

The proof below deviates from the paper's in one inessential way: instead of
expanding `1 − |A_θ(t)|²` as a double sum over all digit pairs, it keeps the
single pair `(0, a)` by the triangle inequality (`‖ΣE‖ ≤ ‖E₀ + E_a‖ + (b−2)`),
which already yields `‖A_θ(t)‖ ≤ 1 − (4/b)‖θg(a) + at‖²` for every digit
`1 ≤ a < b`; and instead of Cauchy–Schwarz over the `b` distances it uses the
maximal one.  Only the value of the constant `c_g` changes. -/

lemma dist01_zero : dist01 0 = 0 := by simp [dist01]

lemma dist01_add_le (a c : ℝ) : dist01 (a + c) ≤ dist01 a + dist01 c := by
  have h := dist01_sub_le a (-c)
  rw [sub_neg_eq_add, dist01_neg] at h
  exact h

lemma dist01_int_mul_le (n : ℤ) (a : ℝ) :
    dist01 ((n : ℝ) * a) ≤ |(n : ℝ)| * dist01 a := by
  calc dist01 ((n : ℝ) * a)
      ≤ |(n : ℝ) * a - ((n * round a : ℤ) : ℝ)| := dist01_le_abs_sub _ (n * round a)
    _ = |(n : ℝ) * (a - ((round a : ℤ) : ℝ))| := by congr 1; push_cast; ring
    _ = |(n : ℝ)| * |a - ((round a : ℤ) : ℝ)| := abs_mul _ _
    _ = |(n : ℝ)| * dist01 a := rfl

lemma dist01_nat_mul_le (n : ℕ) (a : ℝ) :
    dist01 ((n : ℝ) * a) ≤ (n : ℝ) * dist01 a := by
  have h := dist01_int_mul_le (n : ℤ) a
  push_cast at h
  simpa [Nat.abs_cast] using h

lemma dist01_sum_le {ι : Type*} (s : Finset ι) (h : ι → ℝ) :
    dist01 (∑ i ∈ s, h i) ≤ ∑ i ∈ s, dist01 (h i) := by
  induction s using Finset.cons_induction with
  | empty => simp [dist01]
  | cons a s ha ih =>
      rw [Finset.sum_cons, Finset.sum_cons]
      exact le_trans (dist01_add_le _ _) (by linarith)

/-- **Finset Bezout:** the `gcd` of the absolute values of finitely many
integers is a `ℤ`-linear combination of those integers. -/
lemma finset_gcd_bezout (s : Finset ℕ) (f : ℕ → ℤ) :
    ∃ β : ℕ → ℤ, (((s.gcd fun a => (f a).natAbs) : ℕ) : ℤ) = ∑ a ∈ s, β a * f a := by
  induction s using Finset.induction_on with
  | empty => exact ⟨fun _ => 0, by simp⟩
  | insert a s ha ih =>
      obtain ⟨β, hβ⟩ := ih
      obtain ⟨G, hGdef⟩ : ∃ G : ℕ, G = s.gcd fun x => (f x).natAbs := ⟨_, rfl⟩
      refine ⟨fun x => if x = a then Int.gcdA (f a) (G : ℤ)
        else Int.gcdB (f a) (G : ℤ) * β x, ?_⟩
      have hkey : ((Nat.gcd (f a).natAbs G : ℕ) : ℤ)
          = f a * Int.gcdA (f a) (G : ℤ) + (G : ℤ) * Int.gcdB (f a) (G : ℤ) := by
        have h1 : Int.gcd (f a) ((G : ℕ) : ℤ) = Nat.gcd (f a).natAbs G := rfl
        rw [← h1]
        exact Int.gcd_eq_gcd_ab (f a) (G : ℤ)
      have hgcd : (insert a s).gcd (fun x => (f x).natAbs) = Nat.gcd (f a).natAbs G := by
        rw [Finset.gcd_insert, hGdef]
        rfl
      have hsum : ∑ x ∈ s, (if x = a then Int.gcdA (f a) (G : ℤ)
          else Int.gcdB (f a) (G : ℤ) * β x) * f x
          = Int.gcdB (f a) (G : ℤ) * ∑ x ∈ s, β x * f x := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun x hx => ?_
        rw [if_neg (ne_of_mem_of_not_mem hx ha), mul_assoc]
      rw [hgcd, Finset.sum_insert ha]
      dsimp only
      rw [if_pos rfl, hsum, ← hβ, ← hGdef, hkey]
      ring

/-- The characteristic modulus as a `ℤ`-linear combination of `(b−1)g(1)` and
the differences `g(a) − a·g(1)` — the Bezout coefficients behind (17). -/
lemma dg_combination {b : ℕ} (g : Weight b) (hg : g.Coprime₁) :
    ∃ γ : ℤ, ∃ β : ℕ → ℤ,
      (g.dg : ℤ) = γ * (((b : ℤ) - 1) * g.w 1)
        + ∑ a ∈ range b, β a * (g.w a - (a : ℤ) * g.w 1) := by
  obtain ⟨β, hβ⟩ := finset_gcd_bezout (range b) (fun a => g.w a - (a : ℤ) * g.w 1)
  obtain ⟨G, hGdef⟩ : ∃ G : ℕ, G = (range b).gcd fun a => (g.w a - (a : ℤ) * g.w 1).natAbs :=
    ⟨_, rfl⟩
  have hb1 : 1 ≤ b := le_trans (by norm_num) g.hb
  have hdg : ((Nat.gcd ((b - 1) * (g.w 1).natAbs) G : ℕ) : ℤ) = (g.dg : ℤ) := by
    rw [hGdef]
    exact_mod_cast congrArg (Nat.cast : ℕ → ℤ) (gcd_bezout g hg)
  have habs : (b - 1) * (g.w 1).natAbs = (((b : ℤ) - 1) * g.w 1).natAbs := by
    rw [Int.natAbs_mul]
    congr 1
    have : ((b : ℤ) - 1) = ((b - 1 : ℕ) : ℤ) := by push_cast [hb1]; ring
    rw [this, Int.natAbs_natCast]
  have hkey : ((Nat.gcd ((((b : ℤ) - 1) * g.w 1).natAbs) G : ℕ) : ℤ)
      = (((b : ℤ) - 1) * g.w 1) * Int.gcdA (((b : ℤ) - 1) * g.w 1) (G : ℤ)
        + (G : ℤ) * Int.gcdB (((b : ℤ) - 1) * g.w 1) (G : ℤ) := by
    have h1 : Int.gcd (((b : ℤ) - 1) * g.w 1) ((G : ℕ) : ℤ)
        = Nat.gcd ((((b : ℤ) - 1) * g.w 1).natAbs) G := rfl
    rw [← h1]
    exact Int.gcd_eq_gcd_ab _ _
  refine ⟨Int.gcdA (((b : ℤ) - 1) * g.w 1) (G : ℤ),
    fun x => Int.gcdB (((b : ℤ) - 1) * g.w 1) (G : ℤ) * β x, ?_⟩
  have hsum : ∑ a ∈ range b,
      (Int.gcdB (((b : ℤ) - 1) * g.w 1) (G : ℤ) * β a) * (g.w a - (a : ℤ) * g.w 1)
      = Int.gcdB (((b : ℤ) - 1) * g.w 1) (G : ℤ)
          * ∑ a ∈ range b, β a * (g.w a - (a : ℤ) * g.w 1) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => by ring
  rw [hsum, ← hβ, ← hGdef, ← hdg, habs, hkey]
  ring

/-- **The Bezout distance estimate (18):** there is `K = K(g) ≥ 1` with

`‖d_gθ‖ ≤ K·(∑_{1≤a<b} ‖θg(a) + at‖ + ‖θg(1) + bt‖)` for all `θ, t`. -/
lemma dist01_dg_le {b : ℕ} (g : Weight b) (hg : g.Coprime₁) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ θ t : ℝ,
      dist01 ((g.dg : ℝ) * θ)
        ≤ K * ((∑ a ∈ Ico 1 b, dist01 (θ * g.w a + a * t))
            + dist01 (θ * g.w 1 + b * t)) := by
  obtain ⟨γ, β, hcomb⟩ := dg_combination g hg
  refine ⟨(|(γ : ℝ)| + ∑ a ∈ range b, |(β a : ℝ)|) * (b + 1) + 1, ?_, fun θ t => ?_⟩
  · have h1 : (0 : ℝ) ≤ |(γ : ℝ)| + ∑ a ∈ range b, |(β a : ℝ)| := by positivity
    have h2 : (0 : ℝ) ≤ (b : ℝ) + 1 := by positivity
    nlinarith
  obtain ⟨M, hMdef⟩ : ∃ M : ℝ,
      M = (∑ a ∈ Ico 1 b, dist01 (θ * g.w a + a * t)) + dist01 (θ * g.w 1 + b * t) :=
    ⟨_, rfl⟩
  have hM0 : 0 ≤ M := by
    rw [hMdef]
    have h1 : 0 ≤ ∑ a ∈ Ico 1 b, dist01 (θ * g.w a + a * t) :=
      Finset.sum_nonneg fun a _ => dist01_nonneg _
    have h2 := dist01_nonneg (θ * g.w 1 + b * t)
    linarith
  have h1b : (1 : ℕ) ∈ Ico 1 b := by
    rw [mem_Ico]
    exact ⟨le_refl 1, lt_of_lt_of_le (by norm_num) g.hb⟩
  -- each individual distance is at most `M`
  have hxa_le : ∀ a ∈ Ico 1 b, dist01 (θ * g.w a + a * t) ≤ M := by
    intro a ha
    rw [hMdef]
    have h1 : dist01 (θ * g.w a + a * t)
        ≤ ∑ c ∈ Ico 1 b, dist01 (θ * g.w c + c * t) :=
      Finset.single_le_sum (f := fun c : ℕ => dist01 (θ * g.w c + c * t))
        (fun c _ => dist01_nonneg _) ha
    have h2 := dist01_nonneg (θ * g.w 1 + b * t)
    linarith
  have hy_le : dist01 (θ * g.w 1 + b * t) ≤ M := by
    rw [hMdef]
    have h1 : 0 ≤ ∑ a ∈ Ico 1 b, dist01 (θ * g.w a + a * t) :=
      Finset.sum_nonneg fun a _ => dist01_nonneg _
    linarith
  -- the two triangle estimates
  have hX : dist01 ((((b : ℝ) - 1) * g.w 1) * θ) ≤ (b + 1) * M := by
    have hid : (((b : ℝ) - 1) * g.w 1) * θ
        = (b : ℝ) * (θ * g.w 1 + t) - (θ * g.w 1 + b * t) := by ring
    calc dist01 ((((b : ℝ) - 1) * g.w 1) * θ)
        = dist01 ((b : ℝ) * (θ * g.w 1 + t) - (θ * g.w 1 + b * t)) := by rw [hid]
      _ ≤ dist01 ((b : ℝ) * (θ * g.w 1 + t)) + dist01 (θ * g.w 1 + b * t) :=
          dist01_sub_le _ _
      _ ≤ (b : ℝ) * dist01 (θ * g.w 1 + t) + dist01 (θ * g.w 1 + b * t) := by
          have := dist01_nat_mul_le b (θ * g.w 1 + t)
          linarith
      _ ≤ (b : ℝ) * M + M := by
          have h1 := hxa_le 1 h1b
          have h2 : θ * g.w 1 + (1 : ℕ) * t = θ * g.w 1 + t := by push_cast; ring
          rw [h2] at h1
          have hb0 : (0 : ℝ) ≤ b := by positivity
          nlinarith [hy_le]
      _ = (b + 1) * M := by ring
  have hY : ∀ a ∈ range b, dist01 (((g.w a : ℝ) - (a : ℝ) * g.w 1) * θ) ≤ (b + 1) * M := by
    intro a haR
    have hab : a < b := mem_range.mp haR
    rcases Nat.eq_zero_or_pos a with rfl | ha1
    · have h0 : ((g.w 0 : ℝ) - ((0 : ℕ) : ℝ) * g.w 1) * θ = 0 := by
        rw [g.w_zero]
        push_cast
        ring
      rw [h0, dist01_zero]
      positivity
    · have hid : ((g.w a : ℝ) - (a : ℝ) * g.w 1) * θ
          = (θ * g.w a + a * t) - (a : ℝ) * (θ * g.w 1 + t) := by ring
      have haI : a ∈ Ico 1 b := by rw [mem_Ico]; exact ⟨ha1, hab⟩
      calc dist01 (((g.w a : ℝ) - (a : ℝ) * g.w 1) * θ)
          = dist01 ((θ * g.w a + a * t) - (a : ℝ) * (θ * g.w 1 + t)) := by rw [hid]
        _ ≤ dist01 (θ * g.w a + a * t) + dist01 ((a : ℝ) * (θ * g.w 1 + t)) :=
            dist01_sub_le _ _
        _ ≤ dist01 (θ * g.w a + a * t) + (a : ℝ) * dist01 (θ * g.w 1 + t) := by
            have := dist01_nat_mul_le a (θ * g.w 1 + t)
            linarith
        _ ≤ M + (b : ℝ) * M := by
            have h1 := hxa_le a haI
            have h2 := hxa_le 1 h1b
            have h3 : θ * g.w 1 + (1 : ℕ) * t = θ * g.w 1 + t := by push_cast; ring
            rw [h3] at h2
            have ha' : (a : ℝ) ≤ b := by exact_mod_cast le_of_lt hab
            have hd0 := dist01_nonneg (θ * g.w 1 + t)
            nlinarith
        _ = (b + 1) * M := by ring
  -- cast the Bezout combination to `ℝ` and estimate
  have hR : (g.dg : ℝ) * θ
      = (γ : ℝ) * (((((b : ℝ) - 1) * g.w 1)) * θ)
        + ∑ a ∈ range b, (β a : ℝ) * (((g.w a : ℝ) - (a : ℝ) * g.w 1) * θ) := by
    have hC := congrArg (fun z : ℤ => (z : ℝ)) hcomb
    push_cast at hC
    calc (g.dg : ℝ) * θ
        = ((γ : ℝ) * (((b : ℝ) - 1) * g.w 1)
            + ∑ a ∈ range b, (β a : ℝ) * ((g.w a : ℝ) - (a : ℝ) * g.w 1)) * θ := by
          rw [← hC]
      _ = (γ : ℝ) * (((((b : ℝ) - 1) * g.w 1)) * θ)
            + ∑ a ∈ range b, (β a : ℝ) * (((g.w a : ℝ) - (a : ℝ) * g.w 1) * θ) := by
          rw [add_mul, Finset.sum_mul]
          congr 1
          · ring
          · exact Finset.sum_congr rfl fun a _ => by ring
  calc dist01 ((g.dg : ℝ) * θ)
      ≤ dist01 ((γ : ℝ) * (((((b : ℝ) - 1) * g.w 1)) * θ))
        + dist01 (∑ a ∈ range b, (β a : ℝ) * (((g.w a : ℝ) - (a : ℝ) * g.w 1) * θ)) := by
        rw [hR]
        exact dist01_add_le _ _
    _ ≤ |(γ : ℝ)| * dist01 ((((b : ℝ) - 1) * g.w 1) * θ)
        + ∑ a ∈ range b, |(β a : ℝ)| * dist01 (((g.w a : ℝ) - (a : ℝ) * g.w 1) * θ) := by
        have h1 := dist01_int_mul_le γ ((((b : ℝ) - 1) * g.w 1) * θ)
        have h2 := dist01_sum_le (range b)
          (fun a => (β a : ℝ) * (((g.w a : ℝ) - (a : ℝ) * g.w 1) * θ))
        have h3 : ∑ a ∈ range b, dist01 ((β a : ℝ) * (((g.w a : ℝ) - (a : ℝ) * g.w 1) * θ))
            ≤ ∑ a ∈ range b, |(β a : ℝ)| * dist01 (((g.w a : ℝ) - (a : ℝ) * g.w 1) * θ) :=
          Finset.sum_le_sum fun a _ => dist01_int_mul_le (β a) _
        linarith
    _ ≤ |(γ : ℝ)| * ((b + 1) * M)
        + ∑ a ∈ range b, |(β a : ℝ)| * ((b + 1) * M) := by
        have h1 : |(γ : ℝ)| * dist01 ((((b : ℝ) - 1) * g.w 1) * θ)
            ≤ |(γ : ℝ)| * ((b + 1) * M) :=
          mul_le_mul_of_nonneg_left hX (abs_nonneg _)
        have h2 : ∑ a ∈ range b, |(β a : ℝ)| * dist01 (((g.w a : ℝ) - (a : ℝ) * g.w 1) * θ)
            ≤ ∑ a ∈ range b, |(β a : ℝ)| * ((b + 1) * M) :=
          Finset.sum_le_sum fun a ha =>
            mul_le_mul_of_nonneg_left (hY a ha) (abs_nonneg _)
        linarith
    _ = (|(γ : ℝ)| + ∑ a ∈ range b, |(β a : ℝ)|) * (b + 1) * M := by
        rw [← Finset.sum_mul]
        ring
    _ ≤ ((|(γ : ℝ)| + ∑ a ∈ range b, |(β a : ℝ)|) * (b + 1) + 1) * M := by
        nlinarith [hM0]
    _ = ((|(γ : ℝ)| + ∑ a ∈ range b, |(β a : ℝ)|) * (b + 1) + 1)
          * ((∑ a ∈ Ico 1 b, dist01 (θ * g.w a + a * t))
            + dist01 (θ * g.w 1 + b * t)) := by rw [hMdef]

private lemma norm_unit_exp (r : ℝ) :
    ‖Complex.exp (2 * Real.pi * Complex.I * ((r : ℝ) : ℂ))‖ = 1 := by
  have h : 2 * Real.pi * Complex.I * ((r : ℝ) : ℂ)
      = ((2 * Real.pi * r : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [h]
  exact Complex.norm_exp_ofReal_mul_I _

/-- **The one-pair bound:** for every digit `1 ≤ a < b`,

`‖A_θ(t)‖ ≤ 1 − (4/b)·‖θg(a) + at‖²`,

by keeping the pair `(0, a)` and bounding the remaining `b − 2` unit terms
trivially. -/
lemma norm_digitalFactor_le_pair {b : ℕ} (g : Weight b) {a : ℕ} (ha : a ∈ Ico 1 b)
    (θ t : ℝ) :
    ‖digitalFactor g θ t‖ ≤ 1 - 4 / (b : ℝ) * dist01 (θ * g.w a + a * t) ^ 2 := by
  obtain ⟨ha1, hab⟩ := mem_Ico.mp ha
  have hb2 : 2 ≤ b := g.hb
  have hb0 : (0 : ℝ) < b := by
    have : 0 < b := lt_of_lt_of_le (by norm_num) hb2
    exact_mod_cast this
  obtain ⟨q, hqdef⟩ : ∃ q : ℝ, q = dist01 (θ * g.w a + a * t) := ⟨_, rfl⟩
  have hq0 : 0 ≤ q := by rw [hqdef]; exact dist01_nonneg _
  have hqh : q ≤ 1 / 2 := by rw [hqdef]; exact dist01_le_half _
  -- split off the pair (0, a)
  have h0mem : (0 : ℕ) ∈ range b := mem_range.mpr (lt_of_lt_of_le (by norm_num) hb2)
  have hamem : a ∈ (range b).erase 0 := by
    rw [Finset.mem_erase]
    exact ⟨by omega, mem_range.mpr hab⟩
  obtain ⟨E, hEdef⟩ : ∃ E : ℕ → ℂ, E = fun c : ℕ =>
      Complex.exp (2 * Real.pi * Complex.I * ((θ * g.w c + c * t : ℝ) : ℂ)) := ⟨_, rfl⟩
  have hsplit : ∑ c ∈ range b, E c
      = (E 0 + E a) + ∑ c ∈ ((range b).erase 0).erase a, E c := by
    conv_lhs => rw [← Finset.insert_erase h0mem]
    rw [Finset.sum_insert (Finset.notMem_erase 0 (range b))]
    conv_lhs => rw [← Finset.insert_erase hamem]
    rw [Finset.sum_insert (Finset.notMem_erase a ((range b).erase 0))]
    ring
  have hE0 : E 0 = 1 := by
    rw [hEdef]
    have h0 : ((θ * g.w 0 + (0 : ℕ) * t : ℝ) : ℂ) = 0 := by
      rw [g.w_zero]
      push_cast
      ring
    simp only [h0, mul_zero, Complex.exp_zero]
  -- the pair term
  have hpair : ‖E 0 + E a‖ ≤ 2 - 4 * q ^ 2 := by
    rw [hE0, hEdef]
    have hns := normSq_one_add_exp (θ * g.w a + a * t)
    have h17 := one_sub_cos_ge (θ * g.w a + a * t)
    have hnormSq : Complex.normSq (1 + Complex.exp
        (2 * Real.pi * Complex.I * ((θ * g.w a + a * t : ℝ) : ℂ)))
        = ‖(1 + Complex.exp
            (2 * Real.pi * Complex.I * ((θ * g.w a + a * t : ℝ) : ℂ)))‖ ^ 2 :=
      Complex.normSq_eq_norm_sq _
    have hq2 : dist01 (θ * g.w a + a * t) ^ 2 = q ^ 2 := by rw [hqdef]
    have hb1 : ‖(1 + Complex.exp
        (2 * Real.pi * Complex.I * ((θ * g.w a + a * t : ℝ) : ℂ)))‖ ^ 2
        ≤ (2 - 4 * q ^ 2) ^ 2 := by
      rw [← hnormSq, hns]
      nlinarith [sq_nonneg (q ^ 2), h17, hq2]
    have hpos : (0 : ℝ) ≤ 2 - 4 * q ^ 2 := by nlinarith
    nlinarith [norm_nonneg (1 + Complex.exp
      (2 * Real.pi * Complex.I * ((θ * g.w a + a * t : ℝ) : ℂ)))]
  -- the remaining terms
  have hrest : ‖∑ c ∈ ((range b).erase 0).erase a, E c‖ ≤ (b : ℝ) - 2 := by
    have hcard : (((range b).erase 0).erase a).card = b - 2 := by
      rw [Finset.card_erase_of_mem hamem, Finset.card_erase_of_mem h0mem,
        Finset.card_range]
      omega
    calc ‖∑ c ∈ ((range b).erase 0).erase a, E c‖
        ≤ ∑ c ∈ ((range b).erase 0).erase a, ‖E c‖ := norm_sum_le _ _
      _ = ∑ c ∈ ((range b).erase 0).erase a, 1 := by
          refine Finset.sum_congr rfl fun c _ => ?_
          rw [hEdef]
          exact norm_unit_exp _
      _ = ((b : ℝ) - 2) := by
          rw [Finset.sum_const, hcard]
          have : ((b - 2 : ℕ) : ℝ) = (b : ℝ) - 2 := by
            push_cast [hb2]
            ring
          simp [this]
  -- assemble
  have hsum : ‖∑ c ∈ range b, E c‖ ≤ (b : ℝ) - 4 * q ^ 2 := by
    calc ‖∑ c ∈ range b, E c‖
        = ‖(E 0 + E a) + ∑ c ∈ ((range b).erase 0).erase a, E c‖ := by rw [hsplit]
      _ ≤ ‖E 0 + E a‖ + ‖∑ c ∈ ((range b).erase 0).erase a, E c‖ := norm_add_le _ _
      _ ≤ (2 - 4 * q ^ 2) + ((b : ℝ) - 2) := add_le_add hpair hrest
      _ = (b : ℝ) - 4 * q ^ 2 := by ring
  have hA : digitalFactor g θ t = (b : ℂ)⁻¹ * ∑ c ∈ range b, E c := by
    unfold digitalFactor
    rw [hEdef]
  have hnb : ‖(b : ℂ)⁻¹‖ = 1 / (b : ℝ) := by
    rw [norm_inv]
    have hbc : ((b : ℕ) : ℂ) = (((b : ℕ) : ℝ) : ℂ) := by push_cast; ring
    rw [hbc, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hb0, one_div]
  rw [hA, norm_mul, hnb, ← hqdef]
  have h1 : 1 / (b : ℝ) * ‖∑ c ∈ range b, E c‖
      ≤ 1 / (b : ℝ) * ((b : ℝ) - 4 * q ^ 2) := by
    apply mul_le_mul_of_nonneg_left hsum
    positivity
  have h2 : 1 / (b : ℝ) * ((b : ℝ) - 4 * q ^ 2) = 1 - 4 / (b : ℝ) * q ^ 2 := by
    field_simp
  linarith

/-- **Lemma 2.4 of the paper, in every base (the two-digit spectral gap):**
for `b ≥ 2` and `g` primitive there is `c_g > 0` with

`‖A_θ(t) · A_θ(bt)‖ ≤ exp(−c_g·‖d_gθ‖²)`, uniformly in `θ, t`. -/
theorem two_digit_gap {b : ℕ} (g : Weight b) (hg : g.Coprime₁) :
    ∃ c : ℝ, 0 < c ∧ ∀ θ t : ℝ,
      ‖digitalFactor g θ t * digitalFactor g θ ((b : ℝ) * t)‖
        ≤ Real.exp (-c * dist01 ((g.dg : ℝ) * θ) ^ 2) := by
  obtain ⟨K, hK1, hK⟩ := dist01_dg_le g hg
  have hb2 : 2 ≤ b := g.hb
  have hb0 : (0 : ℝ) < b := by
    have : 0 < b := lt_of_lt_of_le (by norm_num) hb2
    exact_mod_cast this
  have hK0 : (0 : ℝ) < K := lt_of_lt_of_le one_pos hK1
  refine ⟨2 / (K ^ 2 * (b : ℝ) ^ 3), by positivity, fun θ t => ?_⟩
  -- the maximal digit distance
  have hne : (Ico 1 b).Nonempty := by
    rw [Finset.nonempty_Ico]
    omega
  obtain ⟨sImg, hsImgdef⟩ : ∃ s : Finset ℝ,
      s = (Ico 1 b).image fun a => dist01 (θ * g.w a + a * t) := ⟨_, rfl⟩
  have hsne : sImg.Nonempty := by
    rw [hsImgdef]
    exact hne.image _
  obtain ⟨q₀, hq₀def⟩ : ∃ q : ℝ, q = sImg.max' hsne := ⟨_, rfl⟩
  obtain ⟨a₀, ha₀I, ha₀⟩ : ∃ a₀ ∈ Ico 1 b, dist01 (θ * g.w a₀ + a₀ * t) = q₀ := by
    have hmem : q₀ ∈ sImg := by rw [hq₀def]; exact sImg.max'_mem hsne
    rw [hsImgdef] at hmem
    obtain ⟨a₀, ha₀I, ha₀⟩ := Finset.mem_image.mp hmem
    exact ⟨a₀, ha₀I, ha₀⟩
  have hq₀max : ∀ a ∈ Ico 1 b, dist01 (θ * g.w a + a * t) ≤ q₀ := by
    intro a ha
    rw [hq₀def]
    exact sImg.le_max' _ (by rw [hsImgdef]; exact Finset.mem_image_of_mem _ ha)
  have hq₀0 : 0 ≤ q₀ := by rw [← ha₀]; exact dist01_nonneg _
  obtain ⟨y, hydef⟩ : ∃ y : ℝ, y = dist01 (θ * g.w 1 + b * t) := ⟨_, rfl⟩
  have hy0 : 0 ≤ y := by rw [hydef]; exact dist01_nonneg _
  -- the two factor bounds
  have hA1 : ‖digitalFactor g θ t‖ ≤ Real.exp (-(4 / (b : ℝ) * q₀ ^ 2)) := by
    have h1 := norm_digitalFactor_le_pair g ha₀I θ t
    rw [ha₀] at h1
    have h2 := Real.add_one_le_exp (-(4 / (b : ℝ) * q₀ ^ 2))
    linarith
  have hA2 : ‖digitalFactor g θ ((b : ℝ) * t)‖ ≤ Real.exp (-(4 / (b : ℝ) * y ^ 2)) := by
    have h1b : (1 : ℕ) ∈ Ico 1 b := by
      rw [mem_Ico]
      omega
    have h1 := norm_digitalFactor_le_pair g h1b θ ((b : ℝ) * t)
    have h2 : θ * g.w 1 + ((1 : ℕ) : ℝ) * ((b : ℝ) * t) = θ * g.w 1 + b * t := by
      push_cast
      ring
    rw [h2, ← hydef] at h1
    have h3 := Real.add_one_le_exp (-(4 / (b : ℝ) * y ^ 2))
    linarith
  -- multiply
  have hprod : ‖digitalFactor g θ t * digitalFactor g θ ((b : ℝ) * t)‖
      ≤ Real.exp (-(4 / (b : ℝ) * (q₀ ^ 2 + y ^ 2))) := by
    rw [norm_mul]
    calc ‖digitalFactor g θ t‖ * ‖digitalFactor g θ ((b : ℝ) * t)‖
        ≤ Real.exp (-(4 / (b : ℝ) * q₀ ^ 2)) * Real.exp (-(4 / (b : ℝ) * y ^ 2)) :=
          mul_le_mul hA1 hA2 (norm_nonneg _) (le_of_lt (Real.exp_pos _))
      _ = Real.exp (-(4 / (b : ℝ) * (q₀ ^ 2 + y ^ 2))) := by
          rw [← Real.exp_add]
          congr 1
          ring
  refine le_trans hprod (Real.exp_le_exp.mpr ?_)
  -- `‖d_gθ‖² ≤ 2K²b²(q₀² + y²)`
  have hdist : dist01 ((g.dg : ℝ) * θ) ≤ K * ((b : ℝ) * (q₀ + y)) := by
    have h1 := hK θ t
    have h2 : (∑ a ∈ Ico 1 b, dist01 (θ * g.w a + a * t))
        + dist01 (θ * g.w 1 + b * t) ≤ (b : ℝ) * (q₀ + y) := by
      have h3 : ∑ a ∈ Ico 1 b, dist01 (θ * g.w a + a * t)
          ≤ ∑ _a ∈ Ico 1 b, q₀ := Finset.sum_le_sum hq₀max
      have h4 : ∑ _a ∈ Ico 1 b, q₀ = ((b - 1 : ℕ) : ℝ) * q₀ := by
        rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
      have h5 : ((b - 1 : ℕ) : ℝ) ≤ (b : ℝ) := by
        have : b - 1 ≤ b := Nat.sub_le _ _
        exact_mod_cast this
      have h6 : ((b - 1 : ℕ) : ℝ) * q₀ ≤ (b : ℝ) * q₀ :=
        mul_le_mul_of_nonneg_right h5 hq₀0
      have hb1' : (1 : ℝ) ≤ (b : ℝ) := by
        have : 1 ≤ b := by omega
        exact_mod_cast this
      have h7 : y ≤ (b : ℝ) * y := by nlinarith
      rw [← hydef] at h1 ⊢
      nlinarith
    calc dist01 ((g.dg : ℝ) * θ)
        ≤ K * ((∑ a ∈ Ico 1 b, dist01 (θ * g.w a + a * t))
            + dist01 (θ * g.w 1 + b * t)) := h1
      _ ≤ K * ((b : ℝ) * (q₀ + y)) := mul_le_mul_of_nonneg_left h2 (le_of_lt hK0)
  have hsq : dist01 ((g.dg : ℝ) * θ) ^ 2 ≤ 2 * K ^ 2 * (b : ℝ) ^ 2 * (q₀ ^ 2 + y ^ 2) := by
    have h1 : dist01 ((g.dg : ℝ) * θ) ^ 2 ≤ (K * ((b : ℝ) * (q₀ + y))) ^ 2 := by
      apply sq_le_sq' _ hdist
      have := dist01_nonneg ((g.dg : ℝ) * θ)
      have hKb : 0 ≤ K * ((b : ℝ) * (q₀ + y)) := by positivity
      linarith
    have h2 : (K * ((b : ℝ) * (q₀ + y))) ^ 2
        ≤ 2 * K ^ 2 * (b : ℝ) ^ 2 * (q₀ ^ 2 + y ^ 2) := by
      nlinarith [mul_nonneg (mul_nonneg (sq_nonneg K) (sq_nonneg ((b : ℝ))))
        (sq_nonneg (q₀ - y))]
    linarith
  -- compare the exponents
  have hc : 2 / (K ^ 2 * (b : ℝ) ^ 3) * dist01 ((g.dg : ℝ) * θ) ^ 2
      ≤ 4 / (b : ℝ) * (q₀ ^ 2 + y ^ 2) := by
    have h1 : 2 / (K ^ 2 * (b : ℝ) ^ 3) * dist01 ((g.dg : ℝ) * θ) ^ 2
        ≤ 2 / (K ^ 2 * (b : ℝ) ^ 3) * (2 * K ^ 2 * (b : ℝ) ^ 2 * (q₀ ^ 2 + y ^ 2)) := by
      apply mul_le_mul_of_nonneg_left hsq
      positivity
    have h2 : 2 / (K ^ 2 * (b : ℝ) ^ 3) * (2 * K ^ 2 * (b : ℝ) ^ 2 * (q₀ ^ 2 + y ^ 2))
        = 4 / (b : ℝ) * (q₀ ^ 2 + y ^ 2) := by
      have hKne : K ≠ 0 := ne_of_gt hK0
      have hbne : (b : ℝ) ≠ 0 := ne_of_gt hb0
      field_simp
      ring
    linarith
  linarith

end DSS
