/-
DSS/Examples.lean

The running examples inherited from the predecessor paper: the power sums
`a ↦ a^r` (its Corollary 1.4), the digit-occurrence counters (its
Corollary 1.5), and in particular

  `S n` = the sum of the squares of the decimal digits of `n`,

for which `μ_S = 57/2` and `d_S = 1`.

Nothing in this file is conditional: it imports no axioms.
-/
import DSS.Weight

namespace DSS

open Finset

/-! ### Power weights `a ↦ a^r` -/

/-- The digit weight `a ↦ a^r` in base `b` (`r ≥ 1`). -/
def powWeight (b r : ℕ) (hb : 2 ≤ b) (hr : 1 ≤ r) : Weight b where
  w := fun a => (a : ℤ) ^ r
  hb := hb
  w_zero := by
    have : r ≠ 0 := by omega
    simp [zero_pow this]

@[simp] lemma powWeight_w (b r : ℕ) (hb : 2 ≤ b) (hr : 1 ≤ r) (a : ℕ) :
    (powWeight b r hb hr).w a = (a : ℤ) ^ r := rfl

/-- Power weights satisfy the coprimality hypothesis (1), because `g(1) = 1`. -/
theorem powWeight_coprime₁ (b r : ℕ) (hb : 2 ≤ b) (hr : 1 ≤ r) :
    (powWeight b r hb hr).Coprime₁ := by
  rw [Weight.coprime₁_def]
  have h1 : (1 : ℕ) ∈ Ico 1 b := by simp; omega
  have := Finset.gcd_dvd (s := Ico 1 b)
      (f := fun a => ((powWeight b r hb hr).w a).natAbs) h1
  simp only [powWeight_w, Nat.cast_one, one_pow, Int.natAbs_one] at this
  exact Nat.eq_one_of_dvd_one this

/-- Power weights have positive mean. -/
theorem powWeight_mu_pos (b r : ℕ) (hb : 2 ≤ b) (hr : 1 ≤ r) :
    0 < (powWeight b r hb hr).mu := by
  rw [Weight.mu_def]
  have hb0 : (0 : ℝ) < b := by
    have : 0 < b := by omega
    exact_mod_cast this
  refine div_pos ?_ hb0
  have hterm : ∀ a ∈ range b, (0 : ℝ) ≤ ((a : ℤ) ^ r : ℤ) := by
    intro a _; positivity
  have h1 : (1 : ℕ) ∈ range b := mem_range.mpr (by omega)
  have hpos : (0 : ℝ) < (((1 : ℕ) : ℤ) ^ r : ℤ) := by norm_num
  calc (0 : ℝ) < (((1 : ℕ) : ℤ) ^ r : ℤ) := hpos
    _ ≤ ∑ a ∈ range b, (((powWeight b r hb hr).w a : ℤ) : ℝ) := by
        refine Finset.single_le_sum (f := fun a => (((powWeight b r hb hr).w a : ℤ) : ℝ))
          (fun a _ => ?_) h1
        simp only [powWeight_w]
        positivity

/-! ### The sum of the `r`-th powers of the digits -/

/-- The sum of the `r`-th powers of the base-`b` digits of `n` (the
predecessor's Corollary 1.4). -/
def powDigitSum (b r n : ℕ) : ℕ := ((Nat.digits b n).map (fun d => d ^ r)).sum

lemma powDigitSum_def (b r n : ℕ) :
    powDigitSum b r n = ((Nat.digits b n).map (fun d => d ^ r)).sum := rfl

theorem eval_powWeight (b r : ℕ) (hb : 2 ≤ b) (hr1 : 1 ≤ r) (n : ℕ) :
    (powWeight b r hb hr1).eval n = (powDigitSum b r n : ℤ) := by
  rw [Weight.eval_def, powDigitSum_def]
  induction Nat.digits b n with
  | nil => simp
  | cons d tl ih =>
      simp only [List.map_cons, List.sum_cons, powWeight_w] at *
      rw [ih]; push_cast; ring

/-! ### `S`: the sum of the squares of the decimal digits -/

/-- `S n` — the sum of the squares of the decimal digits of `n` (OEIS A003132). -/
def S (n : ℕ) : ℕ := ((Nat.digits 10 n).map (fun d => d ^ 2)).sum

lemma S_def (n : ℕ) : S n = ((Nat.digits 10 n).map (fun d => d ^ 2)).sum := rfl

/-- The digit weight underlying `S`. -/
def wS : Weight 10 := powWeight 10 2 (by norm_num) (by norm_num)

@[simp] lemma wS_w (a : ℕ) : wS.w a = (a : ℤ) ^ 2 := rfl

theorem eval_wS (n : ℕ) : wS.eval n = (S n : ℤ) := by
  rw [Weight.eval_def, S_def]
  induction Nat.digits 10 n with
  | nil => simp
  | cons d tl ih =>
      simp only [List.map_cons, List.sum_cons, wS_w] at *
      rw [ih]; push_cast; ring

theorem S_eq_powDigitSum (n : ℕ) : S n = powDigitSum 10 2 n := rfl

theorem wS_coprime₁ : wS.Coprime₁ := powWeight_coprime₁ 10 2 _ _

/-- `μ_S = 57/2`. -/
theorem mu_wS : wS.mu = 57 / 2 := by
  rw [Weight.mu_def]
  norm_num [wS_w, Finset.sum_range_succ]

theorem mu_wS_pos : 0 < wS.mu := by rw [mu_wS]; norm_num

/-- `d_S = 1`: the congruence in the local limit theorem is vacuous for `S`.

`d_S` divides both `9` and `g(2) - 2g(1) = 2`, hence divides `gcd(9,2) = 1`. -/
theorem dg_wS : wS.dg = 1 := by
  have h2 : (2 : ℕ) ∈ range 10 := by decide
  have hdvd : ((range 10).gcd fun a => (wS.w a - (a : ℤ) * wS.w 1).natAbs) ∣ 2 := by
    have h := Finset.gcd_dvd (s := range 10)
        (f := fun a => (wS.w a - (a : ℤ) * wS.w 1).natAbs) h2
    norm_num [wS_w] at h
    exact h
  have h9 : wS.dg ∣ 9 := by
    have h := wS.dg_dvd_sub_one
    norm_num at h
    exact h
  have hg2 : wS.dg ∣ 2 := by
    rw [Weight.dg_def]; exact dvd_trans (Nat.gcd_dvd_right _ _) hdvd
  have hfin : wS.dg ∣ Nat.gcd 9 2 := Nat.dvd_gcd h9 hg2
  norm_num at hfin
  exact hfin

/-! ### `d_g = 1` for every even power in base ten (the predecessor's §6.1)

For `g(a) = a^r` in base ten, the predecessor's §6.1 gives `d_g = 3` for odd
`r ≥ 3` and `d_g = 1`
for `r` even.  We prove the second (and only) case we need: `d_g` divides `9`
and divides `2^r - 2`, and `3 ∤ 2^r - 2` because `2^r ≡ 1 (mod 3)` for even `r`. -/

theorem two_pow_mod_three_of_even {r : ℕ} (hre : Even r) : 2 ^ r % 3 = 1 := by
  obtain ⟨s, hs⟩ := hre
  have hrs : r = 2 * s := by omega
  subst hrs
  rw [pow_mul]
  norm_num [Nat.pow_mod]

/-- **The predecessor's §6.1 for even powers in base ten:** `d_g = 1` for
`g(a) = a^r`, `r` even. -/
theorem dg_powWeight_ten_even (r : ℕ) (hre : Even r)
    (hb : (2 : ℕ) ≤ 10) (hr1 : 1 ≤ r) :
    (powWeight 10 r hb hr1).dg = 1 := by
  set g := powWeight 10 r hb hr1 with hgdef
  have hge : (2 : ℕ) ≤ 2 ^ r := by
    calc (2 : ℕ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ r := Nat.pow_le_pow_right (by norm_num) (by omega)
  -- `d_g ∣ 9`
  have h9 : g.dg ∣ 9 := by
    have h := g.dg_dvd_sub_one
    norm_num at h
    exact h
  -- `d_g ∣ 2^r - 2`
  have hcast : ((2 ^ r - 2 : ℕ) : ℤ) = g.w 2 - (2 : ℤ) * g.w 1 := by
    rw [Nat.cast_sub hge, hgdef]
    simp only [powWeight_w]
    push_cast
    ring
  have hN : g.dg ∣ 2 ^ r - 2 := by
    refine Int.natCast_dvd_natCast.mp ?_
    rw [hcast]
    exact g.dg_dvd_sub 2 (by omega)
  -- `3 ∤ 2^r - 2`
  have hnd : ¬ (3 : ℕ) ∣ 2 ^ r - 2 := by
    have hm := two_pow_mod_three_of_even hre
    omega
  -- hence `gcd(9, 2^r - 2) = 1`
  have hcop3 : Nat.Coprime 3 (2 ^ r - 2) :=
    (Nat.Prime.coprime_iff_not_dvd (by decide)).mpr hnd
  have hcop9 : Nat.Coprime 9 (2 ^ r - 2) := by
    have : (9 : ℕ) = 3 ^ 2 := by norm_num
    rw [this]
    exact Nat.Coprime.pow_left 2 hcop3
  exact Nat.eq_one_of_dvd_one (hcop9 ▸ Nat.dvd_gcd h9 hN)

/-! ### Digit-occurrence weights (the predecessor's Corollary 1.5) -/

/-- The weight counting occurrences of the digit `c`. -/
def digitCount (b c : ℕ) (hb : 2 ≤ b) (hc : 1 ≤ c) : Weight b where
  w := fun a => if a = c then 1 else 0
  hb := hb
  w_zero := by simp; omega

@[simp] lemma digitCount_w (b c : ℕ) (hb : 2 ≤ b) (hc : 1 ≤ c) (a : ℕ) :
    (digitCount b c hb hc).w a = if a = c then 1 else 0 := rfl

/-- The number of times the digit `c` occurs in the base-`b` expansion of `n`. -/
def digitOccurrences (b c n : ℕ) : ℕ := (Nat.digits b n).count c

theorem eval_digitCount (b c : ℕ) (hb : 2 ≤ b) (hc : 1 ≤ c) (n : ℕ) :
    (digitCount b c hb hc).eval n = (digitOccurrences b c n : ℤ) := by
  rw [Weight.eval_def, digitOccurrences]
  induction Nat.digits b n with
  | nil => simp
  | cons d tl ih =>
      simp only [List.map_cons, List.sum_cons, digitCount_w, List.count_cons] at *
      rw [ih]
      by_cases hd : d = c
      · subst hd; simp; ring
      · simp [hd, beq_iff_eq]

/-- `digitCount` satisfies hypothesis (1): the value at `c` itself is `1`. -/
theorem digitCount_coprime₁ (b c : ℕ) (hb : 2 ≤ b) (hc : 1 ≤ c) (hcb : c < b) :
    (digitCount b c hb hc).Coprime₁ := by
  rw [Weight.coprime₁_def]
  have hmem : c ∈ Finset.Ico 1 b := by simp; omega
  have h := Finset.gcd_dvd (s := Finset.Ico 1 b)
      (f := fun a => ((digitCount b c hb hc).w a).natAbs) hmem
  simp only [digitCount_w] at h
  simpa using h

/-- `d_g = 1` for `digitCount` when `2 ≤ c`: then `g(1) = 0`, so the `gcd` of
eq. (2) contains `g(c) = 1`. -/
theorem dg_digitCount (b c : ℕ) (hb : 2 ≤ b) (hc : 1 ≤ c) (hc2 : 2 ≤ c) (hcb : c < b) :
    (digitCount b c hb hc).dg = 1 := by
  have hw1 : (digitCount b c hb hc).w 1 = 0 := by
    rw [digitCount_w, if_neg (by omega : ¬ (1 = c))]
  have hval : ((digitCount b c hb hc).w c
      - (c : ℤ) * (digitCount b c hb hc).w 1).natAbs = 1 := by
    rw [hw1, digitCount_w, if_pos rfl]
    norm_num
  have hmem : c ∈ Finset.range b := Finset.mem_range.mpr hcb
  have h := Finset.gcd_dvd (s := Finset.range b)
      (f := fun a => ((digitCount b c hb hc).w a
        - (a : ℤ) * (digitCount b c hb hc).w 1).natAbs) hmem
  rw [hval] at h
  have hd : (digitCount b c hb hc).dg ∣ 1 := by
    rw [Weight.dg_def]; exact dvd_trans (Nat.gcd_dvd_right _ _) h
  exact Nat.eq_one_of_dvd_one hd

/-- `digitCount` has mean `1/b > 0`. -/
theorem digitCount_mu_pos (b c : ℕ) (hb : 2 ≤ b) (hc : 1 ≤ c) (hcb : c < b) :
    0 < (digitCount b c hb hc).mu := by
  rw [Weight.mu_def]
  have hb0 : (0 : ℝ) < b := by
    have : 0 < b := by omega
    exact_mod_cast this
  refine div_pos ?_ hb0
  have : ∑ a ∈ Finset.range b, (((digitCount b c hb hc).w a : ℤ) : ℝ)
      = ∑ a ∈ Finset.range b, (if a = c then (1 : ℝ) else 0) := by
    refine Finset.sum_congr rfl fun a _ => ?_
    by_cases h : a = c <;> simp [h]
  rw [this, Finset.sum_ite_eq' (Finset.range b) c (fun _ => (1 : ℝ))]
  simp [Finset.mem_range.mpr hcb]

end DSS
