/-
DSS/Digits.lean

The base-`b` digit sum `s_b : ℕ → ℕ` and the three facts about it that the
squares half of the paper runs on:

* block additivity: `s_b(x + b^k·m) = s_b(x) + s_b(m)` for `x < b^k`
  (digit sums add along a base-`b^k` expansion, eq. (23) of the paper);
* the complement rule, eq. (24): `s_b(b^k − c) + s_b(c−1) = k(b−1)`
  for `1 ≤ c ≤ b^k`;
* the carry-free representation lemma: if `n = ∑_j c_j b^j` with every
  `c_j < b`, then `s_b(n) = ∑_j c_j`.

Nothing in this file is conditional: it imports no axioms.
-/
import DSS.Imports

namespace DSS

open Finset

/-- `s_b(n)`, the sum of the base-`b` digits of `n`. -/
def sb (b n : ℕ) : ℕ := (Nat.digits b n).sum

lemma sb_def (b n : ℕ) : sb b n = (Nat.digits b n).sum := rfl

@[simp] lemma sb_zero (b : ℕ) : sb b 0 = 0 := by simp [sb]

/-- Digit sum of a single digit. -/
lemma sb_of_lt {b n : ℕ} (hb : 2 ≤ b) (hn : n < b) : sb b n = n := by
  rcases Nat.eq_zero_or_pos n with h | h
  · simp [h]
  · rw [sb, Nat.digits_def' (by omega : 1 < b) h, Nat.mod_eq_of_lt hn,
      Nat.div_eq_of_lt hn]
    simp

lemma sb_one {b : ℕ} (hb : 2 ≤ b) : sb b 1 = 1 :=
  sb_of_lt hb (by omega)

/-- Appending a digit `d` at the bottom adds `d` to the digit sum. -/
theorem sb_add_mul {b : ℕ} (hb : 2 ≤ b) {d : ℕ} (m : ℕ) (hd : d < b) :
    sb b (d + b * m) = d + sb b m := by
  rcases Nat.eq_zero_or_pos (d + b * m) with h | h
  · have hd0 : d = 0 := by omega
    have hbm : b * m = 0 := by omega
    have hm0 : m = 0 := by
      rcases Nat.mul_eq_zero.mp hbm with h' | h'
      · omega
      · exact h'
    subst hd0; subst hm0; simp
  · have hmod : (d + b * m) % b = d := by
      rw [Nat.add_mul_mod_self_left]; exact Nat.mod_eq_of_lt hd
    have hdiv : (d + b * m) / b = m := by
      rw [Nat.add_mul_div_left _ _ (by omega : 0 < b), Nat.div_eq_of_lt hd]; simp
    rw [sb, Nat.digits_def' (by omega : 1 < b) h, hmod, hdiv, sb]
    simp

/-- **Digit sums add along a base-`b^k` expansion**: for `x < b^k`,
`s_b(x + b^k·m) = s_b(x) + s_b(m)`.  This is the identity behind eq. (23)
of the paper (there in the form of three blocks). -/
theorem sb_add_pow_mul {b : ℕ} (hb : 2 ≤ b) :
    ∀ k x m : ℕ, x < b ^ k → sb b (x + b ^ k * m) = sb b x + sb b m := by
  intro k
  induction k with
  | zero =>
      intro x m hx
      have hx0 : x = 0 := by simpa using hx
      subst hx0; simp
  | succ k ih =>
      intro x m hx
      have hbpos : 0 < b := by omega
      have hd : x % b < b := Nat.mod_lt _ hbpos
      have hxq : x / b < b ^ k := by
        have h1 : x / b < b ^ (k + 1) / b :=
          Nat.div_lt_div_of_lt_of_dvd ⟨b ^ k, by ring⟩ hx
        have h2 : b ^ (k + 1) / b = b ^ k := by
          rw [pow_succ, Nat.mul_div_cancel _ hbpos]
        omega
      have hsplit : x + b ^ (k + 1) * m = x % b + b * (x / b + b ^ k * m) := by
        have h1 : x % b + b * (x / b) = x := Nat.mod_add_div x b
        have h2 : b * (x / b + b ^ k * m) = b * (x / b) + b ^ (k + 1) * m := by
          rw [pow_succ]; ring
        omega
      rw [hsplit, sb_add_mul hb _ hd, ih (x / b) m hxq]
      have hx' : sb b x = x % b + sb b (x / b) := by
        conv_lhs => rw [← Nat.mod_add_div x b]
        exact sb_add_mul hb _ hd
      omega

/-- Multiplying by `b^k` (appending `k` zero digits) does not change the digit
sum; in particular `s_{10}((10n)²) = s_{10}(n²)`, the identity of §8.2. -/
theorem sb_pow_mul {b : ℕ} (hb : 2 ≤ b) (k m : ℕ) :
    sb b (b ^ k * m) = sb b m := by
  have h := sb_add_pow_mul hb k 0 m (by positivity)
  simpa using h

/-- **The complement rule**, eq. (24): the base-`b` digits of `b^k − c`, for
`1 ≤ c ≤ b^k`, are the complements with respect to `b − 1` of the digits of
`c − 1`, padded to length `k`; there are no borrows.  Stated additively, so
that every quantity is a natural number:
`s_b(b^k − c) + s_b(c − 1) = k(b − 1)`. -/
theorem sb_pow_sub {b : ℕ} (hb : 2 ≤ b) :
    ∀ k c : ℕ, 1 ≤ c → c ≤ b ^ k →
      sb b (b ^ k - c) + sb b (c - 1) = k * (b - 1) := by
  intro k
  induction k with
  | zero =>
      intro c h1 h2
      have : c = 1 := by simpa using le_antisymm (by simpa using h2) h1
      subst this; simp
  | succ k ih =>
      intro c h1 h2
      have hbpos : 0 < b := by omega
      obtain ⟨d, hd⟩ : ∃ d, (c - 1) % b = d := ⟨_, rfl⟩
      obtain ⟨m, hm⟩ : ∃ m, (c - 1) / b = m := ⟨_, rfl⟩
      have hdb : d < b := hd ▸ Nat.mod_lt _ hbpos
      have hcm : d + b * m = c - 1 := by rw [← hd, ← hm]; exact Nat.mod_add_div _ _
      have hbk1 : 1 ≤ b ^ k := Nat.one_le_pow _ _ hbpos
      have hmlt : m < b ^ k := by
        rcases Nat.lt_or_ge m (b ^ k) with h' | h'
        · exact h'
        · exfalso
          have h3 : b * b ^ k ≤ b * m := Nat.mul_le_mul_left b h'
          have h4 : b ^ (k + 1) = b * b ^ k := by ring
          omega
      -- the digitwise complement: `b^{k+1} − c = (b−1−d) + b·(b^k − (m+1))`
      have hkey : b ^ (k + 1) - c = (b - 1 - d) + b * (b ^ k - (m + 1)) := by
        obtain ⟨t, ht⟩ : ∃ t, b ^ k = (m + 1) + t := ⟨b ^ k - (m + 1), by omega⟩
        have h5 : b ^ k - (m + 1) = t := by omega
        have h6 : b * ((m + 1) + t) = b * m + b + b * t := by ring
        have h7 : b * ((m + 1) + t) = b ^ (k + 1) := by rw [← ht]; ring
        rw [h5]
        omega
      rw [hkey, sb_add_mul hb _ (by omega : b - 1 - d < b)]
      have hih : sb b (b ^ k - (m + 1)) + sb b m = k * (b - 1) := by
        have h := ih (m + 1) (by omega) (by omega)
        simpa using h
      have hcd : sb b (c - 1) = d + sb b m := by
        conv_lhs => rw [← hcm]
        exact sb_add_mul hb _ hdb
      have hd1 : d ≤ b - 1 := by omega
      have hexpand : (k + 1) * (b - 1) = k * (b - 1) + (b - 1) := by ring
      omega

/-- **The carry-free representation lemma.**  If every coefficient `c j` is a
valid digit (`c j < b`), then the digit sum of `∑_{j<N} c_j b^j` is
`∑_{j<N} c_j`: the coefficients *are* the digits, and no carries occur. -/
theorem sb_sum_pow {b : ℕ} (hb : 2 ≤ b) :
    ∀ (N : ℕ) (c : ℕ → ℕ), (∀ j, c j < b) →
      sb b (∑ j ∈ range N, c j * b ^ j) = ∑ j ∈ range N, c j := by
  intro N
  induction N with
  | zero => intro c _; simp
  | succ N ih =>
      intro c hc
      have hshift : ∑ j ∈ range (N + 1), c j * b ^ j
          = c 0 + b * ∑ j ∈ range N, c (j + 1) * b ^ j := by
        rw [Finset.sum_range_succ' (fun j => c j * b ^ j) N, add_comm]
        congr 1
        · simp
        · rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ => by ring
      rw [hshift, sb_add_mul hb _ (hc 0),
        ih (fun j => c (j + 1)) (fun j => hc (j + 1)),
        Finset.sum_range_succ' c N]
      omega

/-- The digit sum is congruent to the number modulo `b − 1`
(the casting-out-nines rule). -/
theorem sb_modEq {b : ℕ} (hb : 2 ≤ b) (n : ℕ) : n ≡ sb b n [MOD b - 1] := by
  rcases Nat.lt_or_ge b 3 with h | h
  · -- `b = 2`: the modulus is `1`, and everything is congruent modulo `1`
    have h1 : b - 1 = 1 := by omega
    rw [h1]
    exact Nat.modEq_one
  · refine Nat.modEq_digits_sum (b - 1) b ?_ n
    have h3 : b - (b - 1) = 1 := by omega
    calc b % (b - 1) = (b - (b - 1)) % (b - 1) := Nat.mod_eq_sub_mod (by omega)
      _ = 1 % (b - 1) := by rw [h3]
      _ = 1 := Nat.mod_eq_of_lt (by omega)

end DSS
