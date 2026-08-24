/-
EKRev/Digits.lean

Base-`b` digits, the digit-reversal operator `R_λ`, palindromes, and the
elementary "digit calculus" the paper uses throughout:

* the expansion `n = ∑_{j<λ} ε_j(n) b^j` for `n < b^λ`  (eq. (1.2) context);
* uniqueness of base-`b` representations with digits `< b`;
* digits of a concatenation `m·b^h + r`;
* `R_λ` is an involution on `{n : n < b^λ}`, hence injective (§4, opening);
* the congruences of Lemma 4.1 (cf. [DRS, (3.8), (3.9)]):
  `R_λ(n) ≡ b^{λ-1} n (mod b²-1)`, `gcd(R_λ(n), b²-1) = gcd(n, b²-1)`,
  `R_λ(n) ≡ ε_{λ-1}(n) (mod ℓ)` for `ℓ ∣ b`;
* location facts: `R_λ(n) < b^λ`, and `b^{λ-1} ≤ R_λ(p)` when `gcd(p,b)=1`.

Everything in this file is fully proved (no axioms).
-/
import Mathlib.Tactic
import Mathlib.Data.Nat.Log
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace EKRev

open Finset

/-- Compatibility alias with the historical argument order (`m` first). -/
theorem _root_.Nat.pos_pow_of_pos {b : ℕ} (m : ℕ) (hb : 0 < b) : 0 < b ^ m :=
  pow_pos hb m

/-! ### Digits -/

/-- The `j`-th base-`b` digit of `n` (little-endian): `ε_j(n) = ⌊n / b^j⌋ mod b`. -/
def digit (b n j : ℕ) : ℕ := n / b ^ j % b

lemma digit_lt (hb : 0 < b) (n j : ℕ) : digit b n j < b :=
  Nat.mod_lt _ hb

lemma digit_le (hb : 0 < b) (n j : ℕ) : digit b n j ≤ b - 1 :=
  Nat.le_sub_one_of_lt (digit_lt hb n j)

lemma digit_eq_zero_of_lt (h : n < b ^ j) : digit b n j = 0 := by
  simp [digit, Nat.div_eq_of_lt h]

lemma digit_zero (b n : ℕ) : digit b n 0 = n % b := by
  simp [digit]

/-- A number is at most `b^m - 1` if it is a digit combination `∑_{j<m} c_j b^j`
with all `c_j < b`. -/
lemma sum_mul_pow_le (hb : 0 < b) {m : ℕ} {c : ℕ → ℕ} (hc : ∀ j < m, c j < b) :
    ∑ j ∈ range m, c j * b ^ j ≤ b ^ m - 1 := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Finset.sum_range_succ]
      have h1 : ∑ j ∈ range m, c j * b ^ j ≤ b ^ m - 1 :=
        ih fun j hj => hc j (by omega)
      have h2 : c m * b ^ m ≤ (b - 1) * b ^ m :=
        Nat.mul_le_mul_right _ (Nat.le_sub_one_of_lt (hc m (by omega)))
      have h3 : 0 < b ^ m := Nat.pos_pow_of_pos m hb
      have h4 : b ^ (m + 1) = b ^ m * b := by rw [pow_succ]
      have h5 : (b - 1) * b ^ m + b ^ m = b ^ m * b := by
        have hb1 : (b - 1) + 1 = b := by omega
        calc (b - 1) * b ^ m + b ^ m = ((b - 1) + 1) * b ^ m := by ring
          _ = b * b ^ m := by rw [hb1]
          _ = b ^ m * b := by ring
      omega

lemma sum_mul_pow_lt (hb : 0 < b) {m : ℕ} {c : ℕ → ℕ} (hc : ∀ j < m, c j < b) :
    ∑ j ∈ range m, c j * b ^ j < b ^ m := by
  have h := sum_mul_pow_le hb hc
  have : 0 < b ^ m := Nat.pos_pow_of_pos m hb
  omega

/-- The base-`b` expansion: `∑_{j<λ} ε_j(n) b^j = n mod b^λ`. -/
lemma sum_digit_mul_pow (hb : 0 < b) (n : ℕ) :
    ∀ lam, ∑ j ∈ range lam, digit b n j * b ^ j = n % b ^ lam := by
  intro lam
  induction lam with
  | zero => simp [Nat.mod_one]
  | succ m ih =>
      rw [Finset.sum_range_succ, ih]
      -- goal: n % b ^ m + digit b n m * b ^ m = n % b ^ (m + 1)
      have hbm : 0 < b ^ m := Nat.pos_pow_of_pos m hb
      have hbm1 : 0 < b ^ (m + 1) := Nat.pos_pow_of_pos _ hb
      have key : n = (n % b ^ m + digit b n m * b ^ m) + b ^ (m + 1) * (n / b ^ (m + 1)) := by
        have h1 : b ^ m * (n / b ^ m) + n % b ^ m = n := Nat.div_add_mod n (b ^ m)
        have h2 : b * (n / b ^ m / b) + n / b ^ m % b = n / b ^ m := Nat.div_add_mod (n / b ^ m) b
        have h3 : n / b ^ m / b = n / b ^ (m + 1) := by
          rw [Nat.div_div_eq_div_mul, ← pow_succ]
        calc n = b ^ m * (n / b ^ m) + n % b ^ m := h1.symm
          _ = b ^ m * (b * (n / b ^ m / b) + n / b ^ m % b) + n % b ^ m := by rw [h2]
          _ = (n % b ^ m + (n / b ^ m % b) * b ^ m) + (b ^ m * b) * (n / b ^ m / b) := by ring
          _ = (n % b ^ m + digit b n m * b ^ m) + b ^ (m + 1) * (n / b ^ (m + 1)) := by
                rw [h3, ← pow_succ]; rfl
      have hlt : n % b ^ m + digit b n m * b ^ m < b ^ (m + 1) := by
        have h4 : n % b ^ m < b ^ m := Nat.mod_lt _ hbm
        have h5 : digit b n m * b ^ m ≤ (b - 1) * b ^ m :=
          Nat.mul_le_mul_right _ (digit_le hb n m)
        have h6 : b ^ (m + 1) = b ^ m * b := by rw [pow_succ]
        have h7 : (b - 1) * b ^ m + b ^ m = b ^ m * b := by
          have hb1 : (b - 1) + 1 = b := by omega
          calc (b - 1) * b ^ m + b ^ m = ((b - 1) + 1) * b ^ m := by ring
            _ = b * b ^ m := by rw [hb1]
            _ = b ^ m * b := by ring
        omega
      calc n % b ^ m + digit b n m * b ^ m
          = ((n % b ^ m + digit b n m * b ^ m) + b ^ (m + 1) * (n / b ^ (m + 1))) % b ^ (m + 1) := by
            rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]
        _ = n % b ^ (m + 1) := by rw [← key]

/-- For `n < b^λ` the expansion recovers `n` itself. -/
lemma sum_digit_mul_pow_self (hb : 0 < b) (hn : n < b ^ lam) :
    ∑ j ∈ range lam, digit b n j * b ^ j = n := by
  rw [sum_digit_mul_pow hb, Nat.mod_eq_of_lt hn]

/-- Uniqueness of base-`b` representations: the `r`-th digit of
`∑_{j<λ} c_j b^j` is `c_r` whenever all `c_j < b` and `r < λ`. -/
lemma digit_sum_eq (hb : 0 < b) {lam : ℕ} {c : ℕ → ℕ} (hc : ∀ j < lam, c j < b)
    {r : ℕ} (hr : r < lam) :
    digit b (∑ j ∈ range lam, c j * b ^ j) r = c r := by
  -- split the sum at index r
  have hsplit : ∑ j ∈ range lam, c j * b ^ j
      = (∑ j ∈ range r, c j * b ^ j) + c r * b ^ r
        + (∑ j ∈ range (lam - (r + 1)), c (r + 1 + j) * b ^ (r + 1 + j)) := by
    have h1 : ∑ j ∈ range lam, c j * b ^ j
        = ∑ j ∈ range (r + 1), c j * b ^ j
          + ∑ j ∈ Ico (r + 1) lam, c j * b ^ j := by
      rw [Finset.range_eq_Ico, ← Finset.sum_Ico_consecutive _ (by omega : 0 ≤ r + 1) (by omega : r + 1 ≤ lam)]
      congr 1
      rw [Finset.range_eq_Ico]
    rw [h1, Finset.sum_range_succ, Finset.sum_Ico_eq_sum_range]
  rw [hsplit]
  -- rewrite the tail as a multiple of b^(r+1)
  have htail : ∑ j ∈ range (lam - (r + 1)), c (r + 1 + j) * b ^ (r + 1 + j)
      = (∑ j ∈ range (lam - (r + 1)), c (r + 1 + j) * b ^ j) * b ^ (r + 1) := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [pow_add, pow_add]; ring
  set A := ∑ j ∈ range r, c j * b ^ j with hA
  set B := ∑ j ∈ range (lam - (r + 1)), c (r + 1 + j) * b ^ j with hB
  rw [htail]
  have hAlt : A < b ^ r := sum_mul_pow_lt hb fun j hj => hc j (by omega)
  have hbr : 0 < b ^ r := Nat.pos_pow_of_pos r hb
  -- compute the digit
  unfold digit
  have hdiv : (A + c r * b ^ r + B * b ^ (r + 1)) / b ^ r = c r + B * b := by
    have h2 : A + c r * b ^ r + B * b ^ (r + 1) = A + (c r + B * b) * b ^ r := by
      rw [pow_succ]; ring
    rw [h2, Nat.add_mul_div_right _ _ hbr, Nat.div_eq_of_lt hAlt, Nat.zero_add]
  rw [hdiv, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (hc r hr)]

/-! ### Digits of a concatenation -/

/-- Low digits of `m·b^h + r` are the digits of `r`, when `r < b^h`. -/
lemma digit_concat_low (hb : 0 < b) (hr : r < b ^ h) (hj : j < h) (m : ℕ) :
    digit b (m * b ^ h + r) j = digit b r j := by
  unfold digit
  have h1 : m * b ^ h + r = r + (m * b ^ (h - j - 1) * b) * b ^ j := by
    have : b ^ (h - j - 1) * b * b ^ j = b ^ h := by
      rw [mul_assoc, ← pow_succ']
      rw [← pow_add]
      congr 1
      omega
    calc m * b ^ h + r = r + m * (b ^ (h - j - 1) * b * b ^ j) := by rw [this]; ring
      _ = r + (m * b ^ (h - j - 1) * b) * b ^ j := by ring
  rw [h1, Nat.add_mul_div_right _ _ (Nat.pos_pow_of_pos j hb)]
  have h2 : (r / b ^ j + m * b ^ (h - j - 1) * b) % b = r / b ^ j % b := by
    rw [Nat.add_mul_mod_self_right]
  rw [h2]

/-- High digits of `m·b^h + r` are the digits of `m`, when `r < b^h`. -/
lemma digit_concat_high (hb : 0 < b) (hr : r < b ^ h) (m j : ℕ) :
    digit b (m * b ^ h + r) (h + j) = digit b m j := by
  unfold digit
  have h1 : (m * b ^ h + r) / b ^ (h + j) = m / b ^ j := by
    rw [pow_add, ← Nat.div_div_eq_div_mul]
    congr 1
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.pos_pow_of_pos h hb),
      Nat.div_eq_of_lt hr, Nat.zero_add]
  rw [h1]

/-! ### The reversal operator -/

/-- Reversal of the `λ` least significant base-`b` digits of `n` (eq. (1.2)):
`R_λ(n) = ∑_{j<λ} ε_j(n) b^{λ-1-j}`. -/
def rev (b lam n : ℕ) : ℕ := ∑ j ∈ range lam, digit b n j * b ^ (lam - 1 - j)

/-- `R_λ(n)` written with ascending powers: `∑_{j<λ} ε_{λ-1-j}(n) b^j`. -/
lemma rev_eq_sum_rev (b lam n : ℕ) :
    rev b lam n = ∑ j ∈ range lam, digit b n (lam - 1 - j) * b ^ j := by
  unfold rev
  rw [← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' : j < lam := Finset.mem_range.mp hj
  congr 2
  omega

lemma rev_lt (hb : 0 < b) (lam n : ℕ) : rev b lam n < b ^ lam := by
  rw [rev_eq_sum_rev]
  exact sum_mul_pow_lt hb fun j _ => digit_lt hb n _

/-- Digits of the reversal: `ε_j(R_λ(n)) = ε_{λ-1-j}(n)` for `j < λ`. -/
lemma digit_rev (hb : 0 < b) (n : ℕ) {j lam : ℕ} (hj : j < lam) :
    digit b (rev b lam n) j = digit b n (lam - 1 - j) := by
  rw [rev_eq_sum_rev]
  exact digit_sum_eq hb (fun j _ => digit_lt hb n _) hj

/-- `R_λ` is an involution on `{n : n < b^λ}` (§4, opening). -/
lemma rev_rev (hb : 0 < b) (hn : n < b ^ lam) : rev b lam (rev b lam n) = n := by
  have h1 : rev b lam (rev b lam n) = ∑ j ∈ range lam, digit b n j * b ^ j := by
    rw [rev_eq_sum_rev]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' : j < lam := Finset.mem_range.mp hj
    rw [digit_rev hb _ (by omega : lam - 1 - j < lam)]
    congr 2
    omega
  rw [h1, sum_digit_mul_pow_self hb hn]

/-- `R_λ` is injective on `{n : n < b^λ}`. -/
lemma rev_injOn (hb : 0 < b) (lam : ℕ) :
    Set.InjOn (rev b lam) {n : ℕ | n < b ^ lam} := by
  intro x hx y hy h
  have hx' : x < b ^ lam := hx
  have hy' : y < b ^ lam := hy
  rw [← rev_rev hb hx', h, rev_rev hb hy']

/-! ### Congruences (Lemma 4.1, cf. [DRS, (3.8), (3.9)]) -/

private lemma modEq_sum {m : ℕ} {s : Finset ℕ} {f g : ℕ → ℕ}
    (h : ∀ i ∈ s, f i ≡ g i [MOD m]) : ∑ i ∈ s, f i ≡ ∑ i ∈ s, g i [MOD m] := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Nat.ModEq.refl]
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      exact (h a (Finset.mem_insert_self a s)).add
        (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

lemma sq_sub_one_eq (hb : 1 ≤ b) : b ^ 2 - 1 = (b - 1) * (b + 1) := by
  have h1 : 1 ≤ b ^ 2 := Nat.one_le_pow _ _ hb
  zify [h1, hb]
  ring

/-- `b² ≡ 1 (mod b²-1)` for `b ≥ 2`. -/
lemma b_sq_modEq_one (hb : 2 ≤ b) : b ^ 2 ≡ 1 [MOD b ^ 2 - 1] := by
  have h4 : 4 ≤ b ^ 2 := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ b ^ 2 := Nat.pow_le_pow_left hb 2
  set m := b ^ 2 - 1 with hm
  have h1 : b ^ 2 = m + 1 := by omega
  show b ^ 2 % m = 1 % m
  rw [h1, Nat.add_mod_left]

/-- Lemma 4.1(i), main congruence: `R_λ(n) ≡ b^{λ-1} n (mod b²-1)` for `n < b^λ`. -/
lemma rev_modEq_pow_mul (hb : 2 ≤ b) (hn : n < b ^ lam) :
    rev b lam n ≡ b ^ (lam - 1) * n [MOD b ^ 2 - 1] := by
  have hb0 : 0 < b := by omega
  have key : ∀ j < lam,
      digit b n j * b ^ (lam - 1 - j) ≡ digit b n j * b ^ (lam - 1 + j) [MOD b ^ 2 - 1] := by
    intro j hj
    have hexp : lam - 1 + j = (lam - 1 - j) + 2 * j := by omega
    have h2j : b ^ (2 * j) ≡ 1 [MOD b ^ 2 - 1] := by
      calc b ^ (2 * j) = (b ^ 2) ^ j := by rw [← pow_mul]
        _ ≡ 1 ^ j [MOD b ^ 2 - 1] := (b_sq_modEq_one hb).pow j
        _ = 1 := one_pow j
    calc digit b n j * b ^ (lam - 1 - j)
        = digit b n j * b ^ (lam - 1 - j) * 1 := by ring
      _ ≡ digit b n j * b ^ (lam - 1 - j) * b ^ (2 * j) [MOD b ^ 2 - 1] :=
          (h2j.symm).mul_left _
      _ = digit b n j * b ^ (lam - 1 + j) := by rw [hexp, pow_add]; ring
  calc rev b lam n = ∑ j ∈ range lam, digit b n j * b ^ (lam - 1 - j) := rfl
    _ ≡ ∑ j ∈ range lam, digit b n j * b ^ (lam - 1 + j) [MOD b ^ 2 - 1] :=
        modEq_sum fun j hj => key j (Finset.mem_range.mp hj)
    _ = b ^ (lam - 1) * ∑ j ∈ range lam, digit b n j * b ^ j := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j hj => ?_
        rw [pow_add]; ring
    _ = b ^ (lam - 1) * n := by rw [sum_digit_mul_pow_self hb0 hn]

/-- gcd invariance along a congruence. -/
lemma gcd_eq_of_modEq {a c m : ℕ} (h : a ≡ c [MOD m]) : Nat.gcd a m = Nat.gcd c m := by
  unfold Nat.ModEq at h
  rw [Nat.gcd_comm a m, Nat.gcd_comm c m, Nat.gcd_rec m a, Nat.gcd_rec m c, h]

lemma coprime_b_sq_sub_one (hb : 2 ≤ b) : Nat.Coprime b (b ^ 2 - 1) := by
  rw [sq_sub_one_eq (by omega)]
  have h1 : Nat.Coprime b (b - 1) := by
    have h := (Nat.coprime_add_self_left (m := 1) (n := b - 1)).mpr (Nat.coprime_one_left _)
    have hb1 : 1 + (b - 1) = b := by omega
    rwa [hb1] at h
  have h2 : Nat.Coprime b (b + 1) :=
    Nat.coprime_self_add_right.mpr (Nat.coprime_one_right b)
  exact h1.mul_right h2

/-- Lemma 4.1(i), gcd form: `gcd(R_λ(n), b²-1) = gcd(n, b²-1)` for `n < b^λ`. -/
lemma rev_gcd_sq_sub_one (hb : 2 ≤ b) (hn : n < b ^ lam) :
    Nat.gcd (rev b lam n) (b ^ 2 - 1) = Nat.gcd n (b ^ 2 - 1) := by
  rw [gcd_eq_of_modEq (rev_modEq_pow_mul hb hn)]
  exact Nat.Coprime.gcd_mul_left_cancel n ((coprime_b_sq_sub_one hb).pow_left _)

/-- Lemma 4.1(i), consequence: a prime `p > b+1` with `p < b^λ` has
`gcd(R_λ(p), b²-1) = 1`. -/
lemma rev_coprime_sq_sub_one (hb : 2 ≤ b) (hp : Nat.Prime p) (hpb : b + 1 < p)
    (hplt : p < b ^ lam) : Nat.Coprime (rev b lam p) (b ^ 2 - 1) := by
  unfold Nat.Coprime
  rw [rev_gcd_sq_sub_one hb hplt]
  -- gcd(p, b²-1) = 1: a prime `p > b+1` cannot divide `(b-1)(b+1)`.
  have hnd : ¬ p ∣ (b ^ 2 - 1) := by
    intro hdvd
    have h1 : b ^ 2 - 1 = (b - 1) * (b + 1) := sq_sub_one_eq (by omega)
    rw [h1] at hdvd
    rcases (Nat.Prime.dvd_mul hp).mp hdvd with h | h
    · have : p ≤ b - 1 := Nat.le_of_dvd (by omega) h
      omega
    · have : p ≤ b + 1 := Nat.le_of_dvd (by omega) h
      omega
  exact (Nat.Prime.coprime_iff_not_dvd hp).mpr hnd

/-- Lemma 4.1(ii): if `ℓ ∣ b` and `λ ≥ 1` then `R_λ(n) ≡ ε_{λ-1}(n) (mod ℓ)`. -/
lemma rev_modEq_of_dvd_base (hb : 0 < b) (hl : ℓ ∣ b) (hlam : 1 ≤ lam) (n : ℕ) :
    rev b lam n ≡ digit b n (lam - 1) [MOD ℓ] := by
  unfold rev
  have hsplit : ∑ j ∈ range lam, digit b n j * b ^ (lam - 1 - j)
      = (∑ j ∈ range (lam - 1), digit b n j * b ^ (lam - 1 - j))
        + digit b n (lam - 1) * b ^ (lam - 1 - (lam - 1)) := by
    have h2 := Finset.sum_range_succ
      (fun j => digit b n j * b ^ (lam - 1 - j)) (lam - 1)
    have h1 : lam - 1 + 1 = lam := by omega
    rw [h1] at h2
    exact h2
  rw [hsplit]
  have hz : lam - 1 - (lam - 1) = 0 := by omega
  rw [hz, pow_zero, mul_one]
  have hdvd : ℓ ∣ ∑ j ∈ range (lam - 1), digit b n j * b ^ (lam - 1 - j) := by
    refine Finset.dvd_sum fun j hj => ?_
    have hj' : j < lam - 1 := Finset.mem_range.mp hj
    have hpow : 1 ≤ lam - 1 - j := by omega
    have : ℓ ∣ b ^ (lam - 1 - j) := hl.trans (dvd_pow_self b (by omega : lam - 1 - j ≠ 0))
    exact Dvd.dvd.mul_left this _
  calc (∑ j ∈ range (lam - 1), digit b n j * b ^ (lam - 1 - j)) + digit b n (lam - 1)
      ≡ 0 + digit b n (lam - 1) [MOD ℓ] :=
        ((Nat.modEq_zero_iff_dvd).mpr hdvd).add_right _
    _ = digit b n (lam - 1) := by omega

/-! ### Location of `n` and of `R_λ(n)` -/

/-- The top digit of `n < b^λ`: `ε_{λ-1}(n) = ⌊n / b^{λ-1}⌋`. -/
lemma digit_top_eq (hn : n < b ^ lam) (hlam : 1 ≤ lam) :
    digit b n (lam - 1) = n / b ^ (lam - 1) := by
  unfold digit
  refine Nat.mod_eq_of_lt ?_
  refine Nat.div_lt_of_lt_mul ?_
  calc n < b ^ lam := hn
    _ = b ^ (lam - 1) * b := by rw [← pow_succ]; congr 1; omega

/-- If the top digit is positive then `n ≥ b^{λ-1}`. -/
lemma le_of_digit_top_pos (h : 1 ≤ digit b n (lam - 1)) : b ^ (lam - 1) ≤ n := by
  by_contra hcon
  push_neg at hcon
  rw [digit_eq_zero_of_lt hcon] at h
  omega

/-- Conversely, `b^{λ-1} ≤ n < b^λ` forces a positive top digit. -/
lemma digit_top_pos (hb : 0 < b) (h1 : b ^ (lam - 1) ≤ n) (h2 : n < b ^ lam)
    (hlam : 1 ≤ lam) : 1 ≤ digit b n (lam - 1) := by
  rw [digit_top_eq h2 hlam]
  exact Nat.one_le_div_iff (Nat.pos_pow_of_pos _ hb) |>.mpr h1

/-- If `n < b^λ` has a nonzero last digit (`b ∤ n` suffices via `n % b ≥ 1`)
then its reversal has `λ` digits: `b^{λ-1} ≤ R_λ(n)`. -/
lemma rev_ge_of_last_digit_pos (hb : 0 < b) (hn : n < b ^ lam) (hlam : 1 ≤ lam)
    (h0 : 1 ≤ n % b) : b ^ (lam - 1) ≤ rev b lam n := by
  refine le_of_digit_top_pos ?_
  rw [digit_rev hb _ (by omega : lam - 1 < lam)]
  have : lam - 1 - (lam - 1) = 0 := by omega
  rw [this, digit_zero]
  exact h0

/-- A prime `p` with `b < p` has `p mod b ≥ 1`. -/
lemma prime_mod_base_pos (hb : 2 ≤ b) (hp : Nat.Prime p) (hpb : b < p) :
    1 ≤ p % b := by
  rcases Nat.eq_zero_or_pos (p % b) with h | h
  · exfalso
    have hdvd : b ∣ p := Nat.dvd_of_mod_eq_zero h
    have := (Nat.Prime.eq_one_or_self_of_dvd hp b hdvd)
    omega
  · exact h

/-! ### Counting multiples -/

/-- The number of positive multiples of `d` below `N` is at most `N/d`
(eq. (4.2), trivial bound, counting part). -/
lemma card_multiples_lt (hd : 1 ≤ d) (N : ℕ) :
    (((Finset.Ico 1 N).filter (fun n => d ∣ n)).card : ℝ) ≤ (N : ℝ) / d := by
  have hcount : ((Finset.Ico 1 N).filter (fun n => d ∣ n)).card ≤ N / d := by
    classical
    have hinj : Set.InjOn (fun n => n / d) ↑((Finset.Ico 1 N).filter (fun n => d ∣ n)) := by
      intro x hx y hy h
      simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_Ico] at hx hy
      have h' : x / d = y / d := h
      have hx' : d * (x / d) = x := Nat.mul_div_cancel' hx.2
      have hy' : d * (y / d) = y := Nat.mul_div_cancel' hy.2
      rw [← hx', ← hy', h']
    have hmaps : ∀ n ∈ (Finset.Ico 1 N).filter (fun n => d ∣ n),
        n / d ∈ Finset.Icc 1 (N / d) := by
      intro n hn
      simp only [Finset.mem_filter, Finset.mem_Ico] at hn
      obtain ⟨⟨h1, h2⟩, hdn⟩ := hn
      simp only [Finset.mem_Icc]
      have hd0 : 0 < d := hd
      constructor
      · exact (Nat.one_le_div_iff hd0).mpr (Nat.le_of_dvd (by omega) hdn)
      · exact Nat.div_le_div_right (by omega)
    calc ((Finset.Ico 1 N).filter (fun n => d ∣ n)).card
        ≤ (Finset.Icc 1 (N / d)).card := Finset.card_le_card_of_injOn _ hmaps hinj
      _ = N / d := by simp [Nat.card_Icc]
  have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  calc (((Finset.Ico 1 N).filter (fun n => d ∣ n)).card : ℝ)
      ≤ ((N / d : ℕ) : ℝ) := by exact_mod_cast hcount
    _ ≤ (N : ℝ) / d := by
        rw [le_div_iff₀ hd0]
        exact_mod_cast Nat.div_mul_le_self N d

end EKRev
