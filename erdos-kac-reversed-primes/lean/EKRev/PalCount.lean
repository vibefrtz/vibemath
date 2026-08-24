/-
EKRev/PalCount.lean

Palindromes: the sets `𝒯_λ` (fixed length) and `𝒯(z)` (cumulative), the
counting formula `#𝒯_λ = (b-1) b^{⌈λ/2⌉-1}` (§1.2), and the comparison
`#𝒯(b^λ) ≤ 4 #𝒯_λ` realizing eq. (3.1) (`#𝒯(b^λ) ≍ #𝒯_λ`).

Conventions: `h := λ/2 = ⌊λ/2⌋` and `H := λ - h = ⌈λ/2⌉`.  A palindrome is
determined by its top half `⌊n / b^h⌋` (`H` digits, middle digit included
when `λ` is odd).

Everything in this file is fully proved (no axioms).
-/
import Mathlib.Tactic
import EKRev.Digits

namespace EKRev

open Finset

/-! ### More digit calculus -/

/-- Digits of a quotient: `ε_j(⌊n/b^k⌋) = ε_{k+j}(n)`. -/
lemma digit_div_pow (b n k j : ℕ) : digit b (n / b ^ k) j = digit b n (k + j) := by
  unfold digit
  rw [Nat.div_div_eq_div_mul, ← pow_add]

/-- Digits of a remainder: `ε_j(n mod b^k) = ε_j(n)` for `j < k`. -/
lemma digit_mod_pow (hb : 0 < b) (hj : j < k) (n : ℕ) :
    digit b (n % b ^ k) j = digit b n j := by
  conv_rhs => rw [← Nat.div_add_mod n (b ^ k), mul_comm]
  rw [digit_concat_low hb (Nat.mod_lt _ (Nat.pos_pow_of_pos k hb)) hj]

/-- Two numbers below `b^k` with the same digits are equal. -/
lemma eq_of_digit_eq (hb : 0 < b) (hx : x < b ^ k) (hy : y < b ^ k)
    (h : ∀ j < k, digit b x j = digit b y j) : x = y := by
  rw [← sum_digit_mul_pow_self hb hx, ← sum_digit_mul_pow_self hb hy]
  exact Finset.sum_congr rfl fun j hj => by
    rw [h j (Finset.mem_range.mp hj)]

/-- The palindrome condition through digits. -/
lemma rev_eq_self_iff (hb : 0 < b) (hn : n < b ^ lam) :
    rev b lam n = n ↔ ∀ j < lam, digit b n (lam - 1 - j) = digit b n j := by
  constructor
  · intro h j hj
    conv_rhs => rw [← h]
    rw [digit_rev hb _ hj]
  · intro h
    refine eq_of_digit_eq hb (rev_lt hb lam n) hn fun j hj => ?_
    rw [digit_rev hb _ hj]
    exact h j hj

/-! ### Palindrome sets -/

/-- `𝒯_λ`: base-`b` palindromes with exactly `λ` digits. -/
def palSet (b lam : ℕ) : Finset ℕ :=
  (Finset.Ico (b ^ (lam - 1)) (b ^ lam)).filter fun n => rev b lam n = n

lemma mem_palSet_iff {b lam n : ℕ} :
    n ∈ palSet b lam ↔ b ^ (lam - 1) ≤ n ∧ n < b ^ lam ∧ rev b lam n = n := by
  simp [palSet, Finset.mem_filter, Finset.mem_Ico, and_assoc]

/-- Number of base-`b` digits of `n` (for `n ≥ 1`). -/
def numDigits (b n : ℕ) : ℕ := Nat.log b n + 1

/-- `n` is a base-`b` palindrome (any length; positivity keeps the leading
digit nonzero). -/
def IsPal (b n : ℕ) : Prop := 1 ≤ n ∧ rev b (numDigits b n) n = n

instance (b : ℕ) : DecidablePred (IsPal b) := fun _ =>
  inferInstanceAs (Decidable (_ ∧ _))

/-- `𝒯(z)`: palindromes below `z`. -/
def palBelow (b z : ℕ) : Finset ℕ := (Finset.range z).filter (IsPal b)

/-- `𝒯(z, a, q)`: palindromes below `z` congruent to `a mod q`. -/
def palBelowMod (b z a q : ℕ) : Finset ℕ :=
  (palBelow b z).filter fun n => n % q = a % q

lemma numDigits_eq (hb : 2 ≤ b) (h1 : b ^ (lam - 1) ≤ n) (h2 : n < b ^ lam)
    (hlam : 1 ≤ lam) : numDigits b n = lam := by
  unfold numDigits
  have h2' : n < b ^ ((lam - 1) + 1) := by
    have heq : (lam - 1) + 1 = lam := by omega
    rwa [heq]
  rw [Nat.log_eq_of_pow_le_of_lt_pow h1 h2']
  omega

/-- On `[b^{λ-1}, b^λ)` the fixed-length and any-length palindrome conditions
agree. -/
lemma palSet_eq_filter_isPal (hb : 2 ≤ b) (hlam : 1 ≤ lam) :
    palSet b lam = (Finset.Ico (b ^ (lam - 1)) (b ^ lam)).filter (IsPal b) := by
  unfold palSet
  refine Finset.filter_congr fun n hn => ?_
  rw [Finset.mem_Ico] at hn
  have hnd : numDigits b n = lam := numDigits_eq hb hn.1 hn.2 hlam
  unfold IsPal
  rw [hnd]
  have h1 : 1 ≤ n := by
    have : 1 ≤ b ^ (lam - 1) := Nat.one_le_pow _ _ (by omega)
    omega
  simp [h1]

/-- `𝒯(b^λ)` decomposes into the palindromes of each length `ν ≤ λ`. -/
lemma palBelow_pow_eq_biUnion (hb : 2 ≤ b) (lam : ℕ) :
    palBelow b (b ^ lam) = (Finset.Icc 1 lam).biUnion (fun ν => palSet b ν) := by
  ext n
  simp only [palBelow, Finset.mem_filter, Finset.mem_range, Finset.mem_biUnion,
    Finset.mem_Icc]
  constructor
  · rintro ⟨hn, h1, hrev⟩
    have hn0 : n ≠ 0 := by omega
    refine ⟨numDigits b n, ⟨by unfold numDigits; omega, ?_⟩, ?_⟩
    · unfold numDigits
      have hlt : Nat.log b n < lam := by
        rcases Nat.eq_zero_or_pos lam with h | h
        · exfalso
          subst h
          simp only [pow_zero] at hn
          omega
        · exact Nat.log_lt_of_lt_pow hn0 hn
      omega
    · rw [mem_palSet_iff]
      refine ⟨?_, ?_, hrev⟩
      · have h2 : numDigits b n - 1 = Nat.log b n := by unfold numDigits; omega
        calc b ^ (numDigits b n - 1) = b ^ Nat.log b n := by rw [h2]
          _ ≤ n := Nat.pow_log_le_self b hn0
      · exact Nat.lt_pow_succ_log_self (by omega) n
  · rintro ⟨ν, ⟨hν1, hν2⟩, hmem⟩
    rw [mem_palSet_iff] at hmem
    obtain ⟨hlow, hhigh, hrev⟩ := hmem
    have hnd : numDigits b n = ν := numDigits_eq hb hlow hhigh hν1
    have h1 : 1 ≤ n := by
      have : 1 ≤ b ^ (ν - 1) := Nat.one_le_pow _ _ (by omega)
      omega
    refine ⟨?_, h1, ?_⟩
    · calc n < b ^ ν := hhigh
        _ ≤ b ^ lam := Nat.pow_le_pow_right (by omega) hν2
    · rw [hnd]; exact hrev

/-! ### The counting bijection -/

section Count

variable (b lam : ℕ)

/-- Reconstruct a palindrome from its top half `m` (which has
`H = λ - λ/2` digits; for odd `λ` the middle digit is the last digit of `m`
and is dropped before reversing). -/
def unfoldPal (m : ℕ) : ℕ :=
  m * b ^ (lam / 2) + rev b (lam / 2) (m / b ^ ((lam - lam / 2) - lam / 2))

variable {b lam}

/-- For a palindrome `n < b^λ`, reconstruction from the top half `⌊n/b^{λ/2}⌋`
recovers `n`. -/
lemma unfoldPal_top_half (hb : 0 < b) (hn : n < b ^ lam) (hrev : rev b lam n = n) :
    unfoldPal b lam (n / b ^ (lam / 2)) = n := by
  set h := lam / 2 with hh
  set H := lam - h with hH
  have hhH : h ≤ H := by omega
  have hHl : h + H = lam := by omega
  unfold unfoldPal
  rw [← hh, ← hH]
  have e1 : n / b ^ h / b ^ (H - h) = n / b ^ H := by
    rw [Nat.div_div_eq_div_mul, ← pow_add]
    congr 2
    omega
  have e2 : rev b h (n / b ^ H) = n % b ^ h := by
    refine eq_of_digit_eq hb (rev_lt hb _ _) (Nat.mod_lt _ (Nat.pos_pow_of_pos _ hb)) ?_
    intro j hj
    rw [digit_rev hb _ hj, digit_div_pow, digit_mod_pow hb hj]
    have hdig := (rev_eq_self_iff hb hn).mp hrev
    have hidx : H + (h - 1 - j) = lam - 1 - j := by omega
    rw [hidx]
    exact hdig j (by omega)
  rw [e1, e2]
  calc n / b ^ h * b ^ h + n % b ^ h
      = b ^ h * (n / b ^ h) + n % b ^ h := by ring
    _ = n := Nat.div_add_mod n (b ^ h)

/-- Reconstruction lands in `𝒯_λ` when the top half has exactly `H` digits. -/
lemma unfoldPal_mem_palSet (hb : 0 < b) (hlam : 1 ≤ lam)
    (hm1 : b ^ ((lam - lam / 2) - 1) ≤ m) (hm2 : m < b ^ (lam - lam / 2)) :
    unfoldPal b lam m ∈ palSet b lam := by
  set h := lam / 2 with hh
  set H := lam - h with hH
  have hH1 : 1 ≤ H := by omega
  have hhH : h ≤ H := by omega
  have hHl : h + H = lam := by omega
  have hrlt : rev b h (m / b ^ (H - h)) < b ^ h := rev_lt hb _ _
  have hne : unfoldPal b lam m = m * b ^ h + rev b h (m / b ^ (H - h)) := by
    unfold unfoldPal
    rw [← hh, ← hH]
  have hn_lt : unfoldPal b lam m < b ^ lam := by
    rw [hne]
    calc m * b ^ h + rev b h (m / b ^ (H - h))
        < m * b ^ h + b ^ h := by omega
      _ = (m + 1) * b ^ h := by ring
      _ ≤ b ^ H * b ^ h := Nat.mul_le_mul_right _ (by omega)
      _ = b ^ lam := by rw [← pow_add]; congr 1; omega
  have hn_ge : b ^ (lam - 1) ≤ unfoldPal b lam m := by
    rw [hne]
    calc b ^ (lam - 1) = b ^ (H - 1) * b ^ h := by rw [← pow_add]; congr 1; omega
      _ ≤ m * b ^ h := Nat.mul_le_mul_right _ hm1
      _ ≤ m * b ^ h + rev b h (m / b ^ (H - h)) := Nat.le_add_right _ _
  rw [mem_palSet_iff]
  refine ⟨hn_ge, hn_lt, ?_⟩
  rw [rev_eq_self_iff hb hn_lt]
  intro j hj
  -- digit formulas for the concatenation
  have flow : ∀ j' < h, digit b (unfoldPal b lam m) j' = digit b m (H - 1 - j') := by
    intro j' hj'
    rw [hne, digit_concat_low hb hrlt hj', digit_rev hb _ hj', digit_div_pow]
    congr 1
    omega
  have fhigh : ∀ i, digit b (unfoldPal b lam m) (h + i) = digit b m i := by
    intro i
    rw [hne, digit_concat_high hb hrlt]
  by_cases hcase : j < h
  · have hlj : lam - 1 - j = h + (H - 1 - j) := by omega
    rw [hlj, fhigh, flow j hcase]
  · have hi : j = h + (j - h) := by omega
    set i := j - h with hidef
    have hiH : i < H := by omega
    rw [hi, fhigh i]
    have hlj : lam - 1 - (h + i) = H - 1 - i := by omega
    rw [hlj]
    by_cases hcase2 : H - 1 - i < h
    · rw [flow _ hcase2]
      congr 1
      omega
    · -- H-1-i ≥ h forces λ odd and i = 0; the index is exactly h.
      have heq : H - 1 - i = h + 0 := by omega
      rw [heq, fhigh 0]
      congr 1
      omega

/-- The counting formula (§1.2): `#𝒯_λ = (b-1)·b^{⌈λ/2⌉-1}` for `λ ≥ 1`,
where `⌈λ/2⌉ = λ - λ/2`. -/
theorem palSet_card (hb : 2 ≤ b) (hlam : 1 ≤ lam) :
    (palSet b lam).card = (b - 1) * b ^ ((lam - lam / 2) - 1) := by
  have hb0 : 0 < b := by omega
  set h := lam / 2 with hh
  set H := lam - h with hH
  have hH1 : 1 ≤ H := by omega
  have hhH : h ≤ H := by omega
  have hcard : (palSet b lam).card = (Finset.Ico (b ^ (H - 1)) (b ^ H)).card := by
    refine Finset.card_bij' (fun n _ => n / b ^ h) (fun m _ => unfoldPal b lam m)
      ?_ ?_ ?_ ?_
    · -- forward map lands in Ico
      intro n hn
      rw [mem_palSet_iff] at hn
      obtain ⟨h1, h2, _⟩ := hn
      rw [Finset.mem_Ico]
      constructor
      · rw [Nat.le_div_iff_mul_le (Nat.pos_pow_of_pos _ hb0), ← pow_add]
        calc b ^ (H - 1 + h) = b ^ (lam - 1) := by congr 1; omega
          _ ≤ n := h1
      · refine Nat.div_lt_of_lt_mul ?_
        calc n < b ^ lam := h2
          _ = b ^ h * b ^ H := by rw [← pow_add]; congr 1; omega
    · -- backward map lands in palSet
      intro m hm
      rw [Finset.mem_Ico] at hm
      exact unfoldPal_mem_palSet hb0 hlam (by rw [← hH]; exact hm.1) (by rw [← hH]; exact hm.2)
    · -- left inverse
      intro n hn
      rw [mem_palSet_iff] at hn
      exact unfoldPal_top_half hb0 hn.2.1 hn.2.2
    · -- right inverse
      intro m hm
      rw [Finset.mem_Ico] at hm
      have hrlt : rev b h (m / b ^ ((lam - h) - h)) < b ^ h := rev_lt hb0 _ _
      unfold unfoldPal
      rw [← hh]
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.pos_pow_of_pos h hb0),
        Nat.div_eq_of_lt (by rw [← hH] at hrlt ⊢; exact hrlt), Nat.zero_add]
  rw [hcard, Nat.card_Ico]
  have hpow : b ^ H = b * b ^ (H - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  rw [hpow, Nat.sub_mul, one_mul]

/-- Geometric sum identity in `ℕ`: `(b-1)·∑_{K<T} b^K + 1 = b^T`. -/
lemma geom_sum_mul_pred (hb0 : 0 < b) : ∀ T : ℕ,
    (b - 1) * ∑ K ∈ Finset.range T, b ^ K + 1 = b ^ T := by
  intro T
  induction T with
  | zero => simp
  | succ T ih =>
      rw [Finset.sum_range_succ]
      calc (b - 1) * (∑ K ∈ Finset.range T, b ^ K + b ^ T) + 1
          = ((b - 1) * ∑ K ∈ Finset.range T, b ^ K + 1) + (b - 1) * b ^ T := by ring
        _ = b ^ T + (b - 1) * b ^ T := by rw [ih]
        _ = (1 + (b - 1)) * b ^ T := by ring
        _ = b * b ^ T := by
            have h2 : 1 + (b - 1) = b := by omega
            rw [h2]
        _ = b ^ (T + 1) := by rw [← pow_succ']

/-- Comparison of cumulative and per-length palindrome counts, realizing
eq. (3.1): `#𝒯(b^λ) ≤ 4·#𝒯_λ`. -/
theorem palBelow_card_le (hb : 2 ≤ b) (hlam : 1 ≤ lam) :
    (palBelow b (b ^ lam)).card ≤ 4 * (palSet b lam).card := by
  have hb0 : 0 < b := by omega
  have hcards : ∀ ν ∈ Finset.Icc 1 lam,
      (palSet b ν).card ≤ (b - 1) * b ^ ((ν - ν / 2) - 1) := by
    intro ν hν
    rw [Finset.mem_Icc] at hν
    rw [palSet_card hb hν.1]
  have pair : ∀ M : ℕ, ∑ ν ∈ Finset.Icc 1 (2 * M), b ^ ((ν - ν / 2) - 1)
      = 2 * ∑ K ∈ Finset.range M, b ^ K := by
    intro M
    induction M with
    | zero => simp
    | succ M ih =>
        have h1 : 2 * (M + 1) = (2 * M + 1) + 1 := by omega
        rw [h1, Finset.sum_Icc_succ_top (by omega), Finset.sum_Icc_succ_top (by omega), ih,
          Finset.sum_range_succ]
        have e1 : ((2 * M + 1) - (2 * M + 1) / 2) - 1 = M := by omega
        have e2 : (((2 * M + 1) + 1) - ((2 * M + 1) + 1) / 2) - 1 = M := by omega
        rw [e1, e2]
        ring
  have hsub : ∑ ν ∈ Finset.Icc 1 lam, b ^ ((ν - ν / 2) - 1)
      ≤ ∑ ν ∈ Finset.Icc 1 (2 * (lam - lam / 2)), b ^ ((ν - ν / 2) - 1) := by
    refine Finset.sum_le_sum_of_subset ?_
    intro ν hν
    rw [Finset.mem_Icc] at hν ⊢
    omega
  have hgeom := geom_sum_mul_pred hb0 (lam - lam / 2)
  have hTpow : b ^ (lam - lam / 2) = b * b ^ ((lam - lam / 2) - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have key : ∑ ν ∈ Finset.Icc 1 lam, b ^ ((ν - ν / 2) - 1)
      ≤ 4 * b ^ ((lam - lam / 2) - 1) := by
    have hmain : (b - 1) * (∑ ν ∈ Finset.Icc 1 lam, b ^ ((ν - ν / 2) - 1))
        ≤ (b - 1) * (4 * b ^ ((lam - lam / 2) - 1)) := by
      calc (b - 1) * (∑ ν ∈ Finset.Icc 1 lam, b ^ ((ν - ν / 2) - 1))
          ≤ (b - 1) * (∑ ν ∈ Finset.Icc 1 (2 * (lam - lam / 2)), b ^ ((ν - ν / 2) - 1)) :=
            Nat.mul_le_mul_left _ hsub
        _ = (b - 1) * (2 * ∑ K ∈ Finset.range (lam - lam / 2), b ^ K) := by rw [pair]
        _ = 2 * ((b - 1) * ∑ K ∈ Finset.range (lam - lam / 2), b ^ K) := by ring
        _ ≤ 2 * b ^ (lam - lam / 2) := by omega
        _ = 2 * b * b ^ ((lam - lam / 2) - 1) := by rw [hTpow]; ring
        _ ≤ (b - 1) * 4 * b ^ ((lam - lam / 2) - 1) :=
            Nat.mul_le_mul_right _ (by omega)
        _ = (b - 1) * (4 * b ^ ((lam - lam / 2) - 1)) := by ring
    exact Nat.le_of_mul_le_mul_left hmain (by omega : 0 < b - 1)
  calc (palBelow b (b ^ lam)).card
      = ((Finset.Icc 1 lam).biUnion (fun ν => palSet b ν)).card := by
        rw [palBelow_pow_eq_biUnion hb]
    _ ≤ ∑ ν ∈ Finset.Icc 1 lam, (palSet b ν).card := Finset.card_biUnion_le
    _ ≤ ∑ ν ∈ Finset.Icc 1 lam, (b - 1) * b ^ ((ν - ν / 2) - 1) :=
        Finset.sum_le_sum hcards
    _ = (b - 1) * ∑ ν ∈ Finset.Icc 1 lam, b ^ ((ν - ν / 2) - 1) := by
        rw [Finset.mul_sum]
    _ ≤ (b - 1) * (4 * b ^ ((lam - lam / 2) - 1)) := Nat.mul_le_mul_left _ key
    _ = 4 * ((b - 1) * b ^ ((lam - lam / 2) - 1)) := by ring
    _ = 4 * (palSet b lam).card := by rw [palSet_card hb hlam]

end Count

end EKRev
