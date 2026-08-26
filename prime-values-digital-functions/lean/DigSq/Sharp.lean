/-
DigSq/Sharp.lean

§6.2 of the paper: the words *"sufficiently large"* in Theorem 1.1(i) cannot be
dropped, even though `d_S = 1`.

* `S n = 1` forces `n = 10^j`, so `1` is never `S(p)` for a prime `p`;
* `S n = 3` forces `3 ∣ n`, so `3` is never `S(p)` for a prime `p`.

Both `1` and `3` are prime values omitted by `S` on the primes.

Nothing in this file is conditional: it imports no axioms.
-/
import DigSq.Examples

namespace DigSq

/-- The decimal digits of `d + 10·m`, for a digit `d`. -/
theorem digits_ten_add_mul {d m : ℕ} (hd : d < 10) (h : 0 < d + 10 * m) :
    Nat.digits 10 (d + 10 * m) = d :: Nat.digits 10 m := by
  rw [Nat.digits_def' (by norm_num : (1 : ℕ) < 10) h]
  have h1 : (d + 10 * m) % 10 = d := by
    rw [Nat.add_mul_mod_self_left]; exact Nat.mod_eq_of_lt hd
  have h2 : (d + 10 * m) / 10 = m := by
    rw [Nat.add_mul_div_left _ _ (by norm_num : 0 < 10), Nat.div_eq_of_lt hd]; simp
  rw [h1, h2]

/-- The recursion for `S`: appending a decimal digit `d` adds `d²`. -/
theorem S_add_mul {d m : ℕ} (hd : d < 10) : S (d + 10 * m) = d ^ 2 + S m := by
  rcases Nat.eq_zero_or_pos (d + 10 * m) with h | h
  · have hd0 : d = 0 := by omega
    have hm0 : m = 0 := by omega
    subst hd0; subst hm0; simp [S_def]
  · rw [S_def, digits_ten_add_mul hd h, S_def]; simp

/-- The decimal digit sum. -/
def digitSum (n : ℕ) : ℕ := (Nat.digits 10 n).sum

lemma digitSum_def (n : ℕ) : digitSum n = (Nat.digits 10 n).sum := rfl

theorem digitSum_add_mul {d m : ℕ} (hd : d < 10) :
    digitSum (d + 10 * m) = d + digitSum m := by
  rcases Nat.eq_zero_or_pos (d + 10 * m) with h | h
  · have hd0 : d = 0 := by omega
    have hm0 : m = 0 := by omega
    subst hd0; subst hm0; simp [digitSum_def]
  · rw [digitSum_def, digits_ten_add_mul hd h, digitSum_def]; simp

/-- `S n = 0` only for `n = 0`. -/
theorem S_eq_zero_iff {n : ℕ} : S n = 0 ↔ n = 0 := by
  constructor
  · induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro h
      rcases Nat.eq_zero_or_pos n with h0 | h0
      · exact h0
      · exfalso
        have hd : n % 10 < 10 := Nat.mod_lt _ (by norm_num)
        have hrec : S n = (n % 10) ^ 2 + S (n / 10) := by
          conv_lhs => rw [← Nat.mod_add_div n 10]
          exact S_add_mul hd
        rw [h] at hrec
        have h1 : (n % 10) ^ 2 = 0 := by omega
        have h2 : S (n / 10) = 0 := by omega
        have hm : n % 10 = 0 := by
          rcases Nat.eq_zero_or_pos (n % 10) with hz | hz
          · exact hz
          · exfalso; have := pow_pos hz 2; omega
        have hlt : n / 10 < n := Nat.div_lt_self h0 (by norm_num)
        have hzero := ih (n / 10) hlt h2
        omega
  · rintro rfl; simp [S_def]

/-- When `S n ≤ 3` every decimal digit of `n` is `0` or `1`, so `S` agrees with
the plain digit sum. -/
theorem S_eq_digitSum_of_le_three : ∀ {n : ℕ}, S n ≤ 3 → S n = digitSum n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro h
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · subst h0; simp [S_def, digitSum_def]
    · have hd : n % 10 < 10 := Nat.mod_lt _ (by norm_num)
      have hlt : n / 10 < n := Nat.div_lt_self h0 (by norm_num)
      have hrecS : S n = (n % 10) ^ 2 + S (n / 10) := by
        conv_lhs => rw [← Nat.mod_add_div n 10]
        exact S_add_mul hd
      have hrecD : digitSum n = (n % 10) + digitSum (n / 10) := by
        conv_lhs => rw [← Nat.mod_add_div n 10]
        exact digitSum_add_mul hd
      have hsq : (n % 10) ^ 2 ≤ 3 := by omega
      have hle1 : n % 10 ≤ 1 := by
        by_contra hc
        have h2 : 2 ≤ n % 10 := by omega
        have : 2 ^ 2 ≤ (n % 10) ^ 2 := Nat.pow_le_pow_left h2 2
        omega
      have hsq' : (n % 10) ^ 2 = n % 10 := by
        rcases (by omega : n % 10 = 0 ∨ n % 10 = 1) with hc | hc <;> rw [hc] <;> norm_num
      have hsub : S (n / 10) ≤ 3 := by omega
      have := ih (n / 10) hlt hsub
      omega

/-- **§6.2:** `S n = 3` forces `3 ∣ n`. -/
theorem three_dvd_of_S_eq_three {n : ℕ} (h : S n = 3) : 3 ∣ n := by
  have hds : digitSum n = 3 := by rw [← S_eq_digitSum_of_le_three (by omega), h]
  have hmod : n ≡ digitSum n [MOD 3] := Nat.modEq_three_digits_sum n
  rw [hds] at hmod
  have hmm : n % 3 = 3 % 3 := hmod
  omega

/-- **§6.2:** `S n = 1` forces `n = 10^j`. -/
theorem eq_pow_ten_of_S_eq_one : ∀ {n : ℕ}, S n = 1 → ∃ j : ℕ, n = 10 ^ j := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro h
    have h0 : 0 < n := by
      rcases Nat.eq_zero_or_pos n with hz | hz
      · subst hz; simp [S_def] at h
      · exact hz
    have hd : n % 10 < 10 := Nat.mod_lt _ (by norm_num)
    have hlt : n / 10 < n := Nat.div_lt_self h0 (by norm_num)
    have hrec : S n = (n % 10) ^ 2 + S (n / 10) := by
      conv_lhs => rw [← Nat.mod_add_div n 10]
      exact S_add_mul hd
    rw [h] at hrec
    have hsq : (n % 10) ^ 2 ≤ 1 := by omega
    have hle1 : n % 10 ≤ 1 := by
      by_contra hc
      have h2 : 2 ≤ n % 10 := by omega
      have : 2 ^ 2 ≤ (n % 10) ^ 2 := Nat.pow_le_pow_left h2 2
      omega
    rcases (by omega : n % 10 = 0 ∨ n % 10 = 1) with hcase | hcase
    · -- last digit `0`: `n = 10·(n/10)` and `S (n/10) = 1`
      have hz2 : (n % 10) ^ 2 = 0 := by rw [hcase]; norm_num
      have hS' : S (n / 10) = 1 := by omega
      obtain ⟨j, hj⟩ := ih (n / 10) hlt hS'
      refine ⟨j + 1, ?_⟩
      have hn : n = 10 * (n / 10) := by omega
      rw [hn, hj]; ring
    · -- last digit `1`: `S (n/10) = 0`, so `n/10 = 0` and `n = 1`
      have hz2 : (n % 10) ^ 2 = 1 := by rw [hcase]; norm_num
      have hS' : S (n / 10) = 0 := by omega
      have hzz : n / 10 = 0 := S_eq_zero_iff.mp hS'
      exact ⟨0, by omega⟩

/-- `1` is not the value of `S` at a prime. -/
theorem S_ne_one_of_prime {p : ℕ} (hp : Nat.Prime p) : S p ≠ 1 := by
  intro h
  obtain ⟨j, hj⟩ := eq_pow_ten_of_S_eq_one h
  rcases Nat.eq_zero_or_pos j with hz | hz
  · subst hz; norm_num at hj; subst hj; exact Nat.not_prime_one hp
  · have h2 : (2 : ℕ) ∣ p := by
      rw [hj]; exact dvd_pow (by norm_num : (2 : ℕ) ∣ 10) (by omega)
    have hor := Nat.Prime.eq_one_or_self_of_dvd hp 2 h2
    have hge : 10 ≤ p := by
      rw [hj]
      calc (10 : ℕ) = 10 ^ 1 := by norm_num
        _ ≤ 10 ^ j := Nat.pow_le_pow_right (by norm_num) hz
    omega

/-- `3` is not the value of `S` at a prime. -/
theorem S_ne_three_of_prime {p : ℕ} (hp : Nat.Prime p) : S p ≠ 3 := by
  intro h
  have h3 : (3 : ℕ) ∣ p := three_dvd_of_S_eq_three h
  have : p = 3 := ((Nat.prime_dvd_prime_iff_eq (by decide) hp).mp h3).symm
  subst this
  norm_num [S_def] at h

end DigSq
