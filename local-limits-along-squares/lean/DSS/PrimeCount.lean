/-
DSS/PrimeCount.lean

**Corollary 1.9** in bases `2` and `3`: many squares below `X` with prime
digit sum.  Bertrand's postulate (in Mathlib) supplies a prime target
`q ∈ (N, 2N]`; in base `2` every large `q` is admissible, and in base `3`
admissibility modulo `2` holds for every odd prime.  Theorem 1.8 then counts
the representations.

For general bases the corollary needs a prime `≡ 1 (mod b−1)` in a dyadic
window, i.e. the prime number theorem for arithmetic progressions, which is
outside this development; see `VERIFICATION.md`.

Nothing in this file is conditional: it imports no axioms.
-/
import DSS.Squares

namespace DSS

open Finset

/-- The squares of bounded size whose digit sum is prime. -/
def sqPrimeDS (b X : ℕ) : Finset ℕ :=
  (range (X + 1)).filter
    (fun n => Nat.Coprime n b ∧ Nat.Prime (sb b (n ^ 2)) ∧ n ^ 2 ≤ X)

/-- **Corollary 1.9, base 2**: for `N ≥ 36864` there are at least
`2^(√N/72)` odd numbers `n` with `n² ≤ 2^{6N}` and `s_2(n²)` prime. -/
theorem sq_prime_digit_sum_count_two {N : ℕ} (hN : 36864 ≤ N) :
    2 ^ (Nat.sqrt N / 72) ≤ (sqPrimeDS 2 (2 ^ (6 * N))).card := by
  obtain ⟨q, hq, hqN, hq2N⟩ := Nat.exists_prime_lt_and_le_two_mul N (by omega)
  have hqlarge : 36864 ≤ q := by omega
  have hsub : sqSols 2 q ⊆ sqPrimeDS 2 (2 ^ (6 * N)) := by
    intro n hn
    obtain ⟨h1, h2, h3⟩ := (mem_sqSols (le_refl 2)).mp hn
    have hbound : (2 : ℕ) ^ (3 * q) ≤ 2 ^ (6 * N) :=
      Nat.pow_le_pow_right (by omega) (by omega)
    rw [sqPrimeDS, mem_filter, mem_range]
    have hn1 : 1 ≤ n := by
      rcases Nat.eq_zero_or_pos n with rfl | h
      · exfalso
        have h4 : Nat.gcd 0 2 = 1 := h1
        rw [Nat.gcd_zero_left] at h4
        omega
      · exact h
    have hnn : n ≤ n ^ 2 := Nat.le_self_pow (by omega) n
    exact ⟨by omega, h1, by rw [h2]; exact hq, by omega⟩
  calc 2 ^ (Nat.sqrt N / 72) ≤ 2 ^ (Nat.sqrt q / 72) :=
        Nat.pow_le_pow_right (by omega)
          (Nat.div_le_div_right (Nat.sqrt_le_sqrt (by omega)))
    _ ≤ (sqSols 2 q).card := sq_digit_sum_count_two hqlarge
    _ ≤ (sqPrimeDS 2 (2 ^ (6 * N))).card := Finset.card_le_card hsub

/-- **Corollary 1.9, base 3**: for `N ≥ 186624` there are at least
`2^(√N/108)` numbers `n` coprime to `3` with `n² ≤ 3^{6N}` and `s_3(n²)`
prime.  Every odd prime is admissible modulo `2`. -/
theorem sq_prime_digit_sum_count_three {N : ℕ} (hN : 186624 ≤ N) :
    2 ^ (Nat.sqrt N / 108) ≤ (sqPrimeDS 3 (3 ^ (6 * N))).card := by
  obtain ⟨q, hq, hqN, hq2N⟩ := Nat.exists_prime_lt_and_le_two_mul N (by omega)
  have hqlarge : 2304 * 3 ^ 4 ≤ q := by
    have h1 : (2304 : ℕ) * 3 ^ 4 = 186624 := by norm_num
    omega
  -- every odd prime is a square modulo `2`
  have hodd : q % 2 = 1 := by
    rcases Nat.Prime.eq_two_or_odd hq with h | h
    · omega
    · exact h
  have hadm : 1 ^ 2 ≡ q [MOD 3 - 1] := by
    show 1 % 2 = q % 2
    omega
  have hsub : sqSols 3 q ⊆ sqPrimeDS 3 (3 ^ (6 * N)) := by
    intro n hn
    obtain ⟨h1, h2, h3⟩ := (mem_sqSols (by omega : 2 ≤ 3)).mp hn
    have hbound : (3 : ℕ) ^ (3 * q) ≤ 3 ^ (6 * N) :=
      Nat.pow_le_pow_right (by omega) (by omega)
    rw [sqPrimeDS, mem_filter, mem_range]
    have hn1 : 1 ≤ n := by
      rcases Nat.eq_zero_or_pos n with rfl | h
      · exfalso
        have h4 : Nat.gcd 0 3 = 1 := h1
        rw [Nat.gcd_zero_left] at h4
        omega
      · exact h
    have hnn : n ≤ n ^ 2 := Nat.le_self_pow (by omega) n
    exact ⟨by omega, h1, by rw [h2]; exact hq, by omega⟩
  calc 2 ^ (Nat.sqrt N / 108) ≤ 2 ^ (Nat.sqrt q / 108) :=
        Nat.pow_le_pow_right (by omega)
          (Nat.div_le_div_right (Nat.sqrt_le_sqrt (by omega)))
    _ ≤ (sqSols 3 q).card := by
        have h := sq_digit_sum_count (b := 3) (by omega) hqlarge hadm
        have h2 : (36 : ℕ) * 3 = 108 := by norm_num
        rwa [h2] at h
    _ ≤ (sqPrimeDS 3 (3 ^ (6 * N))).card := Finset.card_le_card hsub

end DSS
