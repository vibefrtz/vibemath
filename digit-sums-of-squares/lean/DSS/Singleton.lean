/-
DSS/Singleton.lean

The one-parameter family of Remark 7.3: whenever `b^k > 4`,

  `s_b((2·b^k − 1)²) = (b−1)k + 1`,

from `(2b^k−1)² = 3·b^{2k} + (b^k−4)·b^k + 1` and the complement rule.
Feeding the progression `(b−1)k + 1` to Dirichlet's theorem on primes in
arithmetic progressions (`Nat.forall_exists_prime_gt_and_modEq`, in Mathlib)
yields, **unconditionally and with no axioms**:

  for every base `b ≥ 2` there are infinitely many `n` coprime to `b`
  whose square has prime digit sum.

Nothing in this file is conditional: it imports no axioms.
-/
import DSS.Digits

namespace DSS

open Finset

/-- Roots of the form `a·b^k − 1` with `k ≥ 1` are coprime to the base:
any common prime divisor of `b` would divide both `a·b^k` and its
predecessor. -/
lemma coprime_shifted {b a k : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (hk : 1 ≤ k) :
    Nat.Coprime (a * b ^ k - 1) b := by
  have hpow : 1 ≤ b ^ k := Nat.one_le_pow _ _ hb
  have h1 : 1 ≤ a * b ^ k := le_trans hpow (Nat.le_mul_of_pos_left _ ha)
  have hd := Nat.gcd_dvd_left (a * b ^ k - 1) b
  have hb' := Nat.gcd_dvd_right (a * b ^ k - 1) b
  have h2 : Nat.gcd (a * b ^ k - 1) b ∣ b ^ k := dvd_pow hb' (by omega)
  have h3 : Nat.gcd (a * b ^ k - 1) b ∣ a * b ^ k := Dvd.dvd.mul_left h2 a
  have h4 : Nat.gcd (a * b ^ k - 1) b ∣ 1 := by
    have h6 := Nat.dvd_sub h3 hd
    have h5 : a * b ^ k - (a * b ^ k - 1) = 1 := by omega
    rwa [h5] at h6
  exact Nat.dvd_one.mp h4

/-- **The singleton identity** (Remark 7.3): for `b^k ≥ 5`,
`s_b((2·b^k − 1)²) = k(b−1) + 1`. -/
theorem sb_singleton {b k : ℕ} (hb : 2 ≤ b) (hk : 5 ≤ b ^ k) :
    sb b ((2 * b ^ k - 1) ^ 2) = k * (b - 1) + 1 := by
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with rfl | h
    · simp at hk
    · exact h
  -- the three blocks: `(2B−1)² = 1 + (B−4)·B + 3·B²`
  have hident : (2 * b ^ k - 1) ^ 2
      = (1 + b ^ k * (b ^ k - 4)) + b ^ (2 * k) * 3 := by
    have h1 : 1 ≤ 2 * b ^ k := by omega
    have h4 : 4 ≤ b ^ k := by omega
    zify [h1, h4]
    ring
  rw [hident]
  -- the inner block is below `b^{2k}`
  have hx : 1 + b ^ k * (b ^ k - 4) < b ^ (2 * k) := by
    obtain ⟨u, hu⟩ : ∃ u, b ^ k = 4 + u := ⟨b ^ k - 4, by omega⟩
    have h5 : b ^ k - 4 = u := by omega
    have h6 : b ^ k * b ^ k = b ^ k * 4 + b ^ k * u := by
      calc b ^ k * b ^ k = b ^ k * (4 + u) := congrArg (b ^ k * ·) hu
        _ = b ^ k * 4 + b ^ k * u := Nat.mul_add _ _ _
    have h7 : 5 * 1 ≤ b ^ k * 4 := by
      have := Nat.mul_le_mul hk (show 1 ≤ 4 by omega)
      omega
    have h8 : b ^ (2 * k) = b ^ k * b ^ k := by rw [two_mul, pow_add]
    rw [h5]
    omega
  rw [sb_add_pow_mul hb (2 * k) _ _ hx]
  have h1lt : (1 : ℕ) < b ^ k := by omega
  rw [sb_add_pow_mul hb k 1 _ h1lt, sb_one hb]
  -- the complement rule on the middle block, with `c = 4`
  have hcompl : sb b (b ^ k - 4) + sb b 3 = k * (b - 1) := by
    have h := sb_pow_sub hb k 4 (by omega) (by omega)
    simpa using h
  omega

/-- **Infinitely many squares with prime digit sum** (Remark 7.3 together with
Dirichlet's theorem): for every base `b ≥ 2` there are infinitely many `n`
coprime to `b` such that `s_b(n²)` is prime.

This is unconditional: Dirichlet's theorem on primes in arithmetic
progressions is part of Mathlib. -/
theorem infinite_coprime_sq_prime_digit_sum (b : ℕ) (hb : 2 ≤ b) :
    {n : ℕ | Nat.Coprime n b ∧ Nat.Prime (sb b (n ^ 2))}.Infinite := by
  refine Set.infinite_of_forall_exists_gt fun N => ?_
  -- a prime `ℓ ≡ 1 (mod b−1)` beyond `(b−1)(N+3) + 1`
  obtain ⟨ℓ, hℓgt, hℓp, hℓmod⟩ :=
    Nat.forall_exists_prime_gt_and_modEq ((b - 1) * (N + 4) + 1)
      (q := b - 1) (a := 1) (by omega) (Nat.coprime_one_left _)
  have hdvd : (b - 1) ∣ ℓ - 1 :=
    (Nat.modEq_iff_dvd' (by omega : 1 ≤ ℓ)).mp hℓmod.symm
  obtain ⟨k, hkval⟩ := hdvd
  -- the parameter `k` is large
  have hkN : N + 4 ≤ k := by
    have h1 : (b - 1) * (N + 4) < (b - 1) * k := by omega
    exact le_of_lt (lt_of_mul_lt_mul_left h1 (Nat.zero_le _))
  have hbk : k + 1 ≤ b ^ k := Nat.lt_pow_self (by omega : 1 < b)
  have hbk5 : 5 ≤ b ^ k := by omega
  refine ⟨2 * b ^ k - 1, ⟨coprime_shifted (by omega) (by omega) (by omega), ?_⟩, ?_⟩
  · rw [sb_singleton hb hbk5]
    have : k * (b - 1) + 1 = ℓ := by
      have := hkval
      have hcomm : (b - 1) * k = k * (b - 1) := Nat.mul_comm _ _
      omega
    rwa [this]
  · omega

end DSS
