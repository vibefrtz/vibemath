/-
DigSq/Happy.lean

§6.3 of the paper: the iteration in Corollary 1.6 cannot be continued
indefinitely for `g = S`.

`S` is the map defining the *happy numbers*: every orbit reaches `1` or enters
the eight-cycle `4, 16, 37, 58, 89, 145, 42, 20`.  Since `1` is not prime and
`4` lies on the cycle, no prime has all of its `S`-iterates prime — so the
restriction to finitely many steps in Corollary 1.6 is not an artifact of the
method.

Nothing in this file is conditional: it imports no axioms.
-/
import DigSq.Sharp

namespace DigSq

set_option maxRecDepth 100000

/-! ### `S` eventually decreases -/

/-- `S n ≤ 81 · (number of decimal digits of n)`, since each digit is at most `9`. -/
theorem S_le_length (n : ℕ) : S n ≤ (Nat.digits 10 n).length * 81 := by
  rw [S_def]
  have hbound : ∀ x ∈ (Nat.digits 10 n).map (fun d => d ^ 2), x ≤ 81 := by
    intro x hx
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hx
    have : d < 10 := Nat.digits_lt_base (by norm_num) hd
    have : d ≤ 9 := by omega
    calc d ^ 2 ≤ 9 ^ 2 := Nat.pow_le_pow_left this 2
      _ = 81 := by norm_num
  have h := List.sum_le_card_nsmul _ 81 hbound
  simpa using h

/-- `81 d < 10^{d-1}` for `d ≥ 4`. -/
theorem lt_pow_ten {d : ℕ} (hd : 4 ≤ d) : 81 * d < 10 ^ (d - 1) := by
  induction d with
  | zero => omega
  | succ m ih =>
      rcases Nat.lt_or_ge m 4 with hm | hm
      · have hm3 : m = 3 := by omega
        subst hm3; norm_num
      · have h := ih (by omega)
        have h10 : 10 ^ m = 10 * 10 ^ (m - 1) := by
          conv_lhs => rw [show m = (m - 1) + 1 by omega]
          rw [pow_succ]; ring
        simp only [Nat.add_sub_cancel]
        omega

/-- **§6.3:** `S n < n` once `n ≥ 244`.  (The bound is sharp in order: `S` can
be as large as `243` on three digits.) -/
theorem S_lt_self {n : ℕ} (hn : 244 ≤ n) : S n < n := by
  have hn0 : n ≠ 0 := by omega
  have hSle : S n ≤ (Nat.digits 10 n).length * 81 := S_le_length n
  rcases Nat.lt_or_ge (Nat.digits 10 n).length 4 with h4 | h4
  · have : (Nat.digits 10 n).length * 81 ≤ 243 := by
      have : (Nat.digits 10 n).length ≤ 3 := by omega
      omega
    omega
  · have hlen : (Nat.digits 10 n).length = Nat.log 10 n + 1 :=
      Nat.length_digits 10 n (by norm_num) hn0
    have hpow : 10 ^ ((Nat.digits 10 n).length - 1) ≤ n := by
      rw [hlen]
      simpa using Nat.pow_log_le_self 10 hn0
    have hlt := lt_pow_ten h4
    omega

/-! ### The eight-cycle -/

/-- The cycle of §6.3. -/
def happyCycle : Finset ℕ := {4, 16, 37, 58, 89, 145, 42, 20}

/-- The cycle is closed under `S`. -/
theorem S_mem_happyCycle : ∀ n ∈ happyCycle, S n ∈ happyCycle := by decide

/-- From anywhere on the cycle one reaches `4` within eight steps. -/
theorem exists_iterate_eq_four :
    ∀ n ∈ happyCycle, ∃ j ∈ Finset.range 8, S^[j] n = 4 := by decide

/-- Every `n ≤ 243` reaches `1` or the cycle within thirty steps. -/
theorem small_reaches :
    ∀ n ∈ Finset.Icc 1 243, ∃ m ∈ Finset.range 30,
      S^[m] n = 1 ∨ S^[m] n ∈ happyCycle := by decide

/-- **§6.3, the happy-number theorem:** every `S`-orbit reaches `1` or enters the
eight-cycle `4, 16, 37, 58, 89, 145, 42, 20`. -/
theorem reaches_one_or_cycle {n : ℕ} (hn : 1 ≤ n) :
    ∃ m : ℕ, S^[m] n = 1 ∨ S^[m] n ∈ happyCycle := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.lt_or_ge n 244 with h | h
    · obtain ⟨m, _, hm⟩ := small_reaches n (by simp; omega)
      exact ⟨m, hm⟩
    · have hlt : S n < n := S_lt_self h
      have hpos : 1 ≤ S n := by
        rcases Nat.eq_zero_or_pos (S n) with hz | hz
        · exact absurd (S_eq_zero_iff.mp hz) (by omega)
        · exact hz
      obtain ⟨m, hm⟩ := ih (S n) hlt hpos
      refine ⟨m + 1, ?_⟩
      rwa [Function.iterate_succ_apply]

/-- **§6.3:** no prime has all of its `S`-iterates prime.

The orbit of any `n ≥ 1` reaches `1` or the eight-cycle, and neither `1` nor the
cycle consists of primes: `1` is not prime, and `4` lies on the cycle.  So the
restriction to finitely many steps in Corollary 1.6 is not an artifact of the
method. -/
theorem exists_iterate_not_prime {p : ℕ} (hp : Nat.Prime p) :
    ∃ m : ℕ, ¬ Nat.Prime (S^[m] p) := by
  obtain ⟨m, hm⟩ := reaches_one_or_cycle (le_of_lt hp.one_lt)
  rcases hm with h | h
  · exact ⟨m, by rw [h]; exact Nat.not_prime_one⟩
  · obtain ⟨j, _, hj⟩ := exists_iterate_eq_four _ h
    refine ⟨j + m, ?_⟩
    rw [Function.iterate_add_apply, hj]
    decide

end DigSq
