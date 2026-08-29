/-
DSS/CarryFree.lean

The carry-free construction of §7.1 of the paper, for `b ≥ 3`:

* `aT b T = 1 + ∑_{r∈T} b^r`, the root of the construction;
* geometric bounds and the uniqueness of power-sum representations
  (distinct subsets give distinct roots);
* the exact digit sums `s_b(a_T²) = (t+1)²`, `s_b(a_T² − 1) = t² + 2t`,
  `s_b(2a_T − 1) = 2t + 1`;
* **Lemma 7.2** for `b ≥ 3`: `s_b((a_T·b^k − 1)²) = (b−1)k + t²`
  whenever `b^k > a_T² + 2a_T`.

The binary case of Lemma 7.2 is in `DSS/CarryFreeTwo.lean`.

Nothing in this file is conditional: it imports no axioms.
-/
import DSS.Digits
import DSS.Sidon

namespace DSS

open Finset

/-! ### Digit sums over an arbitrary support -/

/-- `sb_sum_pow` over an arbitrary support: if the coefficients are digits,
the digit sum of `∑_{j∈A} c_j b^j` is `∑_{j∈A} c_j`. -/
theorem sb_sum_over {b : ℕ} (hb : 2 ≤ b) (A : Finset ℕ) (c : ℕ → ℕ)
    (hc : ∀ j ∈ A, c j < b) :
    sb b (∑ j ∈ A, c j * b ^ j) = ∑ j ∈ A, c j := by
  obtain ⟨N, hN⟩ := A.exists_nat_subset_range
  have hc' : ∀ j, (if j ∈ A then c j else 0) < b := by
    intro j
    by_cases h : j ∈ A
    · simpa [h] using hc j h
    · simpa [h] using (show 0 < b by omega)
  have h1 : ∑ j ∈ A, c j * b ^ j
      = ∑ j ∈ range N, (if j ∈ A then c j else 0) * b ^ j := by
    rw [← Finset.sum_subset hN (fun x _ hx => by simp [hx])]
    exact Finset.sum_congr rfl fun j hj => by simp [hj]
  have h2 : ∑ j ∈ A, c j
      = ∑ j ∈ range N, (if j ∈ A then c j else 0) := by
    rw [← Finset.sum_subset hN (fun x _ hx => by simp [hx])]
    exact Finset.sum_congr rfl fun j hj => by simp [hj]
  rw [h1, h2, sb_sum_pow hb N _ hc']

/-! ### Power sums: geometric bound and uniqueness -/

/-- Geometric bound: `∑_{i<n} b^i < b^n` for `b ≥ 2`. -/
lemma sum_pow_range_lt {b : ℕ} (hb : 2 ≤ b) (n : ℕ) :
    ∑ i ∈ range n, b ^ i < b ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ]
      have h1 : b ^ n * 2 ≤ b ^ n * b := Nat.mul_le_mul_left _ hb
      have h2 : b ^ (n + 1) = b ^ n * b := by ring
      omega

/-- A power sum over `A ⊆ range n` is smaller than `b^n`. -/
lemma sum_pow_lt {b : ℕ} (hb : 2 ≤ b) {A : Finset ℕ} {n : ℕ} (hA : A ⊆ range n) :
    ∑ r ∈ A, b ^ r < b ^ n :=
  lt_of_le_of_lt (Finset.sum_le_sum_of_subset hA) (sum_pow_range_lt hb n)

/-- **Uniqueness of power-sum representations**: for `b ≥ 2`, distinct finite
sets of exponents give distinct values of `∑_{r∈A} b^r`.  This is what makes
the `binom(m,t)` subsets of the Sidon set produce distinct roots. -/
theorem sum_pow_injective {b : ℕ} (hb : 2 ≤ b) :
    ∀ N (A B : Finset ℕ), A ⊆ range N → B ⊆ range N →
      (∑ r ∈ A, b ^ r) = (∑ r ∈ B, b ^ r) → A = B := by
  intro N
  induction N with
  | zero =>
      intro A B hA hB _
      have hA' : A = ∅ := by simpa using hA
      have hB' : B = ∅ := by simpa using hB
      rw [hA', hB']
  | succ N ih =>
      intro A B hA hB hsum
      have hsub : ∀ {C : Finset ℕ}, C ⊆ range (N + 1) → N ∉ C → C ⊆ range N := by
        intro C hC hNC r hr
        have h1 := mem_range.mp (hC hr)
        have h2 : r ≠ N := fun h => hNC (h ▸ hr)
        exact mem_range.mpr (by omega)
      by_cases hNA : N ∈ A <;> by_cases hNB : N ∈ B
      · -- peel the top exponent off both sides
        have hA' : A.erase N ⊆ range N :=
          hsub ((Finset.erase_subset _ _).trans hA) (Finset.notMem_erase _ _)
        have hB' : B.erase N ⊆ range N :=
          hsub ((Finset.erase_subset _ _).trans hB) (Finset.notMem_erase _ _)
        have h1 : ∑ r ∈ A.erase N, b ^ r + b ^ N = ∑ r ∈ A, b ^ r :=
          Finset.sum_erase_add _ _ hNA
        have h2 : ∑ r ∈ B.erase N, b ^ r + b ^ N = ∑ r ∈ B, b ^ r :=
          Finset.sum_erase_add _ _ hNB
        have h3 : (∑ r ∈ A.erase N, b ^ r) = ∑ r ∈ B.erase N, b ^ r := by omega
        have h4 := ih (A.erase N) (B.erase N) hA' hB' h3
        rw [← Finset.insert_erase hNA, ← Finset.insert_erase hNB, h4]
      · -- `N ∈ A`, `N ∉ B`: the left side is too large
        exfalso
        have h1 : b ^ N ≤ ∑ r ∈ A, b ^ r :=
          Finset.single_le_sum (fun r _ => Nat.zero_le _) hNA
        have h2 : ∑ r ∈ B, b ^ r < b ^ N := sum_pow_lt hb (hsub hB hNB)
        omega
      · exfalso
        have h1 : b ^ N ≤ ∑ r ∈ B, b ^ r :=
          Finset.single_le_sum (fun r _ => Nat.zero_le _) hNB
        have h2 : ∑ r ∈ A, b ^ r < b ^ N := sum_pow_lt hb (hsub hA hNA)
        omega
      · exact ih A B (hsub hA hNA) (hsub hB hNB) hsum

/-! ### The root `a_T` -/

/-- The root of the carry-free construction: `a_T = 1 + ∑_{r∈T} b^r`,
written as a power sum over `T ∪ {0}`. -/
def aT (b : ℕ) (T : Finset ℕ) : ℕ := ∑ r ∈ insert 0 T, b ^ r

lemma aT_def (b : ℕ) (T : Finset ℕ) : aT b T = ∑ r ∈ insert 0 T, b ^ r := rfl

lemma aT_eq {b : ℕ} {T : Finset ℕ} (h0 : 0 ∉ T) :
    aT b T = 1 + ∑ r ∈ T, b ^ r := by
  rw [aT_def, Finset.sum_insert h0, pow_zero]

lemma aT_pos (b : ℕ) (T : Finset ℕ) : 0 < aT b T := by
  rw [aT_def]
  refine Finset.sum_pos' (fun r _ => Nat.zero_le _) ?_
  refine ⟨0, Finset.mem_insert_self 0 T, ?_⟩
  rcases Nat.eq_zero_or_pos b with rfl | h
  · simp
  · positivity

/-- The size of the root: `T ⊆ range M`, `M ≥ 1`, gives `a_T < b^M`. -/
lemma aT_lt {b : ℕ} (hb : 2 ≤ b) {T : Finset ℕ} {M : ℕ} (hT : T ⊆ range M)
    (hM : 0 < M) : aT b T < b ^ M := by
  refine sum_pow_lt hb ?_
  intro r hr
  rcases mem_insert.mp hr with rfl | hr
  · exact mem_range.mpr hM
  · exact hT hr

/-- Distinct subsets (not containing `0`) give distinct roots. -/
theorem aT_injective {b : ℕ} (hb : 2 ≤ b) {T₁ T₂ : Finset ℕ}
    (h0₁ : 0 ∉ T₁) (h0₂ : 0 ∉ T₂) (h : aT b T₁ = aT b T₂) : T₁ = T₂ := by
  obtain ⟨N, hN⟩ := (T₁ ∪ T₂).exists_nat_subset_range
  have hsub : ∀ {T : Finset ℕ}, T ⊆ T₁ ∪ T₂ → insert 0 T ⊆ range (N + 1) := by
    intro T hT r hr
    rcases mem_insert.mp hr with rfl | hr
    · exact mem_range.mpr (by omega)
    · exact mem_range.mpr (by have := mem_range.mp (hN (hT hr)); omega)
  have h4 := sum_pow_injective hb (N + 1) _ _
    (hsub Finset.subset_union_left) (hsub Finset.subset_union_right) h
  calc T₁ = (insert 0 T₁).erase 0 := (Finset.erase_insert h0₁).symm
    _ = (insert 0 T₂).erase 0 := by rw [h4]
    _ = T₂ := Finset.erase_insert h0₂

/-! ### The digit sums of `a_T²`, `a_T² − 1` and `2a_T − 1`, for `b ≥ 3` -/

/-- `s_b(a_T²) = (t+1)²`: the square of the root is carry-free. -/
theorem sb_aT_sq {b : ℕ} (hb : 3 ≤ b) {T : Finset ℕ} (hT : IsSidon T)
    (hpos : ∀ r ∈ T, 0 < r) (havoid : ∀ r ∈ T, ∀ s ∈ T, r + s ∉ T) :
    sb b ((aT b T) ^ 2) = (T.card + 1) ^ 2 := by
  have hb2 : 2 ≤ b := by omega
  have hA : IsSidon (insert 0 T) := isSidon_insert_zero hT hpos havoid
  obtain ⟨M, hM⟩ := (insert 0 T).exists_nat_subset_range
  have hN : ∀ r ∈ insert 0 T, ∀ s ∈ insert 0 T, r + s < 2 * M := by
    intro r hr s hs
    have h1 := mem_range.mp (hM hr)
    have h2 := mem_range.mp (hM hs)
    omega
  have h0T : 0 ∉ T := fun h => absurd (hpos 0 h) (lt_irrefl 0)
  rw [aT_def, sq_sum_pow b _ (2 * M) hN,
    sb_sum_over hb2 _ _ (fun j _ => lt_of_le_of_lt (sqCoeff_le_two hA j) (by omega)),
    sum_sqCoeff _ _ hN, Finset.card_insert_of_notMem h0T]

/-- `s_b(a_T² − 1) = t² + 2t`: removing the unit digit. -/
theorem sb_aT_sq_sub_one {b : ℕ} (hb : 3 ≤ b) {T : Finset ℕ} (hT : IsSidon T)
    (hpos : ∀ r ∈ T, 0 < r) (havoid : ∀ r ∈ T, ∀ s ∈ T, r + s ∉ T) :
    sb b ((aT b T) ^ 2 - 1) = T.card ^ 2 + 2 * T.card := by
  have hb2 : 2 ≤ b := by omega
  have hA : IsSidon (insert 0 T) := isSidon_insert_zero hT hpos havoid
  obtain ⟨M, hM⟩ := (insert 0 T).exists_nat_subset_range
  have hN : ∀ r ∈ insert 0 T, ∀ s ∈ insert 0 T, r + s < 2 * M := by
    intro r hr s hs
    have h1 := mem_range.mp (hM hr)
    have h2 := mem_range.mp (hM hs)
    omega
  have h0T : 0 ∉ T := fun h => absurd (hpos 0 h) (lt_irrefl 0)
  have hM0 : 0 < 2 * M := by
    have := mem_range.mp (hM (Finset.mem_insert_self 0 T))
    omega
  have h0mem : (0 : ℕ) ∈ range (2 * M) := mem_range.mpr hM0
  -- split off the constant coefficient, which is `1`
  have hsq : (aT b T) ^ 2
      = ∑ j ∈ (range (2 * M)).erase 0, sqCoeff (insert 0 T) j * b ^ j + 1 := by
    rw [aT_def, sq_sum_pow b _ (2 * M) hN, ← Finset.sum_erase_add _ _ h0mem,
      sqCoeff_insert_zero_at_zero]
    norm_num
  rw [hsq, Nat.add_sub_cancel,
    sb_sum_over hb2 _ _ (fun j _ => lt_of_le_of_lt (sqCoeff_le_two hA j) (by omega))]
  have hsum : ∑ j ∈ (range (2 * M)).erase 0, sqCoeff (insert 0 T) j
      + sqCoeff (insert 0 T) 0 = (T.card + 1) ^ 2 := by
    rw [Finset.sum_erase_add _ _ h0mem, sum_sqCoeff _ _ hN,
      Finset.card_insert_of_notMem h0T]
  rw [sqCoeff_insert_zero_at_zero] at hsum
  have hexp : (T.card + 1) ^ 2 = T.card ^ 2 + 2 * T.card + 1 := by ring
  omega

/-- `s_b(2a_T − 1) = 2t + 1`. -/
theorem sb_two_aT_sub_one {b : ℕ} (hb : 3 ≤ b) {T : Finset ℕ}
    (hpos : ∀ r ∈ T, 0 < r) :
    sb b (2 * aT b T - 1) = 2 * T.card + 1 := by
  have hb2 : 2 ≤ b := by omega
  have h0T : 0 ∉ T := fun h => absurd (hpos 0 h) (lt_irrefl 0)
  have hval : 2 * aT b T - 1
      = ∑ j ∈ insert 0 T, (if j = 0 then 1 else 2) * b ^ j := by
    rw [Finset.sum_insert h0T, aT_eq h0T]
    have h1 : ∑ j ∈ T, (if j = 0 then 1 else 2) * b ^ j = ∑ j ∈ T, 2 * b ^ j := by
      refine Finset.sum_congr rfl fun j hj => ?_
      have : j ≠ 0 := by have := hpos j hj; omega
      simp [this]
    have h2 : ∑ j ∈ T, 2 * b ^ j = 2 * ∑ j ∈ T, b ^ j := by
      rw [Finset.mul_sum]
    rw [h1, h2]
    norm_num
    omega
  rw [hval, sb_sum_over hb2 _ _ (fun j _ => by split <;> omega),
    Finset.sum_insert h0T]
  have h1 : ∑ j ∈ T, (if j = 0 then 1 else 2) = ∑ _j ∈ T, 2 := by
    refine Finset.sum_congr rfl fun j hj => ?_
    have : j ≠ 0 := by have := hpos j hj; omega
    simp [this]
  rw [h1, Finset.sum_const, smul_eq_mul]
  norm_num
  omega

/-- **Lemma 7.2, case `b ≥ 3`.**  For `b^k > a_T² + 2a_T`,

`s_b((a_T·b^k − 1)²) = k(b−1) + t²`,

where `t = #T`: the square decomposes into the three carry-free blocks
`a_T² − 1`, `b^k − 2a_T`, `1`, and the complement rule evaluates the middle
block exactly. -/
theorem sb_shifted_sq {b : ℕ} (hb : 3 ≤ b) {T : Finset ℕ} (hT : IsSidon T)
    (hpos : ∀ r ∈ T, 0 < r) (havoid : ∀ r ∈ T, ∀ s ∈ T, r + s ∉ T)
    {k : ℕ} (hk : (aT b T) ^ 2 + 2 * aT b T < b ^ k) :
    sb b ((aT b T * b ^ k - 1) ^ 2) = k * (b - 1) + T.card ^ 2 := by
  have hb2 : 2 ≤ b := by omega
  have hsub1 := sb_aT_sq_sub_one hb hT hpos havoid
  have hsub2 := sb_two_aT_sub_one hb hpos
  obtain ⟨a, ha⟩ : ∃ a, aT b T = a := ⟨_, rfl⟩
  rw [ha] at hk hsub1 hsub2 ⊢
  have hapos : 0 < a := ha ▸ aT_pos b T
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with rfl | h
    · exfalso
      have h1 : a ^ 2 + 2 * a < 1 := by simpa using hk
      have h2 : 0 ≤ a ^ 2 := Nat.zero_le _
      omega
    · exact h
  have hB2 : 2 ≤ b ^ k :=
    le_trans hb2 (Nat.le_self_pow (by omega) b)
  have h2a : 2 * a ≤ b ^ k := by
    have h2 : 0 ≤ a ^ 2 := Nat.zero_le _
    omega
  -- the three-block identity
  have hident : (a * b ^ k - 1) ^ 2
      = (1 + b ^ k * (b ^ k - 2 * a)) + b ^ (2 * k) * (a ^ 2 - 1) := by
    have h1 : 1 ≤ a * b ^ k := by
      have := Nat.mul_le_mul hapos (show 1 ≤ b ^ k by omega)
      omega
    have h3 : 1 ≤ a ^ 2 := Nat.one_le_pow 2 a hapos
    zify [h1, h2a, h3]
    ring
  rw [hident]
  -- the outer block: `+ b^{2k}·(a²−1)`
  have hx : 1 + b ^ k * (b ^ k - 2 * a) < b ^ (2 * k) := by
    obtain ⟨u, hu⟩ : ∃ u, b ^ k = 2 * a + u := ⟨b ^ k - 2 * a, by omega⟩
    have h5 : b ^ k - 2 * a = u := by omega
    have h6 : b ^ k * b ^ k = b ^ k * (2 * a) + b ^ k * u := by
      calc b ^ k * b ^ k = b ^ k * (2 * a + u) := congrArg (b ^ k * ·) hu
        _ = b ^ k * (2 * a) + b ^ k * u := Nat.mul_add _ _ _
    have h7 : 2 * 2 ≤ b ^ k * (2 * a) := Nat.mul_le_mul hB2 (by omega)
    have h8 : b ^ (2 * k) = b ^ k * b ^ k := by rw [two_mul, pow_add]
    rw [h5]
    omega
  rw [sb_add_pow_mul hb2 (2 * k) _ _ hx]
  -- the inner block: `1 + b^k·(b^k − 2a)`
  have h1lt : (1 : ℕ) < b ^ k := by omega
  rw [sb_add_pow_mul hb2 k 1 _ h1lt, sb_one hb2]
  -- the complement rule on the middle block
  have hcompl : sb b (b ^ k - 2 * a) + sb b (2 * a - 1) = k * (b - 1) :=
    sb_pow_sub hb2 k (2 * a) (by omega) h2a
  omega

end DSS
