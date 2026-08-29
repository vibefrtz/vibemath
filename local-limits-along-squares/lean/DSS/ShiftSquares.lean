/-
DSS/ShiftSquares.lean

The digit-shift invariance behind the exact identity at the end of §8:

  `s_b((b·n)²) = s_b(n²)`  —  more generally `g((b·n)²) = g(n²)` for every
  strongly `b`-additive `g` —

and its consequence, verified as an **exact finite identity** over `ℚ`: for
every predicate `Q` on `ℤ`, every base `b` and every height `N`,

  `∑_{n ≤ N, b ∤ n, Q(g(n²))} 1/n
     = ∑_{n ≤ N, Q(g(n²))} 1/n − (1/b)·∑_{m ≤ N/b, Q(g(m²))} 1/m`,

the paper's `S₀(X) = S(X) − (1/10)·S(X/10)` at `b = 10` and
`Q = ` "is prime".  The identity is exact at every height, not merely
asymptotic; the kernel checks it as stated.

Nothing in this file is conditional: it imports no axioms.
-/
import DSS.Weight

namespace DSS

open Finset

variable {b : ℕ} (g : Weight b)

/-- Prepending a zero digit does not change the value: `g(b·n) = g(n)`. -/
theorem eval_base_mul (n : ℕ) : g.eval (b * n) = g.eval n := by
  have h := g.eval_add_mul 0 n g.b_pos
  simpa [g.w_zero] using h

/-- **Digit-shift invariance on squares:** `g((b·n)²) = g(n²)`. -/
theorem eval_sq_base_mul (n : ℕ) : g.eval ((b * n) ^ 2) = g.eval (n ^ 2) := by
  have h1 : (b * n) ^ 2 = b * (b * n ^ 2) := by ring
  rw [h1, eval_base_mul, eval_base_mul]

open Classical in
/-- The reciprocal sum `∑ 1/n` over `1 ≤ n ≤ N` with `Q(g(n²))`. -/
noncomputable def recipSum (Q : ℤ → Prop) (N : ℕ) : ℚ :=
  ∑ n ∈ (Icc 1 N).filter (fun n => Q (g.eval (n ^ 2))), (1 : ℚ) / n

open Classical in
/-- The same sum restricted to `b ∤ n`. -/
noncomputable def recipSumCop (Q : ℤ → Prop) (N : ℕ) : ℚ :=
  ∑ n ∈ (Icc 1 N).filter (fun n => ¬ b ∣ n ∧ Q (g.eval (n ^ 2))), (1 : ℚ) / n

open Classical in
/-- **The exact identity of §8** (there at `b = 10`):

  `S₀(N) = S(N) − (1/b)·S(⌊N/b⌋)`

for every predicate `Q`, at every height `N`.  The multiples of `b` in
`[1, N]` are exactly `b·m` for `m ∈ [1, ⌊N/b⌋]`, and the shift invariance
`g((bm)²) = g(m²)` identifies their contribution with `(1/b)·S(⌊N/b⌋)`. -/
theorem recipSum_split (Q : ℤ → Prop) (N : ℕ) :
    recipSumCop g Q N = recipSum g Q N - (1 / b) * recipSum g Q (N / b) := by
  classical
  have hb0 : 0 < b := g.b_pos
  -- the multiples of `b` inside the full sum
  have hsplit : (Icc 1 N).filter (fun n => Q (g.eval (n ^ 2)))
      = ((Icc 1 N).filter (fun n => ¬ b ∣ n ∧ Q (g.eval (n ^ 2)))) ∪
        ((Icc 1 N).filter (fun n => b ∣ n ∧ Q (g.eval (n ^ 2)))) := by
    ext n
    simp only [mem_filter, mem_union]
    tauto
  have hdisj : Disjoint
      ((Icc 1 N).filter (fun n => ¬ b ∣ n ∧ Q (g.eval (n ^ 2))))
      ((Icc 1 N).filter (fun n => b ∣ n ∧ Q (g.eval (n ^ 2)))) := by
    rw [Finset.disjoint_left]
    intro n h1 h2
    rw [mem_filter] at h1 h2
    exact h1.2.1 h2.2.1
  have hsum : recipSum g Q N
      = recipSumCop g Q N
        + ∑ n ∈ (Icc 1 N).filter (fun n => b ∣ n ∧ Q (g.eval (n ^ 2))), (1 : ℚ) / n := by
    unfold recipSum recipSumCop
    rw [hsplit, Finset.sum_union hdisj]
  -- the multiples reindex through `m ↦ b·m`
  have hbij : ∑ n ∈ (Icc 1 N).filter (fun n => b ∣ n ∧ Q (g.eval (n ^ 2))), (1 : ℚ) / n
      = ∑ m ∈ (Icc 1 (N / b)).filter (fun m => Q (g.eval (m ^ 2))), (1 : ℚ) / (b * m) := by
    apply Finset.sum_nbij' (i := fun n => n / b) (j := fun m => b * m)
    · intro n hn
      rw [mem_filter, mem_Icc] at hn ⊢
      obtain ⟨⟨hn1, hn2⟩, ⟨m, hm⟩, hQ⟩ := hn
      subst hm
      have hm1 : 1 ≤ m := by
        rcases Nat.eq_zero_or_pos m with h | h
        · subst h; omega
        · exact h
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · rw [Nat.mul_div_cancel_left _ hb0]; exact hm1
      · rw [Nat.mul_div_cancel_left _ hb0]; exact Nat.le_div_iff_mul_le hb0 |>.mpr
          (by rw [Nat.mul_comm]; exact hn2)
      · rw [Nat.mul_div_cancel_left _ hb0]
        rw [eval_sq_base_mul g m] at hQ
        exact hQ

    · intro m hm
      rw [mem_filter, mem_Icc] at hm ⊢
      obtain ⟨⟨hm1, hm2⟩, hQ⟩ := hm
      refine ⟨⟨?_, ?_⟩, ⟨m, rfl⟩, ?_⟩
      · calc 1 ≤ m := hm1
          _ ≤ b * m := Nat.le_mul_of_pos_left m hb0
      · exact (Nat.le_div_iff_mul_le hb0).mp hm2 |>.trans_eq' (by ring)
      · rw [eval_sq_base_mul g m]; exact hQ
    · intro n hn
      rw [mem_filter] at hn
      obtain ⟨_, ⟨m, hm⟩, _⟩ := hn
      subst hm
      rw [Nat.mul_div_cancel_left _ hb0]
    · intro m hm
      rw [Nat.mul_div_cancel_left _ hb0]
    · intro n hn
      rw [mem_filter] at hn
      obtain ⟨_, ⟨m, hm⟩, _⟩ := hn
      subst hm
      rw [Nat.mul_div_cancel_left _ hb0]
      push_cast
      ring
  -- extract the factor `1/b`
  have hfac : ∑ m ∈ (Icc 1 (N / b)).filter (fun m => Q (g.eval (m ^ 2))), (1 : ℚ) / (b * m)
      = (1 / b) * recipSum g Q (N / b) := by
    unfold recipSum
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m _
    have hbQ : (b : ℚ) ≠ 0 := by
      have := g.b_pos
      positivity
    field_simp
  rw [hsum, hbij, hfac]
  ring

end DSS
