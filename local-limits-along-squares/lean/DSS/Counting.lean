/-
DSS/Counting.lean

The counting functions appearing in the local limit theorem, at a **real**
cut-off `x` (the paper evaluates the theorem at real heights — the peak
height `b^{k/μ_g}` of a target `k` is generally irrational — so integer
cut-offs would force an avoidable floor-error analysis).

Nothing in this file is conditional: it imports no axioms.
-/
import DSS.Weight

namespace DSS

open Finset

/-- The primes `≤ x`, for a real cut-off `x`. -/
noncomputable def primesLE (x : ℝ) : Finset ℕ :=
  (range (⌊x⌋₊ + 1)).filter (fun p => Nat.Prime p)

lemma mem_primesLE {x : ℝ} (hx : 0 ≤ x) {p : ℕ} :
    p ∈ primesLE x ↔ Nat.Prime p ∧ (p : ℝ) ≤ x := by
  simp only [primesLE, mem_filter, mem_range, Nat.lt_succ_iff]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h2, (Nat.le_floor_iff hx).mp h1⟩
  · rintro ⟨h1, h2⟩; exact ⟨(Nat.le_floor_iff hx).mpr h2, h1⟩

/-- `π(x)`, the number of primes `≤ x`. -/
noncomputable def picount (x : ℝ) : ℕ := (primesLE x).card

/-- `π(x) > 0` once `x ≥ 2`. -/
lemma picount_pos {x : ℝ} (hx : 2 ≤ x) : 0 < picount x := by
  have hx0 : (0 : ℝ) ≤ x := le_trans (by norm_num) hx
  refine card_pos.mpr ⟨2, ?_⟩
  exact (mem_primesLE hx0).mpr ⟨Nat.prime_two, by exact_mod_cast hx⟩

variable {b : ℕ}

/-- `#{p ≤ x : p prime, g(p) = k}`. -/
noncomputable def countEq (g : Weight b) (x : ℝ) (k : ℤ) : ℕ :=
  ((primesLE x).filter (fun p : ℕ => g.eval p = k)).card

/-- `π_k(x) = #{p ≤ x : g(1)·p ≡ k (mod d_g)}` of Theorem 3.1. -/
noncomputable def piCong (g : Weight b) (x : ℝ) (k : ℤ) : ℕ :=
  ((primesLE x).filter
    (fun p : ℕ => (g.w 1 * (p : ℤ)) % (g.dg : ℤ) = k % (g.dg : ℤ))).card

/-- When `d_g = 1` the congruence condition is vacuous, so `π_k(x) = π(x)`. -/
lemma piCong_of_dg_eq_one (g : Weight b) (hdg : g.dg = 1) (x : ℝ) (k : ℤ) :
    piCong g x k = picount x := by
  unfold piCong picount
  congr 1
  apply Finset.filter_true_of_mem
  intro p _
  simp [hdg]

/-- The primes up to `x` are partitioned by the value of `g`: summing `countEq`
over the values actually taken recovers `π(x)`.

This is the check that `countEq` counts each prime exactly once, and it is what a
reader should look at before believing the encoding of the local limit theorem. -/
theorem sum_countEq (g : Weight b) (x : ℝ) :
    ∑ k ∈ (primesLE x).image (fun p => g.eval p), countEq g x k = picount x := by
  unfold countEq picount
  refine (Finset.card_eq_sum_card_fiberwise ?_).symm
  intro p hp
  exact Finset.mem_image_of_mem _ hp

/-- Every prime with `g(p) = k` satisfies the congruence `g(1)·p ≡ k (mod d_g)`,
so `countEq` is bounded by `piCong`.

This ties the two counting functions of Theorem 3.1 together: `π_k(x)` really is
the companion of `#{p ≤ x : g(p) = k}` and not an unrelated count. -/
theorem countEq_le_piCong (g : Weight b) (x : ℝ) (k : ℤ) :
    countEq g x k ≤ piCong g x k := by
  unfold countEq piCong
  refine Finset.card_le_card ?_
  intro p hp
  rw [Finset.mem_filter] at hp ⊢
  refine ⟨hp.1, ?_⟩
  have h := g.dg_dvd_eval_sub p
  rw [hp.2] at h
  exact Int.modEq_iff_dvd.mpr h

/-- A positive count produces an actual prime with the prescribed value. -/
lemma exists_of_countEq_pos (g : Weight b) {x : ℝ} (hx : 0 ≤ x) {k : ℤ}
    (h : 0 < countEq g x k) :
    ∃ p : ℕ, Nat.Prime p ∧ (p : ℝ) ≤ x ∧ g.eval p = k := by
  obtain ⟨p, hp⟩ := card_pos.mp h
  rw [mem_filter] at hp
  obtain ⟨hp1, hp2⟩ := hp
  obtain ⟨hprime, hle⟩ := (mem_primesLE hx).mp hp1
  exact ⟨p, hprime, hle, hp2⟩

end DSS
