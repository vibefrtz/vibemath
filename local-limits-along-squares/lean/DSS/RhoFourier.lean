/-
DSS/RhoFourier.lean

**The finite Fourier identity (37).**

In the proof of Theorem 1.1 the coefficient collected from the centres of the
`d = d_g` major arcs is

  `∑_{j=0}^{d−1} η_j e(−jk/d)
     = (1/d) ∑_{r mod d} ∑_{j mod d} e(j(g(1)r² − k)/d)
     = #{r mod d : g(1)r² ≡ k (mod d)} = ρ_{g,□}(k)`,

which is exactly the statement that the lattice density of eq. (4) is the
finite Fourier transform of the arc-centre coefficients — the instance of the
general formula (46) of Proposition 4.2 that Theorem 1.1 uses.  This file
verifies that computation: the arc coefficients `η_j` are *defined* here
(`etaSq`), and `rhoSq_fourier` is the identity (37).

The only input is the orthogonality of the `d`-th roots of unity
(`sum_ee_mul_eq`), proved from the geometric sum.

Nothing in this file is conditional: it imports no axioms.
-/
import DSS.RhoSquare

namespace DSS

open Finset

/-! ### `e(t) = exp(2πit)` and root-of-unity orthogonality -/

/-- `e(t) = e^{2πit}`, the paper's additive character. -/
noncomputable def ee (t : ℝ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * (t : ℂ))

lemma ee_add (s t : ℝ) : ee (s + t) = ee s * ee t := by
  unfold ee
  rw [← Complex.exp_add]
  push_cast
  ring_nf

lemma ee_intCast (n : ℤ) : ee (n : ℝ) = 1 := by
  unfold ee
  have h : (2 : ℂ) * Real.pi * Complex.I * ((n : ℝ) : ℂ)
      = (n : ℂ) * (2 * Real.pi * Complex.I) := by push_cast; ring
  rw [h]
  exact Complex.exp_int_mul_two_pi_mul_I n

lemma ee_nat_mul (j : ℕ) (t : ℝ) : ee ((j : ℝ) * t) = ee t ^ j := by
  unfold ee
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- `e(t) = 1` exactly when `t` is an integer. -/
lemma ee_eq_one_iff (t : ℝ) : ee t = 1 ↔ ∃ n : ℤ, t = (n : ℝ) := by
  constructor
  · intro h
    obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h
    refine ⟨n, ?_⟩
    have hne : (2 : ℂ) * Real.pi * Complex.I ≠ 0 := by
      have h1 : (Real.pi : ℂ) ≠ 0 := by
        exact_mod_cast ne_of_gt Real.pi_pos
      simp [h1, Complex.I_ne_zero]
    have h2 : ((t : ℝ) : ℂ) * (2 * Real.pi * Complex.I)
        = (n : ℂ) * (2 * Real.pi * Complex.I) := by
      rw [← hn]; ring
    have h3 : ((t : ℝ) : ℂ) = (n : ℂ) := mul_right_cancel₀ hne h2
    exact_mod_cast h3
  · rintro ⟨n, rfl⟩
    exact ee_intCast n

/-- **Orthogonality of the `d`-th roots of unity:**
`∑_{j<d} e(jm/d) = d` if `d ∣ m`, and `0` otherwise. -/
theorem sum_ee_mul_eq {d : ℕ} (hd : 0 < d) (m : ℤ) :
    ∑ j ∈ range d, ee ((j : ℝ) * ((m : ℝ) / (d : ℝ)))
      = if (d : ℤ) ∣ m then (d : ℂ) else 0 := by
  have hdR : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
  have hsum : ∑ j ∈ range d, ee ((j : ℝ) * ((m : ℝ) / (d : ℝ)))
      = ∑ j ∈ range d, (ee ((m : ℝ) / (d : ℝ))) ^ j :=
    Finset.sum_congr rfl (fun j _ => ee_nat_mul j _)
  rw [hsum]
  by_cases hdvd : (d : ℤ) ∣ m
  · obtain ⟨q, rfl⟩ := hdvd
    have hq : ((d : ℤ) * q : ℝ) / (d : ℝ) = (q : ℝ) := by
      push_cast
      field_simp
    rw [show (((d : ℤ) * q : ℤ) : ℝ) / (d : ℝ) = (q : ℝ) by exact_mod_cast hq,
      ee_intCast, if_pos (dvd_mul_right (d : ℤ) q)]
    simp
  · have hne : ee ((m : ℝ) / (d : ℝ)) ≠ 1 := by
      intro h
      obtain ⟨n, hn⟩ := (ee_eq_one_iff _).mp h
      apply hdvd
      refine ⟨n, ?_⟩
      have : (m : ℝ) = (d : ℝ) * (n : ℝ) := by
        field_simp at hn
        linarith [hn]
      exact_mod_cast this
    rw [geom_sum_eq hne]
    have hpow : ee ((m : ℝ) / (d : ℝ)) ^ d = 1 := by
      rw [← ee_nat_mul]
      have : (d : ℝ) * ((m : ℝ) / (d : ℝ)) = ((m : ℤ) : ℝ) := by
        field_simp
      rw [this, ee_intCast]
    rw [hpow, if_neg hdvd]
    simp

/-! ### The identity (37) -/

variable {b : ℕ}

/-- The **arc-centre coefficients** `η_j` of the proof of Theorem 1.1 on
squares: at the major arc centred at `j/d`, `d = d_g`, the characteristic
function tends to `η_j = (1/d) ∑_{r mod d} e(j·g(1)r²/d)` (the average of the
character over the residues the congruence (3) allows on squares). -/
noncomputable def etaSq (g : Weight b) (j : ℕ) : ℂ :=
  (g.dg : ℂ)⁻¹ * ∑ r ∈ range g.dg,
    ee ((j : ℝ) * (((g.w 1 * (r : ℤ) ^ 2 : ℤ) : ℝ) / (g.dg : ℝ)))

/-- **Equation (37):** the coefficient collected from the arc centres is the
lattice density,

`∑_{j<d} η_j e(−jk/d) = #{r mod d : g(1)r² ≡ k (mod d)} = ρ_{g,□}(k)`.

This is the last step of the proof of Theorem 1.1, and the instance of the
general Fourier formula (46) of Proposition 4.2 that the theorem uses. -/
theorem rhoSq_fourier (g : Weight b) (k : ℤ) :
    ∑ j ∈ range g.dg, etaSq g j * ee (-((j : ℝ) * ((k : ℝ) / (g.dg : ℝ))))
      = (rhoSq g k : ℂ) := by
  have hd : 0 < g.dg := g.dg_pos
  have hdR : (g.dg : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
  have hdC : (g.dg : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
  have step1 : ∀ j ∈ range g.dg,
      etaSq g j * ee (-((j : ℝ) * ((k : ℝ) / (g.dg : ℝ))))
        = (g.dg : ℂ)⁻¹ * ∑ r ∈ range g.dg,
            ee ((j : ℝ) * ((((g.w 1 * (r : ℤ) ^ 2 - k : ℤ)) : ℝ) / (g.dg : ℝ))) := by
    intro j _
    unfold etaSq
    rw [mul_assoc, Finset.sum_mul]
    congr 1
    refine Finset.sum_congr rfl (fun r _ => ?_)
    rw [← ee_add]
    congr 1
    push_cast
    field_simp
    ring
  rw [Finset.sum_congr rfl step1, ← Finset.mul_sum, Finset.sum_comm]
  have step2 : ∀ r ∈ range g.dg,
      ∑ j ∈ range g.dg,
          ee ((j : ℝ) * ((((g.w 1 * (r : ℤ) ^ 2 - k : ℤ)) : ℝ) / (g.dg : ℝ)))
        = if ((g.dg : ℤ)) ∣ (g.w 1 * (r : ℤ) ^ 2 - k) then (g.dg : ℂ) else 0 :=
    fun r _ => sum_ee_mul_eq hd _
  rw [Finset.sum_congr rfl step2]
  have step3 : ∀ r ∈ range g.dg,
      (if ((g.dg : ℤ)) ∣ (g.w 1 * (r : ℤ) ^ 2 - k) then (g.dg : ℂ) else 0)
        = (g.dg : ℂ)
          * (if (g.w 1 * (r : ℤ) ^ 2) % (g.dg : ℤ) = k % (g.dg : ℤ) then (1 : ℂ) else 0) := by
    intro r _
    have hiff : ((g.dg : ℤ)) ∣ (g.w 1 * (r : ℤ) ^ 2 - k)
        ↔ (g.w 1 * (r : ℤ) ^ 2) % (g.dg : ℤ) = k % (g.dg : ℤ) := by
      constructor
      · intro h
        have h2 : (g.dg : ℤ) ∣ k - g.w 1 * (r : ℤ) ^ 2 := by
          simpa using dvd_neg.mpr h
        exact Int.modEq_iff_dvd.mpr h2
      · intro h
        have : (g.dg : ℤ) ∣ k - g.w 1 * (r : ℤ) ^ 2 := Int.ModEq.dvd h
        simpa using dvd_neg.mpr this
    by_cases hc : ((g.dg : ℤ)) ∣ (g.w 1 * (r : ℤ) ^ 2 - k)
    · rw [if_pos hc, if_pos (hiff.mp hc), mul_one]
    · rw [if_neg hc, if_neg (fun h => hc (hiff.mpr h)), mul_zero]
  rw [Finset.sum_congr rfl step3, ← Finset.mul_sum, ← mul_assoc,
    inv_mul_cancel₀ hdC, one_mul, Finset.sum_boole]
  rfl


end DSS
