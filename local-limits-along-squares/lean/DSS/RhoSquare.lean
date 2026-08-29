/-
DSS/RhoSquare.lean

The lattice density on squares, eq. (4) of the paper:

  `ρ_{g,□}(k) = #{r mod d_g : g(1)·r² ≡ k (mod d_g)}`,

and the counting identities the output-sieve section consumes:

* `rhoSq_dg_one` — for `d_g = 1` the factor is identically `1` (the situation of
  the `P₂` theorem on squares);
* `sum_rhoSq` — the normalisation `∑_{k mod d} ρ_{g,□}(k) = d` (eq. (40): the
  lattice factor redistributes, rather than changes, the Gaussian mass), used in
  the proof of Theorem 1.2;
* `sum_rhoSq_coprime` — `∑_{(k,d)=1} ρ_{g,□}(k) = φ(d)`, i.e. `κ_{ρ_{g,□}} = 1`:
  the paper's "the congruence rigidity imposes no penalty", the constant of
  Corollary 1.4, computed in §8;
* `coprime_eval_sq_iff` — `(n, d_g) = 1 ↔ (g(n²), d_g) = 1`, the equivalence
  used for the restricted density `ρ♯` in the proof of Theorem 1.2.

Nothing in this file is conditional: it imports no axioms.
-/
import DSS.Counting

namespace DSS

open Finset

variable {b : ℕ} (g : Weight b)

/-- `ρ_{g,□}(k) = #{0 ≤ r < d_g : g(1)·r² ≡ k (mod d_g)}`, eq. (4).  The
congruence is encoded by `Int.emod`, exactly as in `piCong`. -/
def rhoSq (k : ℤ) : ℕ :=
  ((range g.dg).filter
    (fun r : ℕ => (g.w 1 * (r : ℤ) ^ 2) % (g.dg : ℤ) = k % (g.dg : ℤ))).card

lemma rhoSq_def (k : ℤ) :
    rhoSq g k = ((range g.dg).filter
      (fun r : ℕ => (g.w 1 * (r : ℤ) ^ 2) % (g.dg : ℤ) = k % (g.dg : ℤ))).card := rfl

/-- For `d_g = 1` the lattice factor is identically `1`. -/
theorem rhoSq_dg_one (hdg : g.dg = 1) (k : ℤ) : rhoSq g k = 1 := by
  unfold rhoSq
  rw [hdg]
  norm_num

/-- `ρ_{g,□}` is `d_g`-periodic. -/
theorem rhoSq_periodic (k : ℤ) : rhoSq g (k + g.dg) = rhoSq g k := by
  have hmod : (k + (g.dg : ℤ)) % (g.dg : ℤ) = k % (g.dg : ℤ) := by
    have : k + (g.dg : ℤ) = k + (g.dg : ℤ) * 1 := by ring
    rw [this, Int.add_mul_emod_self_left]
  unfold rhoSq
  congr 1
  apply Finset.filter_congr
  intro r _
  rw [hmod]

/-- The value class of `r`, as a natural number below `d_g`. -/
private def sqClass (r : ℕ) : ℕ := ((g.w 1 * (r : ℤ) ^ 2) % (g.dg : ℤ)).toNat

private lemma sqClass_lt (r : ℕ) : sqClass g r < g.dg := by
  have hd : (0 : ℤ) < (g.dg : ℤ) := by exact_mod_cast g.dg_pos
  have h1 : 0 ≤ (g.w 1 * (r : ℤ) ^ 2) % (g.dg : ℤ) := Int.emod_nonneg _ (ne_of_gt hd)
  have h2 : (g.w 1 * (r : ℤ) ^ 2) % (g.dg : ℤ) < (g.dg : ℤ) := Int.emod_lt_of_pos _ hd
  unfold sqClass
  omega

private lemma sqClass_spec {r k : ℕ} (hk : k < g.dg) :
    ((g.w 1 * (r : ℤ) ^ 2) % (g.dg : ℤ) = (k : ℤ) % (g.dg : ℤ)) ↔ sqClass g r = k := by
  have hd : (0 : ℤ) < (g.dg : ℤ) := by exact_mod_cast g.dg_pos
  have h1 : 0 ≤ (g.w 1 * (r : ℤ) ^ 2) % (g.dg : ℤ) := Int.emod_nonneg _ (ne_of_gt hd)
  have hkk : (k : ℤ) % (g.dg : ℤ) = (k : ℤ) := Int.emod_eq_of_lt (by positivity)
    (by exact_mod_cast hk)
  unfold sqClass
  omega

/-- **Normalisation, eq. (40):** `∑_{k mod d_g} ρ_{g,□}(k) = d_g`.  Each residue
`r` lands in exactly one value class, so the fibers partition `{0, …, d_g - 1}`.
This is the identity behind "the lattice factor redistributes, rather than
changes, the total Gaussian mass" (proof of Theorem 1.2). -/
theorem sum_rhoSq : ∑ k ∈ range g.dg, rhoSq g (k : ℤ) = g.dg := by
  have h := Finset.card_eq_sum_card_fiberwise
    (f := sqClass g) (s := range g.dg) (t := range g.dg)
    (fun r _ => mem_range.mpr (sqClass_lt g r))
  rw [card_range] at h
  calc ∑ k ∈ range g.dg, rhoSq g (k : ℤ)
      = ∑ k ∈ range g.dg, ((range g.dg).filter (fun r => sqClass g r = k)).card := by
        apply Finset.sum_congr rfl
        intro k hk
        unfold rhoSq
        congr 1
        apply Finset.filter_congr
        intro r _
        exact sqClass_spec g (mem_range.mp hk)
    _ = g.dg := h.symm

section Coprime

variable {g}

private lemma int_gcd_add_mul (c t : ℤ) (d : ℕ) :
    Int.gcd (c + (d : ℤ) * t) d = Int.gcd c d := by
  have h1 : Int.gcd (c + (d : ℤ) * t) d = Int.gcd d (c + (d : ℤ) * t) :=
    Int.gcd_comm _ _
  have h2 : Int.gcd d (c + (d : ℤ) * t) = Int.gcd d c := by
    have he : c + (d : ℤ) * t = c + t * (d : ℤ) := by ring
    rw [he]
    exact Int.gcd_add_mul_right_right d c t
  rw [h1, h2, Int.gcd_comm]

private lemma gcd_of_cong {a c : ℤ} (h : a % (g.dg : ℤ) = c % (g.dg : ℤ)) :
    Int.gcd a g.dg = Int.gcd c g.dg := by
  obtain ⟨t, ht⟩ : ((g.dg : ℤ)) ∣ a - c := Int.ModEq.dvd (Int.ModEq.symm h)
  have hac : a = c + (g.dg : ℤ) * t := by linarith
  rw [hac, int_gcd_add_mul]

/-- Under (1), `g(1)·r²` is a reduced residue exactly when `r` is. -/
private lemma gcd_w1_sq (hg : g.Coprime₁) (r : ℕ) :
    Int.gcd (g.w 1 * (r : ℤ) ^ 2) g.dg = 1 ↔ Nat.Coprime r g.dg := by
  have hw1 : Nat.Coprime (g.w 1).natAbs g.dg := Weight.coprime_w_one_dg hg
  have h1 : Int.gcd (g.w 1 * (r : ℤ) ^ 2) g.dg
      = Nat.gcd ((g.w 1).natAbs * (r ^ 2)) g.dg := by
    have hc : ((r : ℤ) ^ 2) = ((r ^ 2 : ℕ) : ℤ) := by push_cast; ring
    rw [hc]
    simp [Int.gcd, Int.natAbs_mul]
  rw [h1]
  have h2 : Nat.gcd ((g.w 1).natAbs * (r ^ 2)) g.dg = Nat.gcd (r ^ 2) g.dg :=
    Nat.Coprime.gcd_mul_left_cancel _ hw1
  rw [h2]
  constructor
  · intro h
    have hsq : Nat.Coprime (r ^ 2) g.dg := h
    exact Nat.Coprime.coprime_dvd_left (dvd_pow_self r two_ne_zero) hsq
  · intro h
    exact Nat.Coprime.pow_left 2 h

end Coprime

/-- **`κ_{ρ_{g,□}} = 1`:** the reduced classes carry total lattice mass
`φ(d_g)`, i.e.

  `∑_{k mod d_g, (k,d_g)=1} ρ_{g,□}(k) = φ(d_g)`.

This is the computation in the proof of Corollary 1.4 (§8): since
`(g(1), d_g) = 1`, the map `r ↦ g(1)·r²` sends reduced residues to reduced
residues and only reduced residues to reduced targets, so the reduced fibers
partition the reduced residues.  It is the reason no local factor appears in
the Mertens asymptotic for prime values of `g(n²)`. -/
theorem sum_rhoSq_coprime (hg : g.Coprime₁) :
    ∑ k ∈ (range g.dg).filter (fun k => Nat.Coprime k g.dg), rhoSq g (k : ℤ)
      = Nat.totient g.dg := by
  classical
  -- the reduced residues, as a subset of `range d_g`
  have htot : Nat.totient g.dg
      = ((range g.dg).filter (fun r => Nat.Coprime r g.dg)).card := by
    rw [Nat.totient]
    congr 1
    apply Finset.filter_congr
    intro r _
    simp [Nat.coprime_comm, Nat.Coprime]
  rw [htot]
  -- fiberwise counting over the value-class map, restricted to reduced residues
  have hmap : ∀ r ∈ (range g.dg).filter (fun r => Nat.Coprime r g.dg),
      sqClass g r ∈ (range g.dg).filter (fun k => Nat.Coprime k g.dg) := by
    intro r hr
    rw [mem_filter] at hr ⊢
    refine ⟨mem_range.mpr (sqClass_lt g r), ?_⟩
    -- the class of `r` is congruent to `g(1)r²`, hence reduced
    have hcong : ((sqClass g r : ℕ) : ℤ) % (g.dg : ℤ)
        = (g.w 1 * (r : ℤ) ^ 2) % (g.dg : ℤ) := by
      have := (sqClass_spec g (sqClass_lt g r) (r := r)).mpr rfl
      exact this.symm
    have h1 : Int.gcd ((sqClass g r : ℕ) : ℤ) g.dg
        = Int.gcd (g.w 1 * (r : ℤ) ^ 2) g.dg := gcd_of_cong hcong
    have h2 : Int.gcd (g.w 1 * (r : ℤ) ^ 2) g.dg = 1 :=
      (gcd_w1_sq hg r).mpr hr.2
    have h3 : Int.gcd ((sqClass g r : ℕ) : ℤ) g.dg = Nat.gcd (sqClass g r) g.dg :=
      Int.gcd_natCast_natCast _ _
    rw [h3, h2] at h1
    exact h1
  have h := Finset.card_eq_sum_card_fiberwise hmap
  rw [h]
  apply Finset.sum_congr rfl
  intro k hk
  rw [mem_filter] at hk
  obtain ⟨hk1, hk2⟩ := hk
  unfold rhoSq
  congr 1
  ext r
  simp only [mem_filter, mem_range]
  constructor
  · rintro ⟨hr, hcong⟩
    -- congruent to a reduced target forces `r` reduced
    have h1 : Int.gcd (g.w 1 * (r : ℤ) ^ 2) g.dg = Int.gcd ((k : ℕ) : ℤ) g.dg :=
      gcd_of_cong hcong
    have h2 : Int.gcd ((k : ℕ) : ℤ) g.dg = Nat.gcd k g.dg := Int.gcd_natCast_natCast _ _
    rw [h2] at h1
    have h3 : Int.gcd (g.w 1 * (r : ℤ) ^ 2) g.dg = 1 := by rw [h1]; exact hk2
    have h4 : Nat.Coprime r g.dg := (gcd_w1_sq hg r).mp h3
    exact ⟨⟨hr, h4⟩, (sqClass_spec g (mem_range.mp hk1)).mp hcong⟩
  · rintro ⟨⟨hr, _⟩, hclass⟩
    exact ⟨hr, (sqClass_spec g (mem_range.mp hk1)).mpr hclass⟩

/-- **The restriction equivalence of Theorem 1.2:** `(n, d_g) = 1` if and only
if `(g(n²), d_g) = 1`.  From the congruence (3): `g(n²) ≡ g(1)·n² (mod d_g)`,
and `(g(1), d_g) = 1`. -/
theorem coprime_eval_sq_iff (hg : g.Coprime₁) (n : ℕ) :
    Nat.Coprime n g.dg ↔ Int.gcd (g.eval (n ^ 2)) g.dg = 1 := by
  have hcong := g.dg_dvd_eval_sub (n ^ 2)
  -- `g(n²) = g(1)·n² + d_g·t`
  obtain ⟨t, ht⟩ := hcong
  have heval : g.eval (n ^ 2) = g.w 1 * ((n ^ 2 : ℕ) : ℤ) + (g.dg : ℤ) * t := by
    linarith
  have hcast : ((n ^ 2 : ℕ) : ℤ) = (n : ℤ) ^ 2 := by push_cast; ring
  have h1 : Int.gcd (g.eval (n ^ 2)) g.dg = Int.gcd (g.w 1 * (n : ℤ) ^ 2) g.dg := by
    rw [heval, hcast]
    exact int_gcd_add_mul _ _ _
  rw [h1]
  exact (gcd_w1_sq hg n).symm

end DSS
