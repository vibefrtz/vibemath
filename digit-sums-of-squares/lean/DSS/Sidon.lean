/-
DSS/Sidon.lean

Sidon sets of natural numbers: the definition, the closure properties used in
the proof of Lemma 7.1 (monotonicity, translation, dilation), the fact that
adjoining `0` to a Sidon set avoiding its own sumset is again Sidon, and the
two counting facts about the coefficients of `(∑_{r∈A} b^r)²` that drive the
carry-free computation of Lemma 7.2:

* each coefficient is a fiber count `#{(r,s) ∈ A² : r+s = j}`, at most `2`
  for Sidon `A`;
* the coefficients total `(#A)²`.

Nothing in this file is conditional: it imports no axioms.
-/
import DSS.Imports

namespace DSS

open Finset

/-- A finite set of naturals is a **Sidon set** if all pairwise sums are
distinct: `a + b = c + d` with all four members forces `{a, b} = {c, d}`. -/
def IsSidon (S : Finset ℕ) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, ∀ d ∈ S,
    a + b = c + d → (a = c ∧ b = d) ∨ (a = d ∧ b = c)

/-- A subset of a Sidon set is Sidon. -/
lemma IsSidon.mono {S T : Finset ℕ} (hTS : T ⊆ S) (hS : IsSidon S) : IsSidon T :=
  fun a ha b hb c hc d hd h => hS a (hTS ha) b (hTS hb) c (hTS hc) d (hTS hd) h

/-- Translation preserves the Sidon property. -/
lemma IsSidon.image_add {S : Finset ℕ} (hS : IsSidon S) (x : ℕ) :
    IsSidon (S.image (· + x)) := by
  intro a' ha' b' hb' c' hc' d' hd' h
  obtain ⟨a, ha, rfl⟩ := mem_image.mp ha'
  obtain ⟨b, hb, rfl⟩ := mem_image.mp hb'
  obtain ⟨c, hc, rfl⟩ := mem_image.mp hc'
  obtain ⟨d, hd, rfl⟩ := mem_image.mp hd'
  rcases hS a ha b hb c hc d hd (by omega) with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨by omega, by omega⟩
  · exact Or.inr ⟨by omega, by omega⟩

/-- Dilation by a positive factor preserves the Sidon property. -/
lemma IsSidon.image_mul {S : Finset ℕ} (hS : IsSidon S) {x : ℕ} (hx : 0 < x) :
    IsSidon (S.image (x * ·)) := by
  intro a' ha' b' hb' c' hc' d' hd' h
  obtain ⟨a, ha, rfl⟩ := mem_image.mp ha'
  obtain ⟨b, hb, rfl⟩ := mem_image.mp hb'
  obtain ⟨c, hc, rfl⟩ := mem_image.mp hc'
  obtain ⟨d, hd, rfl⟩ := mem_image.mp hd'
  have hsum : a + b = c + d := by
    have h' : x * (a + b) = x * (c + d) := by ring_nf; ring_nf at h; omega
    exact Nat.eq_of_mul_eq_mul_left hx h'
  rcases hS a ha b hb c hc d hd hsum with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨by rw [h1], by rw [h2]⟩
  · exact Or.inr ⟨by rw [h1], by rw [h2]⟩

/-- Adjoining `0` to a Sidon set of positive integers that avoids its own
sumset produces a Sidon set.  This is the set `T ∪ {0}` of exponents of
`a_T = 1 + ∑_{r∈T} b^r` in Lemma 7.2. -/
lemma isSidon_insert_zero {T : Finset ℕ} (hT : IsSidon T)
    (hpos : ∀ r ∈ T, 0 < r) (havoid : ∀ r ∈ T, ∀ s ∈ T, r + s ∉ T) :
    IsSidon (insert 0 T) := by
  intro a ha b hb c hc d hd h
  rcases mem_insert.mp ha with rfl | ha <;>
    rcases mem_insert.mp hb with rfl | hb <;>
    rcases mem_insert.mp hc with rfl | hc <;>
    rcases mem_insert.mp hd with rfl | hd
  -- `a = b = 0`
  · exact Or.inl ⟨rfl, rfl⟩
  · exact absurd h (by have := hpos d hd; omega)
  · exact absurd h (by have := hpos c hc; omega)
  · exact absurd h (by have := hpos c hc; have := hpos d hd; omega)
  -- `a = 0, b ∈ T`
  · exact absurd h (by have := hpos b hb; omega)
  · exact Or.inl ⟨rfl, by omega⟩
  · exact Or.inr ⟨by omega, by omega⟩
  · exact absurd (show c + d ∈ T by rw [← show (0:ℕ) + b = c + d from h]; simpa using hb)
      (havoid c hc d hd)
  -- `a ∈ T, b = 0`
  · exact absurd h (by have := hpos a ha; omega)
  · exact Or.inr ⟨by omega, rfl⟩
  · exact Or.inl ⟨by omega, rfl⟩
  · exact absurd (show c + d ∈ T by rw [← show a + (0:ℕ) = c + d from h]; simpa using ha)
      (havoid c hc d hd)
  -- `a, b ∈ T`
  · exact absurd h (by have := hpos a ha; have := hpos b hb; omega)
  · exact absurd (show a + b ∈ T by rw [show a + b = d from by omega]; exact hd)
      (havoid a ha b hb)
  · exact absurd (show a + b ∈ T by rw [show a + b = c from by omega]; exact hc)
      (havoid a ha b hb)
  · exact hT a ha b hb c hc d hd h

/-- The coefficient of `b^j` in `(∑_{r∈A} b^r)²`: the number of ordered pairs
of exponents summing to `j`. -/
def sqCoeff (A : Finset ℕ) (j : ℕ) : ℕ :=
  ((A ×ˢ A).filter (fun p => p.1 + p.2 = j)).card

lemma sqCoeff_def (A : Finset ℕ) (j : ℕ) :
    sqCoeff A j = ((A ×ˢ A).filter (fun p => p.1 + p.2 = j)).card := rfl

/-- For a Sidon set every coefficient is at most `2`: the fiber over `j` is
contained in `{(r,s), (s,r)}` for any of its members `(r,s)`. -/
lemma sqCoeff_le_two {A : Finset ℕ} (hA : IsSidon A) (j : ℕ) : sqCoeff A j ≤ 2 := by
  rw [sqCoeff_def]
  rcases Finset.eq_empty_or_nonempty ((A ×ˢ A).filter (fun p => p.1 + p.2 = j)) with h | h
  · simp [h]
  · obtain ⟨⟨r, s⟩, hrs⟩ := h
    rw [mem_filter, mem_product] at hrs
    obtain ⟨⟨hr, hs⟩, hj⟩ := hrs
    have hsub : (A ×ˢ A).filter (fun p => p.1 + p.2 = j)
        ⊆ insert (r, s) {(s, r)} := by
      rintro ⟨r', s'⟩ h'
      rw [mem_filter, mem_product] at h'
      obtain ⟨⟨hr', hs'⟩, hj'⟩ := h'
      rcases hA r' hr' s' hs' r hr s hs (by omega) with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · subst h1; subst h2; simp
      · subst h1; subst h2; simp
    calc ((A ×ˢ A).filter (fun p => p.1 + p.2 = j)).card
        ≤ (insert (r, s) ({(s, r)} : Finset (ℕ × ℕ))).card := card_le_card hsub
      _ ≤ 2 := by
          refine le_trans (card_insert_le _ _) ?_
          simp

/-- The zero coefficient: for a set of positive integers together with `0`,
the only pair summing to `0` is `(0,0)`. -/
lemma sqCoeff_insert_zero_at_zero (T : Finset ℕ) :
    sqCoeff (insert 0 T) 0 = 1 := by
  rw [sqCoeff_def]
  have : (((insert 0 T) ×ˢ (insert 0 T)).filter (fun p => p.1 + p.2 = 0))
      = {((0 : ℕ), (0 : ℕ))} := by
    ext ⟨r, s⟩
    rw [mem_filter, mem_product, mem_insert, mem_insert, mem_singleton]
    constructor
    · rintro ⟨⟨hr, hs⟩, hj⟩
      have hr0 : r = 0 := by omega
      have hs0 : s = 0 := by omega
      simp [hr0, hs0]
    · rintro h
      rw [Prod.ext_iff] at h
      obtain ⟨h1, h2⟩ := h
      subst h1; subst h2
      exact ⟨⟨Or.inl rfl, Or.inl rfl⟩, rfl⟩
  rw [this, card_singleton]

/-- The square of a power sum, coefficient by coefficient:
`(∑_{r∈A} b^r)² = ∑_{j<N} sqCoeff A j · b^j` once `N` exceeds every pairwise
sum of exponents. -/
lemma sq_sum_pow (b : ℕ) (A : Finset ℕ) (N : ℕ)
    (hN : ∀ r ∈ A, ∀ s ∈ A, r + s < N) :
    (∑ r ∈ A, b ^ r) ^ 2 = ∑ j ∈ range N, sqCoeff A j * b ^ j := by
  have hmaps : ∀ p ∈ A ×ˢ A, p.1 + p.2 ∈ range N := by
    rintro ⟨r, s⟩ hp
    rw [mem_product] at hp
    exact mem_range.mpr (hN r hp.1 s hp.2)
  calc (∑ r ∈ A, b ^ r) ^ 2
      = ∑ r ∈ A, ∑ s ∈ A, b ^ r * b ^ s := by rw [sq, Finset.sum_mul_sum]
    _ = ∑ p ∈ A ×ˢ A, b ^ (p.1 + p.2) := by
        rw [Finset.sum_product]
        exact Finset.sum_congr rfl fun r _ =>
          Finset.sum_congr rfl fun s _ => (pow_add b r s).symm
    _ = ∑ j ∈ range N, ∑ p ∈ (A ×ˢ A).filter (fun p => p.1 + p.2 = j),
          b ^ (p.1 + p.2) := (Finset.sum_fiberwise_of_maps_to hmaps _).symm
    _ = ∑ j ∈ range N, sqCoeff A j * b ^ j := by
        refine Finset.sum_congr rfl fun j _ => ?_
        have h1 : ∑ p ∈ (A ×ˢ A).filter (fun p => p.1 + p.2 = j), b ^ (p.1 + p.2)
            = ∑ _p ∈ (A ×ˢ A).filter (fun p => p.1 + p.2 = j), b ^ j :=
          Finset.sum_congr rfl fun p hp => by rw [(mem_filter.mp hp).2]
        rw [h1, Finset.sum_const, smul_eq_mul, sqCoeff_def]

/-- The coefficients of `(∑_{r∈A} b^r)²` total `(#A)²`. -/
lemma sum_sqCoeff (A : Finset ℕ) (N : ℕ) (hN : ∀ r ∈ A, ∀ s ∈ A, r + s < N) :
    ∑ j ∈ range N, sqCoeff A j = A.card ^ 2 := by
  have hmaps : ∀ p ∈ A ×ˢ A, p.1 + p.2 ∈ range N := by
    rintro ⟨r, s⟩ hp
    rw [mem_product] at hp
    exact mem_range.mpr (hN r hp.1 s hp.2)
  have h := Finset.card_eq_sum_card_fiberwise hmaps
  rw [Finset.card_product] at h
  simp only [sqCoeff_def]
  rw [← h, sq]

end DSS
