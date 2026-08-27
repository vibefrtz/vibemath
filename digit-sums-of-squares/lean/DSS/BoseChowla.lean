/-
DSS/BoseChowla.lean

**The theorem of Bose and Chowla** (Comment. Math. Helv. 37 (1962/63), 141–147),
in the form quoted by the paper's Lemma 7.1: for every prime `p` there is a
Sidon set of `p` natural numbers below `p²`.

The construction is the classical one in the field with `p²` elements: fix a
generator `θ` of `F_{p²}ˣ` and take the discrete logarithms of `θ + a` for
`a ∈ F_p`.  If two pairwise sums of logarithms agree then
`(θ+a)(θ+c) = (θ+e)(θ+f)`, and since `θ` has degree two over the prime field,
comparing coefficients forces `{a,c} = {e,f}` by Vieta.

Together with Bertrand's postulate (`Nat.exists_prime_lt_and_le_two_mul`,
in Mathlib) this gives, for every `m ≥ 1`, a Sidon set of exactly `m` elements
below `4m²` — the input the proof of Theorem 1.10 consumes.

**This file proves the quoted result inside Lean; it declares no axioms.**
-/
import DSS.Sidon

namespace DSS

open Finset

/-- Vieta: in a field, two pairs with the same sum and the same product agree
up to order. -/
lemma pair_eq_of_sum_prod {K : Type*} [Field K] {x y z w : K}
    (hs : x + y = z + w) (hp : x * y = z * w) :
    (x = z ∧ y = w) ∨ (x = w ∧ y = z) := by
  have h0 : (z - x) * (z - y) = 0 := by linear_combination (-z) * hs + hp
  rcases mul_eq_zero.mp h0 with h | h
  · left
    have hxz : z = x := by
      have := sub_eq_zero.mp h
      exact this
    constructor
    · exact hxz.symm
    · have h1 : x + y = x + w := by rw [hs, ← hxz]
      exact add_left_cancel h1
  · right
    have hyz : z = y := by
      have := sub_eq_zero.mp h
      exact this
    constructor
    · have h1 : x + y = w + y := by rw [hs, ← hyz]; ring
      exact add_right_cancel h1
    · exact hyz.symm

/-- **Bose–Chowla**: for every prime `p` there is a Sidon set of `p` natural
numbers below `p²`. -/
theorem bose_chowla (p : ℕ) (hp : p.Prime) :
    ∃ S : Finset ℕ, S ⊆ range (p ^ 2) ∧ S.card = p ∧ IsSidon S := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  set F := GaloisField p 2 with hF
  have : Finite F := by
    refine Nat.finite_of_card_ne_zero ?_
    rw [GaloisField.card p 2 (by norm_num)]
    exact pow_ne_zero 2 hp.pos.ne'
  have : Fintype F := Fintype.ofFinite F
  have hcardF : Fintype.card F = p ^ 2 := by
    have h := GaloisField.card p 2 (by norm_num)
    rwa [Nat.card_eq_fintype_card] at h
  -- a generator of the (cyclic) unit group
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Fˣ)
  have horder : orderOf g = p ^ 2 - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_units,
      Nat.card_eq_fintype_card, hcardF]
  have hp2 : 2 ≤ p := hp.two_le
  have hpsq : 4 ≤ p ^ 2 := by
    have h := Nat.pow_le_pow_left hp2 2
    simpa using h
  have hord_pos : 0 < p ^ 2 - 1 := by omega
  -- `θ = ↑g` does not lie in the prime field
  have hθ : ∀ c : ZMod p, algebraMap (ZMod p) F c ≠ (g : F) := by
    intro c hc
    have hc0 : c ≠ 0 := by
      intro h0
      rw [h0, map_zero] at hc
      exact Units.ne_zero g hc.symm
    have h1 : (g : F) ^ (p - 1) = 1 := by
      rw [← hc, ← map_pow, ZMod.pow_card_sub_one_eq_one hc0, map_one]
    have h2 : g ^ (p - 1) = 1 := by
      ext
      rw [Units.val_pow_eq_pow_val, h1, Units.val_one]
    have h3 := orderOf_dvd_of_pow_eq_one h2
    rw [horder] at h3
    have h4 : p ^ 2 - 1 ≤ p - 1 := Nat.le_of_dvd (by omega) h3
    have h5 : 2 * p ≤ p * p := Nat.mul_le_mul_right p hp2
    have h6 : p ^ 2 = p * p := by ring
    omega
  -- `θ + a` is a unit for every `a` in the prime field
  have hunit : ∀ a : ZMod p, IsUnit ((g : F) + algebraMap (ZMod p) F a) := by
    intro a
    rw [isUnit_iff_ne_zero]
    intro h0
    refine hθ (-a) ?_
    rw [map_neg]
    exact neg_eq_of_add_eq_zero_left h0
  -- discrete logarithms
  have hdl : ∀ a : ZMod p, ∃ k : ℕ, k < p ^ 2 - 1 ∧ g ^ k = (hunit a).unit := by
    intro a
    have hmem : (hunit a).unit ∈ Submonoid.powers g :=
      mem_powers_iff_mem_zpowers.mpr (hg _)
    obtain ⟨n, hn⟩ := hmem
    refine ⟨n % (p ^ 2 - 1), Nat.mod_lt _ hord_pos, ?_⟩
    rw [← horder, pow_mod_orderOf]
    exact hn
  choose f hflt hfval using hdl
  -- injectivity of the logarithm
  have hfinj : Function.Injective f := by
    intro a a' h
    have h1 : (hunit a).unit = (hunit a').unit := by
      rw [← hfval a, ← hfval a', h]
    have h2 : (g : F) + algebraMap (ZMod p) F a
        = (g : F) + algebraMap (ZMod p) F a' := by
      have h3 := congrArg Units.val h1
      rwa [IsUnit.unit_spec, IsUnit.unit_spec] at h3
    exact (algebraMap (ZMod p) F).injective (add_left_cancel h2)
  refine ⟨Finset.image f Finset.univ, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨a, _, rfl⟩ := mem_image.mp hx
    exact mem_range.mpr (by have := hflt a; omega)
  · rw [Finset.card_image_of_injective _ hfinj, Finset.card_univ, ZMod.card]
  · -- the Sidon property
    intro α hα β hβ γ hγ δ hδ hsum
    obtain ⟨x, _, rfl⟩ := mem_image.mp hα
    obtain ⟨y, _, rfl⟩ := mem_image.mp hβ
    obtain ⟨z, _, rfl⟩ := mem_image.mp hγ
    obtain ⟨w, _, rfl⟩ := mem_image.mp hδ
    -- the unit equation `(θ+x̄)(θ+ȳ) = (θ+z̄)(θ+w̄)`
    have hu : (hunit x).unit * (hunit y).unit = (hunit z).unit * (hunit w).unit := by
      rw [← hfval x, ← hfval y, ← hfval z, ← hfval w, ← pow_add, ← pow_add, hsum]
    have hFeq : ((g : F) + algebraMap (ZMod p) F x) * ((g : F) + algebraMap (ZMod p) F y)
        = ((g : F) + algebraMap (ZMod p) F z) * ((g : F) + algebraMap (ZMod p) F w) := by
      have h3 := congrArg Units.val hu
      rwa [Units.val_mul, Units.val_mul, IsUnit.unit_spec, IsUnit.unit_spec,
        IsUnit.unit_spec, IsUnit.unit_spec] at h3
    -- comparing coefficients: the sums agree …
    have hsumZ : x + y = z + w := by
      by_contra hne
      have hA : algebraMap (ZMod p) F (x + y - (z + w)) ≠ 0 := by
        intro h0
        refine hne (sub_eq_zero.mp ?_)
        exact (algebraMap (ZMod p) F).injective (by rw [h0, map_zero])
      refine hθ ((z * w - x * y) / (x + y - (z + w))) ?_
      rw [map_div₀, div_eq_iff hA]
      simp only [map_sub, map_add, map_mul]
      linear_combination -hFeq
    -- … and so do the products
    have hprodZ : x * y = z * w := by
      have h2 : algebraMap (ZMod p) F (x + y) = algebraMap (ZMod p) F (z + w) :=
        congrArg _ hsumZ
      have h1 : algebraMap (ZMod p) F (x * y) = algebraMap (ZMod p) F (z * w) := by
        simp only [map_add, map_mul] at h2 ⊢
        linear_combination hFeq - (g : F) * h2
      exact (algebraMap (ZMod p) F).injective h1
    -- Vieta
    rcases pair_eq_of_sum_prod hsumZ hprodZ with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨congrArg f h1, congrArg f h2⟩
    · exact Or.inr ⟨congrArg f h1, congrArg f h2⟩

/-- Bose–Chowla + Bertrand: for every `m ≥ 1` there is a Sidon set of exactly
`m` elements below `4m²`.  This is the form the proof of Theorem 1.10 uses. -/
theorem exists_sidon_of_card (m : ℕ) (hm : 1 ≤ m) :
    ∃ S : Finset ℕ, S ⊆ range (4 * m ^ 2) ∧ S.card = m ∧ IsSidon S := by
  obtain ⟨q, hq, hqm, hq2m⟩ := Nat.exists_prime_lt_and_le_two_mul m (by omega)
  obtain ⟨S, hSsub, hScard, hSsidon⟩ := bose_chowla q hq
  obtain ⟨T, hTS, hTcard⟩ := Finset.exists_subset_card_eq
    (show m ≤ S.card by omega)
  refine ⟨T, ?_, hTcard, hSsidon.mono hTS⟩
  intro x hx
  have h1 : x ∈ range (q ^ 2) := hSsub (hTS hx)
  have h2 : q ^ 2 ≤ 4 * m ^ 2 := by
    calc q ^ 2 ≤ (2 * m) ^ 2 := Nat.pow_le_pow_left hq2m 2
      _ = 4 * m ^ 2 := by ring
  rw [Finset.mem_range] at h1 ⊢
  omega

end DSS
