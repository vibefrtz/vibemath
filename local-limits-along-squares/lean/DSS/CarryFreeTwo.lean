/-
DSS/CarryFreeTwo.lean

The binary case of the carry-free construction (§7.1 of the paper).  For `b = 2`
the coefficient `2` is not a digit, so the paper takes the Sidon set to consist
of **even** integers: the doubled cross terms `2·2^{r+s} = 2^{r+s+1}` then land
on odd positions, the diagonal terms `2^{2r}` on even ones, and parity together
with the Sidon property keeps all exponents distinct.

Main results, for `T` Sidon, positive, even, avoiding its own sumset:

* `s_2(a_T²) = 1 + 2t + C(t,2)`;
* the cardinality of the exponent set is `1 + 2t + C(t,2)`.

The digit sums `s_2(a_T² − 1)`, `s_2(2a_T − 1)` and the binary case of
Lemma 7.2 are derived in `DSS/Squares.lean` alongside the `b ≥ 3` case.

Nothing in this file is conditional: it imports no axioms.
-/
import DSS.CarryFree

namespace DSS

open Finset

/-- The ordered pairs of distinct exponents: `{(r,s) ∈ T² : r < s}`. -/
def pairsLT (T : Finset ℕ) : Finset (ℕ × ℕ) :=
  (T ×ˢ T).filter (fun p => p.1 < p.2)

/-- The exponent set of `a_T²` in base `2`:
`{0} ∪ (T+1) ∪ (2T) ∪ {r+s+1 : r < s ∈ T}`. -/
def expSet (T : Finset ℕ) : Finset ℕ :=
  insert 0 (T.image (· + 1) ∪ T.image (2 * ·)
    ∪ (pairsLT T).image (fun p => p.1 + p.2 + 1))

lemma mem_pairsLT {T : Finset ℕ} {p : ℕ × ℕ} :
    p ∈ pairsLT T ↔ p.1 ∈ T ∧ p.2 ∈ T ∧ p.1 < p.2 := by
  rw [pairsLT, mem_filter, mem_product]
  tauto

/-! ### The three-way decomposition of `T × T` -/

/-- The strictly-upper pairs are the swap of the strictly-lower ones. -/
lemma pairsGT_eq_image_swap (T : Finset ℕ) :
    (T ×ˢ T).filter (fun p => p.2 < p.1) = (pairsLT T).image Prod.swap := by
  ext ⟨r, s⟩
  simp only [mem_filter, mem_product, mem_image]
  constructor
  · rintro ⟨⟨hr, hs⟩, hlt⟩
    exact ⟨(s, r), mem_pairsLT.mpr ⟨hs, hr, hlt⟩, rfl⟩
  · rintro ⟨⟨x, y⟩, hxy, h⟩
    obtain ⟨hx, hy, hlt⟩ := mem_pairsLT.mp hxy
    have h1 : y = r := congrArg Prod.fst h
    have h2 : x = s := congrArg Prod.snd h
    subst h1; subst h2
    exact ⟨⟨hy, hx⟩, hlt⟩

lemma disjoint_pairsLT_pairsGT (T : Finset ℕ) :
    Disjoint (pairsLT T) ((T ×ˢ T).filter (fun p => p.2 < p.1)) := by
  rw [Finset.disjoint_left]
  rintro ⟨r, s⟩ h1 h2
  obtain ⟨_, _, h3⟩ := mem_pairsLT.mp h1
  have h4 : s < r := (mem_filter.mp h2).2
  omega

lemma diag_filter_eq_image (T : Finset ℕ) :
    (T ×ˢ T).filter (fun p => p.1 = p.2) = T.image (fun r => (r, r)) := by
  ext ⟨r, s⟩
  simp only [mem_filter, mem_product, mem_image]
  constructor
  · rintro ⟨⟨hr, _⟩, h⟩
    exact ⟨r, hr, by rw [show s = r from h.symm]⟩
  · rintro ⟨x, hx, h⟩
    have h1 : x = r := congrArg Prod.fst h
    have h2 : x = s := congrArg Prod.snd h
    subst h1
    rw [← h2]
    exact ⟨⟨hx, hx⟩, rfl⟩

lemma disjoint_diag_pairs (T : Finset ℕ) :
    Disjoint ((T ×ˢ T).filter (fun p => p.1 = p.2))
      (pairsLT T ∪ (T ×ˢ T).filter (fun p => p.2 < p.1)) := by
  rw [Finset.disjoint_left]
  rintro ⟨r, s⟩ h1 h2
  have h3 : r = s := (mem_filter.mp h1).2
  rcases Finset.mem_union.mp h2 with h4 | h4
  · have := (mem_pairsLT.mp h4).2.2
    omega
  · have := (mem_filter.mp h4).2
    omega

lemma diag_union_pairs (T : Finset ℕ) :
    (T ×ˢ T).filter (fun p => p.1 = p.2)
      ∪ (pairsLT T ∪ (T ×ˢ T).filter (fun p => p.2 < p.1)) = T ×ˢ T := by
  ext ⟨r, s⟩
  simp only [Finset.mem_union, mem_filter, mem_product, mem_pairsLT]
  constructor
  · rintro (⟨⟨hr, hs⟩, _⟩ | ⟨hr, hs, _⟩ | ⟨⟨hr, hs⟩, _⟩) <;> exact ⟨hr, hs⟩
  · rintro ⟨hr, hs⟩
    rcases Nat.lt_trichotomy r s with h | h | h
    · exact Or.inr (Or.inl ⟨hr, hs, h⟩)
    · exact Or.inl ⟨⟨hr, hs⟩, h⟩
    · exact Or.inr (Or.inr ⟨⟨hr, hs⟩, h⟩)

/-- The number of unordered pairs: `#(pairsLT T) = C(t, 2)`. -/
lemma card_pairsLT (T : Finset ℕ) : (pairsLT T).card = T.card.choose 2 := by
  have hcard : T.card * T.card
      = T.card + ((pairsLT T).card + (pairsLT T).card) := by
    calc T.card * T.card = (T ×ˢ T).card := (Finset.card_product T T).symm
      _ = ((T ×ˢ T).filter (fun p => p.1 = p.2)).card
          + (pairsLT T ∪ (T ×ˢ T).filter (fun p => p.2 < p.1)).card := by
            rw [← Finset.card_union_of_disjoint (disjoint_diag_pairs T),
              diag_union_pairs T]
      _ = T.card + ((pairsLT T).card + (pairsLT T).card) := by
            rw [diag_filter_eq_image T,
              Finset.card_image_of_injective _
                (fun x y h => congrArg Prod.fst h),
              Finset.card_union_of_disjoint (disjoint_pairsLT_pairsGT T),
              pairsGT_eq_image_swap T,
              Finset.card_image_of_injective _ Prod.swap_injective]
  have hch : T.card.choose 2 * 2 = T.card * T.card - T.card := by
    rw [Nat.choose_two_right]
    have heven : 2 ∣ T.card * (T.card - 1) := by
      rcases Nat.even_or_odd T.card with h | h
      · exact Dvd.dvd.mul_right h.two_dvd _
      · rcases Nat.eq_zero_or_pos T.card with h0 | h0
        · simp [h0]
        · have he : Even (T.card - 1) := by
            rcases h with ⟨m, hm⟩
            exact ⟨m, by omega⟩
          exact Dvd.dvd.mul_left he.two_dvd _
    rw [Nat.div_mul_cancel heven]
    rcases Nat.eq_zero_or_pos T.card with h0 | h0
    · simp [h0]
    · have h1 : T.card - 1 + 1 = T.card := by omega
      calc T.card * (T.card - 1) = T.card * (T.card - 1) + T.card - T.card := by omega
        _ = T.card * ((T.card - 1) + 1) - T.card := by rw [Nat.mul_add, mul_one]
        _ = T.card * T.card - T.card := by rw [h1]
  omega

/-! ### Disjointness of the exponent classes -/

section ExpSet

variable {T : Finset ℕ}

lemma expSet_disjoint_shift_double (heven : ∀ r ∈ T, Even r) :
    Disjoint (T.image (· + 1)) (T.image (2 * ·)) := by
  rw [Finset.disjoint_left]
  intro j h1 h2
  obtain ⟨r, hr, rfl⟩ := mem_image.mp h1
  obtain ⟨s, hs, hj⟩ := mem_image.mp h2
  obtain ⟨u, hu⟩ := heven r hr
  omega

lemma expSet_disjoint_pairs (heven : ∀ r ∈ T, Even r)
    (havoid : ∀ r ∈ T, ∀ s ∈ T, r + s ∉ T) :
    Disjoint (T.image (· + 1) ∪ T.image (2 * ·))
      ((pairsLT T).image (fun p => p.1 + p.2 + 1)) := by
  rw [Finset.disjoint_left]
  intro j h1 h2
  obtain ⟨⟨r, s⟩, hrs, hj⟩ := mem_image.mp h2
  obtain ⟨hr, hs, _⟩ := mem_pairsLT.mp hrs
  have hj' : r + s + 1 = j := hj
  rcases Finset.mem_union.mp h1 with h3 | h3
  · obtain ⟨x, hx, hj2⟩ := mem_image.mp h3
    have hxrs : x = r + s := by omega
    exact havoid r hr s hs (hxrs ▸ hx)
  · obtain ⟨x, hx, hj2⟩ := mem_image.mp h3
    obtain ⟨u, hu⟩ := heven r hr
    obtain ⟨v, hv⟩ := heven s hs
    omega

lemma zero_notMem_expSet_core (hpos : ∀ r ∈ T, 0 < r) :
    0 ∉ T.image (· + 1) ∪ T.image (2 * ·)
      ∪ (pairsLT T).image (fun p => p.1 + p.2 + 1) := by
  intro h
  rcases Finset.mem_union.mp h with h1 | h1
  · rcases Finset.mem_union.mp h1 with h2 | h2
    · obtain ⟨r, hr, hj⟩ := mem_image.mp h2
      omega
    · obtain ⟨r, hr, hj⟩ := mem_image.mp h2
      have := hpos r hr
      omega
  · obtain ⟨⟨r, s⟩, _, hj⟩ := mem_image.mp h1
    have hj' : r + s + 1 = 0 := hj
    omega

lemma pairsLT_sum_injOn (hT : IsSidon T) :
    ∀ p ∈ pairsLT T, ∀ q ∈ pairsLT T,
      p.1 + p.2 + 1 = q.1 + q.2 + 1 → p = q := by
  rintro ⟨r, s⟩ h1 ⟨r', s'⟩ h2 h
  obtain ⟨hr, hs, hrs⟩ := mem_pairsLT.mp h1
  obtain ⟨hr', hs', hrs'⟩ := mem_pairsLT.mp h2
  rcases hT r hr s hs r' hr' s' hs' (by omega) with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · rw [Prod.ext_iff]; exact ⟨ha, hb⟩
  · omega

/-! ### The binary expansion of `a_T²` -/

/-- The square of the power sum, decomposed over the diagonal and the two
triangles: `X² = ∑_{r∈T} 2^{2r} + ∑_{r<s} 2^{r+s+1}`. -/
lemma sq_sum_pow_two (T : Finset ℕ) :
    (∑ r ∈ T, 2 ^ r) * (∑ r ∈ T, 2 ^ r)
      = ∑ r ∈ T, 2 ^ (2 * r) + ∑ p ∈ pairsLT T, 2 ^ (p.1 + p.2 + 1) := by
  calc (∑ r ∈ T, 2 ^ r) * (∑ r ∈ T, 2 ^ r)
      = ∑ r ∈ T, ∑ s ∈ T, 2 ^ r * 2 ^ s := Finset.sum_mul_sum _ _ _ _
    _ = ∑ p ∈ T ×ˢ T, 2 ^ (p.1 + p.2) := by
        rw [Finset.sum_product]
        exact Finset.sum_congr rfl fun r _ =>
          Finset.sum_congr rfl fun s _ => (pow_add 2 r s).symm
    _ = ∑ p ∈ (T ×ˢ T).filter (fun p => p.1 = p.2), 2 ^ (p.1 + p.2)
        + (∑ p ∈ pairsLT T, 2 ^ (p.1 + p.2)
           + ∑ p ∈ (T ×ˢ T).filter (fun p => p.2 < p.1), 2 ^ (p.1 + p.2)) := by
        rw [← Finset.sum_union (disjoint_pairsLT_pairsGT T),
          ← Finset.sum_union (disjoint_diag_pairs T), diag_union_pairs T]
    _ = ∑ r ∈ T, 2 ^ (2 * r) + ∑ p ∈ pairsLT T, 2 ^ (p.1 + p.2 + 1) := by
        congr 1
        · rw [diag_filter_eq_image T,
            Finset.sum_image (fun x _ y _ h => congrArg Prod.fst h)]
          exact Finset.sum_congr rfl fun r _ => by
            have : r + r = 2 * r := by omega
            rw [show ((r, r) : ℕ × ℕ).1 + ((r, r) : ℕ × ℕ).2 = 2 * r from this]
        · rw [pairsGT_eq_image_swap T,
            Finset.sum_image (fun x _ y _ h => Prod.swap_injective h)]
          have hswap : ∑ p ∈ pairsLT T, 2 ^ ((p.swap).1 + (p.swap).2)
              = ∑ p ∈ pairsLT T, 2 ^ (p.1 + p.2) := by
            refine Finset.sum_congr rfl fun ⟨r, s⟩ _ => ?_
            have : ((r, s) : ℕ × ℕ).swap.1 + ((r, s) : ℕ × ℕ).swap.2 = r + s := by
              show s + r = r + s
              omega
            rw [this]
          rw [hswap, ← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun p _ => by
            rw [pow_succ]
            ring

/-- **The binary expansion of `a_T²`**: for `T` Sidon, positive, even, avoiding
its own sumset, the square is the sum of `2^j` over `expSet T`. -/
theorem aT_sq_eq_sum_expSet (hT : IsSidon T)
    (hpos : ∀ r ∈ T, 0 < r) (heven : ∀ r ∈ T, Even r)
    (havoid : ∀ r ∈ T, ∀ s ∈ T, r + s ∉ T) :
    (aT 2 T) ^ 2 = ∑ j ∈ expSet T, 2 ^ j := by
  have h0T : 0 ∉ T := fun h => absurd (hpos 0 h) (lt_irrefl 0)
  have hsum1 : ∑ j ∈ T.image (· + 1), 2 ^ j = ∑ r ∈ T, 2 ^ (r + 1) :=
    Finset.sum_image (fun x _ y _ h => by omega)
  have hsum2 : ∑ j ∈ T.image (2 * ·), 2 ^ j = ∑ r ∈ T, 2 ^ (2 * r) :=
    Finset.sum_image (fun x _ y _ h => by omega)
  have hsum3 : ∑ j ∈ (pairsLT T).image (fun p => p.1 + p.2 + 1), 2 ^ j
      = ∑ p ∈ pairsLT T, 2 ^ (p.1 + p.2 + 1) :=
    Finset.sum_image (pairsLT_sum_injOn hT)
  rw [expSet, Finset.sum_insert (zero_notMem_expSet_core hpos),
    Finset.sum_union (expSet_disjoint_pairs heven havoid),
    Finset.sum_union (expSet_disjoint_shift_double heven),
    hsum1, hsum2, hsum3, aT_eq h0T, pow_zero]
  have h2X : ∑ r ∈ T, 2 ^ (r + 1) = 2 * ∑ r ∈ T, 2 ^ r := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun r _ => by rw [pow_succ]; ring
  have hXX : (1 + ∑ r ∈ T, 2 ^ r) ^ 2
      = 1 + 2 * ∑ r ∈ T, 2 ^ r + (∑ r ∈ T, 2 ^ r) * (∑ r ∈ T, 2 ^ r) := by
    ring
  rw [hXX, sq_sum_pow_two T, h2X]
  ring

/-- The cardinality of the exponent set: `1 + 2t + C(t,2)`. -/
theorem card_expSet (hT : IsSidon T)
    (hpos : ∀ r ∈ T, 0 < r) (heven : ∀ r ∈ T, Even r)
    (havoid : ∀ r ∈ T, ∀ s ∈ T, r + s ∉ T) :
    (expSet T).card = 1 + 2 * T.card + T.card.choose 2 := by
  have hinj1 : Function.Injective (· + 1 : ℕ → ℕ) := fun x y h => by
    have h' : x + 1 = y + 1 := h
    omega
  have hinj2 : Function.Injective (2 * · : ℕ → ℕ) := fun x y h => by
    have h' : 2 * x = 2 * y := h
    omega
  rw [expSet, Finset.card_insert_of_notMem (zero_notMem_expSet_core hpos),
    Finset.card_union_of_disjoint (expSet_disjoint_pairs heven havoid),
    Finset.card_union_of_disjoint (expSet_disjoint_shift_double heven),
    Finset.card_image_of_injective _ hinj1,
    Finset.card_image_of_injective _ hinj2,
    Finset.card_image_of_injOn (fun p hp q hq h =>
      pairsLT_sum_injOn hT p (Finset.mem_coe.mp hp) q (Finset.mem_coe.mp hq) h),
    card_pairsLT]
  omega

/-- `s_2(a_T²) = 1 + 2t + C(t,2)`. -/
theorem sb_aT_sq_two (hT : IsSidon T)
    (hpos : ∀ r ∈ T, 0 < r) (heven : ∀ r ∈ T, Even r)
    (havoid : ∀ r ∈ T, ∀ s ∈ T, r + s ∉ T) :
    sb 2 ((aT 2 T) ^ 2) = 1 + 2 * T.card + T.card.choose 2 := by
  rw [aT_sq_eq_sum_expSet hT hpos heven havoid]
  have h1 : ∑ j ∈ expSet T, (2 : ℕ) ^ j = ∑ j ∈ expSet T, 1 * 2 ^ j := by
    exact Finset.sum_congr rfl fun j _ => (one_mul _).symm
  rw [h1, sb_sum_over (le_refl 2) _ _ (fun j _ => one_lt_two)]
  rw [Finset.sum_const, smul_eq_mul, mul_one,
    card_expSet hT hpos heven havoid]

/-- `s_2(a_T² − 1) = 2t + C(t,2)`. -/
theorem sb_aT_sq_sub_one_two (hT : IsSidon T)
    (hpos : ∀ r ∈ T, 0 < r) (heven : ∀ r ∈ T, Even r)
    (havoid : ∀ r ∈ T, ∀ s ∈ T, r + s ∉ T) :
    sb 2 ((aT 2 T) ^ 2 - 1) = 2 * T.card + T.card.choose 2 := by
  have h0mem : (0 : ℕ) ∈ expSet T := Finset.mem_insert_self 0 _
  have hsq : (aT 2 T) ^ 2 = ∑ j ∈ (expSet T).erase 0, 2 ^ j + 1 := by
    rw [aT_sq_eq_sum_expSet hT hpos heven havoid, ← Finset.sum_erase_add _ _ h0mem,
      pow_zero]
  rw [hsq, Nat.add_sub_cancel]
  have h1 : ∑ j ∈ (expSet T).erase 0, (2 : ℕ) ^ j
      = ∑ j ∈ (expSet T).erase 0, 1 * 2 ^ j := by
    exact Finset.sum_congr rfl fun j _ => (one_mul _).symm
  rw [h1, sb_sum_over (le_refl 2) _ _ (fun j _ => one_lt_two),
    Finset.sum_const, smul_eq_mul, mul_one, Finset.card_erase_of_mem h0mem,
    card_expSet hT hpos heven havoid]
  omega

/-- `s_2(2a_T − 1) = t + 1`. -/
theorem sb_two_aT_sub_one_two (hpos : ∀ r ∈ T, 0 < r) :
    sb 2 (2 * aT 2 T - 1) = T.card + 1 := by
  have h0T : 0 ∉ T := fun h => absurd (hpos 0 h) (lt_irrefl 0)
  have h0T1 : 0 ∉ T.image (· + 1) := by
    intro h
    obtain ⟨r, _, hj⟩ := mem_image.mp h
    omega
  have hinj1 : Function.Injective (· + 1 : ℕ → ℕ) := fun x y h => by
    have h' : x + 1 = y + 1 := h
    omega
  have himg : ∑ j ∈ T.image (· + 1), (2 : ℕ) ^ j = ∑ r ∈ T, 2 ^ (r + 1) :=
    Finset.sum_image (fun x _ y _ h => hinj1 h)
  have hval : 2 * aT 2 T - 1 = ∑ j ∈ insert 0 (T.image (· + 1)), 2 ^ j := by
    rw [Finset.sum_insert h0T1, pow_zero, himg, aT_eq h0T]
    have h2X : ∑ r ∈ T, 2 ^ (r + 1) = 2 * ∑ r ∈ T, 2 ^ r := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun r _ => by rw [pow_succ]; ring
    omega
  rw [hval]
  have h1 : ∑ j ∈ insert 0 (T.image (· + 1)), (2 : ℕ) ^ j
      = ∑ j ∈ insert 0 (T.image (· + 1)), 1 * 2 ^ j := by
    exact Finset.sum_congr rfl fun j _ => (one_mul _).symm
  rw [h1, sb_sum_over (le_refl 2) _ _ (fun j _ => one_lt_two),
    Finset.sum_const, smul_eq_mul, mul_one, Finset.card_insert_of_notMem h0T1,
    Finset.card_image_of_injective _ hinj1]

/-- **Lemma 7.2, case `b = 2`.**  For `2^k > a_T² + 2a_T`,

`s_2((a_T·2^k − 1)²) = k + C(t+1, 2)`,

where `t = #T` and `C(t+1,2) = t(t+1)/2`. -/
theorem sb_shifted_sq_two (hT : IsSidon T)
    (hpos : ∀ r ∈ T, 0 < r) (heven : ∀ r ∈ T, Even r)
    (havoid : ∀ r ∈ T, ∀ s ∈ T, r + s ∉ T)
    {k : ℕ} (hk : (aT 2 T) ^ 2 + 2 * aT 2 T < 2 ^ k) :
    sb 2 ((aT 2 T * 2 ^ k - 1) ^ 2) = k + (T.card + 1).choose 2 := by
  have hsub1 := sb_aT_sq_sub_one_two hT hpos heven havoid
  have hsub2 := sb_two_aT_sub_one_two hpos
  obtain ⟨a, ha⟩ : ∃ a, aT 2 T = a := ⟨_, rfl⟩
  rw [ha] at hk hsub1 hsub2 ⊢
  have hapos : 0 < a := ha ▸ aT_pos 2 T
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with rfl | h
    · exfalso
      have h1 : a ^ 2 + 2 * a < 1 := by simpa using hk
      have h2 : 0 ≤ a ^ 2 := Nat.zero_le _
      omega
    · exact h
  have hB2 : 2 ≤ 2 ^ k := Nat.le_self_pow (by omega) 2
  have h2a : 2 * a ≤ 2 ^ k := by
    have h2 : 0 ≤ a ^ 2 := Nat.zero_le _
    omega
  have hident : (a * 2 ^ k - 1) ^ 2
      = (1 + 2 ^ k * (2 ^ k - 2 * a)) + 2 ^ (2 * k) * (a ^ 2 - 1) := by
    have h1 : 1 ≤ a * 2 ^ k := by
      have := Nat.mul_le_mul hapos (show 1 ≤ 2 ^ k by omega)
      omega
    have h3 : 1 ≤ a ^ 2 := Nat.one_le_pow 2 a hapos
    zify [h1, h2a, h3]
    ring
  rw [hident]
  have hx : 1 + 2 ^ k * (2 ^ k - 2 * a) < 2 ^ (2 * k) := by
    obtain ⟨u, hu⟩ : ∃ u, 2 ^ k = 2 * a + u := ⟨2 ^ k - 2 * a, by omega⟩
    have h5 : 2 ^ k - 2 * a = u := by omega
    have h6 : 2 ^ k * 2 ^ k = 2 ^ k * (2 * a) + 2 ^ k * u := by
      calc 2 ^ k * 2 ^ k = 2 ^ k * (2 * a + u) := congrArg (2 ^ k * ·) hu
        _ = 2 ^ k * (2 * a) + 2 ^ k * u := Nat.mul_add _ _ _
    have h7 : 2 * 2 ≤ 2 ^ k * (2 * a) := Nat.mul_le_mul hB2 (by omega)
    have h8 : 2 ^ (2 * k) = 2 ^ k * 2 ^ k := by rw [two_mul, pow_add]
    rw [h5]
    omega
  rw [sb_add_pow_mul (le_refl 2) (2 * k) _ _ hx]
  have h1lt : (1 : ℕ) < 2 ^ k := by omega
  rw [sb_add_pow_mul (le_refl 2) k 1 _ h1lt, sb_one (le_refl 2)]
  have hcompl : sb 2 (2 ^ k - 2 * a) + sb 2 (2 * a - 1) = k * (2 - 1) :=
    sb_pow_sub (le_refl 2) k (2 * a) (by omega) h2a
  have hpascal : (T.card + 1).choose 2 = T.card + T.card.choose 2 := by
    rw [Nat.choose_succ_succ' T.card 1, Nat.choose_one_right]
  omega

end ExpSet

end DSS
