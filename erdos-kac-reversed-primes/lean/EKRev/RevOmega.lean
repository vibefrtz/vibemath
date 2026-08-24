/-
EKRev/RevOmega.lean

**Lemma 4.5** (with Lemma 4.2(ii) and Lemma 4.1 as ingredients):
`∑_{p∈𝒫_{λ,i}} (Ω(R_λ(p)) - ω(R_λ(p))) ≪ π_{λ,i}`.

Structure of the proof (following §4.2, with the identity of Lemma 3.3(iii)):
after transporting to `∑_{p ∈ 𝒫_λ}` and applying `sum_excess_eq`, the
prime-power moduli `ℓ^m` are split into four classes:

* `ℓ^m > b^{ξλ}`: the trivial bound (4.2) (`card_dvd_rev_le`) plus
  `ℓ^{-(m-1)} ≤ b^{-ξλ/2}` and the crude Mertens bound;
* `ℓ^m ≤ b^{ξλ}` (which forces `2m ≤ λ` since `ξ ≤ log 2/(4 log b)`), and
  - `ℓ ∣ b²-1`: the count is zero for `λ ≥ 3`, by Lemma 4.1
    (`rev_coprime_sq_sub_one`);
  - `ℓ ∣ b`: the leading-block argument of Lemma 4.2(ii): the condition
    `ℓ^m ∣ R_λ(p)` depends only on the top `m` digits of `p`
    (`rev_modEq_top_block`), the number of admissible blocks is
    `≤ b^m ℓ^{-m} + 1` (`card_blocks_le`, using that reversal permutes the
    blocks), and each block carries `≪ b^{λ-m}/λ` primes by
    Brun–Titchmarsh (`count_block_le`);
  - `ℓ ∤ b(b²-1)`: the level of distribution, summed over the `b-1`
    leading digits (`PLam_filter_card_eq_sum` and [DRS, Thm. 1.3]).

Fully proved from the axioms of `Cited.lean`.
-/
import Mathlib.Tactic
import EKRev.RevHyp

namespace EKRev

open Finset Filter Real Topology

variable {b i lam m ℓ : ℕ} {ξ : ℝ}

/-! ### The top-block congruence (proof of Lemma 4.2(ii)) -/

/-- Modulo `b^m`, the reversal of a `λ`-digit block depends only on the top
`m` digits: `R_λ(n) ≡ R_m(⌊n/b^{λ-m}⌋) (mod b^m)`. -/
lemma rev_modEq_top_block (hm : m ≤ lam) (n : ℕ) :
    rev b lam n ≡ rev b m (n / b ^ (lam - m)) [MOD b ^ m] := by
  have hdisj : Disjoint (Finset.range (lam - m)) (Finset.Ico (lam - m) lam) := by
    refine Finset.disjoint_left.mpr fun j hj1 hj2 => ?_
    rw [Finset.mem_range] at hj1
    rw [Finset.mem_Ico] at hj2
    omega
  have h2 : ∑ j ∈ Finset.Ico (lam - m) lam, digit b n j * b ^ (lam - 1 - j)
      = rev b m (n / b ^ (lam - m)) := by
    unfold rev
    rw [Finset.sum_Ico_eq_sum_range]
    have hcount : lam - (lam - m) = m := by omega
    rw [hcount]
    refine Finset.sum_congr rfl fun r hr => ?_
    rw [Finset.mem_range] at hr
    have hexp : lam - 1 - (lam - m + r) = m - 1 - r := by omega
    rw [digit_div_pow, hexp]
  have hLHS : rev b lam n
      = (∑ j ∈ Finset.range (lam - m), digit b n j * b ^ (lam - 1 - j))
        + ∑ j ∈ Finset.Ico (lam - m) lam, digit b n j * b ^ (lam - 1 - j) := by
    unfold rev
    rw [← Finset.sum_union hdisj]
    congr 1
    rw [Finset.range_eq_Ico, Finset.range_eq_Ico,
      Finset.Ico_union_Ico_eq_Ico (Nat.zero_le _) (by omega)]
  rw [hLHS, ← h2]
  have h1 : b ^ m ∣ ∑ j ∈ Finset.range (lam - m),
      digit b n j * b ^ (lam - 1 - j) := by
    refine Finset.dvd_sum fun j hj => ?_
    rw [Finset.mem_range] at hj
    exact Dvd.dvd.mul_left (pow_dvd_pow b (by omega : m ≤ lam - 1 - j)) _
  have h3 := (Nat.modEq_zero_iff_dvd).mpr h1
  calc (∑ j ∈ Finset.range (lam - m), digit b n j * b ^ (lam - 1 - j))
        + ∑ j ∈ Finset.Ico (lam - m) lam, digit b n j * b ^ (lam - 1 - j)
      ≡ 0 + ∑ j ∈ Finset.Ico (lam - m) lam, digit b n j * b ^ (lam - 1 - j)
        [MOD b ^ m] := Nat.ModEq.add_right _ h3
    _ = ∑ j ∈ Finset.Ico (lam - m) lam, digit b n j * b ^ (lam - 1 - j) :=
        zero_add _

/-- The number of admissible top blocks: since reversal permutes
`{0,…,b^m-1}`, `#{t < b^m : D ∣ R_m(t)} = #{u < b^m : D ∣ u} ≤ b^m/D + 1`. -/
lemma card_blocks_le (hb : 2 ≤ b) {D : ℕ} (hD : 1 ≤ D) (m : ℕ) :
    (((Finset.range (b ^ m)).filter fun t => D ∣ rev b m t).card : ℝ)
      ≤ (b:ℝ) ^ m / (D:ℝ) + 1 := by
  have hb0 : 0 < b := by omega
  have hcard : ((Finset.range (b ^ m)).filter fun t => D ∣ rev b m t).card
      = ((Finset.range (b ^ m)).filter fun u => D ∣ u).card := by
    refine Finset.card_bij' (fun t _ => rev b m t) (fun u _ => rev b m u)
      ?_ ?_ ?_ ?_
    · intro t ht
      rw [Finset.mem_filter, Finset.mem_range] at ht ⊢
      exact ⟨rev_lt hb0 m t, ht.2⟩
    · intro u hu
      rw [Finset.mem_filter, Finset.mem_range] at hu ⊢
      refine ⟨rev_lt hb0 m u, ?_⟩
      rw [rev_rev hb0 hu.1]
      exact hu.2
    · intro t ht
      rw [Finset.mem_filter, Finset.mem_range] at ht
      exact rev_rev hb0 ht.1
    · intro u hu
      rw [Finset.mem_filter, Finset.mem_range] at hu
      exact rev_rev hb0 hu.1
  rw [hcard]
  have hsplit : (Finset.range (b ^ m)).filter (fun u => D ∣ u)
      = insert 0 ((Finset.Ico 1 (b ^ m)).filter fun u => D ∣ u) := by
    ext u
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert,
      Finset.mem_Ico]
    constructor
    · rintro ⟨hu, hdvd⟩
      rcases Nat.eq_zero_or_pos u with h | h
      · exact Or.inl h
      · exact Or.inr ⟨⟨by omega, hu⟩, hdvd⟩
    · rintro (rfl | ⟨⟨h1, h2⟩, hdvd⟩)
      · exact ⟨Nat.pos_pow_of_pos _ hb0, dvd_zero D⟩
      · exact ⟨h2, hdvd⟩
  rw [hsplit, Finset.card_insert_of_notMem
    (by simp [Finset.mem_filter, Finset.mem_Ico])]
  have h1 := card_multiples_lt hD (b ^ m)
  push_cast
  push_cast at h1
  linarith

/-- The leading-block bound (Lemma 4.2(ii), with `j = m`): for `ℓ ∣ b`,
`2 ≤ m`, `2m ≤ λ`,
`#{p ∈ 𝒫_λ : ℓ^m ∣ R_λ(p)} ≤ (b^λ ℓ^{-m} + b^{λ-m}) · 2C_{BT}/(λ log b)`. -/
lemma count_block_le (hb : 2 ≤ b) (hm2 : 2 ≤ m) (h2m : 2 * m ≤ lam)
    (hℓb : ℓ ∣ b) {CBT : ℝ} (hCBT : 0 ≤ CBT)
    (hBT : ∀ x y : ℕ, 2 ≤ y →
      ((primesIn x (x + y)).card : ℝ) ≤ CBT * (y : ℝ) / Real.log (y : ℝ)) :
    (((PLam b lam).filter fun p => ℓ ^ m ∣ rev b lam p).card : ℝ)
      ≤ ((b:ℝ) ^ lam * ((ℓ:ℝ)⁻¹) ^ m + (b:ℝ) ^ (lam - m))
          * (2 * CBT / ((lam:ℝ) * Real.log b)) := by
  have hb0 : 0 < b := by omega
  have hbR : (1:ℝ) < (b:ℝ) := by exact_mod_cast (by omega : 1 < b)
  have hlogb : 0 < Real.log b := Real.log_pos hbR
  have hℓ1 : 1 ≤ ℓ := Nat.pos_of_dvd_of_pos hℓb hb0
  have hlam4 : 4 ≤ lam := by omega
  have hlamR0 : (0:ℝ) < (lam:ℝ) := by
    have : (0:ℕ) < lam := by omega
    exact_mod_cast this
  set B' : ℕ := b ^ (lam - m) with hB'def
  have hB'2 : 2 ≤ B' := by
    rw [hB'def]
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (lam - m) := Nat.pow_le_pow_right (by omega) (by omega)
      _ ≤ b ^ (lam - m) := Nat.pow_le_pow_left hb _
  have hB'0 : 0 < B' := by omega
  set Tadm : Finset ℕ := (Finset.range (b ^ m)).filter
    (fun t => ℓ ^ m ∣ rev b m t) with hTadm
  -- fiber decomposition over the top block
  have hfiber : ((PLam b lam).filter fun p => ℓ ^ m ∣ rev b lam p).card
      = ∑ t ∈ Tadm, (((PLam b lam).filter fun p => ℓ ^ m ∣ rev b lam p).filter
          (fun p => p / B' = t)).card := by
    refine Finset.card_eq_sum_card_fiberwise ?_
    intro p hp
    rw [Finset.mem_coe, Finset.mem_filter] at hp
    obtain ⟨hpP, hpd⟩ := hp
    rw [mem_PLam_iff] at hpP
    show p / B' ∈ (Tadm : Set ℕ)
    rw [Finset.mem_coe, hTadm, Finset.mem_filter, Finset.mem_range]
    constructor
    · rw [Nat.div_lt_iff_lt_mul hB'0]
      calc p < b ^ lam := hpP.2.1
        _ = b ^ m * B' := by
            rw [hB'def, ← pow_add]
            congr 1
            omega
    · have hmod := rev_modEq_top_block (by omega : m ≤ lam) (b := b) p
      have hmod2 : rev b lam p ≡ rev b m (p / b ^ (lam - m)) [MOD ℓ ^ m] :=
        hmod.of_dvd (pow_dvd_pow_of_dvd hℓb m)
      have h0 : rev b lam p ≡ 0 [MOD ℓ ^ m] := (Nat.modEq_zero_iff_dvd).mpr hpd
      exact (Nat.modEq_zero_iff_dvd).mp (hmod2.symm.trans h0)
  -- each fiber lies in an interval of length B'
  have hfibsub : ∀ t : ℕ,
      ((PLam b lam).filter fun p => ℓ ^ m ∣ rev b lam p).filter
        (fun p => p / B' = t) ⊆ primesIn (t * B') (t * B' + B') := by
    intro t p hp
    rw [Finset.mem_filter, Finset.mem_filter] at hp
    obtain ⟨⟨hpP, _⟩, hdiv⟩ := hp
    rw [mem_PLam_iff] at hpP
    unfold primesIn
    rw [Finset.mem_filter, Finset.mem_Ico]
    have h1 : t * B' ≤ p := by
      rw [← hdiv]
      exact Nat.div_mul_le_self p B'
    have h2 : p < t * B' + B' := by
      have h3 := Nat.div_add_mod p B'
      have h4 : p % B' < B' := Nat.mod_lt _ hB'0
      calc p = B' * (p / B') + p % B' := h3.symm
        _ = B' * t + p % B' := by rw [hdiv]
        _ < B' * t + B' := Nat.add_lt_add_left h4 _
        _ = t * B' + B' := by ring
    exact ⟨⟨h1, h2⟩, hpP.2.2⟩
  have hfibbound : ∀ t : ℕ,
      ((((PLam b lam).filter fun p => ℓ ^ m ∣ rev b lam p).filter
        (fun p => p / B' = t)).card : ℝ)
      ≤ CBT * (B' : ℝ) / Real.log (B' : ℝ) := by
    intro t
    calc ((((PLam b lam).filter fun p => ℓ ^ m ∣ rev b lam p).filter
          (fun p => p / B' = t)).card : ℝ)
        ≤ ((primesIn (t * B') (t * B' + B')).card : ℝ) := by
          exact_mod_cast Finset.card_le_card (hfibsub t)
      _ ≤ CBT * (B' : ℝ) / Real.log (B' : ℝ) := hBT (t * B') B' hB'2
  -- the log of the block length
  have hlogB' : Real.log ((B' : ℕ) : ℝ) = ((lam - m : ℕ) : ℝ) * Real.log b := by
    rw [hB'def]
    push_cast
    exact Real.log_pow (b:ℝ) (lam - m)
  have hcastsub : ((lam - m : ℕ) : ℝ) = (lam:ℝ) - (m:ℝ) := by
    have : m ≤ lam := by omega
    rw [Nat.cast_sub this]
  have hmR : (m:ℝ) ≤ (lam:ℝ) / 2 := by
    have : (2 * m : ℕ) ≤ lam := h2m
    have h1 : ((2 * m : ℕ):ℝ) ≤ (lam:ℝ) := by exact_mod_cast this
    push_cast at h1
    linarith
  have hlogB'ge : (lam:ℝ) / 2 * Real.log b ≤ Real.log ((B' : ℕ) : ℝ) := by
    rw [hlogB', hcastsub]
    have h1 : (lam:ℝ) / 2 ≤ (lam:ℝ) - (m:ℝ) := by linarith
    nlinarith [hlogb]
  have hlogB'0 : 0 < Real.log ((B' : ℕ) : ℝ) := by
    have : (0:ℝ) < (lam:ℝ)/2 * Real.log b := by positivity
    linarith
  -- assemble
  have hTadmle : ((Tadm.card : ℕ) : ℝ) ≤ (b:ℝ) ^ m * ((ℓ:ℝ)⁻¹) ^ m + 1 := by
    have h1 := card_blocks_le hb (Nat.one_le_pow _ _ (by omega : 0 < ℓ)) m
      (b := b) (D := ℓ ^ m)
    rw [hTadm]
    calc ((((Finset.range (b ^ m)).filter fun t => ℓ ^ m ∣ rev b m t).card : ℕ) : ℝ)
        ≤ (b:ℝ) ^ m / ((ℓ ^ m : ℕ):ℝ) + 1 := h1
      _ = (b:ℝ) ^ m * ((ℓ:ℝ)⁻¹) ^ m + 1 := by
          push_cast
          rw [div_eq_mul_inv, inv_pow]
  have hsum : (((PLam b lam).filter fun p => ℓ ^ m ∣ rev b lam p).card : ℝ)
      ≤ ((Tadm.card : ℕ) : ℝ) * (CBT * (B' : ℝ) / Real.log ((B' : ℕ) : ℝ)) := by
    rw [hfiber]
    push_cast
    calc ∑ t ∈ Tadm, ((((PLam b lam).filter fun p => ℓ ^ m ∣ rev b lam p).filter
          (fun p => p / B' = t)).card : ℝ)
        ≤ ∑ _t ∈ Tadm, CBT * (B' : ℝ) / Real.log ((B' : ℕ) : ℝ) :=
          Finset.sum_le_sum (fun t _ => hfibbound t)
      _ = (Tadm.card : ℝ) * (CBT * (B' : ℝ) / Real.log ((B' : ℕ) : ℝ)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  have hfrac : CBT * (B' : ℝ) / Real.log ((B' : ℕ) : ℝ)
      ≤ 2 * CBT * (B' : ℝ) / ((lam:ℝ) * Real.log b) := by
    have hd0 : (0:ℝ) < (lam:ℝ) * Real.log b := by positivity
    rw [div_le_div_iff₀ hlogB'0 hd0]
    have hCB0 : (0:ℝ) ≤ CBT * (B' : ℝ) := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hlogB'ge hCB0, hCB0, hlogB'0]
  have hfrac0 : (0:ℝ) ≤ CBT * (B' : ℝ) / Real.log ((B' : ℕ) : ℝ) := by
    positivity
  have hTadm0 : (0:ℝ) ≤ ((Tadm.card : ℕ) : ℝ) := by positivity
  have hBB : (b:ℝ) ^ m * (B' : ℝ) = (b:ℝ) ^ lam := by
    rw [hB'def]
    push_cast
    rw [← pow_add]
    congr 1
    omega
  calc (((PLam b lam).filter fun p => ℓ ^ m ∣ rev b lam p).card : ℝ)
      ≤ ((Tadm.card : ℕ) : ℝ) * (CBT * (B' : ℝ) / Real.log ((B' : ℕ) : ℝ)) :=
        hsum
    _ ≤ ((b:ℝ) ^ m * ((ℓ:ℝ)⁻¹) ^ m + 1)
          * (2 * CBT * (B' : ℝ) / ((lam:ℝ) * Real.log b)) := by
        refine mul_le_mul hTadmle hfrac hfrac0 ?_
        have : (0:ℝ) ≤ ((ℓ:ℝ)⁻¹) ^ m := by positivity
        positivity
    _ = ((b:ℝ) ^ lam * ((ℓ:ℝ)⁻¹) ^ m + (b:ℝ) ^ (lam - m))
          * (2 * CBT / ((lam:ℝ) * Real.log b)) := by
        have hB'cast : ((B' : ℕ) : ℝ) = (b:ℝ) ^ (lam - m) := by
          rw [hB'def]
          push_cast
          rfl
        have e2 : (b:ℝ) ^ m * (b:ℝ) ^ (lam - m) = (b:ℝ) ^ lam := by
          rw [← pow_add]
          congr 1
          omega
        rw [hB'cast]
        linear_combination
          (2 * CBT / ((lam:ℝ) * Real.log b)) * ((ℓ:ℝ)⁻¹) ^ m * e2

/-! ### Decomposition over the leading digit -/

/-- `#{p ∈ 𝒫_λ : P p} = ∑_{i=1}^{b-1} #{p ∈ 𝒫_{λ,i} : P p}`. -/
lemma PLam_filter_card_eq_sum (hb : 2 ≤ b) (hlam : 1 ≤ lam)
    (P : ℕ → Prop) [DecidablePred P] :
    ((PLam b lam).filter P).card
      = ∑ j ∈ Finset.Icc 1 (b - 1), ((PLamI b lam j).filter P).card := by
  rw [PLam_eq_biUnion hb hlam, Finset.filter_biUnion]
  refine Finset.card_biUnion ?_
  intro x _ y _ hxy
  refine Finset.disjoint_filter_filter ?_
  refine Finset.disjoint_left.mpr fun p hp1 hp2 => ?_
  rw [mem_PLamI_iff] at hp1 hp2
  have hB : 0 < b ^ (lam - 1) := Nat.pos_pow_of_pos _ (by omega)
  rcases Nat.lt_or_ge x y with h | h
  · have : (x + 1) * b ^ (lam - 1) ≤ y * b ^ (lam - 1) :=
      Nat.mul_le_mul_right _ (by omega)
    omega
  · have hyx : y < x := by omega
    have : (y + 1) * b ^ (lam - 1) ≤ x * b ^ (lam - 1) :=
      Nat.mul_le_mul_right _ (by omega)
    omega

/-! ### A `λ²` decay lemma -/

lemma tendsto_sqLL_div_ytr (hb : 2 ≤ b) (hξ : 0 < ξ) {K : ℕ} (hK : 1 ≤ K)
    (c c' : ℝ) (hc : 0 ≤ c) (hc' : 0 ≤ c') :
    Tendsto (fun lam : ℕ => c * (lam:ℝ) ^ 2 * (LL b lam + c') / ytr b ξ K lam)
      atTop (𝓝 0) := by
  have hbR : (1:ℝ) < (b:ℝ) := by exact_mod_cast (by omega : 1 < b)
  have hb0R : (0:ℝ) < (b:ℝ) := by linarith
  have hlogb : 0 < Real.log b := Real.log_pos hbR
  have hK0 : (0:ℝ) < (K:ℝ) := by exact_mod_cast hK
  set a : ℝ := ξ * Real.log b / (K:ℝ) with hadef
  have ha : 0 < a := div_pos (mul_pos hξ hlogb) hK0
  have hytr : ∀ lam : ℕ, ytr b ξ K lam = Real.exp (a * lam) := by
    intro lam
    unfold ytr
    rw [Real.rpow_def_of_pos hb0R]
    congr 1
    rw [hadef]
    ring
  set Kc : ℝ := c * (Real.log b + c') with hKcdef
  have hKc0 : 0 ≤ Kc := mul_nonneg hc (by linarith)
  have hg2 : Tendsto (fun x : ℝ => x ^ (((3:ℕ)):ℝ) * Real.exp (-a * x))
      atTop (𝓝 0) := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero _ a ha
  have hg3 : Tendsto (fun x : ℝ => (x:ℝ) ^ (3:ℕ) * Real.exp (-a * x))
      atTop (𝓝 0) := by
    refine hg2.congr' ?_
    filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
    rw [Real.rpow_natCast]
  have hg4 : Tendsto (fun x : ℝ => Kc * (x ^ (3:ℕ) * Real.exp (-a * x)))
      atTop (𝓝 0) := by
    have := hg3.const_mul Kc
    rwa [mul_zero] at this
  have hgn : Tendsto (fun lam : ℕ => Kc * ((lam:ℝ) ^ (3:ℕ) * Real.exp (-a * lam)))
      atTop (𝓝 0) := hg4.comp tendsto_natCast_atTop_atTop
  have h0f : ∀ᶠ lam : ℕ in atTop,
      0 ≤ c * (lam:ℝ) ^ 2 * (LL b lam + c') / ytr b ξ K lam := by
    filter_upwards [(tendsto_LL_atTop hb).eventually_ge_atTop 0] with lam hLL
    have hy := ytr_pos (b := b) (ξ := ξ) (K := K) (lam := lam) hb
    have hlm0 : (0:ℝ) ≤ (lam:ℝ) ^ 2 := by positivity
    exact div_nonneg (mul_nonneg (mul_nonneg hc hlm0) (by linarith)) hy.le
  have hfg : ∀ᶠ lam : ℕ in atTop,
      c * (lam:ℝ) ^ 2 * (LL b lam + c') / ytr b ξ K lam
        ≤ Kc * ((lam:ℝ) ^ (3:ℕ) * Real.exp (-a * lam)) := by
    filter_upwards [eventually_ge_atTop 1,
      (tendsto_LL_atTop hb).eventually_ge_atTop 0] with lam hlm1 hLL0
    rw [hytr lam]
    have hlmR : (1:ℝ) ≤ (lam:ℝ) := by exact_mod_cast hlm1
    have hLLle : LL b lam ≤ (lam:ℝ) * Real.log b := by
      unfold LL
      have hlogpow : Real.log ((b:ℝ) ^ (lam:ℕ)) = (lam:ℝ) * Real.log b :=
        Real.log_pow (b:ℝ) lam
      have hlog0 : 0 < Real.log ((b:ℝ) ^ (lam:ℕ)) := by
        rw [hlogpow]
        have : (0:ℝ) < (lam:ℝ) := by linarith
        positivity
      calc Real.log (Real.log ((b:ℝ) ^ (lam:ℕ)))
          ≤ Real.log ((b:ℝ) ^ (lam:ℕ)) - 1 := Real.log_le_sub_one_of_pos hlog0
        _ ≤ Real.log ((b:ℝ) ^ (lam:ℕ)) := by linarith
        _ = (lam:ℝ) * Real.log b := hlogpow
    have hnum : c * (lam:ℝ) ^ 2 * (LL b lam + c') ≤ Kc * (lam:ℝ) ^ (3:ℕ) := by
      have h1 : LL b lam + c' ≤ (lam:ℝ) * (Real.log b + c') := by
        have h2 : c' * 1 ≤ c' * (lam:ℝ) :=
          mul_le_mul_of_nonneg_left hlmR hc'
        nlinarith [hLLle]
      have h3 : (0:ℝ) ≤ (lam:ℝ) ^ 2 := by positivity
      calc c * (lam:ℝ) ^ 2 * (LL b lam + c')
          ≤ c * (lam:ℝ) ^ 2 * ((lam:ℝ) * (Real.log b + c')) :=
            mul_le_mul_of_nonneg_left h1 (mul_nonneg hc h3)
        _ = Kc * (lam:ℝ) ^ (3:ℕ) := by
            rw [hKcdef]
            ring
    have hexp : (0:ℝ) < Real.exp (a * lam) := Real.exp_pos _
    calc c * (lam:ℝ) ^ 2 * (LL b lam + c') / Real.exp (a * lam)
        ≤ Kc * (lam:ℝ) ^ (3:ℕ) / Real.exp (a * lam) :=
          div_le_div_of_le' hexp hnum
      _ = Kc * ((lam:ℝ) ^ (3:ℕ) * Real.exp (-a * lam)) := by
          rw [neg_mul, Real.exp_neg, div_eq_mul_inv]
          ring
  exact squeeze_zero' h0f hfg hgn


/-! ### Hypothesis (iii) for reversed primes (Lemma 4.5) -/

set_option maxHeartbeats 1600000 in
/-- **Lemma 4.5** (using Lemmas 4.1 and 4.2(ii)):
`∑_{n∈AFam}(Ω(n)-ω(n)) ≪ #AFam` for the reversed primes with fixed leading
digit `i`. -/
theorem revOmegaHyp (hb : 2 ≤ b) (hi1 : 1 ≤ i) (hi2 : i ≤ b - 1) :
    OmegaHyp (AFam b i) := by
  obtain ⟨ξ0, hξ00, hdrs0⟩ := drs_thm13 b hb
  have hbR : (1:ℝ) < (b:ℝ) := by exact_mod_cast (by omega : 1 < b)
  have hb0R : (0:ℝ) < (b:ℝ) := by linarith
  have hlogb : 0 < Real.log b := Real.log_pos hbR
  have hlog2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  set ξw : ℝ := min (ξ0/2) (Real.log 2 / (4 * Real.log b)) with hξwdef
  have hξw0 : 0 < ξw := lt_min (by linarith) (by positivity)
  have hξwξ0 : ξw < ξ0 := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hξwlog : ξw ≤ Real.log 2 / (4 * Real.log b) := min_le_right _ _
  obtain ⟨c, C, hc0, hC0, lam0, hdrs⟩ := hdrs0 ξw hξw0 hξwξ0
  obtain ⟨CBT, hCBT0, hBT⟩ := brun_titchmarsh
  obtain ⟨Cm, hCm0, hmert⟩ := mertens_regular.bound
  obtain ⟨κ, hκ0, hκev⟩ := pilam_lower hb hi1 hi2
  obtain ⟨Cu, hCu0, hCuev⟩ := pilam_upper hb
  have hK0 : (0:ℝ) ≤ 2 * CBT / Real.log b := by positivity
  refine ⟨(((b:ℝ)+1) * (2 * CBT / Real.log b) + 2 * Cu + 2 * κ) / κ, ?_, ?_⟩
  · have h1 : (0:ℝ) ≤ ((b:ℝ)+1) * (2 * CBT / Real.log b) :=
      mul_nonneg (by linarith) hK0
    have h2 : (0:ℝ) ≤ 2 * Cu := by linarith
    have h3 : (0:ℝ) ≤ 2 * κ := by linarith
    exact div_nonneg (by linarith) hκ0.le
  · -- eventual smallness facts
    have hevL : ∀ᶠ lam : ℕ in atTop,
        (b:ℝ) * (lam:ℝ)^2 * (LL b lam + Cm) / ytr b ξw 2 lam ≤ κ := by
      have h0 := tendsto_sqLL_div_ytr hb hξw0 (K := 2) (by omega) (b:ℝ) Cm
        (by linarith) hCm0
      exact (h0.eventually (Iio_mem_nhds hκ0)).mono (fun lam h => le_of_lt h)
    have hevD : ∀ᶠ lam : ℕ in atTop,
        2*(b:ℝ)^2*C * ((lam:ℝ)^(2:ℕ) * (b:ℝ)^(-(c * Real.sqrt (lam:ℝ)))) ≤ κ := by
      have h0 := tendsto_rpow_mul_rpow_neg_sqrt hb hc0 (((2:ℕ)):ℝ)
      have h0' : Tendsto (fun lam : ℕ =>
          (lam:ℝ)^(2:ℕ) * (b:ℝ)^(-(c * Real.sqrt (lam:ℝ)))) atTop (𝓝 0) := by
        refine h0.congr fun lam => ?_
        rw [Real.rpow_natCast]
      have h1 := h0'.const_mul (2*(b:ℝ)^2*C)
      rw [mul_zero] at h1
      exact (h1.eventually (Iio_mem_nhds hκ0)).mono (fun lam h => le_of_lt h)
    filter_upwards [eventually_ge_atTop lam0, eventually_ge_atTop 3,
      hevL, hevD, hκev, hCuev, AFam_eventually_eq hb hi1 hi2,
      AFam_card_eventually hb hi1 hi2,
      (tendsto_LL_atTop hb).eventually_ge_atTop 0]
      with lam hlam0' hlam3 hL hD hκlam hCulam hAeq hAcard hLL0
    obtain ⟨Bnd, hB0, hBptw, hBsum⟩ := hdrs lam hlam0'
    have hlam1 : 1 ≤ lam := by omega
    have hlamR : (1:ℝ) ≤ (lam:ℝ) := by exact_mod_cast hlam1
    have hlamR0 : (0:ℝ) < (lam:ℝ) := by linarith
    set M : ℕ := b * lam with hMdef
    have hM2 : 2 ≤ M := by
      rw [hMdef]
      have := Nat.mul_le_mul hb hlam1
      omega
    set Ylam : ℕ := ⌊(b:ℝ) ^ (ξw * (lam:ℝ))⌋₊ with hYlam
    have hpow0 : (0:ℝ) < (b:ℝ) ^ lam := by positivity
    -- pointwise: Ω ≥ ω
    have hΩω : ∀ n : ℕ, (smallOmega n : ℝ) ≤ (bigOmega n : ℝ) := by
      intro n
      have h1 : smallOmega n ≤ bigOmega n := by
        unfold smallOmega bigOmega
        rw [Finset.card_eq_sum_ones]
        exact Finset.sum_le_sum fun ℓ hℓ =>
          factorization_pos_of_mem_primeFactors hℓ
      exact_mod_cast h1
    -- reduce the sum over AFam to the double count over 𝒫_λ
    have hchain : ∑ n ∈ AFam b i lam, ((bigOmega n : ℝ) - (smallOmega n : ℝ))
        ≤ ∑ p ∈ PLam b lam,
            ((bigOmega (rev b lam p) : ℝ) - (smallOmega (rev b lam p) : ℝ)) := by
      rw [hAeq]
      have hsub : ∀ q ∈ PLamI b lam i, q < b ^ lam := by
        intro q hq
        rw [mem_PLamI_iff] at hq
        calc q < (i + 1) * b ^ (lam - 1) := hq.2.1
          _ ≤ b * b ^ (lam - 1) := Nat.mul_le_mul_right _ (by omega)
          _ = b ^ lam := by
              rw [← pow_succ']
              congr 1
              omega
      have hinj : ∀ x ∈ PLamI b lam i, ∀ y ∈ PLamI b lam i,
          rev b lam x = rev b lam y → x = y := by
        intro x hx y hy hxy
        exact rev_injOn (by omega : (0:ℕ) < b) lam (hsub x hx) (hsub y hy) hxy
      have himg : ∑ n ∈ ALamI b lam i, ((bigOmega n : ℝ) - (smallOmega n : ℝ))
          = ∑ p ∈ PLamI b lam i,
              ((bigOmega (rev b lam p) : ℝ) - (smallOmega (rev b lam p) : ℝ)) := by
        unfold ALamI
        exact Finset.sum_image hinj
      rw [himg]
      refine Finset.sum_le_sum_of_subset_of_nonneg
        (PLamI_subset_PLam hb hlam1 hi1 hi2) ?_
      intro p _ _
      have := hΩω (rev b lam p)
      linarith
    -- the double-count identity over 𝒫_λ
    have hpos : ∀ p ∈ PLam b lam, 1 ≤ rev b lam p := by
      intro p hp
      rw [mem_PLam_iff] at hp
      have := hp.2.2.two_le
      exact rev_pos (by omega) hp.2.1 (by omega)
    have hltb : ∀ p ∈ PLam b lam, rev b lam p < b ^ lam :=
      fun p _ => rev_lt (by omega) lam p
    have hid := sum_excess_eq hb lam (PLam b lam) (rev b lam) hpos hltb
    -- size forces `2m ≤ λ`
    have hsmall_m : ∀ m ℓ : ℕ, 2 ≤ m → ℓ.Prime → ℓ ^ m ≤ Ylam → 2 * m ≤ lam := by
      intro m ℓ hm2 hp hsm
      have h2ℓ : 2 ≤ ℓ := hp.two_le
      have h1 : ((2 ^ m : ℕ) : ℝ) ≤ (b:ℝ) ^ (ξw * (lam:ℝ)) := by
        calc ((2 ^ m : ℕ) : ℝ) ≤ ((ℓ ^ m : ℕ) : ℝ) := by
              exact_mod_cast Nat.pow_le_pow_left h2ℓ m
          _ ≤ (Ylam : ℝ) := by exact_mod_cast hsm
          _ ≤ (b:ℝ) ^ (ξw * (lam:ℝ)) := Nat.floor_le (Real.rpow_nonneg hb0R.le _)
      have h2 : (m:ℝ) * Real.log 2 ≤ ξw * (lam:ℝ) * Real.log b := by
        have h3 := Real.log_le_log (by positivity) h1
        rw [Real.log_rpow hb0R] at h3
        have h4 : Real.log ((2 ^ m : ℕ) : ℝ) = (m:ℝ) * Real.log 2 := by
          push_cast
          exact Real.log_pow (2:ℝ) m
        linarith [h4 ▸ h3]
      have h5 : ξw * (lam:ℝ) * Real.log b ≤ (lam:ℝ) * Real.log 2 / 4 := by
        have h6 : ξw * ((lam:ℝ) * Real.log b)
            ≤ Real.log 2 / (4 * Real.log b) * ((lam:ℝ) * Real.log b) := by
          refine mul_le_mul_of_nonneg_right hξwlog ?_
          positivity
        have h7 : Real.log 2 / (4 * Real.log b) * ((lam:ℝ) * Real.log b)
            = (lam:ℝ) * Real.log 2 / 4 := by
          field_simp
          try ring
        calc ξw * (lam:ℝ) * Real.log b = ξw * ((lam:ℝ) * Real.log b) := by ring
          _ ≤ (lam:ℝ) * Real.log 2 / 4 := by rw [← h7] at *; linarith [h6]
      have h8 : (m:ℝ) ≤ (lam:ℝ) / 4 := by
        have h9 : (m:ℝ) * Real.log 2 ≤ (lam:ℝ) / 4 * Real.log 2 := by
          calc (m:ℝ) * Real.log 2 ≤ ξw * (lam:ℝ) * Real.log b := h2
            _ ≤ (lam:ℝ) * Real.log 2 / 4 := h5
            _ = (lam:ℝ) / 4 * Real.log 2 := by ring
        exact le_of_mul_le_mul_right h9 hlog2
      have h10 : ((2 * m : ℕ) : ℝ) ≤ (lam:ℝ) := by
        push_cast
        linarith
      exact_mod_cast h10

    -- ── Part Z: `ℓ ∣ b²-1` contributes nothing (Lemma 4.1) ──
    have hboundZ : ∀ m ∈ Finset.Icc 2 M,
        ∀ ℓ ∈ ((Pamb b lam).filter (fun ℓ => ℓ ^ m ≤ Ylam)).filter
          (fun ℓ => ℓ ∣ b ^ 2 - 1),
        (((PLam b lam).filter fun p => ℓ ^ m ∣ rev b lam p).card : ℝ) = 0 := by
      intro m hm ℓ hℓ
      rw [Finset.mem_Icc] at hm
      rw [Finset.mem_filter, Finset.mem_filter] at hℓ
      obtain ⟨⟨hPam, _⟩, hdvd21⟩ := hℓ
      have hp : ℓ.Prime := (mem_Pamb.mp hPam).2
      have hempty : (PLam b lam).filter (fun p => ℓ ^ m ∣ rev b lam p) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro p hpP hcon
        rw [mem_PLam_iff] at hpP
        have hbp : b + 1 < p := by
          have h1 : b ^ 2 ≤ b ^ (lam - 1) :=
            Nat.pow_le_pow_right (by omega) (by omega)
          have h2 : b * b ≤ b ^ 2 := by
            have : b ^ 2 = b * b := by ring
            omega
          have h3 : 2 * b ≤ b * b := Nat.mul_le_mul_right _ hb
          have := hpP.1
          omega
        have hcop := rev_coprime_sq_sub_one hb hpP.2.2 hbp hpP.2.1
        have hℓrev : ℓ ∣ rev b lam p :=
          dvd_trans (dvd_pow_self ℓ (by omega : m ≠ 0)) hcon
        have hgcd : ℓ ∣ Nat.gcd (rev b lam p) (b ^ 2 - 1) :=
          Nat.dvd_gcd hℓrev hdvd21
        unfold Nat.Coprime at hcop
        rw [hcop] at hgcd
        have hone := Nat.dvd_one.mp hgcd
        exact absurd hone (Nat.Prime.ne_one hp)
      rw [hempty]
      simp
    -- ── Part B: `ℓ ∣ b` — the leading-block bound ──
    have hboundB : ∑ m ∈ Finset.Icc 2 M,
        ∑ ℓ ∈ (((Pamb b lam).filter (fun ℓ => ℓ ^ m ≤ Ylam)).filter
          (fun ℓ => ¬ ℓ ∣ b ^ 2 - 1)).filter (fun ℓ => ℓ ∣ b),
          (((PLam b lam).filter fun p => ℓ ^ m ∣ rev b lam p).card : ℝ)
        ≤ ((b:ℝ)+1) * (2 * CBT / Real.log b) * ((b:ℝ) ^ lam / (lam:ℝ)) := by
      -- pointwise, with the `m ≤ λ`-free upper bound
      have hptwB : ∀ m ∈ Finset.Icc 2 M,
          ∀ ℓ ∈ (((Pamb b lam).filter (fun ℓ => ℓ ^ m ≤ Ylam)).filter
            (fun ℓ => ¬ ℓ ∣ b ^ 2 - 1)).filter (fun ℓ => ℓ ∣ b),
          (((PLam b lam).filter fun p => ℓ ^ m ∣ rev b lam p).card : ℝ)
            ≤ ((b:ℝ) ^ lam * ((ℓ:ℝ)⁻¹) ^ m + (b:ℝ) ^ lam * ((b:ℝ)⁻¹) ^ m)
                * (2 * CBT / ((lam:ℝ) * Real.log b)) := by
        intro m hm ℓ hℓ
        rw [Finset.mem_Icc] at hm
        rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_filter] at hℓ
        obtain ⟨⟨⟨hPam, hsm⟩, _⟩, hℓb⟩ := hℓ
        have hp : ℓ.Prime := (mem_Pamb.mp hPam).2
        have h2m := hsmall_m m ℓ hm.1 hp hsm
        have h1 := count_block_le hb hm.1 h2m hℓb hCBT0 hBT
        refine le_trans h1 ?_
        have hK0' : (0:ℝ) ≤ 2 * CBT / ((lam:ℝ) * Real.log b) := by positivity
        refine mul_le_mul_of_nonneg_right ?_ hK0'
        have hmle : m ≤ lam := by omega
        have e1 : (b:ℝ) ^ (lam - m) = (b:ℝ) ^ lam * ((b:ℝ)⁻¹) ^ m := by
          have hbm0 : ((b:ℝ)) ^ m ≠ 0 := by positivity
          rw [inv_pow, eq_comm, mul_inv_eq_iff_eq_mul₀ hbm0, ← pow_add]
          congr 1
          omega
        rw [e1]
      calc ∑ m ∈ Finset.Icc 2 M,
            ∑ ℓ ∈ (((Pamb b lam).filter (fun ℓ => ℓ ^ m ≤ Ylam)).filter
              (fun ℓ => ¬ ℓ ∣ b ^ 2 - 1)).filter (fun ℓ => ℓ ∣ b),
            (((PLam b lam).filter fun p => ℓ ^ m ∣ rev b lam p).card : ℝ)
          ≤ ∑ m ∈ Finset.Icc 2 M,
            ∑ ℓ ∈ (Pamb b lam).filter (fun ℓ => ℓ ∣ b),
              ((b:ℝ) ^ lam * ((ℓ:ℝ)⁻¹) ^ m + (b:ℝ) ^ lam * ((b:ℝ)⁻¹) ^ m)
                * (2 * CBT / ((lam:ℝ) * Real.log b)) := by
            refine Finset.sum_le_sum fun m hm => ?_
            refine le_trans (Finset.sum_le_sum (hptwB m hm)) ?_
            refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
            · intro ℓ hℓ
              rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_filter] at hℓ
              rw [Finset.mem_filter]
              exact ⟨hℓ.1.1.1, hℓ.2⟩
            · intro ℓ _ _
              have h1 : (0:ℝ) ≤ ((ℓ:ℝ)⁻¹) ^ m := by positivity
              have h2 : (0:ℝ) ≤ ((b:ℝ)⁻¹) ^ m := by positivity
              have h3 : (0:ℝ) ≤ 2 * CBT / ((lam:ℝ) * Real.log b) := by positivity
              have h4 : (0:ℝ) ≤ (b:ℝ) ^ lam := by positivity
              exact mul_nonneg (by nlinarith) h3
        _ = ∑ ℓ ∈ (Pamb b lam).filter (fun ℓ => ℓ ∣ b),
              ∑ m ∈ Finset.Icc 2 M,
              ((b:ℝ) ^ lam * ((ℓ:ℝ)⁻¹) ^ m + (b:ℝ) ^ lam * ((b:ℝ)⁻¹) ^ m)
                * (2 * CBT / ((lam:ℝ) * Real.log b)) := Finset.sum_comm
        _ ≤ ∑ _ℓ ∈ (Pamb b lam).filter (fun ℓ => ℓ ∣ b),
              (b:ℝ) ^ lam * (2 * CBT / ((lam:ℝ) * Real.log b)) := by
            refine Finset.sum_le_sum fun ℓ hℓ => ?_
            rw [Finset.mem_filter] at hℓ
            have hp : ℓ.Prime := (mem_Pamb.mp hℓ.1).2
            have h2ℓ : (2:ℝ) ≤ (ℓ:ℝ) := by exact_mod_cast hp.two_le
            have h2b : (2:ℝ) ≤ (b:ℝ) := by exact_mod_cast hb
            have hgeomℓ : ∑ m ∈ Finset.Icc 2 M, ((ℓ:ℝ)⁻¹) ^ m ≤ 1/2 := by
              have h1 := sum_Icc_geom_le (x := (ℓ:ℝ)⁻¹) (by positivity) ?_ M
              · have h2 : ((ℓ:ℝ)⁻¹) ^ 2 ≤ (1/2 : ℝ) ^ 2 := by
                  have h3 : (ℓ:ℝ)⁻¹ ≤ 1/2 := by
                    have := inv_le_inv_of_le' (by norm_num : (0:ℝ) < 2) h2ℓ
                    rw [show ((2:ℝ))⁻¹ = 1/2 by norm_num] at this
                    exact this
                  exact pow_le_pow_left' (by positivity) h3 2
                nlinarith [h1]
              · have := inv_le_inv_of_le' (by norm_num : (0:ℝ) < 2) h2ℓ
                rw [show ((2:ℝ))⁻¹ = 1/2 by norm_num] at this
                exact this
            have hgeomb : ∑ m ∈ Finset.Icc 2 M, ((b:ℝ)⁻¹) ^ m ≤ 1/2 := by
              have h1 := sum_Icc_geom_le (x := (b:ℝ)⁻¹) (by positivity) ?_ M
              · have h3 : (b:ℝ)⁻¹ ≤ 1/2 := by
                  have := inv_le_inv_of_le' (by norm_num : (0:ℝ) < 2) h2b
                  rw [show ((2:ℝ))⁻¹ = 1/2 by norm_num] at this
                  exact this
                have h2 : ((b:ℝ)⁻¹) ^ 2 ≤ (1/2 : ℝ) ^ 2 :=
                  pow_le_pow_left' (by positivity) h3 2
                nlinarith [h1]
              · have := inv_le_inv_of_le' (by norm_num : (0:ℝ) < 2) h2b
                rw [show ((2:ℝ))⁻¹ = 1/2 by norm_num] at this
                exact this
            have hK0' : (0:ℝ) ≤ 2 * CBT / ((lam:ℝ) * Real.log b) := by positivity
            calc ∑ m ∈ Finset.Icc 2 M,
                  ((b:ℝ) ^ lam * ((ℓ:ℝ)⁻¹) ^ m + (b:ℝ) ^ lam * ((b:ℝ)⁻¹) ^ m)
                    * (2 * CBT / ((lam:ℝ) * Real.log b))
                = ((b:ℝ) ^ lam * ∑ m ∈ Finset.Icc 2 M, ((ℓ:ℝ)⁻¹) ^ m
                    + (b:ℝ) ^ lam * ∑ m ∈ Finset.Icc 2 M, ((b:ℝ)⁻¹) ^ m)
                    * (2 * CBT / ((lam:ℝ) * Real.log b)) := by
                  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
                    ← Finset.sum_mul]
              _ ≤ ((b:ℝ) ^ lam * (1/2) + (b:ℝ) ^ lam * (1/2))
                    * (2 * CBT / ((lam:ℝ) * Real.log b)) := by
                  refine mul_le_mul_of_nonneg_right ?_ hK0'
                  have h5 := mul_le_mul_of_nonneg_left hgeomℓ hpow0.le
                  have h6 := mul_le_mul_of_nonneg_left hgeomb hpow0.le
                  linarith
              _ = (b:ℝ) ^ lam * (2 * CBT / ((lam:ℝ) * Real.log b)) := by ring
        _ ≤ ((b:ℝ) + 1) * ((b:ℝ) ^ lam * (2 * CBT / ((lam:ℝ) * Real.log b))) := by
            rw [Finset.sum_const, nsmul_eq_mul]
            refine mul_le_mul_of_nonneg_right ?_ ?_
            · have hcard : ((Pamb b lam).filter (fun ℓ => ℓ ∣ b)).card ≤ b + 1 := by
                have hsub : (Pamb b lam).filter (fun ℓ => ℓ ∣ b)
                    ⊆ Finset.range (b + 1) := by
                  intro ℓ hℓ
                  rw [Finset.mem_filter] at hℓ
                  rw [Finset.mem_range]
                  have := Nat.le_of_dvd (by omega) hℓ.2
                  omega
                calc ((Pamb b lam).filter (fun ℓ => ℓ ∣ b)).card
                    ≤ (Finset.range (b + 1)).card := Finset.card_le_card hsub
                  _ = b + 1 := Finset.card_range _
              calc (((Pamb b lam).filter (fun ℓ => ℓ ∣ b)).card : ℝ)
                  ≤ ((b + 1 : ℕ) : ℝ) := by exact_mod_cast hcard
                _ = (b:ℝ) + 1 := by push_cast; ring
            · positivity
        _ = ((b:ℝ)+1) * (2 * CBT / Real.log b) * ((b:ℝ) ^ lam / (lam:ℝ)) := by
            field_simp
            try ring
    -- ── Part D: `ℓ ∤ b(b²-1)`, small — the level of distribution ──
    have hcntD : ∀ m ∈ Finset.Icc 2 M,
        ∀ ℓ ∈ (((Pamb b lam).filter (fun ℓ => ℓ ^ m ≤ Ylam)).filter
          (fun ℓ => ¬ ℓ ∣ b ^ 2 - 1)).filter (fun ℓ => ¬ ℓ ∣ b),
        (((PLam b lam).filter fun p => ℓ ^ m ∣ rev b lam p).card : ℝ)
          ≤ ((PLam b lam).card : ℝ) * ((ℓ:ℝ)⁻¹) ^ m
            + (b:ℝ) * (2 * Bnd (ℓ ^ m)) := by
      intro m hm ℓ hℓ
      rw [Finset.mem_Icc] at hm
      rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_filter] at hℓ
      obtain ⟨⟨⟨hPam, hsm⟩, hnd21⟩, hndb⟩ := hℓ
      have hp : ℓ.Prime := (mem_Pamb.mp hPam).2
      have hcop : Nat.Coprime ℓ (b * (b ^ 2 - 1)) := by
        rw [Nat.Prime.coprime_iff_not_dvd hp]
        intro hdvd
        rcases (Nat.Prime.dvd_mul hp).mp hdvd with h | h
        · exact hndb h
        · exact hnd21 h
      have hcopm : Nat.Coprime (ℓ ^ m) (b * (b ^ 2 - 1)) :=
        Nat.Coprime.pow_left _ hcop
      have hdle : ((ℓ ^ m : ℕ) : ℝ) ≤ (b:ℝ) ^ (ξw * (lam:ℝ)) := by
        calc ((ℓ ^ m : ℕ) : ℝ) ≤ (Ylam : ℝ) := by exact_mod_cast hsm
          _ ≤ (b:ℝ) ^ (ξw * (lam:ℝ)) := Nat.floor_le (Real.rpow_nonneg hb0R.le _)
      have hd1 : 1 ≤ ℓ ^ m := Nat.one_le_pow _ _ hp.pos
      have hremj : ∀ j : ℕ, 1 ≤ j → j ≤ b - 1 →
          |rem (ALamI b lam j) (ℓ ^ m)| ≤ 2 * Bnd (ℓ ^ m) := by
        intro j hj1 hj2
        have hz1 : b ^ (lam - 1) ≤ (j + 1) * b ^ (lam - 1) :=
          Nat.le_mul_of_pos_left _ (by omega)
        have hz2 : (j + 1) * b ^ (lam - 1) ≤ b ^ lam := by
          calc (j + 1) * b ^ (lam - 1) ≤ b * b ^ (lam - 1) :=
                Nat.mul_le_mul_right _ (by omega)
            _ = b ^ lam := by
                rw [← pow_succ']
                congr 1
                omega
        have hz3 : b ^ (lam - 1) ≤ j * b ^ (lam - 1) :=
          Nat.le_mul_of_pos_left _ (by omega)
        have hz4 : j * b ^ (lam - 1) ≤ b ^ lam :=
          le_trans (Nat.mul_le_mul_right _ (by omega)) hz2
        have h1 := hBptw (ℓ ^ m) hd1 hcopm hdle
          ((j + 1) * b ^ (lam - 1)) hz1 hz2 (ℓ ^ m)
        have h2 := hBptw (ℓ ^ m) hd1 hcopm hdle
          (j * b ^ (lam - 1)) hz3 hz4 (ℓ ^ m)
        exact rev_rem_le hb hlam1 hj1 hj2 hd1 h1 h2
      have hcastdecomp :
          (((PLam b lam).filter fun p => ℓ ^ m ∣ rev b lam p).card : ℝ)
          = ∑ j ∈ Finset.Icc 1 (b - 1),
              (((PLamI b lam j).filter fun p => ℓ ^ m ∣ rev b lam p).card : ℝ) := by
        rw [PLam_filter_card_eq_sum hb hlam1 (fun p => ℓ ^ m ∣ rev b lam p)]
        push_cast
        rfl
      have hπsum : ((PLam b lam).card : ℝ)
          = ∑ j ∈ Finset.Icc 1 (b - 1), ((PLamI b lam j).card : ℝ) := by
        rw [PLam_card_eq_sum hb hlam1]
        push_cast
        rfl
      have hperj : ∀ j ∈ Finset.Icc 1 (b - 1),
          (((PLamI b lam j).filter fun p => ℓ ^ m ∣ rev b lam p).card : ℝ)
            ≤ ((PLamI b lam j).card : ℝ) * ((ℓ:ℝ)⁻¹) ^ m + 2 * Bnd (ℓ ^ m) := by
        intro j hj
        rw [Finset.mem_Icc] at hj
        have hjb : j + 1 ≤ b := by omega
        have e1 : ((PLamI b lam j).filter fun p => ℓ ^ m ∣ rev b lam p).card
            = ((ALamI b lam j).filter fun n => ℓ ^ m ∣ n).card :=
          (ALamI_filter_dvd_card hb hlam1 hjb (ℓ ^ m)).symm
        have e2 : (ALamI b lam j).card = (PLamI b lam j).card :=
          ALamI_card hb hlam1 hjb
        have e3 : (((ALamI b lam j).filter fun n => ℓ ^ m ∣ n).card : ℝ)
            = ((ALamI b lam j).card : ℝ) / ((ℓ ^ m : ℕ) : ℝ)
              + rem (ALamI b lam j) (ℓ ^ m) := by
          unfold rem
          ring
        have hremj' := hremj j hj.1 hj.2
        have h5 := le_abs_self (rem (ALamI b lam j) (ℓ ^ m))
        have hdiv : ((ALamI b lam j).card : ℝ) / ((ℓ ^ m : ℕ) : ℝ)
            = ((PLamI b lam j).card : ℝ) * ((ℓ:ℝ)⁻¹) ^ m := by
          rw [e2]
          push_cast
          rw [div_eq_mul_inv, inv_pow]
        rw [e1, e3, hdiv]
        linarith
      calc (((PLam b lam).filter fun p => ℓ ^ m ∣ rev b lam p).card : ℝ)
          = ∑ j ∈ Finset.Icc 1 (b - 1),
              (((PLamI b lam j).filter fun p => ℓ ^ m ∣ rev b lam p).card : ℝ) :=
            hcastdecomp
        _ ≤ ∑ j ∈ Finset.Icc 1 (b - 1),
              (((PLamI b lam j).card : ℝ) * ((ℓ:ℝ)⁻¹) ^ m + 2 * Bnd (ℓ ^ m)) :=
            Finset.sum_le_sum hperj
        _ = (∑ j ∈ Finset.Icc 1 (b - 1), ((PLamI b lam j).card : ℝ))
              * ((ℓ:ℝ)⁻¹) ^ m
            + ((Finset.Icc 1 (b - 1)).card : ℝ) * (2 * Bnd (ℓ ^ m)) := by
            rw [Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_const,
              nsmul_eq_mul]
        _ ≤ ((PLam b lam).card : ℝ) * ((ℓ:ℝ)⁻¹) ^ m
              + (b:ℝ) * (2 * Bnd (ℓ ^ m)) := by
            rw [← hπsum]
            have hcard : ((Finset.Icc 1 (b - 1)).card : ℝ) ≤ (b:ℝ) := by
              have h6 : (Finset.Icc 1 (b - 1)).card ≤ b := by
                rw [Nat.card_Icc]
                omega
              exact_mod_cast h6
            have hB0' : (0:ℝ) ≤ 2 * Bnd (ℓ ^ m) := by linarith [hB0 (ℓ ^ m)]
            nlinarith [hcard, hB0']
    -- D-part, summed
    have hboundD : ∑ m ∈ Finset.Icc 2 M,
        ∑ ℓ ∈ (((Pamb b lam).filter (fun ℓ => ℓ ^ m ≤ Ylam)).filter
          (fun ℓ => ¬ ℓ ∣ b ^ 2 - 1)).filter (fun ℓ => ¬ ℓ ∣ b),
          (((PLam b lam).filter fun p => ℓ ^ m ∣ rev b lam p).card : ℝ)
        ≤ 2 * ((PLam b lam).card : ℝ) + κ * ((b:ℝ) ^ lam / (lam:ℝ)) := by
      have hπ0 : (0:ℝ) ≤ ((PLam b lam).card : ℝ) := by positivity
      have hmainD : ∑ m ∈ Finset.Icc 2 M,
          ∑ ℓ ∈ (((Pamb b lam).filter (fun ℓ => ℓ ^ m ≤ Ylam)).filter
            (fun ℓ => ¬ ℓ ∣ b ^ 2 - 1)).filter (fun ℓ => ¬ ℓ ∣ b),
            ((PLam b lam).card : ℝ) * ((ℓ:ℝ)⁻¹) ^ m
          ≤ 2 * ((PLam b lam).card : ℝ) := by
        have hstep1 : ∀ m ∈ Finset.Icc 2 M,
            ∑ ℓ ∈ (((Pamb b lam).filter (fun ℓ => ℓ ^ m ≤ Ylam)).filter
              (fun ℓ => ¬ ℓ ∣ b ^ 2 - 1)).filter (fun ℓ => ¬ ℓ ∣ b),
              ((PLam b lam).card : ℝ) * ((ℓ:ℝ)⁻¹) ^ m
            ≤ ∑ ℓ ∈ Pamb b lam, ((PLam b lam).card : ℝ) * ((ℓ:ℝ)⁻¹) ^ m := by
          intro m _
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
          · exact ((Finset.filter_subset _ _).trans
              (Finset.filter_subset _ _)).trans (Finset.filter_subset _ _)
          · intro ℓ _ _
            exact mul_nonneg hπ0 (by positivity)
        calc ∑ m ∈ Finset.Icc 2 M,
              ∑ ℓ ∈ (((Pamb b lam).filter (fun ℓ => ℓ ^ m ≤ Ylam)).filter
                (fun ℓ => ¬ ℓ ∣ b ^ 2 - 1)).filter (fun ℓ => ¬ ℓ ∣ b),
                ((PLam b lam).card : ℝ) * ((ℓ:ℝ)⁻¹) ^ m
            ≤ ∑ m ∈ Finset.Icc 2 M,
                ∑ ℓ ∈ Pamb b lam, ((PLam b lam).card : ℝ) * ((ℓ:ℝ)⁻¹) ^ m :=
              Finset.sum_le_sum hstep1
          _ = ∑ ℓ ∈ Pamb b lam,
                ∑ m ∈ Finset.Icc 2 M, ((PLam b lam).card : ℝ) * ((ℓ:ℝ)⁻¹) ^ m :=
              Finset.sum_comm
          _ ≤ ∑ ℓ ∈ Pamb b lam,
                ((PLam b lam).card : ℝ) * (2 * ((ℓ:ℝ)⁻¹) ^ 2) := by
              refine Finset.sum_le_sum fun ℓ hℓ => ?_
              have hp : ℓ.Prime := (mem_Pamb.mp hℓ).2
              have h2ℓ : (2:ℝ) ≤ (ℓ:ℝ) := by exact_mod_cast hp.two_le
              rw [← Finset.mul_sum]
              refine mul_le_mul_of_nonneg_left ?_ hπ0
              refine sum_Icc_geom_le (by positivity) ?_ M
              have hinv := inv_le_inv_of_le' (by norm_num : (0:ℝ) < 2) h2ℓ
              rw [show ((2:ℝ))⁻¹ = 1/2 by norm_num] at hinv
              exact hinv
          _ = 2 * ((PLam b lam).card : ℝ) * ∑ ℓ ∈ Pamb b lam, ((ℓ:ℝ)⁻¹) ^ 2 := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun ℓ _ => ?_
              ring
          _ ≤ 2 * ((PLam b lam).card : ℝ) * 1 := by
              refine mul_le_mul_of_nonneg_left ?_ (by linarith)
              have hsub2 : Pamb b lam ⊆ Finset.Ioc 1 (b ^ lam) := by
                intro ℓ hℓ
                have h := mem_Pamb.mp hℓ
                rw [Finset.mem_Ioc]
                have := h.2.two_le
                omega
              have hIoc := sum_Ioc_inv_sq_le (u := 1) (N := b ^ lam) le_rfl
                (Nat.one_le_pow _ _ (by omega))
              have hN0 : (0:ℝ) ≤ ((b ^ lam : ℕ):ℝ)⁻¹ := by positivity
              calc ∑ ℓ ∈ Pamb b lam, ((ℓ:ℝ)⁻¹) ^ 2
                  ≤ ∑ n ∈ Finset.Ioc 1 (b ^ lam), ((n:ℝ)⁻¹) ^ 2 :=
                    Finset.sum_le_sum_of_subset_of_nonneg hsub2
                      (fun n _ _ => by positivity)
                _ ≤ ((1:ℕ):ℝ)⁻¹ - ((b ^ lam : ℕ):ℝ)⁻¹ := hIoc
                _ ≤ 1 := by
                    have e : ((1:ℕ):ℝ)⁻¹ = 1 := by norm_num
                    rw [e]
                    linarith
          _ = 2 * ((PLam b lam).card : ℝ) := by ring
      have hbndD : ∑ m ∈ Finset.Icc 2 M,
          ∑ ℓ ∈ (((Pamb b lam).filter (fun ℓ => ℓ ^ m ≤ Ylam)).filter
            (fun ℓ => ¬ ℓ ∣ b ^ 2 - 1)).filter (fun ℓ => ¬ ℓ ∣ b),
            (b:ℝ) * (2 * Bnd (ℓ ^ m))
          ≤ κ * ((b:ℝ) ^ lam / (lam:ℝ)) := by
        have hperm : ∀ m ∈ Finset.Icc 2 M,
            ∑ ℓ ∈ (((Pamb b lam).filter (fun ℓ => ℓ ^ m ≤ Ylam)).filter
              (fun ℓ => ¬ ℓ ∣ b ^ 2 - 1)).filter (fun ℓ => ¬ ℓ ∣ b),
              Bnd (ℓ ^ m)
            ≤ C * (b:ℝ) ^ ((lam:ℝ) - c * Real.sqrt (lam:ℝ)) := by
          intro m hm
          rw [Finset.mem_Icc] at hm
          have hinj : ∀ x ∈ (((Pamb b lam).filter (fun ℓ => ℓ ^ m ≤ Ylam)).filter
              (fun ℓ => ¬ ℓ ∣ b ^ 2 - 1)).filter (fun ℓ => ¬ ℓ ∣ b),
              ∀ y ∈ (((Pamb b lam).filter (fun ℓ => ℓ ^ m ≤ Ylam)).filter
              (fun ℓ => ¬ ℓ ∣ b ^ 2 - 1)).filter (fun ℓ => ¬ ℓ ∣ b),
              x ^ m = y ^ m → x = y :=
            fun x _ y _ h => Nat.pow_left_injective (by omega : m ≠ 0) h
          rw [← Finset.sum_image hinj]
          have hsubm : ((((Pamb b lam).filter (fun ℓ => ℓ ^ m ≤ Ylam)).filter
              (fun ℓ => ¬ ℓ ∣ b ^ 2 - 1)).filter (fun ℓ => ¬ ℓ ∣ b)).image (· ^ m)
              ⊆ (Finset.Icc 1 (⌈(b : ℝ) ^ (ξw * (lam : ℝ))⌉₊)).filter
                (fun d => Nat.Coprime d (b * (b ^ 2 - 1))
                  ∧ (d : ℝ) ≤ (b : ℝ) ^ (ξw * (lam : ℝ))) := by
            intro d hd
            simp only [Finset.mem_image] at hd
            obtain ⟨ℓ, hℓ, rfl⟩ := hd
            rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_filter] at hℓ
            obtain ⟨⟨⟨hPam, hsm⟩, hnd21⟩, hndb⟩ := hℓ
            have hp : ℓ.Prime := (mem_Pamb.mp hPam).2
            have hcop : Nat.Coprime ℓ (b * (b ^ 2 - 1)) := by
              rw [Nat.Prime.coprime_iff_not_dvd hp]
              intro hdvd
              rcases (Nat.Prime.dvd_mul hp).mp hdvd with h | h
              · exact hndb h
              · exact hnd21 h
            have hdle : ((ℓ ^ m : ℕ) : ℝ) ≤ (b:ℝ) ^ (ξw * (lam:ℝ)) := by
              calc ((ℓ ^ m : ℕ) : ℝ) ≤ (Ylam : ℝ) := by exact_mod_cast hsm
                _ ≤ (b:ℝ) ^ (ξw * (lam:ℝ)) :=
                  Nat.floor_le (Real.rpow_nonneg hb0R.le _)
            simp only [Finset.mem_filter, Finset.mem_Icc]
            refine ⟨⟨Nat.one_le_pow _ _ hp.pos, ?_⟩,
              Nat.Coprime.pow_left _ hcop, hdle⟩
            have hle2 : ((ℓ ^ m : ℕ):ℝ) ≤ (⌈(b : ℝ) ^ (ξw * (lam : ℝ))⌉₊ : ℝ) :=
              le_trans hdle (Nat.le_ceil _)
            exact_mod_cast hle2
          calc ∑ d ∈ ((((Pamb b lam).filter (fun ℓ => ℓ ^ m ≤ Ylam)).filter
                (fun ℓ => ¬ ℓ ∣ b ^ 2 - 1)).filter (fun ℓ => ¬ ℓ ∣ b)).image
                  (· ^ m), Bnd d
              ≤ ∑ d ∈ (Finset.Icc 1 (⌈(b : ℝ) ^ (ξw * (lam : ℝ))⌉₊)).filter
                  (fun d => Nat.Coprime d (b * (b ^ 2 - 1))
                    ∧ (d : ℝ) ≤ (b : ℝ) ^ (ξw * (lam : ℝ))), Bnd d :=
                Finset.sum_le_sum_of_subset_of_nonneg hsubm (fun d _ _ => hB0 d)
            _ ≤ C * (b:ℝ) ^ ((lam:ℝ) - c * Real.sqrt (lam:ℝ)) := hBsum
        have hconv : (b:ℝ) ^ ((lam:ℝ) - c * Real.sqrt (lam:ℝ))
            = (b:ℝ) ^ lam * (b:ℝ) ^ (-(c * Real.sqrt (lam:ℝ))) := by
          rw [← Real.rpow_natCast (b:ℝ) lam, ← Real.rpow_add hb0R]
          congr 1
          try ring
        calc ∑ m ∈ Finset.Icc 2 M,
              ∑ ℓ ∈ (((Pamb b lam).filter (fun ℓ => ℓ ^ m ≤ Ylam)).filter
                (fun ℓ => ¬ ℓ ∣ b ^ 2 - 1)).filter (fun ℓ => ¬ ℓ ∣ b),
                (b:ℝ) * (2 * Bnd (ℓ ^ m))
            = ∑ m ∈ Finset.Icc 2 M,
                (2 * (b:ℝ)) * ∑ ℓ ∈ (((Pamb b lam).filter
                  (fun ℓ => ℓ ^ m ≤ Ylam)).filter
                  (fun ℓ => ¬ ℓ ∣ b ^ 2 - 1)).filter (fun ℓ => ¬ ℓ ∣ b),
                  Bnd (ℓ ^ m) := by
              refine Finset.sum_congr rfl fun m _ => ?_
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun ℓ _ => ?_
              ring
          _ ≤ ∑ _m ∈ Finset.Icc 2 M,
                (2 * (b:ℝ)) * (C * (b:ℝ) ^ ((lam:ℝ) - c * Real.sqrt (lam:ℝ))) := by
              refine Finset.sum_le_sum fun m hm => ?_
              refine mul_le_mul_of_nonneg_left (hperm m hm) ?_
              linarith
          _ = ((Finset.Icc 2 M).card : ℝ)
                * ((2 * (b:ℝ)) * (C * (b:ℝ) ^ ((lam:ℝ) - c * Real.sqrt (lam:ℝ)))) := by
              rw [Finset.sum_const, nsmul_eq_mul]
          _ ≤ ((b:ℝ) * (lam:ℝ))
                * ((2 * (b:ℝ)) * (C * (b:ℝ) ^ ((lam:ℝ) - c * Real.sqrt (lam:ℝ)))) := by
              refine mul_le_mul_of_nonneg_right ?_ ?_
              · have hcard : (Finset.Icc 2 M).card ≤ M := by
                  rw [Nat.card_Icc]
                  omega
                calc ((Finset.Icc 2 M).card : ℝ) ≤ (M:ℝ) := by exact_mod_cast hcard
                  _ = (b:ℝ) * (lam:ℝ) := by rw [hMdef]; push_cast; ring
              · have h1 : (0:ℝ) ≤ (b:ℝ) ^ ((lam:ℝ) - c * Real.sqrt (lam:ℝ)) :=
                  Real.rpow_nonneg hb0R.le _
                have h2 : (0:ℝ) ≤ C * (b:ℝ) ^ ((lam:ℝ) - c * Real.sqrt (lam:ℝ)) :=
                  mul_nonneg hC0 h1
                nlinarith [hb0R]
          _ ≤ κ * ((b:ℝ) ^ lam / (lam:ℝ)) := by
              rw [hconv]
              have hX0 : (0:ℝ) ≤ (b:ℝ) ^ (-(c * Real.sqrt (lam:ℝ))) :=
                Real.rpow_nonneg hb0R.le _
              rw [div_eq_mul_inv, ← sub_nonneg]
              have expand : κ * ((b:ℝ) ^ lam * ((lam:ℝ))⁻¹)
                  - (b:ℝ) * (lam:ℝ)
                    * (2 * (b:ℝ) * (C * ((b:ℝ) ^ lam
                      * (b:ℝ) ^ (-(c * Real.sqrt (lam:ℝ))))))
                  = ((κ - 2*(b:ℝ)^2*C * ((lam:ℝ)^(2:ℕ)
                      * (b:ℝ) ^ (-(c * Real.sqrt (lam:ℝ)))))
                      * (b:ℝ) ^ lam) / (lam:ℝ) := by
                field_simp
                try ring
              rw [expand]
              refine div_nonneg ?_ hlamR0.le
              refine mul_nonneg ?_ hpow0.le
              linarith [hD]
      calc ∑ m ∈ Finset.Icc 2 M,
            ∑ ℓ ∈ (((Pamb b lam).filter (fun ℓ => ℓ ^ m ≤ Ylam)).filter
              (fun ℓ => ¬ ℓ ∣ b ^ 2 - 1)).filter (fun ℓ => ¬ ℓ ∣ b),
              (((PLam b lam).filter fun p => ℓ ^ m ∣ rev b lam p).card : ℝ)
          ≤ ∑ m ∈ Finset.Icc 2 M,
              ∑ ℓ ∈ (((Pamb b lam).filter (fun ℓ => ℓ ^ m ≤ Ylam)).filter
                (fun ℓ => ¬ ℓ ∣ b ^ 2 - 1)).filter (fun ℓ => ¬ ℓ ∣ b),
                (((PLam b lam).card : ℝ) * ((ℓ:ℝ)⁻¹) ^ m
                  + (b:ℝ) * (2 * Bnd (ℓ ^ m))) :=
            Finset.sum_le_sum (fun m hm => Finset.sum_le_sum (hcntD m hm))
        _ = (∑ m ∈ Finset.Icc 2 M,
              ∑ ℓ ∈ (((Pamb b lam).filter (fun ℓ => ℓ ^ m ≤ Ylam)).filter
                (fun ℓ => ¬ ℓ ∣ b ^ 2 - 1)).filter (fun ℓ => ¬ ℓ ∣ b),
                ((PLam b lam).card : ℝ) * ((ℓ:ℝ)⁻¹) ^ m)
            + ∑ m ∈ Finset.Icc 2 M,
              ∑ ℓ ∈ (((Pamb b lam).filter (fun ℓ => ℓ ^ m ≤ Ylam)).filter
                (fun ℓ => ¬ ℓ ∣ b ^ 2 - 1)).filter (fun ℓ => ¬ ℓ ∣ b),
                (b:ℝ) * (2 * Bnd (ℓ ^ m)) := by
            rw [← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl fun m _ => ?_
            rw [← Finset.sum_add_distrib]
        _ ≤ 2 * ((PLam b lam).card : ℝ) + κ * ((b:ℝ) ^ lam / (lam:ℝ)) :=
            add_le_add hmainD hbndD
    -- ── Part L: large prime powers, the trivial bound ──
    have hN3 : 3 ≤ b ^ lam := by
      calc 3 ≤ 2^2 := by norm_num
        _ ≤ b^2 := Nat.pow_le_pow_left hb 2
        _ ≤ b^lam := Nat.pow_le_pow_right (by omega) (by omega)
    have hpRSle : primeRecipSum {p : ℕ | p.Prime} (b ^ lam) ≤ LL b lam + Cm := by
      have hmN := hmert (b ^ lam) hN3
      rw [one_mul] at hmN
      have hLLN : Real.log (Real.log ((b ^ lam : ℕ):ℝ)) = LL b lam := by
        unfold LL
        push_cast
        rfl
      have := (abs_le.mp hmN).2
      rw [hLLN] at this
      linarith
    have hytr2pos : (0:ℝ) < ytr b ξw 2 lam := ytr_pos hb
    have hboundL : ∑ m ∈ Finset.Icc 2 M,
        ∑ ℓ ∈ (Pamb b lam).filter (fun ℓ => ¬ ℓ ^ m ≤ Ylam),
          (((PLam b lam).filter fun p => ℓ ^ m ∣ rev b lam p).card : ℝ)
        ≤ κ * ((b:ℝ) ^ lam / (lam:ℝ)) := by
      have hptwL : ∀ m ∈ Finset.Icc 2 M,
          ∀ ℓ ∈ (Pamb b lam).filter (fun ℓ => ¬ ℓ ^ m ≤ Ylam),
          (((PLam b lam).filter fun p => ℓ ^ m ∣ rev b lam p).card : ℝ)
            ≤ (b:ℝ) ^ lam * ((1:ℝ)/(ℓ:ℝ) * (ytr b ξw 2 lam)⁻¹) := by
        intro m hm ℓ hℓ
        rw [Finset.mem_Icc] at hm
        rw [Finset.mem_filter] at hℓ
        obtain ⟨hPam, hlg⟩ := hℓ
        have hp : ℓ.Prime := (mem_Pamb.mp hPam).2
        have hℓ0 : (0:ℝ) < (ℓ:ℝ) := by exact_mod_cast hp.pos
        have h1 := card_dvd_rev_le hb (Nat.one_le_pow _ _ hp.pos)
          (hlam1) (d := ℓ ^ m)
        have hbig : (b:ℝ) ^ (ξw * (lam:ℝ)) < (ℓ:ℝ) ^ m := by
          have h2 : Ylam < ℓ ^ m := by omega
          have h3 := (Nat.floor_lt (Real.rpow_nonneg hb0R.le _)).mp h2
          calc (b:ℝ) ^ (ξw * (lam:ℝ)) < ((ℓ ^ m : ℕ):ℝ) := h3
            _ = (ℓ:ℝ) ^ m := by push_cast; rfl
        have hℓgt : ytr b ξw m lam < (ℓ:ℝ) := by
          by_contra hcon
          push_neg at hcon
          have h4 : (ℓ:ℝ) ^ m ≤ (ytr b ξw m lam) ^ m :=
            pow_le_pow_left' hℓ0.le hcon m
          rw [ytr_pow_K hb (by omega : 1 ≤ m) hξw0] at h4
          linarith
        have hpowge : ytr b ξw 2 lam ≤ (ℓ:ℝ) ^ (m - 1) := by
          have h5 : (ytr b ξw m lam) ^ (m - 1)
              = (b:ℝ) ^ (ξw * (lam:ℝ) * (((m:ℝ) - 1) / (m:ℝ))) := by
            unfold ytr
            rw [← Real.rpow_natCast ((b:ℝ) ^ (ξw * (lam:ℝ) / ((m:ℕ):ℝ))) (m - 1),
              ← Real.rpow_mul hb0R.le]
            congr 1
            have hc : ((m - 1 : ℕ):ℝ) = (m:ℝ) - 1 := by
              have h1m : (1:ℕ) ≤ m := by omega
              rw [Nat.cast_sub h1m]
              norm_num
            have hm0 : ((m:ℕ):ℝ) ≠ 0 := by
              have : (0:ℕ) < m := by omega
              positivity
            rw [hc]
            field_simp
            try ring
          have h6 : ytr b ξw 2 lam
              ≤ (b:ℝ) ^ (ξw * (lam:ℝ) * (((m:ℝ) - 1) / (m:ℝ))) := by
            unfold ytr
            rw [Real.rpow_le_rpow_left_iff hbR]
            have hm2R : (2:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm.1
            have hm0 : (0:ℝ) < (m:ℝ) := by linarith
            have hxil : (0:ℝ) ≤ ξw * (lam:ℝ) :=
              mul_nonneg hξw0.le (by positivity)
            have hfrac : (1:ℝ)/2 ≤ ((m:ℝ) - 1) / (m:ℝ) := by
              rw [div_le_div_iff₀ (by norm_num) hm0]
              linarith
            have hpc : ((2:ℕ):ℝ) = (2:ℝ) := by norm_num
            calc ξw * (lam:ℝ) / ((2:ℕ):ℝ) = ξw * (lam:ℝ) * ((1:ℝ)/2) := by
                  rw [hpc]
                  ring
              _ ≤ ξw * (lam:ℝ) * (((m:ℝ) - 1) / (m:ℝ)) :=
                  mul_le_mul_of_nonneg_left hfrac hxil
          have h7 : (ytr b ξw m lam) ^ (m - 1) ≤ (ℓ:ℝ) ^ (m - 1) :=
            pow_le_pow_left' (ytr_nonneg hb) hℓgt.le _
          calc ytr b ξw 2 lam
              ≤ (b:ℝ) ^ (ξw * (lam:ℝ) * (((m:ℝ) - 1) / (m:ℝ))) := h6
            _ = (ytr b ξw m lam) ^ (m - 1) := h5.symm
            _ ≤ (ℓ:ℝ) ^ (m - 1) := h7
        have hkey : (((ℓ ^ m : ℕ)):ℝ)⁻¹ ≤ (1:ℝ)/(ℓ:ℝ) * (ytr b ξw 2 lam)⁻¹ := by
          have e1 : ((ℓ:ℝ)) ^ m = (ℓ:ℝ) * (ℓ:ℝ) ^ (m - 1) := by
            have e2 : m = 1 + (m - 1) := by omega
            calc ((ℓ:ℝ)) ^ m = ((ℓ:ℝ)) ^ (1 + (m - 1)) := by rw [← e2]
              _ = (ℓ:ℝ) * (ℓ:ℝ) ^ (m - 1) := by rw [pow_add, pow_one]
          have hge : (ℓ:ℝ) * ytr b ξw 2 lam ≤ (ℓ:ℝ) * (ℓ:ℝ) ^ (m - 1) :=
            mul_le_mul_of_nonneg_left hpowge hℓ0.le
          have hpos2 : (0:ℝ) < (ℓ:ℝ) * ytr b ξw 2 lam := mul_pos hℓ0 hytr2pos
          have hcast : (((ℓ ^ m : ℕ)):ℝ) = (ℓ:ℝ) ^ m := by push_cast; rfl
          rw [hcast, e1]
          calc ((ℓ:ℝ) * (ℓ:ℝ) ^ (m - 1))⁻¹
              ≤ ((ℓ:ℝ) * ytr b ξw 2 lam)⁻¹ := inv_le_inv_of_le' hpos2 hge
            _ = (1:ℝ)/(ℓ:ℝ) * (ytr b ξw 2 lam)⁻¹ := by
                rw [mul_inv, one_div]
        calc (((PLam b lam).filter fun p => ℓ ^ m ∣ rev b lam p).card : ℝ)
            ≤ (b:ℝ) ^ lam / ((ℓ ^ m : ℕ):ℝ) := h1
          _ = (b:ℝ) ^ lam * (((ℓ ^ m : ℕ)):ℝ)⁻¹ := by
              rw [div_eq_mul_inv]
          _ ≤ (b:ℝ) ^ lam * ((1:ℝ)/(ℓ:ℝ) * (ytr b ξw 2 lam)⁻¹) :=
              mul_le_mul_of_nonneg_left hkey hpow0.le
      have hperL : ∀ m ∈ Finset.Icc 2 M,
          ∑ ℓ ∈ (Pamb b lam).filter (fun ℓ => ¬ ℓ ^ m ≤ Ylam),
            (((PLam b lam).filter fun p => ℓ ^ m ∣ rev b lam p).card : ℝ)
          ≤ (b:ℝ) ^ lam * (ytr b ξw 2 lam)⁻¹ * (LL b lam + Cm) := by
        intro m hm
        have hsum1 : ∑ ℓ ∈ (Pamb b lam).filter (fun ℓ => ¬ ℓ ^ m ≤ Ylam),
            (1:ℝ)/(ℓ:ℝ) ≤ LL b lam + Cm := by
          have h1 : ∀ ℓ ∈ (Pamb b lam).filter (fun ℓ => ¬ ℓ ^ m ≤ Ylam),
              ℓ.Prime ∧ ℓ ≤ b ^ lam := by
            intro ℓ hℓ
            rw [Finset.mem_filter] at hℓ
            have hmem := mem_Pamb.mp hℓ.1
            exact ⟨hmem.2, by omega⟩
          exact le_trans (sum_primes_le h1) hpRSle
        calc ∑ ℓ ∈ (Pamb b lam).filter (fun ℓ => ¬ ℓ ^ m ≤ Ylam),
              (((PLam b lam).filter fun p => ℓ ^ m ∣ rev b lam p).card : ℝ)
            ≤ ∑ ℓ ∈ (Pamb b lam).filter (fun ℓ => ¬ ℓ ^ m ≤ Ylam),
                (b:ℝ) ^ lam * ((1:ℝ)/(ℓ:ℝ) * (ytr b ξw 2 lam)⁻¹) :=
              Finset.sum_le_sum (hptwL m hm)
          _ = (b:ℝ) ^ lam * (ytr b ξw 2 lam)⁻¹
                * ∑ ℓ ∈ (Pamb b lam).filter (fun ℓ => ¬ ℓ ^ m ≤ Ylam),
                  (1:ℝ)/(ℓ:ℝ) := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun ℓ _ => ?_
              ring
          _ ≤ (b:ℝ) ^ lam * (ytr b ξw 2 lam)⁻¹ * (LL b lam + Cm) := by
              refine mul_le_mul_of_nonneg_left hsum1 ?_
              exact mul_nonneg hpow0.le (by positivity)
      calc ∑ m ∈ Finset.Icc 2 M,
            ∑ ℓ ∈ (Pamb b lam).filter (fun ℓ => ¬ ℓ ^ m ≤ Ylam),
              (((PLam b lam).filter fun p => ℓ ^ m ∣ rev b lam p).card : ℝ)
          ≤ ∑ _m ∈ Finset.Icc 2 M,
              (b:ℝ) ^ lam * (ytr b ξw 2 lam)⁻¹ * (LL b lam + Cm) :=
            Finset.sum_le_sum hperL
        _ = ((Finset.Icc 2 M).card : ℝ)
              * ((b:ℝ) ^ lam * (ytr b ξw 2 lam)⁻¹ * (LL b lam + Cm)) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ((b:ℝ) * (lam:ℝ))
              * ((b:ℝ) ^ lam * (ytr b ξw 2 lam)⁻¹ * (LL b lam + Cm)) := by
            refine mul_le_mul_of_nonneg_right ?_ ?_
            · have hcard : (Finset.Icc 2 M).card ≤ M := by
                rw [Nat.card_Icc]
                omega
              calc ((Finset.Icc 2 M).card : ℝ) ≤ (M:ℝ) := by exact_mod_cast hcard
                _ = (b:ℝ) * (lam:ℝ) := by rw [hMdef]; push_cast; ring
            · refine mul_nonneg (mul_nonneg hpow0.le (by positivity)) ?_
              linarith
        _ ≤ κ * ((b:ℝ) ^ lam / (lam:ℝ)) := by
            rw [div_eq_mul_inv, ← sub_nonneg]
            have expand : κ * ((b:ℝ) ^ lam * ((lam:ℝ))⁻¹)
                - (b:ℝ) * (lam:ℝ)
                  * ((b:ℝ) ^ lam * (ytr b ξw 2 lam)⁻¹ * (LL b lam + Cm))
                = ((κ - (b:ℝ) * (lam:ℝ)^2 * (LL b lam + Cm)
                      * (ytr b ξw 2 lam)⁻¹) * (b:ℝ) ^ lam) / (lam:ℝ) := by
              field_simp
              try ring
            rw [expand]
            refine div_nonneg ?_ hlamR0.le
            refine mul_nonneg ?_ hpow0.le
            have hLdiv : (b:ℝ) * (lam:ℝ)^2 * (LL b lam + Cm)
                * (ytr b ξw 2 lam)⁻¹
                = (b:ℝ) * (lam:ℝ)^2 * (LL b lam + Cm) / ytr b ξw 2 lam := by
              rw [div_eq_mul_inv]
            rw [hLdiv]
            linarith [hL]
    -- ── assemble the four parts ──
    have hZsum : ∑ m ∈ Finset.Icc 2 M,
        ∑ ℓ ∈ ((Pamb b lam).filter (fun ℓ => ℓ ^ m ≤ Ylam)).filter
          (fun ℓ => ℓ ∣ b ^ 2 - 1),
          (((PLam b lam).filter fun p => ℓ ^ m ∣ rev b lam p).card : ℝ) = 0 :=
      Finset.sum_eq_zero fun m hm => Finset.sum_eq_zero (hboundZ m hm)
    have hsplit : ∀ m ∈ Finset.Icc 2 M,
        ∑ ℓ ∈ Pamb b lam,
          (((PLam b lam).filter fun p => ℓ ^ m ∣ rev b lam p).card : ℝ)
        = ((∑ ℓ ∈ ((Pamb b lam).filter (fun ℓ => ℓ ^ m ≤ Ylam)).filter
              (fun ℓ => ℓ ∣ b ^ 2 - 1),
              (((PLam b lam).filter fun p => ℓ ^ m ∣ rev b lam p).card : ℝ))
            + ((∑ ℓ ∈ (((Pamb b lam).filter (fun ℓ => ℓ ^ m ≤ Ylam)).filter
                (fun ℓ => ¬ ℓ ∣ b ^ 2 - 1)).filter (fun ℓ => ℓ ∣ b),
                (((PLam b lam).filter fun p => ℓ ^ m ∣ rev b lam p).card : ℝ))
              + (∑ ℓ ∈ (((Pamb b lam).filter (fun ℓ => ℓ ^ m ≤ Ylam)).filter
                (fun ℓ => ¬ ℓ ∣ b ^ 2 - 1)).filter (fun ℓ => ¬ ℓ ∣ b),
                (((PLam b lam).filter fun p => ℓ ^ m ∣ rev b lam p).card : ℝ))))
          + ∑ ℓ ∈ (Pamb b lam).filter (fun ℓ => ¬ ℓ ^ m ≤ Ylam),
              (((PLam b lam).filter fun p => ℓ ^ m ∣ rev b lam p).card : ℝ) := by
      intro m _
      have h1 := Finset.sum_filter_add_sum_filter_not (Pamb b lam)
        (fun ℓ => ℓ ^ m ≤ Ylam)
        (fun ℓ => (((PLam b lam).filter fun p => ℓ ^ m ∣ rev b lam p).card : ℝ))
      have h2 := Finset.sum_filter_add_sum_filter_not
        ((Pamb b lam).filter (fun ℓ => ℓ ^ m ≤ Ylam))
        (fun ℓ => ℓ ∣ b ^ 2 - 1)
        (fun ℓ => (((PLam b lam).filter fun p => ℓ ^ m ∣ rev b lam p).card : ℝ))
      have h3 := Finset.sum_filter_add_sum_filter_not
        (((Pamb b lam).filter (fun ℓ => ℓ ^ m ≤ Ylam)).filter
          (fun ℓ => ¬ ℓ ∣ b ^ 2 - 1))
        (fun ℓ => ℓ ∣ b)
        (fun ℓ => (((PLam b lam).filter fun p => ℓ ^ m ∣ rev b lam p).card : ℝ))
      linarith
    have hκb0 : (0:ℝ) ≤ (b:ℝ) ^ lam / (lam:ℝ) := by positivity
    have hG0 : (0:ℝ) ≤ ((b:ℝ)+1) * (2 * CBT / Real.log b) + 2 * Cu + 2 * κ := by
      have h1 : (0:ℝ) ≤ ((b:ℝ)+1) * (2 * CBT / Real.log b) :=
        mul_nonneg (by linarith) hK0
      linarith
    calc ∑ n ∈ AFam b i lam, ((bigOmega n : ℝ) - (smallOmega n : ℝ))
        ≤ ∑ p ∈ PLam b lam,
            ((bigOmega (rev b lam p) : ℝ) - (smallOmega (rev b lam p) : ℝ)) :=
          hchain
      _ = ∑ m ∈ Finset.Icc 2 M, ∑ ℓ ∈ Pamb b lam,
            (((PLam b lam).filter fun p => ℓ ^ m ∣ rev b lam p).card : ℝ) := hid
      _ = (∑ m ∈ Finset.Icc 2 M,
            ∑ ℓ ∈ ((Pamb b lam).filter (fun ℓ => ℓ ^ m ≤ Ylam)).filter
              (fun ℓ => ℓ ∣ b ^ 2 - 1),
              (((PLam b lam).filter fun p => ℓ ^ m ∣ rev b lam p).card : ℝ))
          + ((∑ m ∈ Finset.Icc 2 M,
              ∑ ℓ ∈ (((Pamb b lam).filter (fun ℓ => ℓ ^ m ≤ Ylam)).filter
                (fun ℓ => ¬ ℓ ∣ b ^ 2 - 1)).filter (fun ℓ => ℓ ∣ b),
                (((PLam b lam).filter fun p => ℓ ^ m ∣ rev b lam p).card : ℝ))
            + (∑ m ∈ Finset.Icc 2 M,
              ∑ ℓ ∈ (((Pamb b lam).filter (fun ℓ => ℓ ^ m ≤ Ylam)).filter
                (fun ℓ => ¬ ℓ ∣ b ^ 2 - 1)).filter (fun ℓ => ¬ ℓ ∣ b),
                (((PLam b lam).filter fun p => ℓ ^ m ∣ rev b lam p).card : ℝ)))
          + ∑ m ∈ Finset.Icc 2 M,
              ∑ ℓ ∈ (Pamb b lam).filter (fun ℓ => ¬ ℓ ^ m ≤ Ylam),
                (((PLam b lam).filter fun p => ℓ ^ m ∣ rev b lam p).card : ℝ) := by
          rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib,
            Finset.sum_add_distrib, Finset.sum_add_distrib]
      _ ≤ 0 + ((((b:ℝ)+1) * (2 * CBT / Real.log b) * ((b:ℝ) ^ lam / (lam:ℝ)))
            + (2 * ((PLam b lam).card : ℝ) + κ * ((b:ℝ) ^ lam / (lam:ℝ))))
          + κ * ((b:ℝ) ^ lam / (lam:ℝ)) := by
          refine add_le_add (add_le_add (le_of_eq hZsum)
            (add_le_add hboundB hboundD)) hboundL
      _ ≤ (((b:ℝ)+1) * (2 * CBT / Real.log b) + 2 * Cu + 2 * κ)
            * ((b:ℝ) ^ lam / (lam:ℝ)) := by
          have hπup : ((PLam b lam).card : ℝ) ≤ Cu * (b:ℝ) ^ lam / (lam:ℝ) :=
            hCulam
          have e1 : Cu * (b:ℝ) ^ lam / (lam:ℝ)
              = Cu * ((b:ℝ) ^ lam / (lam:ℝ)) := by ring
          rw [e1] at hπup
          nlinarith [hκb0, hπup]
      _ ≤ ((((b:ℝ)+1) * (2 * CBT / Real.log b) + 2 * Cu + 2 * κ) / κ)
            * ((AFam b i lam).card : ℝ) := by
          rw [hAcard]
          have h1 : κ * ((b:ℝ) ^ lam / (lam:ℝ)) ≤ ((PLamI b lam i).card : ℝ) := by
            have e2 : κ * ((b:ℝ) ^ lam / (lam:ℝ))
                = κ * (b:ℝ) ^ lam / (lam:ℝ) := by ring
            rw [e2]
            exact hκlam
          calc (((b:ℝ)+1) * (2 * CBT / Real.log b) + 2 * Cu + 2 * κ)
                * ((b:ℝ) ^ lam / (lam:ℝ))
              = ((((b:ℝ)+1) * (2 * CBT / Real.log b) + 2 * Cu + 2 * κ) / κ)
                  * (κ * ((b:ℝ) ^ lam / (lam:ℝ))) := by
                field_simp
            _ ≤ ((((b:ℝ)+1) * (2 * CBT / Real.log b) + 2 * Cu + 2 * κ) / κ)
                  * ((PLamI b lam i).card : ℝ) := by
                refine mul_le_mul_of_nonneg_left h1 ?_
                exact div_nonneg hG0 hκ0.le

end EKRev
