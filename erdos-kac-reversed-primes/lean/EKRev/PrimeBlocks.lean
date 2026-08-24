/-
EKRev/PrimeBlocks.lean

Prime blocks: `𝒫_λ` (primes with `λ` base-`b` digits), the leading-digit
blocks `𝒫_{λ,i}`, the reversed sets `𝒜_λ, 𝒜_{λ,i}` (eq. (1.6)), the counting
function π, and the transfer of divisor counts through the injectivity of the
reversal (§1.2 discussion after eq. (1.6), and eq. (4.2)).

Everything in this file is fully proved (no axioms).
-/
import Mathlib.Tactic
import EKRev.PalCount

namespace EKRev

open Finset

/-! ### Prime counting -/

/-- `π(x)`: the number of primes `< x`. -/
def pic (x : ℕ) : ℕ := ((Finset.range x).filter Nat.Prime).card

/-- Primes in `[x, y)`. -/
def primesIn (x y : ℕ) : Finset ℕ := (Finset.Ico x y).filter Nat.Prime

lemma pic_add_primesIn_card (h : x ≤ y) : pic x + (primesIn x y).card = pic y := by
  unfold pic primesIn
  rw [Finset.range_eq_Ico, Finset.range_eq_Ico,
    ← Finset.card_union_of_disjoint (Finset.disjoint_filter_filter
      (Finset.Ico_disjoint_Ico_consecutive 0 x y))]
  congr 1
  rw [← Finset.filter_union, Finset.Ico_union_Ico_eq_Ico (Nat.zero_le x) h]

lemma primesIn_card_mono_right (h : y ≤ z) (x : ℕ) :
    (primesIn x y).card ≤ (primesIn x z).card := by
  refine Finset.card_le_card (Finset.filter_subset_filter _ ?_)
  exact Finset.Ico_subset_Ico le_rfl h

/-- Splitting `[x, z) = [x, y) ∪ [y, z)` splits the prime count. -/
lemma primesIn_card_split (h1 : x ≤ y) (h2 : y ≤ z) :
    (primesIn x y).card + (primesIn y z).card = (primesIn x z).card := by
  unfold primesIn
  rw [← Finset.card_union_of_disjoint]
  · congr 1
    rw [← Finset.filter_union, Finset.Ico_union_Ico_eq_Ico h1 h2]
  · exact Finset.disjoint_filter_filter (Finset.Ico_disjoint_Ico_consecutive x y z)

/-! ### The blocks -/

/-- `𝒫_λ`: primes with exactly `λ` base-`b` digits. -/
def PLam (b lam : ℕ) : Finset ℕ := primesIn (b ^ (lam - 1)) (b ^ lam)

/-- `𝒫_{λ,i}`: primes with `λ` digits and leading digit `i` (§1.2):
`𝒫_{λ,i} = {p prime : i b^{λ-1} ≤ p < (i+1) b^{λ-1}}`. -/
def PLamI (b lam i : ℕ) : Finset ℕ :=
  primesIn (i * b ^ (lam - 1)) ((i + 1) * b ^ (lam - 1))

/-- `𝒜_λ`: reversals of the `λ`-digit primes (eq. (1.6)). -/
def ALam (b lam : ℕ) : Finset ℕ := (PLam b lam).image (rev b lam)

/-- `𝒜_{λ,i}` (eq. (1.6)). -/
def ALamI (b lam i : ℕ) : Finset ℕ := (PLamI b lam i).image (rev b lam)

lemma mem_PLam_iff : p ∈ PLam b lam ↔ b ^ (lam - 1) ≤ p ∧ p < b ^ lam ∧ p.Prime := by
  simp [PLam, primesIn, Finset.mem_filter, Finset.mem_Ico, and_assoc]

lemma mem_PLamI_iff : p ∈ PLamI b lam i ↔
    i * b ^ (lam - 1) ≤ p ∧ p < (i + 1) * b ^ (lam - 1) ∧ p.Prime := by
  simp [PLamI, primesIn, Finset.mem_filter, Finset.mem_Ico, and_assoc]

lemma PLamI_subset_PLam (hb : 2 ≤ b) (hlam : 1 ≤ lam) (hi1 : 1 ≤ i) (hi2 : i ≤ b - 1) :
    PLamI b lam i ⊆ PLam b lam := by
  intro p hp
  rw [mem_PLamI_iff] at hp
  rw [mem_PLam_iff]
  obtain ⟨h1, h2, h3⟩ := hp
  have hB : 0 < b ^ (lam - 1) := Nat.pos_pow_of_pos _ (by omega)
  refine ⟨?_, ?_, h3⟩
  · calc b ^ (lam - 1) = 1 * b ^ (lam - 1) := by ring
      _ ≤ i * b ^ (lam - 1) := Nat.mul_le_mul_right _ hi1
      _ ≤ p := h1
  · calc p < (i + 1) * b ^ (lam - 1) := h2
      _ ≤ b * b ^ (lam - 1) := Nat.mul_le_mul_right _ (by omega)
      _ = b ^ lam := by rw [← pow_succ']; congr 1; omega

lemma PLam_subset_lt (hb : 2 ≤ b) : ∀ p ∈ PLam b lam, p < b ^ lam := by
  intro p hp
  exact (mem_PLam_iff.mp hp).2.1

/-- `𝒫_λ` is the disjoint union of the `𝒫_{λ,i}`, `1 ≤ i ≤ b-1` (§1.2). -/
lemma PLam_eq_biUnion (hb : 2 ≤ b) (hlam : 1 ≤ lam) :
    PLam b lam = (Finset.Icc 1 (b - 1)).biUnion (fun i => PLamI b lam i) := by
  ext p
  rw [mem_PLam_iff]
  simp only [Finset.mem_biUnion, Finset.mem_Icc]
  constructor
  · rintro ⟨h1, h2, h3⟩
    set B := b ^ (lam - 1) with hBdef
    have hB : 0 < B := Nat.pos_pow_of_pos _ (by omega)
    set i := p / B with hidef
    have hge : i * B ≤ p := by
      rw [hidef, Nat.mul_comm]
      exact Nat.mul_div_le p B
    have hlt : p < (i + 1) * B := by
      have hdm := Nat.div_add_mod p B
      have hml := Nat.mod_lt p hB
      calc p = B * (p / B) + p % B := hdm.symm
        _ < B * (p / B) + B := by omega
        _ = (p / B + 1) * B := by ring
        _ = (i + 1) * B := by rw [hidef]
    refine ⟨i, ⟨?_, ?_⟩, ?_⟩
    · rw [hidef]
      exact (Nat.one_le_div_iff hB).mpr h1
    · have : p < b * B := by
        calc p < b ^ lam := h2
          _ = b * B := by rw [hBdef, ← pow_succ']; congr 1; omega
      have hib : i < b := by
        rw [hidef]
        exact Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm] at this)
      omega
    · rw [mem_PLamI_iff]
      exact ⟨hge, hlt, h3⟩
  · rintro ⟨i, ⟨hi1, hi2⟩, hp⟩
    have := PLamI_subset_PLam hb hlam hi1 hi2 hp
    rw [mem_PLam_iff] at this
    exact this

/-- The blocks are pairwise disjoint, so the cardinalities add up. -/
lemma PLam_card_eq_sum (hb : 2 ≤ b) (hlam : 1 ≤ lam) :
    (PLam b lam).card = ∑ i ∈ Finset.Icc 1 (b - 1), (PLamI b lam i).card := by
  rw [PLam_eq_biUnion hb hlam]
  refine Finset.card_biUnion ?_
  intro i _ j _ hij
  refine Finset.disjoint_left.mpr ?_
  intro p hpi hpj
  rw [mem_PLamI_iff] at hpi hpj
  set B := b ^ (lam - 1) with hBdef
  have hB : 0 < B := Nat.pos_pow_of_pos _ (by omega)
  rcases Nat.lt_or_ge i j with h | h
  · have : (i + 1) * B ≤ j * B := Nat.mul_le_mul_right _ (by omega)
    omega
  · have hji : j < i := by omega
    have : (j + 1) * B ≤ i * B := Nat.mul_le_mul_right _ (by omega)
    omega

/-- The leading digit of `p ∈ 𝒫_{λ,i}` is `i` (remark after eq. (1.6):
"`i` is the last digit of `R_λ(p)`" pairs with this via `digit_rev`). -/
lemma digit_top_of_mem_PLamI (hb : 2 ≤ b) (hlam : 1 ≤ lam) (hi2 : i ≤ b - 1)
    (hp : p ∈ PLamI b lam i) : digit b p (lam - 1) = i := by
  rw [mem_PLamI_iff] at hp
  obtain ⟨h1, h2, _⟩ := hp
  have hB : 0 < b ^ (lam - 1) := Nat.pos_pow_of_pos _ (by omega)
  have hplt : p < b ^ lam := by
    calc p < (i + 1) * b ^ (lam - 1) := h2
      _ ≤ b * b ^ (lam - 1) := Nat.mul_le_mul_right _ (by omega)
      _ = b ^ lam := by rw [← pow_succ']; congr 1; omega
  rw [digit_top_eq hplt hlam]
  exact Nat.div_eq_of_lt_le h1 h2

/-! ### Transfer through the reversal -/

lemma ALamI_card (hb : 2 ≤ b) (hlam : 1 ≤ lam) (hi2 : i + 1 ≤ b) :
    (ALamI b lam i).card = (PLamI b lam i).card := by
  refine Finset.card_image_of_injOn ?_
  intro x hx y hy hxy
  have hsub : ∀ q ∈ PLamI b lam i, q < b ^ lam := by
    intro q hq
    rw [mem_PLamI_iff] at hq
    calc q < (i + 1) * b ^ (lam - 1) := hq.2.1
      _ ≤ b * b ^ (lam - 1) := Nat.mul_le_mul_right _ hi2
      _ = b ^ lam := by rw [← pow_succ']; congr 1; omega
  exact rev_injOn (by omega) lam (hsub x hx) (hsub y hy) hxy

lemma ALam_card (hb : 2 ≤ b) : (ALam b lam).card = (PLam b lam).card := by
  refine Finset.card_image_of_injOn ?_
  intro x hx y hy hxy
  exact rev_injOn (by omega : (0:ℕ) < b) lam
    (PLam_subset_lt hb x hx) (PLam_subset_lt hb y hy) hxy

/-- Divisor counts transfer: `#{n ∈ 𝒜_{λ,i} : d ∣ n} = #{p ∈ 𝒫_{λ,i} : d ∣ R_λ(p)}`. -/
lemma ALamI_filter_dvd_card (hb : 2 ≤ b) (hlam : 1 ≤ lam) (hi2 : i + 1 ≤ b) (d : ℕ) :
    ((ALamI b lam i).filter (fun n => d ∣ n)).card
      = ((PLamI b lam i).filter (fun p => d ∣ rev b lam p)).card := by
  unfold ALamI
  rw [Finset.filter_image]
  refine Finset.card_image_of_injOn ?_
  intro x hx y hy hxy
  rw [Finset.mem_coe, Finset.mem_filter] at hx hy
  have hsub : ∀ q ∈ PLamI b lam i, q < b ^ lam := by
    intro q hq
    rw [mem_PLamI_iff] at hq
    calc q < (i + 1) * b ^ (lam - 1) := hq.2.1
      _ ≤ b * b ^ (lam - 1) := Nat.mul_le_mul_right _ hi2
      _ = b ^ lam := by rw [← pow_succ']; congr 1; omega
  exact rev_injOn (by omega) lam (hsub x hx.1) (hsub y hy.1) hxy

/-- Positivity of the reversal of a positive `n < b^λ`. -/
lemma rev_pos (hb : 0 < b) (hn : n < b ^ lam) (h0 : 1 ≤ n) : 1 ≤ rev b lam n := by
  by_contra hcon
  push_neg at hcon
  have hz : rev b lam n = 0 := by omega
  have hall : ∀ j < lam, digit b n j = 0 := by
    intro j hj
    have := Finset.sum_eq_zero_iff.mp hz j (Finset.mem_range.mpr hj)
    have hbp : 0 < b ^ (lam - 1 - j) := Nat.pos_pow_of_pos _ hb
    rcases Nat.mul_eq_zero.mp this with h | h
    · exact h
    · omega
  have : n = 0 := by
    rw [← sum_digit_mul_pow_self hb hn]
    exact Finset.sum_eq_zero fun j hj => by
      rw [hall j (Finset.mem_range.mp hj)]
      ring
  omega

/-- The trivial bound (eq. (4.2)): the reversals are distinct positive integers
below `b^λ`, so at most `b^λ/d` of them are divisible by `d`. -/
lemma card_dvd_rev_le (hb : 2 ≤ b) (hd : 1 ≤ d) (hlam : 1 ≤ lam) :
    (((PLam b lam).filter (fun p => d ∣ rev b lam p)).card : ℝ)
      ≤ (b : ℝ) ^ lam / d := by
  have hb0 : 0 < b := by omega
  have hinj : Set.InjOn (rev b lam) ↑((PLam b lam).filter (fun p => d ∣ rev b lam p)) := by
    intro x hx y hy hxy
    rw [Finset.mem_coe, Finset.mem_filter] at hx hy
    exact rev_injOn hb0 lam (PLam_subset_lt hb x hx.1) (PLam_subset_lt hb y hy.1) hxy
  have hmaps : ∀ p ∈ (PLam b lam).filter (fun p => d ∣ rev b lam p),
      rev b lam p ∈ (Finset.Ico 1 (b ^ lam)).filter (fun n => d ∣ n) := by
    intro p hp
    rw [Finset.mem_filter] at hp
    obtain ⟨hpP, hpd⟩ := hp
    rw [mem_PLam_iff] at hpP
    rw [Finset.mem_filter, Finset.mem_Ico]
    have hp1 : 1 ≤ p := by
      have := hpP.2.2.two_le
      omega
    exact ⟨⟨rev_pos hb0 hpP.2.1 hp1, rev_lt hb0 lam p⟩, hpd⟩
  have hcard : ((PLam b lam).filter (fun p => d ∣ rev b lam p)).card
      ≤ ((Finset.Ico 1 (b ^ lam)).filter (fun n => d ∣ n)).card :=
    Finset.card_le_card_of_injOn _ hmaps hinj
  calc (((PLam b lam).filter (fun p => d ∣ rev b lam p)).card : ℝ)
      ≤ (((Finset.Ico 1 (b ^ lam)).filter (fun n => d ∣ n)).card : ℝ) := by
        exact_mod_cast hcard
    _ ≤ ((b ^ lam : ℕ) : ℝ) / d := card_multiples_lt hd _
    _ = (b : ℝ) ^ lam / d := by push_cast; ring_nf

/-! ### The counting function `π̄_λ(z, a, d)` of §4.2 -/

/-- `π̄_λ(z,a,d)`: the number of primes `b^{λ-1} ≤ p < z` with
`R_λ(p) ≡ a (mod d)` (§4.2; residues via `% d`, so `a = d` is the class `0`). -/
def revCount (b lam z d a : ℕ) : ℕ :=
  ((primesIn (b ^ (lam - 1)) z).filter fun p => rev b lam p % d = a % d).card

/-- `π_λ(z)` of §4.2: primes `b^{λ-1} ≤ p < z`. -/
def picLam (b lam z : ℕ) : ℕ := (primesIn (b ^ (lam - 1)) z).card

/-- Divisibility as the residue class `a = d`. -/
lemma filter_dvd_eq_filter_mod (s : Finset ℕ) (d : ℕ) :
    (s.filter fun n => d ∣ n) = s.filter fun n => n % d = d % d := by
  refine Finset.filter_congr fun n _ => ?_
  rw [Nat.mod_self]
  constructor
  · rintro ⟨c, rfl⟩
    exact Nat.mul_mod_right d c
  · intro h
    exact Nat.dvd_of_mod_eq_zero h

/-- Block counts as differences of the cumulative counts (proof of Lemma 4.4):
`#{p ∈ 𝒫_{λ,i} : R_λ(p) ≡ a (d)}` is `π̄_λ((i+1)b^{λ-1},a,d) - π̄_λ(i b^{λ-1},a,d)`,
stated additively. -/
lemma revCount_block (hb : 2 ≤ b) (hlam : 1 ≤ lam) (hi1 : 1 ≤ i) (hi2 : i ≤ b - 1)
    (d a : ℕ) :
    revCount b lam (i * b ^ (lam - 1)) d a
      + ((PLamI b lam i).filter fun p => rev b lam p % d = a % d).card
      = revCount b lam ((i + 1) * b ^ (lam - 1)) d a := by
  unfold revCount PLamI
  have hB : 0 < b ^ (lam - 1) := Nat.pos_pow_of_pos _ (by omega)
  have h1 : b ^ (lam - 1) ≤ i * b ^ (lam - 1) := by
    calc b ^ (lam - 1) = 1 * b ^ (lam - 1) := by ring
      _ ≤ i * b ^ (lam - 1) := Nat.mul_le_mul_right _ hi1
  have h2 : i * b ^ (lam - 1) ≤ (i + 1) * b ^ (lam - 1) :=
    Nat.mul_le_mul_right _ (by omega)
  unfold primesIn
  rw [← Finset.card_union_of_disjoint, ← Finset.filter_union, ← Finset.filter_union,
    Finset.Ico_union_Ico_eq_Ico h1 h2]
  exact Finset.disjoint_filter_filter (Finset.disjoint_filter_filter
    (Finset.Ico_disjoint_Ico_consecutive _ _ _))

/-- Same additive splitting for the plain prime counts. -/
lemma picLam_block (hb : 2 ≤ b) (hlam : 1 ≤ lam) (hi1 : 1 ≤ i) :
    picLam b lam (i * b ^ (lam - 1)) + (PLamI b lam i).card
      = picLam b lam ((i + 1) * b ^ (lam - 1)) := by
  unfold picLam PLamI
  have hB : 0 < b ^ (lam - 1) := Nat.pos_pow_of_pos _ (by omega)
  have h1 : b ^ (lam - 1) ≤ i * b ^ (lam - 1) := by
    calc b ^ (lam - 1) = 1 * b ^ (lam - 1) := by ring
      _ ≤ i * b ^ (lam - 1) := Nat.mul_le_mul_right _ hi1
  have h2 : i * b ^ (lam - 1) ≤ (i + 1) * b ^ (lam - 1) :=
    Nat.mul_le_mul_right _ (by omega)
  exact primesIn_card_split h1 h2

end EKRev
