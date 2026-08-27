/-
DSS/Squares.lean

**Theorem 1.10 of the paper**: for every base `b ≥ 2` and every sufficiently
large admissible `q` (every large `q` when `b = 2`), the equation
`s_b(n²) = q` has at least `2^(√q/(36b))` solutions `n` with `(n, b) = 1` and
`n² ≤ b^{3q}`.

The proof is the paper's: a Sidon set of `m ≈ √q/(12b)` even integers avoiding
its own sumset (Bose–Chowla + Bertrand, both proved in Lean), the carry-free
digit sums of `(a_T·b^k − 1)²` from `DSS/CarryFree(Two)`, a congruence-adjusted
choice of `t = #T`, and the binomial count `C(m,t) ≥ 2^{m/3}` over the subsets.

Nothing in this file is conditional: it imports no axioms.
-/
import DSS.CarryFreeTwo
import DSS.BoseChowla
import DSS.Singleton

namespace DSS

open Finset

/-! ### Binomial lower bounds -/

/-- `2^t ≤ C(m,t)` for `2t ≤ m`, by the doubling recurrence. -/
lemma two_pow_le_choose : ∀ t m : ℕ, 2 * t ≤ m → 2 ^ t ≤ m.choose t := by
  intro t
  induction t with
  | zero => intro m _; simp
  | succ t ih =>
      intro m hm
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      have h1 : (m' + 1) * m'.choose t = (m' + 1).choose (t + 1) * (t + 1) :=
        Nat.add_one_mul_choose_eq m' t
      have h2 : 2 ^ t ≤ m'.choose t := ih m' (by omega)
      have h3 : 2 * (t + 1) * m'.choose t ≤ (m' + 1) * m'.choose t :=
        Nat.mul_le_mul_right _ (by omega)
      have h4 : 2 * (t + 1) * m'.choose t = (2 * m'.choose t) * (t + 1) := by ring
      have h5 : 2 * m'.choose t ≤ (m' + 1).choose (t + 1) := by
        have h6 : (2 * m'.choose t) * (t + 1) ≤ (m' + 1).choose (t + 1) * (t + 1) := by
          omega
        exact Nat.le_of_mul_le_mul_right h6 (by omega)
      calc 2 ^ (t + 1) = 2 * 2 ^ t := by ring
        _ ≤ 2 * m'.choose t := by omega
        _ ≤ (m' + 1).choose (t + 1) := h5

/-- `2^l ≤ C(m,t)` whenever `l ≤ t`, `l ≤ m − t`, `t ≤ m`: the binomial
coefficient in the middle third dominates `2^{m/3}`. -/
lemma two_pow_le_choose_of_le {m t l : ℕ} (hl : l ≤ t) (hl2 : l ≤ m - t)
    (htm : t ≤ m) : 2 ^ l ≤ m.choose t := by
  rcases Nat.lt_or_ge m (2 * t) with h | h
  · have h1 : 2 * (m - t) ≤ m := by omega
    calc 2 ^ l ≤ 2 ^ (m - t) := Nat.pow_le_pow_right (by omega) hl2
      _ ≤ m.choose (m - t) := two_pow_le_choose _ m h1
      _ = m.choose t := Nat.choose_symm htm
  · calc 2 ^ l ≤ 2 ^ t := Nat.pow_le_pow_right (by omega) hl
      _ ≤ m.choose t := two_pow_le_choose t m h

/-! ### A residue in a window of length `d` -/

/-- Every window of `d` consecutive integers contains a representative of any
residue class modulo `d`. -/
lemma exists_residue_in_window (d l u : ℕ) (hd : 1 ≤ d) :
    ∃ t, l ≤ t ∧ t ≤ l + (d - 1) ∧ t ≡ u [MOD d] := by
  have hld := Nat.mod_lt l (show 0 < d by omega)
  have hud := Nat.mod_lt u (show 0 < d by omega)
  rcases Nat.lt_or_ge (u % d) (l % d) with h | h
  · refine ⟨l + (u % d + d - l % d), by omega, by omega, ?_⟩
    calc l + (u % d + d - l % d)
        ≡ l % d + (u % d + d - l % d) [MOD d] :=
          Nat.ModEq.add_right _ (Nat.mod_modEq l d).symm
      _ = u % d + d := by omega
      _ ≡ u % d [MOD d] := Nat.add_mod_right (u % d) d
      _ ≡ u [MOD d] := Nat.mod_modEq u d
  · refine ⟨l + (u % d - l % d), by omega, by omega, ?_⟩
    calc l + (u % d - l % d)
        ≡ l % d + (u % d - l % d) [MOD d] :=
          Nat.ModEq.add_right _ (Nat.mod_modEq l d).symm
      _ = u % d := by omega
      _ ≡ u [MOD d] := Nat.mod_modEq u d

/-! ### The solution set -/

/-- The solutions counted by Theorem 1.10: `n` coprime to the base, with
`s_b(n²) = q` and at most `3q` digits in `n²`. -/
def sqSols (b q : ℕ) : Finset ℕ :=
  (range (b ^ (3 * q) + 1)).filter
    (fun n => Nat.Coprime n b ∧ sb b (n ^ 2) = q ∧ n ^ 2 ≤ b ^ (3 * q))

lemma mem_sqSols {b q n : ℕ} (hb : 2 ≤ b) :
    n ∈ sqSols b q ↔ Nat.Coprime n b ∧ sb b (n ^ 2) = q ∧ n ^ 2 ≤ b ^ (3 * q) := by
  rw [sqSols, mem_filter, mem_range]
  constructor
  · rintro ⟨_, h⟩
    exact h
  · rintro ⟨h1, h2, h3⟩
    refine ⟨?_, h1, h2, h3⟩
    have hn1 : 1 ≤ n := by
      rcases Nat.eq_zero_or_pos n with rfl | h
      · exfalso
        have h4 : Nat.gcd 0 b = 1 := h1
        rw [Nat.gcd_zero_left] at h4
        omega
      · exact h
    have hnn : n ≤ n ^ 2 := Nat.le_self_pow (by omega) n
    omega

/-! ### The transformed Sidon set -/

/-- Pushing a subset of the Bose–Chowla set into position: translating by
`4m²` and doubling produces an **even, positive** Sidon set inside
`[8m², 16m²)` that avoids its own sumset. -/
lemma transform_props (m : ℕ) {S₀ T₀ : Finset ℕ} (hS : IsSidon S₀)
    (hsub : S₀ ⊆ range (4 * m ^ 2)) (hT₀ : T₀ ⊆ S₀) :
    IsSidon (T₀.image (fun s => 2 * (s + 4 * m ^ 2)))
      ∧ (∀ r ∈ T₀.image (fun s => 2 * (s + 4 * m ^ 2)), 0 < r)
      ∧ (∀ r ∈ T₀.image (fun s => 2 * (s + 4 * m ^ 2)), Even r)
      ∧ (∀ r ∈ T₀.image (fun s => 2 * (s + 4 * m ^ 2)),
          ∀ s ∈ T₀.image (fun s => 2 * (s + 4 * m ^ 2)),
            r + s ∉ T₀.image (fun s => 2 * (s + 4 * m ^ 2)))
      ∧ T₀.image (fun s => 2 * (s + 4 * m ^ 2)) ⊆ range (16 * m ^ 2)
      ∧ (T₀.image (fun s => 2 * (s + 4 * m ^ 2))).card = T₀.card := by
  have hmem : ∀ r ∈ T₀.image (fun s => 2 * (s + 4 * m ^ 2)),
      ∃ s ∈ T₀, 2 * (s + 4 * m ^ 2) = r ∧ s < 4 * m ^ 2 := by
    intro r hr
    obtain ⟨s, hs, rfl⟩ := mem_image.mp hr
    exact ⟨s, hs, rfl, mem_range.mp (hsub (hT₀ hs))⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- Sidon: translation then dilation
    have h1 : IsSidon (T₀.image (· + 4 * m ^ 2)) := (hS.mono hT₀).image_add _
    have h2 : IsSidon ((T₀.image (· + 4 * m ^ 2)).image (2 * ·)) :=
      h1.image_mul (by omega)
    rw [Finset.image_image] at h2
    exact h2
  · intro r hr
    obtain ⟨s, _, rfl, _⟩ := hmem r hr
    omega
  · intro r hr
    obtain ⟨s, _, rfl, _⟩ := hmem r hr
    exact ⟨s + 4 * m ^ 2, by ring⟩
  · intro r hr s hs hmem'
    obtain ⟨x, _, rfl, hx⟩ := hmem r hr
    obtain ⟨y, _, rfl, hy⟩ := hmem s hs
    obtain ⟨z, _, hz, hz'⟩ := hmem _ hmem'
    omega
  · intro r hr
    obtain ⟨s, _, rfl, hs⟩ := hmem r hr
    exact mem_range.mpr (by omega)
  · refine Finset.card_image_of_injective _ ?_
    intro x y h
    have h' : 2 * (x + 4 * m ^ 2) = 2 * (y + 4 * m ^ 2) := h
    omega

/-! ### Theorem 1.10 -/

/-- **Theorem 1.10, `b ≥ 3`.**  If `q ≥ 2304·b⁴` is admissible — congruent to
a square modulo `b − 1` — then `s_b(n²) = q` has at least `2^(√q/(36b))`
solutions `n` coprime to `b` with `n² ≤ b^{3q}`. -/
theorem sq_digit_sum_count {b : ℕ} (hb : 3 ≤ b) {q u : ℕ}
    (hq : 2304 * b ^ 4 ≤ q) (hadm : u ^ 2 ≡ q [MOD b - 1]) :
    2 ^ (Nat.sqrt q / (36 * b)) ≤ (sqSols b q).card := by
  have hb2 : 2 ≤ b := by omega
  obtain ⟨d, hd⟩ : ∃ d, b = d + 1 := ⟨b - 1, by omega⟩
  have hd2 : 2 ≤ d := by omega
  -- the Sidon parameter `m`
  obtain ⟨m, hm⟩ : ∃ m, Nat.sqrt q / (12 * b) = m := ⟨_, rfl⟩
  have hq48 : 48 * b ^ 2 ≤ Nat.sqrt q := by
    rw [Nat.le_sqrt]
    calc 48 * b ^ 2 * (48 * b ^ 2) = 2304 * b ^ 4 := by ring
      _ ≤ q := hq
  have hm4b : 4 * b ≤ m := by
    rw [← hm]
    have h1 : (48 * b ^ 2) / (12 * b) ≤ Nat.sqrt q / (12 * b) :=
      Nat.div_le_div_right hq48
    have h2 : (48 * b ^ 2) / (12 * b) = 4 * b := by
      rw [show 48 * b ^ 2 = (12 * b) * (4 * b) by ring]
      exact Nat.mul_div_cancel_left _ (by omega)
    omega
  have hm1 : 1 ≤ m := by omega
  have hm2 : 1 ≤ m ^ 2 := Nat.one_le_pow 2 m (by omega)
  have hmsq : 144 * b ^ 2 * m ^ 2 ≤ q := by
    have h1 : m * (12 * b) ≤ Nat.sqrt q := by
      rw [← hm]
      exact Nat.div_mul_le_self _ _
    calc 144 * b ^ 2 * m ^ 2 = (m * (12 * b)) * (m * (12 * b)) := by ring
      _ ≤ Nat.sqrt q * Nat.sqrt q := Nat.mul_le_mul h1 h1
      _ ≤ q := Nat.sqrt_le q
  -- the Sidon source and the size `t` of the subsets
  obtain ⟨S₀, hS₀sub, hS₀card, hS₀sidon⟩ := exists_sidon_of_card m hm1
  obtain ⟨t, htl, htu, htmod⟩ := exists_residue_in_window d (m / 3) u (by omega)
  have htm : t ≤ m := by omega
  have ht2 : t ^ 2 ≡ q [MOD d] := by
    have h1 : t ^ 2 ≡ u ^ 2 [MOD d] := htmod.pow 2
    have h2 : u ^ 2 ≡ q [MOD b - 1] := hadm
    rw [show b - 1 = d by omega] at h2
    exact h1.trans h2
  have htmsq : t ^ 2 ≤ m ^ 2 := Nat.pow_le_pow_left htm 2
  have hmsq' : m ^ 2 ≤ 144 * b ^ 2 * m ^ 2 := by
    have h1 : 1 * m ^ 2 ≤ (144 * b ^ 2) * m ^ 2 :=
      Nat.mul_le_mul_right _ (by nlinarith)
    omega
  have ht2q : t ^ 2 ≤ q := by omega
  -- the exponent `k`
  have hdvd : d ∣ q - t ^ 2 := (Nat.modEq_iff_dvd' ht2q).mp ht2
  obtain ⟨k, hkval⟩ : ∃ k, q - t ^ 2 = d * k := hdvd
  have hdk : d * k = k * d := Nat.mul_comm d k
  have hkeq : k * d + t ^ 2 = q := by omega
  have hklarge : 32 * m ^ 2 + 1 ≤ k := by
    -- `(32m²+1)·d + t² ≤ 34·d·m² + m² ≤ 144·b²·m² ≤ q`
    have h2 : d * 1 ≤ d * m ^ 2 := Nat.mul_le_mul_left _ hm2
    have h3 : (32 * m ^ 2 + 1) * d = 32 * (d * m ^ 2) + d := by ring
    have h4 : 34 * (d * m ^ 2) + m ^ 2 ≤ 144 * b ^ 2 * m ^ 2 := by
      have h6 : d * m ^ 2 ≤ b * m ^ 2 := Nat.mul_le_mul_right _ (by omega)
      have h8 : 1 * m ^ 2 ≤ b * m ^ 2 := Nat.mul_le_mul_right _ (by omega)
      have h9 : 144 * b ^ 2 * m ^ 2 = 144 * (b * (b * m ^ 2)) := by ring
      have h7 : 1 * (b * m ^ 2) ≤ b * (b * m ^ 2) := Nat.mul_le_mul_right _ (by omega)
      omega
    have h11 : d * (32 * m ^ 2 + 1) ≤ d * k := by
      have h12 : d * (32 * m ^ 2 + 1) = (32 * m ^ 2 + 1) * d := by ring
      omega
    exact Nat.le_of_mul_le_mul_left h11 (by omega)
  have hk1 : 1 ≤ k := by omega
  have hbk_pos : 0 < b ^ k := pow_pos (by omega) k
  -- the injection from `t`-subsets of the Sidon source into the solutions
  have hcount : (Finset.powersetCard t S₀).card ≤ (sqSols b q).card := by
    refine Finset.card_le_card_of_injOn
      (fun T₀ => aT b (T₀.image (fun s => 2 * (s + 4 * m ^ 2))) * b ^ k - 1)
      ?_ ?_
    · -- membership
      intro T₀ hT₀
      simp only [Finset.mem_coe] at hT₀ ⊢
      obtain ⟨hT₀sub, hT₀card⟩ := Finset.mem_powersetCard.mp hT₀
      obtain ⟨hsidon, hpos, heven, havoid, hrange, hcard⟩ :=
        transform_props m hS₀sidon hS₀sub hT₀sub
      have hsb0 := sb_shifted_sq (T := T₀.image (fun s => 2 * (s + 4 * m ^ 2)))
        hb hsidon hpos havoid (k := k)
      obtain ⟨a, ha⟩ : ∃ a, aT b (T₀.image (fun s => 2 * (s + 4 * m ^ 2))) = a :=
        ⟨_, rfl⟩
      rw [ha, hcard, hT₀card] at hsb0
      have hapos : 0 < a := ha ▸ aT_pos b _
      have haB : a < b ^ (16 * m ^ 2) :=
        ha ▸ aT_lt hb2 hrange (by omega)
      -- the growth condition `b^k > a² + 2a`
      have hk_growth : a ^ 2 + 2 * a < b ^ k := by
        have h1 : a ^ 2 + 2 * a + 1 = (a + 1) ^ 2 := by ring
        have h2 : (a + 1) ^ 2 ≤ (b ^ (16 * m ^ 2)) ^ 2 :=
          Nat.pow_le_pow_left (by omega) 2
        have h3 : (b ^ (16 * m ^ 2)) ^ 2 = b ^ (32 * m ^ 2) := by
          rw [← pow_mul]
          congr 1
          ring
        have h4 : b ^ (32 * m ^ 2) ≤ b ^ k :=
          Nat.pow_le_pow_right (by omega) (by omega)
        omega
      have hsb : sb b ((a * b ^ k - 1) ^ 2) = q := by
        have h := hsb0 hk_growth
        rw [show b - 1 = d from by omega] at h
        omega
      -- size of the solution
      have hnsize : (a * b ^ k - 1) ^ 2 ≤ b ^ (3 * q) := by
        have h1 : a * b ^ k < b ^ (16 * m ^ 2 + k) := by
          rw [pow_add]
          exact (Nat.mul_lt_mul_right hbk_pos).mpr haB
        have h2 : (a * b ^ k - 1) ^ 2 ≤ (a * b ^ k) ^ 2 :=
          Nat.pow_le_pow_left (by omega) 2
        have h3 : (a * b ^ k) ^ 2 ≤ (b ^ (16 * m ^ 2 + k)) ^ 2 :=
          Nat.pow_le_pow_left (by omega) 2
        have h4 : (b ^ (16 * m ^ 2 + k)) ^ 2 = b ^ (32 * m ^ 2 + 2 * k) := by
          rw [← pow_mul]
          congr 1
          ring
        have hkq : k ≤ q := by
          have h5 : k * 1 ≤ k * d := Nat.mul_le_mul_left _ (by omega)
          omega
        have h6 : b ^ (32 * m ^ 2 + 2 * k) ≤ b ^ (3 * q) :=
          Nat.pow_le_pow_right (by omega) (by omega)
        omega
      show aT b (T₀.image (fun s => 2 * (s + 4 * m ^ 2))) * b ^ k - 1 ∈ sqSols b q
      rw [ha, mem_sqSols hb2]
      exact ⟨coprime_shifted (by omega) (by omega) hk1, hsb, hnsize⟩
    · -- injectivity
      intro T₀ hT₀ T₀' hT₀' heq
      simp only [Finset.mem_coe, Finset.mem_powersetCard] at hT₀ hT₀'
      obtain ⟨hsidon, hpos, _, _, _, _⟩ :=
        transform_props m hS₀sidon hS₀sub hT₀.1
      obtain ⟨hsidon', hpos', _, _, _, _⟩ :=
        transform_props m hS₀sidon hS₀sub hT₀'.1
      have h1 : aT b (T₀.image (fun s => 2 * (s + 4 * m ^ 2))) * b ^ k
          = aT b (T₀'.image (fun s => 2 * (s + 4 * m ^ 2))) * b ^ k := by
        have heq' : aT b (T₀.image (fun s => 2 * (s + 4 * m ^ 2))) * b ^ k - 1
            = aT b (T₀'.image (fun s => 2 * (s + 4 * m ^ 2))) * b ^ k - 1 := heq
        have ha1 : 1 * 1 ≤ aT b (T₀.image (fun s => 2 * (s + 4 * m ^ 2))) * b ^ k :=
          Nat.mul_le_mul (aT_pos b _) hbk_pos
        have ha2 : 1 * 1 ≤ aT b (T₀'.image (fun s => 2 * (s + 4 * m ^ 2))) * b ^ k :=
          Nat.mul_le_mul (aT_pos b _) hbk_pos
        omega
      have h2 := Nat.eq_of_mul_eq_mul_right hbk_pos h1
      have h3 := aT_injective hb2
        (fun h => absurd (hpos 0 h) (lt_irrefl 0))
        (fun h => absurd (hpos' 0 h) (lt_irrefl 0)) h2
      -- undo the image
      have himg : Function.Injective
          (Finset.image (fun s : ℕ => 2 * (s + 4 * m ^ 2))) := by
        refine Finset.image_injective ?_
        intro x y h
        have h' : 2 * (x + 4 * m ^ 2) = 2 * (y + 4 * m ^ 2) := h
        omega
      exact himg h3
  -- the binomial count
  have hchoose : 2 ^ (m / 3) ≤ (Finset.powersetCard t S₀).card := by
    rw [Finset.card_powersetCard, hS₀card]
    exact two_pow_le_choose_of_le htl (by omega) htm
  have hexp : Nat.sqrt q / (36 * b) = m / 3 := by
    rw [← hm, Nat.div_div_eq_div_mul]
    congr 1
    ring
  rw [hexp]
  omega

/-- **Theorem 1.10, `b = 2`.**  Every `q ≥ 36864` — no admissibility condition
in base `2` — is the binary digit sum of at least `2^(√q/72)` squares of odd
numbers `n` with `n² ≤ 2^{3q}`. -/
theorem sq_digit_sum_count_two {q : ℕ} (hq : 36864 ≤ q) :
    2 ^ (Nat.sqrt q / 72) ≤ (sqSols 2 q).card := by
  -- the Sidon parameter `m`
  obtain ⟨m, hm⟩ : ∃ m, Nat.sqrt q / 24 = m := ⟨_, rfl⟩
  have hq48 : 192 ≤ Nat.sqrt q := by
    rw [Nat.le_sqrt]
    omega
  have hm8 : 8 ≤ m := by
    rw [← hm]
    have h1 : 192 / 24 ≤ Nat.sqrt q / 24 := Nat.div_le_div_right hq48
    omega
  have hm1 : 1 ≤ m := by omega
  have hm2 : 1 ≤ m ^ 2 := Nat.one_le_pow 2 m (by omega)
  have hmsq : 576 * m ^ 2 ≤ q := by
    have h1 : m * 24 ≤ Nat.sqrt q := by
      rw [← hm]
      exact Nat.div_mul_le_self _ _
    calc 576 * m ^ 2 = (m * 24) * (m * 24) := by ring
      _ ≤ Nat.sqrt q * Nat.sqrt q := Nat.mul_le_mul h1 h1
      _ ≤ q := Nat.sqrt_le q
  obtain ⟨S₀, hS₀sub, hS₀card, hS₀sidon⟩ := exists_sidon_of_card m hm1
  -- the subset size and the exponent
  obtain ⟨t, ht⟩ : ∃ t, m / 3 = t := ⟨_, rfl⟩
  have htm : t ≤ m := by omega
  have hchle : (t + 1).choose 2 ≤ 4 * m ^ 2 := by
    have h1 : (t + 1).choose 2 ≤ (t + 1) ^ 2 := by
      rw [Nat.choose_two_right]
      have h2 : (t + 1) * ((t + 1) - 1) / 2 ≤ (t + 1) * ((t + 1) - 1) :=
        Nat.div_le_self _ _
      have h4 : (t + 1) * t ≤ (t + 1) * (t + 1) := Nat.mul_le_mul_left _ (by omega)
      have h5 : (t + 1) ^ 2 = (t + 1) * (t + 1) := by ring
      have h3 : (t + 1) * ((t + 1) - 1) = (t + 1) * t := by
        rw [Nat.add_sub_cancel]
      omega
    have h6 : (t + 1) ^ 2 ≤ (2 * m) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    have h7 : (2 * m) ^ 2 = 4 * m ^ 2 := by ring
    omega
  obtain ⟨k, hk⟩ : ∃ k, q - (t + 1).choose 2 = k := ⟨_, rfl⟩
  have hkeq : k + (t + 1).choose 2 = q := by omega
  have hklarge : 32 * m ^ 2 + 1 ≤ k := by omega
  have hk1 : 1 ≤ k := by omega
  have hbk_pos : 0 < (2 : ℕ) ^ k := pow_pos (by omega) k
  -- the injection
  have hcount : (Finset.powersetCard t S₀).card ≤ (sqSols 2 q).card := by
    refine Finset.card_le_card_of_injOn
      (fun T₀ => aT 2 (T₀.image (fun s => 2 * (s + 4 * m ^ 2))) * 2 ^ k - 1)
      ?_ ?_
    · intro T₀ hT₀
      simp only [Finset.mem_coe] at hT₀ ⊢
      obtain ⟨hT₀sub, hT₀card⟩ := Finset.mem_powersetCard.mp hT₀
      obtain ⟨hsidon, hpos, heven, havoid, hrange, hcard⟩ :=
        transform_props m hS₀sidon hS₀sub hT₀sub
      have hsb0 := sb_shifted_sq_two (T := T₀.image (fun s => 2 * (s + 4 * m ^ 2)))
        hsidon hpos heven havoid (k := k)
      obtain ⟨a, ha⟩ : ∃ a, aT 2 (T₀.image (fun s => 2 * (s + 4 * m ^ 2))) = a :=
        ⟨_, rfl⟩
      rw [ha, hcard, hT₀card] at hsb0
      have hapos : 0 < a := ha ▸ aT_pos 2 _
      have haB : a < 2 ^ (16 * m ^ 2) :=
        ha ▸ aT_lt (le_refl 2) hrange (by omega)
      have hk_growth : a ^ 2 + 2 * a < 2 ^ k := by
        have h1 : a ^ 2 + 2 * a + 1 = (a + 1) ^ 2 := by ring
        have h2 : (a + 1) ^ 2 ≤ ((2 : ℕ) ^ (16 * m ^ 2)) ^ 2 :=
          Nat.pow_le_pow_left (by omega) 2
        have h3 : ((2 : ℕ) ^ (16 * m ^ 2)) ^ 2 = 2 ^ (32 * m ^ 2) := by
          rw [← pow_mul]
          congr 1
          ring
        have h4 : (2 : ℕ) ^ (32 * m ^ 2) ≤ 2 ^ k :=
          Nat.pow_le_pow_right (by omega) (by omega)
        omega
      have hsb : sb 2 ((a * 2 ^ k - 1) ^ 2) = q := by
        have h := hsb0 hk_growth
        omega
      have hnsize : (a * 2 ^ k - 1) ^ 2 ≤ 2 ^ (3 * q) := by
        have h1 : a * 2 ^ k < 2 ^ (16 * m ^ 2 + k) := by
          rw [pow_add]
          exact (Nat.mul_lt_mul_right hbk_pos).mpr haB
        have h2 : (a * 2 ^ k - 1) ^ 2 ≤ (a * 2 ^ k) ^ 2 :=
          Nat.pow_le_pow_left (by omega) 2
        have h3 : (a * 2 ^ k) ^ 2 ≤ ((2 : ℕ) ^ (16 * m ^ 2 + k)) ^ 2 :=
          Nat.pow_le_pow_left (by omega) 2
        have h4 : ((2 : ℕ) ^ (16 * m ^ 2 + k)) ^ 2 = 2 ^ (32 * m ^ 2 + 2 * k) := by
          rw [← pow_mul]
          congr 1
          ring
        have hkq : k ≤ q := by omega
        have h6 : (2 : ℕ) ^ (32 * m ^ 2 + 2 * k) ≤ 2 ^ (3 * q) :=
          Nat.pow_le_pow_right (by omega) (by omega)
        omega
      show aT 2 (T₀.image (fun s => 2 * (s + 4 * m ^ 2))) * 2 ^ k - 1 ∈ sqSols 2 q
      rw [ha, mem_sqSols (le_refl 2)]
      exact ⟨coprime_shifted (by omega) (by omega) hk1, hsb, hnsize⟩
    · intro T₀ hT₀ T₀' hT₀' heq
      simp only [Finset.mem_coe, Finset.mem_powersetCard] at hT₀ hT₀'
      obtain ⟨_, hpos, _, _, _, _⟩ :=
        transform_props m hS₀sidon hS₀sub hT₀.1
      obtain ⟨_, hpos', _, _, _, _⟩ :=
        transform_props m hS₀sidon hS₀sub hT₀'.1
      have h1 : aT 2 (T₀.image (fun s => 2 * (s + 4 * m ^ 2))) * 2 ^ k
          = aT 2 (T₀'.image (fun s => 2 * (s + 4 * m ^ 2))) * 2 ^ k := by
        have heq' : aT 2 (T₀.image (fun s => 2 * (s + 4 * m ^ 2))) * 2 ^ k - 1
            = aT 2 (T₀'.image (fun s => 2 * (s + 4 * m ^ 2))) * 2 ^ k - 1 := heq
        have ha1 : 1 * 1 ≤ aT 2 (T₀.image (fun s => 2 * (s + 4 * m ^ 2))) * 2 ^ k :=
          Nat.mul_le_mul (aT_pos 2 _) hbk_pos
        have ha2 : 1 * 1 ≤ aT 2 (T₀'.image (fun s => 2 * (s + 4 * m ^ 2))) * 2 ^ k :=
          Nat.mul_le_mul (aT_pos 2 _) hbk_pos
        omega
      have h2 := Nat.eq_of_mul_eq_mul_right hbk_pos h1
      have h3 := aT_injective (le_refl 2)
        (fun h => absurd (hpos 0 h) (lt_irrefl 0))
        (fun h => absurd (hpos' 0 h) (lt_irrefl 0)) h2
      have himg : Function.Injective
          (Finset.image (fun s : ℕ => 2 * (s + 4 * m ^ 2))) := by
        refine Finset.image_injective ?_
        intro x y h
        have h' : 2 * (x + 4 * m ^ 2) = 2 * (y + 4 * m ^ 2) := h
        omega
      exact himg h3
  have hchoose : 2 ^ (m / 3) ≤ (Finset.powersetCard t S₀).card := by
    rw [Finset.card_powersetCard, hS₀card]
    exact two_pow_le_choose_of_le (show m / 3 ≤ t by omega) (by omega) htm
  have hexp : Nat.sqrt q / 72 = m / 3 := by
    rw [← hm, Nat.div_div_eq_div_mul]
  rw [hexp]
  omega

end DSS
