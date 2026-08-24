/-
EKRev/OmegaS.lean

The additive functions ω, Ω, their `S`-restricted versions ω_S, Ω_S
(§1.2, after eq. (1.10)), the "excess" `Ω_S - ω_S = ∑_{ℓ∈S} max(v_ℓ-1,0)`,
and the prime-power identity
`Ω(n) - ω(n) = ∑_{m≥2} #{ℓ : ℓ^m ∣ n}` used in Lemmas 3.3 and 4.5.

Everything in this file is fully proved (no axioms).
-/
import Mathlib.Tactic
import Mathlib.Data.Nat.Factorization.Basic
import EKRev.PrimeBlocks

namespace EKRev

open Finset

/-- `ω(n)`: the number of distinct prime factors. -/
def smallOmega (n : ℕ) : ℕ := n.primeFactors.card

/-- `Ω(n)`: the number of prime factors counted with multiplicity. -/
def bigOmega (n : ℕ) : ℕ := ∑ ℓ ∈ n.primeFactors, n.factorization ℓ

open Classical in
/-- `ω_S(n) = #{ℓ ∈ S : ℓ ∣ n}` for a set `S` of primes. -/
noncomputable def omegaS (S : Set ℕ) (n : ℕ) : ℕ :=
  (n.primeFactors.filter (· ∈ S)).card

open Classical in
/-- `Ω_S(n) = ∑_{ℓ ∈ S} v_ℓ(n)`. -/
noncomputable def bigOmegaS (S : Set ℕ) (n : ℕ) : ℕ :=
  ∑ ℓ ∈ n.primeFactors.filter (· ∈ S), n.factorization ℓ

open Classical in
/-- The excess `Ω_S(n) - ω_S(n) = ∑_{ℓ ∈ S} max(v_ℓ(n) - 1, 0)`, kept in
additive form to avoid truncated subtraction. -/
noncomputable def excessS (S : Set ℕ) (n : ℕ) : ℕ :=
  ∑ ℓ ∈ n.primeFactors.filter (· ∈ S), (n.factorization ℓ - 1)

open Classical

lemma factorization_pos_of_mem_primeFactors {n ℓ : ℕ} (hℓ : ℓ ∈ n.primeFactors) :
    1 ≤ n.factorization ℓ := by
  rw [← Nat.support_factorization] at hℓ
  exact Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hℓ)

/-- `Ω_S = ω_S + excess_S`. -/
lemma bigOmegaS_eq (S : Set ℕ) (n : ℕ) :
    bigOmegaS S n = omegaS S n + excessS S n := by
  unfold bigOmegaS omegaS excessS
  rw [Finset.card_eq_sum_ones, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun ℓ hℓ => ?_
  have h1 : 1 ≤ n.factorization ℓ :=
    factorization_pos_of_mem_primeFactors (Finset.mem_filter.mp hℓ).1
  omega

/-- Monotonicity of the excess in `S`; with `S = univ` this is
`Ω_S - ω_S ≤ Ω - ω` (used in the proof of Proposition 2.1, last part). -/
lemma excessS_le (S : Set ℕ) (n : ℕ) : excessS S n ≤ excessS Set.univ n := by
  unfold excessS
  refine Finset.sum_le_sum_of_subset ?_
  intro ℓ hℓ
  simp only [Finset.mem_filter, Set.mem_univ, and_true] at hℓ ⊢
  exact hℓ.1

lemma excessS_univ (n : ℕ) : excessS Set.univ n = bigOmega n - smallOmega n := by
  have h := bigOmegaS_eq Set.univ n
  have h1 : bigOmegaS Set.univ n = bigOmega n := by
    unfold bigOmegaS bigOmega
    congr 1
    simp
  have h2 : omegaS Set.univ n = smallOmega n := by
    unfold omegaS smallOmega
    congr 1
    simp
  omega

/-- For the set of all primes, `ω_S = ω`. -/
lemma omegaS_primes (n : ℕ) : omegaS {p : ℕ | p.Prime} n = smallOmega n := by
  unfold omegaS smallOmega
  congr 1
  ext ℓ
  simp only [Finset.mem_filter, Set.mem_setOf_eq]
  exact ⟨fun h => h.1, fun h => ⟨h, Nat.prime_of_mem_primeFactors h⟩⟩

/-- For the set of all primes, `Ω_S = Ω`. -/
lemma bigOmegaS_primes (n : ℕ) : bigOmegaS {p : ℕ | p.Prime} n = bigOmega n := by
  unfold bigOmegaS bigOmega
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext ℓ
  simp only [Finset.mem_filter, Set.mem_setOf_eq]
  exact ⟨fun h => h.1, fun h => ⟨h, Nat.prime_of_mem_primeFactors h⟩⟩

/-! ### The prime-power identity -/

/-- Exponents are bounded: `v_ℓ(n) ≤ M` once `n < 2^M` (`n ≥ 1`). -/
lemma factorization_le_of_lt_two_pow (hn : 1 ≤ n) (hM : n < 2 ^ M)
    (hℓ : ℓ ∈ n.primeFactors) : n.factorization ℓ ≤ M := by
  by_contra hcon
  push_neg at hcon
  have hp : ℓ.Prime := Nat.prime_of_mem_primeFactors hℓ
  have hdvd : ℓ ^ (M + 1) ∣ n := by
    refine (Nat.Prime.pow_dvd_iff_le_factorization hp (by omega)).mpr (by omega)
  have h1 : ℓ ^ (M + 1) ≤ n := Nat.le_of_dvd (by omega) hdvd
  have h2 : 2 ^ (M + 1) ≤ ℓ ^ (M + 1) := Nat.pow_le_pow_left hp.two_le _
  have h3 : 2 ^ M < 2 ^ (M + 1) := by
    have : (2:ℕ) ^ M * 1 < 2 ^ M * 2 := by
      have : (0:ℕ) < 2 ^ M := Nat.pos_pow_of_pos _ (by omega)
      omega
    calc (2:ℕ) ^ M = 2 ^ M * 1 := by ring
      _ < 2 ^ M * 2 := this
      _ = 2 ^ (M + 1) := by rw [← pow_succ]
  omega

/-- The layer-cake count: for `1 ≤ v ≤ M`,
`#{m ∈ [2, M] : m ≤ v} = v - 1`. -/
lemma card_Icc_filter_le (h1 : 1 ≤ v) (h2 : v ≤ M) :
    ((Finset.Icc 2 M).filter (· ≤ v)).card = v - 1 := by
  have heq : (Finset.Icc 2 M).filter (· ≤ v) = Finset.Icc 2 v := by
    ext m
    simp only [Finset.mem_filter, Finset.mem_Icc]
    omega
  rw [heq, Nat.card_Icc]
  omega

/-- The identity `Ω(n) = ω(n) + ∑_{m=2}^{M} #{ℓ : ℓ^m ∣ n}` for `n < 2^M`
(the identity of Lemma 3.3(iii)'s proof, in bounded form). -/
theorem bigOmega_eq_add_sum_powers (hn : 1 ≤ n) (hM : n < 2 ^ M) :
    bigOmega n = smallOmega n
      + ∑ m ∈ Finset.Icc 2 M, (n.primeFactors.filter fun ℓ => ℓ ^ m ∣ n).card := by
  -- pointwise layer cake, then swap the order of summation
  have hswap : ∑ m ∈ Finset.Icc 2 M, (n.primeFactors.filter fun ℓ => ℓ ^ m ∣ n).card
      = ∑ ℓ ∈ n.primeFactors, ((Finset.Icc 2 M).filter fun m => ℓ ^ m ∣ n).card := by
    simp only [Finset.card_filter]
    rw [Finset.sum_comm]
  rw [hswap]
  unfold bigOmega smallOmega
  rw [Finset.card_eq_sum_ones, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun ℓ hℓ => ?_
  have hp : ℓ.Prime := Nat.prime_of_mem_primeFactors hℓ
  have hv1 : 1 ≤ n.factorization ℓ := factorization_pos_of_mem_primeFactors hℓ
  have hvM : n.factorization ℓ ≤ M := factorization_le_of_lt_two_pow hn hM hℓ
  have hdvd : ∀ m, ℓ ^ m ∣ n ↔ m ≤ n.factorization ℓ := fun m =>
    Nat.Prime.pow_dvd_iff_le_factorization hp (by omega)
  have heq : ((Finset.Icc 2 M).filter fun m => ℓ ^ m ∣ n)
      = (Finset.Icc 2 M).filter (· ≤ n.factorization ℓ) := by
    refine Finset.filter_congr fun m _ => ?_
    rw [hdvd m]
  rw [heq, card_Icc_filter_le hv1 hvM]
  omega

/-! ### Comparison with `ω_R` over a finite set of primes -/

/-- `ω_R(n) = #{ℓ ∈ R : ℓ ∣ n}` for a finite set `R` (§2, before Prop. 2.2). -/
def omegaR (R : Finset ℕ) (n : ℕ) : ℕ := (R.filter (· ∣ n)).card

/-- For `n ≥ 1` and `R` a set of primes contained in `S`,
`ω_R(n) = #{ℓ ∈ primeFactors(n) ∩ R}`. -/
lemma omegaR_eq_card_inter (hn : 1 ≤ n) (hR : ∀ ℓ ∈ R, Nat.Prime ℓ) :
    omegaR R n = (n.primeFactors.filter (· ∈ R)).card := by
  unfold omegaR
  congr 1
  ext ℓ
  simp only [Finset.mem_filter, Nat.mem_primeFactors]
  constructor
  · rintro ⟨hℓR, hdvd⟩
    exact ⟨⟨hR ℓ hℓR, hdvd, by omega⟩, hℓR⟩
  · rintro ⟨⟨_, hdvd, _⟩, hℓR⟩
    exact ⟨hℓR, hdvd⟩

/-- Large prime divisors are few: `y^m ≤ n` where
`m = #{ℓ ∈ primeFactors(n) : ℓ > y}` (Lemma 2.3(ii) mechanism). -/
lemma pow_card_large_primeFactors_le (hn : 1 ≤ n) (y : ℕ) :
    y ^ ((n.primeFactors.filter fun ℓ => y < ℓ).card) ≤ n := by
  set s := n.primeFactors.filter fun ℓ => y < ℓ with hs
  have h1 : y ^ s.card ≤ ∏ ℓ ∈ s, ℓ := by
    refine Finset.pow_card_le_prod s _ _ fun ℓ hℓ => ?_
    rw [hs, Finset.mem_filter] at hℓ
    omega
  have h2 : (∏ ℓ ∈ s, ℓ) ∣ n := by
    refine (Finset.prod_dvd_prod_of_subset s n.primeFactors (fun ℓ => ℓ) ?_).trans
      (Nat.prod_primeFactors_dvd n)
    exact Finset.filter_subset _ _
  exact h1.trans (Nat.le_of_dvd (by omega) h2)

/-- Sandwich: `ω_Q(n) ≤ ω_S(n)` and
`ω_S(n) ≤ ω_Q(n) + #E + #{ℓ ∣ n : ℓ > y}` when
`Q = {ℓ ≤ y : ℓ ∈ S, ℓ ∉ E}` (Lemma 2.3(ii)). -/
lemma omegaS_sub_omegaR_bound (hn : 1 ≤ n) {S : Set ℕ} {E : Finset ℕ} {y : ℝ}
    (R : Finset ℕ) (hR : ∀ ℓ, ℓ ∈ R ↔ ℓ.Prime ∧ ℓ ∈ S ∧ (ℓ : ℝ) ≤ y ∧ ℓ ∉ E) :
    omegaR R n ≤ omegaS S n ∧
    omegaS S n ≤ omegaR R n + E.card
      + (n.primeFactors.filter fun ℓ : ℕ => y < (ℓ : ℝ)).card := by
  have hRp : ∀ ℓ ∈ R, Nat.Prime ℓ := fun ℓ hℓ => ((hR ℓ).mp hℓ).1
  rw [omegaR_eq_card_inter hn hRp]
  unfold omegaS
  constructor
  · refine Finset.card_le_card ?_
    intro ℓ hℓ
    rw [Finset.mem_filter] at hℓ ⊢
    exact ⟨hℓ.1, ((hR ℓ).mp hℓ.2).2.1⟩
  · -- split S-elements into those in R, those in E, those > y
    have hsplit : n.primeFactors.filter (· ∈ S)
        ⊆ (n.primeFactors.filter (· ∈ R))
          ∪ (n.primeFactors.filter (· ∈ E))
          ∪ (n.primeFactors.filter fun ℓ : ℕ => y < (ℓ : ℝ)) := by
      intro ℓ hℓ
      rw [Finset.mem_filter] at hℓ
      obtain ⟨hpf, hS⟩ := hℓ
      have hp : ℓ.Prime := Nat.prime_of_mem_primeFactors hpf
      by_cases hE : ℓ ∈ E
      · exact Finset.mem_union_left _ (Finset.mem_union_right _
          (Finset.mem_filter.mpr ⟨hpf, hE⟩))
      · by_cases hy : (ℓ : ℝ) ≤ y
        · exact Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_filter.mpr ⟨hpf, (hR ℓ).mpr ⟨hp, hS, hy, hE⟩⟩))
        · push_neg at hy
          exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hpf, hy⟩)
    calc (n.primeFactors.filter (· ∈ S)).card
        ≤ ((n.primeFactors.filter (· ∈ R))
            ∪ (n.primeFactors.filter (· ∈ E))
            ∪ (n.primeFactors.filter fun ℓ : ℕ => y < (ℓ : ℝ))).card :=
          Finset.card_le_card hsplit
      _ ≤ ((n.primeFactors.filter (· ∈ R))
            ∪ (n.primeFactors.filter (· ∈ E))).card
            + (n.primeFactors.filter fun ℓ : ℕ => y < (ℓ : ℝ)).card :=
          Finset.card_union_le _ _
      _ ≤ (n.primeFactors.filter (· ∈ R)).card
            + (n.primeFactors.filter (· ∈ E)).card
            + (n.primeFactors.filter fun ℓ : ℕ => y < (ℓ : ℝ)).card := by
          have := Finset.card_union_le (n.primeFactors.filter (· ∈ R))
            (n.primeFactors.filter (· ∈ E))
          omega
      _ ≤ (n.primeFactors.filter (· ∈ R)).card + E.card
            + (n.primeFactors.filter fun ℓ : ℕ => y < (ℓ : ℝ)).card := by
          have : (n.primeFactors.filter (· ∈ E)).card ≤ E.card := by
            refine Finset.card_le_card_of_injOn id ?_ ?_
            · intro ℓ hℓ
              exact (Finset.mem_filter.mp hℓ).2
            · intro a _ b _ h
              exact h
          omega

end EKRev
