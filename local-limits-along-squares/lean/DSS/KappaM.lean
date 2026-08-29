/-
DSS/KappaM.lean

**The shellwise local factor `κ_m(A, d)` of Theorem 5.12** — the verified
part.

The paper defines, for the zero-mean digit-weight theorem,

  `κ_m(A,d) = d/φ(d)² · #{a mod d : (a,d) = 1, (a − Am, d) = 1}`      (58)

and proves the product formula (60)

  `κ_m(A,d) = ∏_{ℓ∣d, ℓ∣Am} ℓ/(ℓ−1) · ∏_{ℓ∣d, ℓ∤Am} ℓ(ℓ−2)/(ℓ−1)²`

together with the mean formula (61): averaging over `m` modulo `d` gives
`κ(A,d) = ∏_{ℓ∣d, ℓ∣A} ℓ/(ℓ−1)`.

This file verifies, with `N(c,d) = #{a < d : (a,d) = 1, (a−c,d) = 1}`:

* `nboth_prime` — the count at a prime modulus: `N(c,ℓ) = ℓ−1` if `ℓ ∣ c`,
  `ℓ−2` otherwise;
* `nboth_prime_pow` — the count at a prime power:
  `N(c,ℓ^e) = ℓ^{e−1}·N(c,ℓ)` (both conditions factor through `a mod ℓ`, and
  each class below `ℓ` has exactly `ℓ^{e−1}` lifts);
* `kappaM_prime`, `kappaM_prime_pow` — the resulting exact values of
  `d/φ(d)²·N`, which are the local factors of (60): `ℓ/(ℓ−1)` when
  `ℓ ∣ c` and `ℓ(ℓ−2)/(ℓ−1)²` when `ℓ ∤ c`, **for `d` any power of `ℓ`** —
  the prime-power case of the product formula;
* `local_average` — the per-prime mean identity behind (61):
  `(1/ℓ)·ℓ/(ℓ−1) + ((ℓ−1)/ℓ)·ℓ(ℓ−2)/(ℓ−1)² = 1`;
* `nboth_mul` — **multiplicativity** of `N(c,·)` for coprime moduli, by the
  Chinese remainder theorem: `ZMod.chineseRemainder` is a ring isomorphism
  `ZMod (d₁d₂) ≃+* ZMod d₁ × ZMod d₂`, both conditions in (58) say "is a
  unit", and a pair is a unit exactly when both coordinates are;
* `kappaM_product` — **the product formula (60) for an arbitrary modulus `d`**,
  obtained from the prime-power values by multiplicativity;
* `kappaM_average` — **the mean formula (61)**: the average of `κ_m(A,d)` over
  a full period `m = 0, …, d−1` is `∏_{ℓ∣d, ℓ∣A} ℓ/(ℓ−1) = κ(A,d)`.

(The previously verified base-3 instance, `base3_odd_shell_forcing`, is the
case `d = 2` of `nboth_prime`.)

Not formalised: the shellwise density statement (57) itself, which needs the
prime number theorem with error and Mertens' theorems.

Nothing in this file is conditional: it imports no axioms.
-/
import DSS.Imports

namespace DSS

open Finset

/-- `N(c, d) = #{0 ≤ a < d : (a, d) = 1 and (a − c, d) = 1}`, the count in
(58); the shifted condition is read in `ℤ`. -/
def nboth (c : ℤ) (d : ℕ) : ℕ :=
  ((range d).filter
    (fun a : ℕ => Nat.Coprime a d ∧ Int.gcd ((a : ℤ) - c) d = 1)).card

/-! ### The prime modulus -/

/-- At a prime modulus the two conditions read `a ≠ 0` and `a ≢ c`. -/
theorem nboth_prime {ℓ : ℕ} (hℓ : ℓ.Prime) (c : ℤ) :
    nboth c ℓ = if (ℓ : ℤ) ∣ c then ℓ - 1 else ℓ - 2 := by
  classical
  have hℓ0 : 0 < ℓ := hℓ.pos
  have hℓ1 : 1 < ℓ := hℓ.one_lt
  have hℓZ : (0 : ℤ) < (ℓ : ℤ) := by exact_mod_cast hℓ0
  -- the residue of `c`
  obtain ⟨ĉ, hĉdef⟩ : ∃ t : ℕ, t = (c % (ℓ : ℤ)).toNat := ⟨_, rfl⟩
  have hem0 : 0 ≤ c % (ℓ : ℤ) := Int.emod_nonneg _ (ne_of_gt hℓZ)
  have hem1 : c % (ℓ : ℤ) < ℓ := Int.emod_lt_of_pos _ hℓZ
  have hĉlt : ĉ < ℓ := by omega
  have hĉcast : ((ĉ : ℕ) : ℤ) = c % (ℓ : ℤ) := by
    rw [hĉdef]
    exact Int.toNat_of_nonneg hem0
  -- `ℓ ∣ ĉ − c`
  have hĉdvd : (ℓ : ℤ) ∣ ((ĉ : ℤ) - c) := by
    rw [hĉcast]
    have hme : c % (ℓ : ℤ) % (ℓ : ℤ) = c % (ℓ : ℤ) :=
      Int.emod_emod_of_dvd c (dvd_refl _)
    have h2 : (ℓ : ℤ) ∣ (c - c % (ℓ : ℤ)) := Int.ModEq.dvd hme
    have h3 : (c % (ℓ : ℤ) - c) = -(c - c % (ℓ : ℤ)) := by ring
    rw [h3]
    exact dvd_neg.mpr h2
  -- a prime does not divide `a − c` iff `a ≠ ĉ`, for `a < ℓ`
  have hdvd_iff : ∀ a : ℕ, a < ℓ → ((ℓ : ℤ) ∣ ((a : ℤ) - c) ↔ a = ĉ) := by
    intro a halt
    constructor
    · intro hd
      have h1 : (ℓ : ℤ) ∣ ((a : ℤ) - (ĉ : ℤ)) := by
        have h3 : ((a : ℤ) - (ĉ : ℤ)) = ((a : ℤ) - c) - ((ĉ : ℤ) - c) := by ring
        rw [h3]
        exact dvd_sub hd hĉdvd
      rcases h1 with ⟨t, ht⟩
      have hb1 : -(ℓ : ℤ) < (a : ℤ) - ĉ := by
        have h0 : (0 : ℤ) ≤ (a : ℤ) := by positivity
        omega
      have hb2 : (a : ℤ) - ĉ < ℓ := by
        have h0 : (0 : ℤ) ≤ (ĉ : ℤ) := by positivity
        omega
      have ht0 : t = 0 := by
        rcases lt_trichotomy t 0 with h | h | h
        · exfalso; nlinarith
        · exact h
        · exfalso; nlinarith
      have : (a : ℤ) = ĉ := by
        rw [ht0] at ht
        omega
      exact_mod_cast this
    · intro hac
      rw [hac]
      exact hĉdvd
  -- rewrite the two conditions for `a < ℓ`
  have hcond : ∀ a ∈ range ℓ,
      ((Nat.Coprime a ℓ ∧ Int.gcd ((a : ℤ) - c) ℓ = 1) ↔ (a ≠ 0 ∧ a ≠ ĉ)) := by
    intro a ha
    have halt : a < ℓ := mem_range.mp ha
    have hgcd_iff : Int.gcd ((a : ℤ) - c) ℓ = 1 ↔ ¬ (ℓ : ℤ) ∣ ((a : ℤ) - c) := by
      constructor
      · intro h hd
        have h1 : ℓ ∣ ((a : ℤ) - c).natAbs :=
          Int.natCast_dvd_natCast.mp (Int.dvd_natAbs.mpr hd)
        have h2 : ℓ ∣ Nat.gcd ((a : ℤ) - c).natAbs ℓ := Nat.dvd_gcd h1 (dvd_refl ℓ)
        have h3 : Int.gcd ((a : ℤ) - c) ℓ = Nat.gcd ((a : ℤ) - c).natAbs ℓ := rfl
        rw [← h3, h] at h2
        have h4 : ℓ = 1 := Nat.eq_one_of_dvd_one h2
        omega
      · intro h
        have h4 : Nat.Coprime ((a : ℤ) - c).natAbs ℓ := by
          rw [Nat.coprime_comm]
          apply (hℓ.coprime_iff_not_dvd).mpr
          intro h5
          exact h (Int.dvd_natAbs.mp (Int.natCast_dvd_natCast.mpr h5))
        exact h4
    have hcop_iff : Nat.Coprime a ℓ ↔ a ≠ 0 := by
      constructor
      · intro h1 h0
        subst h0
        rw [Nat.Coprime, Nat.gcd_zero_left] at h1
        omega
      · intro h0
        rw [Nat.coprime_comm]
        apply (hℓ.coprime_iff_not_dvd).mpr
        intro hdvd
        have := Nat.le_of_dvd (Nat.pos_of_ne_zero h0) hdvd
        omega
    rw [hcop_iff, hgcd_iff, hdvd_iff a halt]
  rw [nboth, Finset.filter_congr hcond]
  -- count `{a < ℓ : a ≠ 0, a ≠ ĉ}`
  by_cases hc0 : ĉ = 0
  · -- the two exclusions coincide
    have heq : ((range ℓ).filter (fun a => a ≠ 0 ∧ a ≠ ĉ)).card
        = ((range ℓ).filter (fun a => a ≠ 0)).card := by
      congr 1
      apply Finset.filter_congr
      intro a _
      subst hc0
      simp [and_self]
    rw [heq]
    have hdvd : (ℓ : ℤ) ∣ c := by
      have h1 : ((ĉ : ℕ) : ℤ) = 0 := by rw [hc0]; norm_num
      rw [h1] at hĉcast
      exact Int.dvd_of_emod_eq_zero hĉcast.symm
    rw [if_pos hdvd]
    have hIco : (range ℓ).filter (fun a => a ≠ 0) = Ico 1 ℓ := by
      ext a
      simp only [mem_filter, mem_range, mem_Ico]
      omega
    rw [hIco, Nat.card_Ico]
  · -- two distinct exclusions
    have hnd : ¬ (ℓ : ℤ) ∣ c := by
      intro hdvd
      have h1 : c % (ℓ : ℤ) = 0 := Int.emod_eq_zero_of_dvd hdvd
      rw [h1] at hĉcast
      have : ĉ = 0 := by omega
      exact hc0 this
    rw [if_neg hnd]
    have herase : (range ℓ).filter (fun a => a ≠ 0 ∧ a ≠ ĉ)
        = ((range ℓ).erase 0).erase ĉ := by
      ext a
      simp only [mem_filter, mem_range, mem_erase]
      tauto
    rw [herase]
    have h0mem : (0 : ℕ) ∈ range ℓ := mem_range.mpr hℓ0
    have hĉmem : ĉ ∈ (range ℓ).erase 0 := by
      rw [mem_erase]
      exact ⟨hc0, mem_range.mpr hĉlt⟩
    rw [Finset.card_erase_of_mem hĉmem, Finset.card_erase_of_mem h0mem, card_range]
    omega

/-! ### The prime power -/

/-- Counting a mod-`n` condition over `range (m·n)`: each class has `m`
lifts. -/
lemma card_filter_mod (m n : ℕ) (hn : 0 < n) (Q : ℕ → Prop) [DecidablePred Q] :
    ((range (m * n)).filter (fun a => Q (a % n))).card
      = m * ((range n).filter Q).card := by
  classical
  have hfiber : ∀ r ∈ (range n).filter Q,
      ((range (m * n)).filter (fun a => Q (a % n))).filter (fun a => a % n = r)
        = (range m).image (fun q => q * n + r) := by
    intro r hr
    rw [mem_filter, mem_range] at hr
    ext a
    simp only [mem_filter, mem_range, mem_image]
    constructor
    · rintro ⟨⟨ha, _⟩, har⟩
      refine ⟨a / n, ?_, ?_⟩
      · exact (Nat.div_lt_iff_lt_mul hn).mpr ha
      · have h1 := Nat.div_add_mod a n
        have h2 : a / n * n = n * (a / n) := Nat.mul_comm _ _
        omega
    · rintro ⟨q, hq, hqa⟩
      have har : a % n = r := by
        subst hqa
        have h1 : q * n + r = r + n * q := by ring
        rw [h1, Nat.add_mul_mod_self_left]
        exact Nat.mod_eq_of_lt hr.1
      refine ⟨⟨?_, by rw [har]; exact hr.2⟩, har⟩
      subst hqa
      calc q * n + r < q * n + n := by omega
        _ = (q + 1) * n := by ring
        _ ≤ m * n := Nat.mul_le_mul (by omega) (le_refl n)
  have hmap : ∀ a ∈ (range (m * n)).filter (fun a => Q (a % n)),
      a % n ∈ (range n).filter Q := by
    intro a ha
    rw [mem_filter] at ha ⊢
    exact ⟨mem_range.mpr (Nat.mod_lt _ hn), ha.2⟩
  rw [Finset.card_eq_sum_card_fiberwise hmap]
  have hconst : ∀ r ∈ (range n).filter Q,
      (((range (m * n)).filter (fun a => Q (a % n))).filter
        (fun a => a % n = r)).card = m := by
    intro r hr
    rw [hfiber r hr, Finset.card_image_of_injective _ (fun q₁ q₂ h => by
      have h1 : q₁ * n = q₂ * n := by omega
      exact Nat.eq_of_mul_eq_mul_right hn h1), card_range]
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, smul_eq_mul, Nat.mul_comm]

/-- **The prime-power count:** `N(c, ℓ^e) = ℓ^{e−1} · N(c, ℓ)` for `e ≥ 1`:
both conditions factor through `a mod ℓ`. -/
theorem nboth_prime_pow {ℓ : ℕ} (hℓ : ℓ.Prime) (c : ℤ) {e : ℕ} (he : 1 ≤ e) :
    nboth c (ℓ ^ e) = ℓ ^ (e - 1) * nboth c ℓ := by
  classical
  have hℓ0 : 0 < ℓ := hℓ.pos
  have hdvd : ℓ ∣ ℓ ^ e := dvd_pow_self ℓ (by omega)
  -- the conditions at modulus `ℓ^e` reduce to conditions on `a % ℓ`
  have hcond : ∀ a : ℕ,
      ((Nat.Coprime a (ℓ ^ e) ∧ Int.gcd ((a : ℤ) - c) (((ℓ ^ e : ℕ)) : ℤ) = 1)
        ↔ (Nat.Coprime (a % ℓ) ℓ ∧ Int.gcd (((a % ℓ : ℕ) : ℤ) - c) ℓ = 1)) := by
    intro a
    have h1 : Nat.Coprime a (ℓ ^ e) ↔ ¬ ℓ ∣ a := by
      rw [Nat.coprime_pow_right_iff (by omega), Nat.coprime_comm]
      exact hℓ.coprime_iff_not_dvd
    have h2 : Nat.Coprime (a % ℓ) ℓ ↔ ¬ ℓ ∣ a := by
      rw [Nat.coprime_comm, hℓ.coprime_iff_not_dvd, Nat.dvd_mod_iff (dvd_refl ℓ)]
    have h3 : Int.gcd ((a : ℤ) - c) (((ℓ ^ e : ℕ)) : ℤ) = 1
        ↔ ¬ (ℓ : ℤ) ∣ ((a : ℤ) - c) := by
      constructor
      · intro h hd
        have h1 : ℓ ∣ ((a : ℤ) - c).natAbs :=
          Int.natCast_dvd_natCast.mp (Int.dvd_natAbs.mpr hd)
        have h2 : ℓ ∣ Nat.gcd ((a : ℤ) - c).natAbs (ℓ ^ e) :=
          Nat.dvd_gcd h1 (dvd_pow_self ℓ (by omega))
        have h' : Nat.gcd ((a : ℤ) - c).natAbs (ℓ ^ e) = 1 := h
        rw [h'] at h2
        have h4 : ℓ = 1 := Nat.eq_one_of_dvd_one h2
        have := hℓ.one_lt
        omega
      · intro h
        have h4 : Nat.Coprime ((a : ℤ) - c).natAbs ℓ := by
          rw [Nat.coprime_comm]
          apply (hℓ.coprime_iff_not_dvd).mpr
          intro h5
          exact h (Int.dvd_natAbs.mp (Int.natCast_dvd_natCast.mpr h5))
        have h6 : Nat.Coprime ((a : ℤ) - c).natAbs (ℓ ^ e) :=
          Nat.Coprime.pow_right e h4
        exact h6
    have h4 : (ℓ : ℤ) ∣ ((a : ℤ) - c) ↔ (ℓ : ℤ) ∣ (((a % ℓ : ℕ) : ℤ) - c) := by
      have hsplit : (a : ℤ) = ((a % ℓ : ℕ) : ℤ) + (ℓ : ℤ) * ((a / ℓ : ℕ) : ℤ) := by
        have h0 : a % ℓ + ℓ * (a / ℓ) = a := Nat.mod_add_div a ℓ
        exact_mod_cast h0.symm
      constructor
      · intro hd
        have : ((a % ℓ : ℕ) : ℤ) - c = ((a : ℤ) - c) - (ℓ : ℤ) * ((a / ℓ : ℕ) : ℤ) := by
          rw [hsplit]; ring
        rw [this]
        exact dvd_sub hd ⟨_, rfl⟩
      · intro hd
        have : (a : ℤ) - c = (((a % ℓ : ℕ) : ℤ) - c) + (ℓ : ℤ) * ((a / ℓ : ℕ) : ℤ) := by
          rw [hsplit]; ring
        rw [this]
        exact dvd_add hd ⟨_, rfl⟩
    have h5 : Int.gcd (((a % ℓ : ℕ) : ℤ) - c) ℓ = 1
        ↔ ¬ (ℓ : ℤ) ∣ (((a % ℓ : ℕ) : ℤ) - c) := by
      constructor
      · intro h hd
        have h1 : ℓ ∣ (((a % ℓ : ℕ) : ℤ) - c).natAbs :=
          Int.natCast_dvd_natCast.mp (Int.dvd_natAbs.mpr hd)
        have h2 : ℓ ∣ Nat.gcd (((a % ℓ : ℕ) : ℤ) - c).natAbs ℓ :=
          Nat.dvd_gcd h1 (dvd_refl ℓ)
        have h3' : Int.gcd (((a % ℓ : ℕ) : ℤ) - c) (ℓ : ℤ)
            = Nat.gcd (((a % ℓ : ℕ) : ℤ) - c).natAbs ℓ := rfl
        rw [← h3', h] at h2
        have h4 : ℓ = 1 := Nat.eq_one_of_dvd_one h2
        have := hℓ.one_lt
        omega
      · intro h
        have h4 : Nat.Coprime (((a % ℓ : ℕ) : ℤ) - c).natAbs ℓ := by
          rw [Nat.coprime_comm]
          apply (hℓ.coprime_iff_not_dvd).mpr
          intro h5
          exact h (Int.dvd_natAbs.mp (Int.natCast_dvd_natCast.mpr h5))
        exact h4
    rw [h1, h2, h3, h5, h4]
  -- now count via `card_filter_mod`
  have hpow : ℓ ^ e = ℓ ^ (e - 1) * ℓ := by
    conv_lhs => rw [show e = (e - 1) + 1 by omega]
    rw [pow_succ]
  unfold nboth
  have hstep : ((range (ℓ ^ e)).filter
      (fun a : ℕ => Nat.Coprime a (ℓ ^ e) ∧ Int.gcd ((a : ℤ) - c) (((ℓ ^ e : ℕ)) : ℤ) = 1))
      = ((range (ℓ ^ (e - 1) * ℓ)).filter
        (fun a => (fun r : ℕ => Nat.Coprime r ℓ ∧ Int.gcd ((r : ℤ) - c) ℓ = 1)
          (a % ℓ))) := by
    rw [← hpow]
    apply Finset.filter_congr
    intro a _
    exact hcond a
  rw [hstep]
  exact card_filter_mod (ℓ ^ (e - 1)) ℓ hℓ0
    (fun r : ℕ => Nat.Coprime r ℓ ∧ Int.gcd ((r : ℤ) - c) ℓ = 1)

/-! ### The exact local factors of (60) -/

/-- **The prime local factor:** `ℓ/φ(ℓ)² · N(c,ℓ)` is `ℓ/(ℓ−1)` when
`ℓ ∣ c` and `ℓ(ℓ−2)/(ℓ−1)²` when `ℓ ∤ c` — the factors of (60) at a prime
modulus. -/
theorem kappaM_prime {ℓ : ℕ} (hℓ : ℓ.Prime) (c : ℤ) :
    (ℓ : ℚ) / (Nat.totient ℓ : ℚ) ^ 2 * (nboth c ℓ : ℚ)
      = if (ℓ : ℤ) ∣ c then (ℓ : ℚ) / (ℓ - 1)
        else (ℓ : ℚ) * (ℓ - 2) / (ℓ - 1) ^ 2 := by
  have h1 := nboth_prime hℓ c
  have hφ : (Nat.totient ℓ : ℚ) = (ℓ : ℚ) - 1 := by
    rw [Nat.totient_prime hℓ, Nat.cast_sub hℓ.one_le, Nat.cast_one]
  have hℓ2 : (2 : ℕ) ≤ ℓ := hℓ.two_le
  have hne : ((ℓ : ℚ) - 1) ≠ 0 := by
    have : (2 : ℚ) ≤ (ℓ : ℚ) := by exact_mod_cast hℓ2
    linarith
  by_cases hd : (ℓ : ℤ) ∣ c
  · rw [if_pos hd] at h1 ⊢
    rw [h1, hφ]
    have hcast : ((ℓ - 1 : ℕ) : ℚ) = (ℓ : ℚ) - 1 := by
      rw [Nat.cast_sub hℓ.one_le, Nat.cast_one]
    rw [hcast]
    field_simp
  · rw [if_neg hd] at h1 ⊢
    rw [h1, hφ]
    have hcast : ((ℓ - 2 : ℕ) : ℚ) = (ℓ : ℚ) - 2 := by
      rw [Nat.cast_sub hℓ.two_le]
      norm_num
    rw [hcast]
    field_simp

/-- **The prime-power local factor:** for every `e ≥ 1`,
`ℓ^e/φ(ℓ^e)² · N(c, ℓ^e)` equals the *same* local factor as at `e = 1` —
the prime-power case of the product formula (60). -/
theorem kappaM_prime_pow {ℓ : ℕ} (hℓ : ℓ.Prime) (c : ℤ) {e : ℕ} (he : 1 ≤ e) :
    ((ℓ ^ e : ℕ) : ℚ) / (Nat.totient (ℓ ^ e) : ℚ) ^ 2 * (nboth c (ℓ ^ e) : ℚ)
      = if (ℓ : ℤ) ∣ c then (ℓ : ℚ) / (ℓ - 1)
        else (ℓ : ℚ) * (ℓ - 2) / (ℓ - 1) ^ 2 := by
  have h1 := nboth_prime_pow hℓ c he
  have hφ : (Nat.totient (ℓ ^ e) : ℚ) = (ℓ : ℚ) ^ (e - 1) * ((ℓ : ℚ) - 1) := by
    rw [Nat.totient_prime_pow hℓ (by omega)]
    push_cast [Nat.cast_sub hℓ.one_le]
    ring
  have hℓ2 : (2 : ℕ) ≤ ℓ := hℓ.two_le
  have hℓQ : (2 : ℚ) ≤ (ℓ : ℚ) := by exact_mod_cast hℓ2
  have hne : ((ℓ : ℚ) - 1) ≠ 0 := by linarith
  have hpne : ((ℓ : ℚ) ^ (e - 1)) ≠ 0 := by positivity
  have hpow : ((ℓ ^ e : ℕ) : ℚ) = (ℓ : ℚ) ^ (e - 1) * (ℓ : ℚ) := by
    have h2 : ℓ ^ e = ℓ ^ (e - 1) * ℓ := by
      rw [← pow_succ, Nat.sub_add_cancel he]
    rw [h2]
    push_cast
    ring
  rw [h1, hφ, hpow]
  push_cast
  rw [← kappaM_prime hℓ c]
  have hφ1 : (Nat.totient ℓ : ℚ) = (ℓ : ℚ) - 1 := by
    rw [Nat.totient_prime hℓ, Nat.cast_sub hℓ.one_le, Nat.cast_one]
  rw [hφ1]
  field_simp

/-- **The per-prime mean identity behind (61):** averaging the local factor
over the residue of `m` modulo `ℓ` (when `ℓ ∤ A`, the class `ℓ ∣ Am` occurs
for exactly one `m` in `ℓ`) returns `1`:

`(1/ℓ)·ℓ/(ℓ−1) + ((ℓ−1)/ℓ)·ℓ(ℓ−2)/(ℓ−1)² = 1`. -/
theorem local_average {ℓ : ℚ} (h1 : ℓ ≠ 0) (h2 : ℓ ≠ 1) :
    (1 / ℓ) * (ℓ / (ℓ - 1)) + ((ℓ - 1) / ℓ) * (ℓ * (ℓ - 2) / (ℓ - 1) ^ 2) = 1 := by
  have hne : ℓ - 1 ≠ 0 := fun h => h2 (by linarith [sub_eq_zero.mp h])
  field_simp
  ring

/-! ### Multiplicativity, the product formula (60), and the mean (61)

The two conditions in (58) say that a residue class and its shift by `c` are
*units*; the Chinese remainder theorem for `ZMod` is a ring isomorphism, so
both conditions factor across coprime moduli and `N(c,·)` is multiplicative.
With the prime-power values above, the product formula (60) follows for every
`d`, and averaging over a period gives (61).
-/

open Classical in
/-- `N(c, d)` read inside `ZMod d`: the classes that are units and whose shift
by `c` is a unit.  This is the shape in which the Chinese remainder theorem
acts (`ZMod.chineseRemainder` is a *ring* isomorphism, and a pair is a unit
exactly when both coordinates are); `nboth_eq_nbothZ` is the bridge back to the
counting definition (58). -/
noncomputable def nbothZ {d : ℕ} [NeZero d] (c : ZMod d) : ℕ :=
  (Finset.univ.filter (fun a : ZMod d => IsUnit a ∧ IsUnit (a - c))).card

private lemma isUnit_ringEquiv {R S : Type*} [Monoid R] [Monoid S] (e : R ≃* S) (a : R) :
    IsUnit (e a) ↔ IsUnit a :=
  ⟨fun hu => by simpa using hu.map (e.symm : S →* R), fun hu => hu.map (e : R →* S)⟩

private lemma isUnit_intCast_iff {d : ℕ} (n : ℤ) :
    IsUnit ((n : ZMod d)) ↔ Int.gcd n (d : ℤ) = 1 := by
  have key : IsUnit ((n : ZMod d)) ↔ IsUnit (((n.natAbs : ℕ) : ZMod d)) := by
    rcases Int.natAbs_eq n with h | h
    · have he : ((n : ZMod d)) = ((n.natAbs : ℕ) : ZMod d) := by
        conv_lhs => rw [h]
        exact Int.cast_natCast _
      rw [he]
    · have he : ((n : ZMod d)) = -((n.natAbs : ℕ) : ZMod d) := by
        conv_lhs => rw [h]
        rw [Int.cast_neg, Int.cast_natCast]
      rw [he, IsUnit.neg_iff]
  rw [key, ZMod.isUnit_iff_coprime]
  rfl

private lemma nboth_eq_nbothZ (c : ℤ) (d : ℕ) [NeZero d] :
    nboth c d = nbothZ ((c : ZMod d)) := by
  unfold nboth nbothZ
  refine Finset.card_nbij' (fun a : ℕ => ((a : ℕ) : ZMod d)) (fun a : ZMod d => a.val)
    ?_ ?_ ?_ ?_
  · intro a ha
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at ha
    rw [Finset.mem_coe, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, (ZMod.isUnit_iff_coprime a d).mpr ha.2.1, ?_⟩
    have hsub : ((a : ℕ) : ZMod d) - ((c : ℤ) : ZMod d) = (((a : ℤ) - c : ℤ) : ZMod d) := by
      push_cast
      ring
    rw [hsub, isUnit_intCast_iff]
    exact ha.2.2
  · intro x hx
    rw [Finset.mem_coe, Finset.mem_filter] at hx
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range]
    refine ⟨ZMod.val_lt x, ?_, ?_⟩
    · rw [← ZMod.isUnit_iff_coprime, ZMod.natCast_val, ZMod.cast_id]
      exact hx.2.1
    · rw [← isUnit_intCast_iff]
      have hs : ((((x.val : ℤ) - c : ℤ)) : ZMod d) = x - ((c : ℤ) : ZMod d) := by
        push_cast
        rw [ZMod.natCast_val, ZMod.cast_id]
      rw [hs]
      exact hx.2.2
  · intro a ha
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at ha
    exact ZMod.val_cast_of_lt ha.1
  · intro x _
    exact ZMod.natCast_zmod_val x

private lemma nbothZ_mul {d₁ d₂ : ℕ} [NeZero d₁] [NeZero d₂] [NeZero (d₁ * d₂)]
    (h : Nat.Coprime d₁ d₂) (c : ZMod (d₁ * d₂)) :
    nbothZ c
      = nbothZ ((ZMod.chineseRemainder h) c).1 * nbothZ ((ZMod.chineseRemainder h) c).2 := by
  unfold nbothZ
  rw [← Finset.card_product]
  refine Finset.card_equiv (ZMod.chineseRemainder h).toEquiv ?_
  intro a
  have hcoe : ∀ y : ZMod (d₁ * d₂),
      (ZMod.chineseRemainder h).toEquiv y = (ZMod.chineseRemainder h) y := fun _ => rfl
  have h1 : IsUnit a ↔ IsUnit ((ZMod.chineseRemainder h) a).1
      ∧ IsUnit ((ZMod.chineseRemainder h) a).2 := by
    rw [← Prod.isUnit_iff]
    exact (isUnit_ringEquiv (ZMod.chineseRemainder h).toMulEquiv a).symm
  have h2 : IsUnit (a - c)
      ↔ IsUnit (((ZMod.chineseRemainder h) a).1 - ((ZMod.chineseRemainder h) c).1)
        ∧ IsUnit (((ZMod.chineseRemainder h) a).2 - ((ZMod.chineseRemainder h) c).2) := by
    have he : (ZMod.chineseRemainder h) (a - c)
        = (((ZMod.chineseRemainder h) a).1 - ((ZMod.chineseRemainder h) c).1,
           ((ZMod.chineseRemainder h) a).2 - ((ZMod.chineseRemainder h) c).2) := by
      rw [map_sub]
      rfl
    rw [← isUnit_ringEquiv (ZMod.chineseRemainder h).toMulEquiv (a - c)]
    show IsUnit ((ZMod.chineseRemainder h) (a - c)) ↔ _
    rw [he, Prod.isUnit_iff]
  rw [Finset.mem_filter, hcoe, Finset.mem_product, Finset.mem_filter, Finset.mem_filter, h1, h2]
  simp only [Finset.mem_univ, true_and]
  tauto

/-- **Theorem 5.12, multiplicativity of (58):** for coprime moduli,

`N(c, d₁d₂) = N(c, d₁) · N(c, d₂)`.

Both conditions defining `N` say that a class is a unit, and
`ZMod.chineseRemainder` carries `ZMod (d₁d₂)` isomorphically onto
`ZMod d₁ × ZMod d₂`, where the units are exactly the pairs of units. -/
theorem nboth_mul {d₁ d₂ : ℕ} (h₁ : 0 < d₁) (h₂ : 0 < d₂) (h : Nat.Coprime d₁ d₂) (c : ℤ) :
    nboth c (d₁ * d₂) = nboth c d₁ * nboth c d₂ := by
  have : NeZero d₁ := ⟨h₁.ne'⟩
  have : NeZero d₂ := ⟨h₂.ne'⟩
  have : NeZero (d₁ * d₂) := ⟨Nat.mul_ne_zero h₁.ne' h₂.ne'⟩
  rw [nboth_eq_nbothZ, nboth_eq_nbothZ, nboth_eq_nbothZ, nbothZ_mul h]
  have hc : (ZMod.chineseRemainder h) ((c : ZMod (d₁ * d₂)))
      = ((c : ZMod d₁), (c : ZMod d₂)) := by
    rw [map_intCast]
    rfl
  rw [hc]

private lemma sum_range_zmod {M : Type*} [AddCommMonoid M] (d : ℕ) [NeZero d] (f : ZMod d → M) :
    ∑ m ∈ Finset.range d, f ((m : ℕ) : ZMod d) = ∑ m : ZMod d, f m := by
  refine Finset.sum_nbij' (fun m : ℕ => ((m : ℕ) : ZMod d)) (fun a : ZMod d => a.val)
    ?_ ?_ ?_ ?_ ?_
  · intro a _; exact Finset.mem_univ _
  · intro x _; exact Finset.mem_range.mpr (ZMod.val_lt x)
  · intro a ha; exact ZMod.val_cast_of_lt (Finset.mem_range.mp ha)
  · intro x _; exact ZMod.natCast_zmod_val x
  · intro a _; rfl

private lemma sum_nbothZ_mul {d₁ d₂ : ℕ} [NeZero d₁] [NeZero d₂] [NeZero (d₁ * d₂)]
    (h : Nat.Coprime d₁ d₂) (A : ℤ) :
    ∑ m : ZMod (d₁ * d₂), (nbothZ ((A : ZMod (d₁ * d₂)) * m) : ℚ)
      = (∑ m : ZMod d₁, (nbothZ ((A : ZMod d₁) * m) : ℚ))
        * (∑ m : ZMod d₂, (nbothZ ((A : ZMod d₂) * m) : ℚ)) := by
  have hprod : (∑ m : ZMod d₁, (nbothZ ((A : ZMod d₁) * m) : ℚ))
        * (∑ m : ZMod d₂, (nbothZ ((A : ZMod d₂) * m) : ℚ))
      = ∑ p : ZMod d₁ × ZMod d₂,
          (nbothZ ((A : ZMod d₁) * p.1) : ℚ) * (nbothZ ((A : ZMod d₂) * p.2) : ℚ) := by
    rw [Finset.sum_mul_sum, Fintype.sum_prod_type]
  rw [hprod]
  refine Fintype.sum_equiv (ZMod.chineseRemainder h).toEquiv _ _ ?_
  intro m
  have hm : (ZMod.chineseRemainder h) ((A : ZMod (d₁ * d₂)) * m)
      = ((A : ZMod d₁) * ((ZMod.chineseRemainder h) m).1,
         (A : ZMod d₂) * ((ZMod.chineseRemainder h) m).2) := by
    rw [map_mul, map_intCast]
    rfl
  rw [nbothZ_mul h ((A : ZMod (d₁ * d₂)) * m), hm]
  push_cast
  rfl

private lemma nboth_one (c : ℤ) : nboth c 1 = 1 := by
  unfold nboth
  rw [Finset.filter_true_of_mem]
  · simp
  · intro a _
    exact ⟨Nat.coprime_one_right a, Int.gcd_one_right _⟩

/-- The product formula in `if`-form; `kappaM_product` splits the two products.
The induction is over the multiplicative structure of `d`. -/
private lemma kappaM_prod_if (c : ℤ) : ∀ d : ℕ, 0 < d →
    (d : ℚ) / (Nat.totient d : ℚ) ^ 2 * (nboth c d : ℚ)
      = ∏ ℓ ∈ d.primeFactors,
          (if (ℓ : ℤ) ∣ c then (ℓ : ℚ) / (ℓ - 1)
            else (ℓ : ℚ) * (ℓ - 2) / (ℓ - 1) ^ 2) := by
  intro d
  induction d using Nat.recOnPosPrimePosCoprime with
  | zero => intro h; exact absurd h (lt_irrefl 0)
  | one =>
      intro _
      rw [nboth_one]
      simp
  | prime_pow p n hp hn =>
      intro _
      rw [Nat.primeFactors_prime_pow hn.ne' hp, Finset.prod_singleton]
      exact kappaM_prime_pow hp c hn
  | coprime a b ha hb hab iha ihb =>
      intro _
      have ha0 : 0 < a := by omega
      have hb0 : 0 < b := by omega
      rw [hab.primeFactors_mul, Finset.prod_union hab.disjoint_primeFactors,
        ← iha ha0, ← ihb hb0, nboth_mul ha0 hb0 hab, Nat.totient_mul hab]
      push_cast
      ring

private lemma sum_nbothZ_range (d : ℕ) [NeZero d] (A : ℤ) :
    ∑ m ∈ Finset.range d, (nbothZ ((A : ZMod d) * ((m : ℕ) : ZMod d)) : ℚ)
      = ∑ m : ZMod d, (nbothZ ((A : ZMod d) * m) : ℚ) :=
  sum_range_zmod d (fun z => (nbothZ ((A : ZMod d) * z) : ℚ))

private lemma nboth_mul_cast (d : ℕ) [NeZero d] (A : ℤ) (m : ℕ) :
    (nboth (A * m) d : ℚ) = (nbothZ ((A : ZMod d) * ((m : ℕ) : ZMod d)) : ℚ) := by
  rw [nboth_eq_nbothZ]
  congr 2
  push_cast
  ring

/-- The period sum `∑_{m<d} N(Am, d)` is multiplicative in `d`: the Chinese
remainder isomorphism reindexes the sum over `ZMod (d₁d₂)` as a double sum. -/
private lemma sum_nboth_range_mul {d₁ d₂ : ℕ} (h₁ : 0 < d₁) (h₂ : 0 < d₂)
    (h : Nat.Coprime d₁ d₂) (A : ℤ) :
    (∑ m ∈ Finset.range (d₁ * d₂), (nboth (A * m) (d₁ * d₂) : ℚ))
      = (∑ m ∈ Finset.range d₁, (nboth (A * m) d₁ : ℚ))
        * (∑ m ∈ Finset.range d₂, (nboth (A * m) d₂ : ℚ)) := by
  have e₁ : NeZero d₁ := ⟨h₁.ne'⟩
  have e₂ : NeZero d₂ := ⟨h₂.ne'⟩
  have e₃ : NeZero (d₁ * d₂) := ⟨Nat.mul_ne_zero h₁.ne' h₂.ne'⟩
  simp_rw [nboth_mul_cast]
  rw [sum_nbothZ_range, sum_nbothZ_range, sum_nbothZ_range]
  exact sum_nbothZ_mul h A

/-- For `ℓ ∤ A` prime, exactly `ℓ^{e−1}` of the residues `m < ℓ^e` satisfy
`ℓ ∣ Am` — namely the multiples of `ℓ`. -/
private lemma card_dvd_mul_filter {ℓ : ℕ} (hℓ : ℓ.Prime) {A : ℤ} (hA : ¬ (ℓ : ℤ) ∣ A)
    {e : ℕ} (he : 1 ≤ e) :
    ((Finset.range (ℓ ^ e)).filter (fun m : ℕ => (ℓ : ℤ) ∣ A * m)).card = ℓ ^ (e - 1) := by
  have hpZ : Prime ((ℓ : ℕ) : ℤ) := Int.prime_iff_natAbs_prime.mpr (by simpa using hℓ)
  have hpow : ℓ ^ e = ℓ ^ (e - 1) * ℓ := by
    rw [← pow_succ, Nat.sub_add_cancel he]
  have hcond : ∀ m : ℕ, ((ℓ : ℤ) ∣ A * m) ↔ (m % ℓ = 0) := by
    intro m
    constructor
    · intro hd
      rcases (hpZ.dvd_mul).mp hd with h | h
      · exact absurd h hA
      · have hm : ℓ ∣ m := by exact_mod_cast h
        exact Nat.dvd_iff_mod_eq_zero.mp hm
    · intro hm
      have hm' : ℓ ∣ m := Nat.dvd_of_mod_eq_zero hm
      have : (ℓ : ℤ) ∣ (m : ℤ) := by exact_mod_cast hm'
      exact this.mul_left A
  have hset : (Finset.range (ℓ ^ e)).filter (fun m : ℕ => (ℓ : ℤ) ∣ A * m)
      = (Finset.range (ℓ ^ (e - 1) * ℓ)).filter
        (fun m : ℕ => (fun r : ℕ => r = 0) (m % ℓ)) := by
    rw [← hpow]
    exact Finset.filter_congr (fun m _ => by simpa using hcond m)
  rw [hset, card_filter_mod (ℓ ^ (e - 1)) ℓ hℓ.pos (fun r : ℕ => r = 0)]
  rw [Finset.filter_eq' (Finset.range ℓ) 0, if_pos (Finset.mem_range.mpr hℓ.pos)]
  simp

private lemma kappaM_avg_aux (A : ℤ) : ∀ d : ℕ, 0 < d →
    (1 / (d : ℚ)) * ((d : ℚ) / (Nat.totient d : ℚ) ^ 2)
        * (∑ m ∈ Finset.range d, (nboth (A * m) d : ℚ))
      = ∏ ℓ ∈ d.primeFactors.filter (fun ℓ : ℕ => (ℓ : ℤ) ∣ A), (ℓ : ℚ) / (ℓ - 1) := by
  intro d
  induction d using Nat.recOnPosPrimePosCoprime with
  | zero => intro h; exact absurd h (lt_irrefl 0)
  | one =>
      intro _
      simp [nboth_one]
  | prime_pow p n hp hn =>
      intro _
      have hq0 : ((p : ℚ)) ≠ 0 := by
        have : (0 : ℕ) < p := hp.pos
        positivity
      have hp2 : (2 : ℕ) ≤ p := hp.two_le
      have hqQ : (2 : ℚ) ≤ (p : ℚ) := by exact_mod_cast hp2
      have hq1 : ((p : ℚ)) ≠ 1 := by linarith
      have hqm : ((p : ℚ) - 1) ≠ 0 := by linarith
      have hPow : ((p ^ n : ℕ) : ℚ) = (p : ℚ) ^ (n - 1) * (p : ℚ) := by
        have h2 : p ^ n = p ^ (n - 1) * p := by
          rw [← pow_succ, Nat.sub_add_cancel hn]
        rw [h2]; push_cast; ring
      have hP0 : ((p : ℚ)) ^ (n - 1) ≠ 0 := by positivity
      rw [mul_assoc, Finset.mul_sum,
        Finset.sum_congr rfl (fun m (_ : m ∈ Finset.range (p ^ n)) =>
          kappaM_prime_pow hp (A * m) hn),
        Nat.primeFactors_prime_pow hn.ne' hp, Finset.filter_singleton]
      by_cases hA : (p : ℤ) ∣ A
      · rw [if_pos hA, Finset.prod_singleton]
        rw [Finset.sum_congr rfl (fun m (_ : m ∈ Finset.range (p ^ n)) => by
          rw [if_pos (hA.mul_right (m : ℤ))]), Finset.sum_const, Finset.card_range,
          nsmul_eq_mul]
        rw [hPow]
        field_simp
      · rw [if_neg hA, Finset.prod_empty]
        rw [← Finset.sum_filter_add_sum_filter_not (Finset.range (p ^ n))
          (fun m : ℕ => (p : ℤ) ∣ A * m)]
        have hc1 : ((Finset.range (p ^ n)).filter (fun m : ℕ => (p : ℤ) ∣ A * m)).card
            = p ^ (n - 1) := card_dvd_mul_filter hp hA hn
        have hc2 : ((Finset.range (p ^ n)).filter (fun m : ℕ => (p : ℤ) ∣ A * m)).card
            + ((Finset.range (p ^ n)).filter (fun m : ℕ => ¬ (p : ℤ) ∣ A * m)).card
            = p ^ n := by
          rw [Finset.card_filter_add_card_filter_not, Finset.card_range]
        have hc2' : (((Finset.range (p ^ n)).filter
            (fun m : ℕ => ¬ (p : ℤ) ∣ A * m)).card : ℚ)
            = (p : ℚ) ^ (n - 1) * (p : ℚ) - (p : ℚ) ^ (n - 1) := by
          have h3 : (((Finset.range (p ^ n)).filter
              (fun m : ℕ => (p : ℤ) ∣ A * m)).card : ℚ)
              + (((Finset.range (p ^ n)).filter
                (fun m : ℕ => ¬ (p : ℤ) ∣ A * m)).card : ℚ) = ((p ^ n : ℕ) : ℚ) := by
            exact_mod_cast congrArg (fun t : ℕ => (t : ℚ)) hc2
          rw [hc1] at h3
          rw [hPow] at h3
          push_cast at h3 ⊢
          linarith
        rw [Finset.sum_congr rfl (fun m (hm : m ∈ (Finset.range (p ^ n)).filter
              (fun m : ℕ => (p : ℤ) ∣ A * m)) => by
            rw [if_pos (Finset.mem_filter.mp hm).2]),
          Finset.sum_congr rfl (fun m (hm : m ∈ (Finset.range (p ^ n)).filter
              (fun m : ℕ => ¬ (p : ℤ) ∣ A * m)) => by
            rw [if_neg (Finset.mem_filter.mp hm).2]),
          Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul, hc1, hc2', hPow]
        push_cast
        have hstep : (1 / ((p : ℚ) ^ (n - 1) * (p : ℚ)))
            * ((p : ℚ) ^ (n - 1) * ((p : ℚ) / ((p : ℚ) - 1))
               + ((p : ℚ) ^ (n - 1) * (p : ℚ) - (p : ℚ) ^ (n - 1))
                 * ((p : ℚ) * ((p : ℚ) - 2) / (((p : ℚ) - 1) ^ 2)))
            = (1 / (p : ℚ)) * ((p : ℚ) / ((p : ℚ) - 1))
              + (((p : ℚ) - 1) / (p : ℚ))
                * ((p : ℚ) * ((p : ℚ) - 2) / (((p : ℚ) - 1) ^ 2)) := by
          field_simp
          try ring
        rw [hstep]
        exact local_average hq0 hq1
  | coprime a b ha hb hab iha ihb =>
      intro _
      have ha0 : 0 < a := by omega
      have hb0 : 0 < b := by omega
      rw [hab.primeFactors_mul, Finset.filter_union,
        Finset.prod_union (Finset.disjoint_filter_filter hab.disjoint_primeFactors),
        ← iha ha0, ← ihb hb0, sum_nboth_range_mul ha0 hb0 hab, Nat.totient_mul hab]
      push_cast
      ring

/-- **Theorem 5.12, the product formula (60), for an arbitrary modulus `d`:**

`d/φ(d)² · N(c,d) = ∏_{ℓ ∣ d, ℓ ∣ c} ℓ/(ℓ−1) · ∏_{ℓ ∣ d, ℓ ∤ c} ℓ(ℓ−2)/(ℓ−1)²`.

Both sides are multiplicative in `d` (`nboth_mul`, `Nat.totient_mul`,
`Nat.Coprime.primeFactors_mul`) and agree at prime powers
(`kappaM_prime_pow`), so they agree everywhere.  Taking `c = Am` gives (60)
verbatim. -/
theorem kappaM_product (c : ℤ) {d : ℕ} (hd : 0 < d) :
    (d : ℚ) / (Nat.totient d : ℚ) ^ 2 * (nboth c d : ℚ)
      = (∏ ℓ ∈ d.primeFactors.filter (fun ℓ : ℕ => (ℓ : ℤ) ∣ c), (ℓ : ℚ) / (ℓ - 1))
        * ∏ ℓ ∈ d.primeFactors.filter (fun ℓ : ℕ => ¬ (ℓ : ℤ) ∣ c),
            (ℓ : ℚ) * (ℓ - 2) / (ℓ - 1) ^ 2 := by
  rw [kappaM_prod_if c d hd, Finset.prod_ite]

/-- **Theorem 5.12, the mean formula (61):** averaging `κ_m(A,d)` over a full
period `m = 0, …, d−1`,

`(1/d) ∑_{m<d} d/φ(d)² · N(Am,d) = ∏_{ℓ ∣ d, ℓ ∣ A} ℓ/(ℓ−1) = κ(A,d)`.

The average is again multiplicative in `d` (`sum_nboth_range_mul`); at a prime
power `ℓ^e` it is `ℓ/(ℓ−1)` when `ℓ ∣ A` (every `m` contributes that factor)
and, when `ℓ ∤ A`, exactly `1` — the class `ℓ ∣ m` occupies a proportion `1/ℓ`
of the period, and `local_average` is the resulting identity. -/
theorem kappaM_average (A : ℤ) {d : ℕ} (hd : 0 < d) :
    (1 / (d : ℚ)) * ∑ m ∈ Finset.range d,
        ((d : ℚ) / (Nat.totient d : ℚ) ^ 2 * (nboth (A * m) d : ℚ))
      = ∏ ℓ ∈ d.primeFactors.filter (fun ℓ : ℕ => (ℓ : ℤ) ∣ A), (ℓ : ℚ) / (ℓ - 1) := by
  rw [← Finset.mul_sum, ← mul_assoc]
  exact kappaM_avg_aux A d hd

end DSS
