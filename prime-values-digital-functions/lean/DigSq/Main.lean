/-
DigSq/Main.lean

**Theorem 1.1** of the paper in the case `d_g = 1`, and the headline corollary:

  `A052034_infinite` — there are infinitely many primes `p` such that the sum of
  the squares of the decimal digits of `p` is again prime.

The only axiom used is `mmr` (Martin–Mauduit–Rivat).  In particular the
argument needs *no* prime number theorem: at the peak `k = μ_g log_b x` the
factor `π(x)` is common to the main term and the error term of Theorem 2.1 and
cancels, leaving the elementary comparison `√L` versus `L^{3/4}` of
`DigSq.Analytic`.
-/
import DigSq.Cited
import DigSq.Analytic
import DigSq.Examples

namespace DigSq

open Finset Real

variable {b : ℕ}

/-! ### Theorem 1.1(i), for `d_g = 1` -/

/-- **Theorem 1.1(i)** when `d_g = 1`: *every sufficiently large integer* is the
value of `g` at some prime.  (For `g = S` this is the assertion of §6.1 that
every sufficiently large integer occurs as `S(p)`.) -/
theorem exists_prime_eval_eq_of_dg_one (g : Weight b) (hg : g.Coprime₁)
    (hdg : g.dg = 1) (hmu : 0 < g.mu) :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k → ∃ p : ℕ, Nat.Prime p ∧ g.eval p = (k : ℤ) := by
  have hb1 : (1 : ℝ) < (b : ℝ) := by exact_mod_cast g.one_lt_b
  have hb2 : (2 : ℝ) ≤ (b : ℝ) := by exact_mod_cast g.hb
  have hb0 : (0 : ℝ) < (b : ℝ) := lt_trans one_pos hb1
  have hbne : (b : ℝ) ≠ 1 := ne_of_gt hb1
  have hlogb : 0 < Real.log (b : ℝ) := Real.log_pos hb1
  have hsig : 0 < g.sigSq := Weight.sigSq_pos hg
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hWpos : (0 : ℝ) < 2 * Real.pi * g.sigSq := by positivity
  -- Theorem 2.1 with `ε = 1/4`
  obtain ⟨C, hC0, hC⟩ := mmr g hg (ε := (1 : ℝ) / 4) (by norm_num) (by norm_num)
  -- the elementary comparison
  obtain ⟨L₀, hL₀1, hL₀⟩ :=
    sqrt_lt_rpow_three_quarters (A := Real.log (b : ℝ) ^ ((3 : ℝ) / 4))
      (B := C * Real.sqrt (2 * Real.pi * g.sigSq))
      (Real.rpow_pos_of_pos hlogb _) (mul_nonneg hC0 (Real.sqrt_nonneg _))
  refine ⟨⌈g.mu * max 2 L₀⌉₊ + 1, ?_⟩
  intro k hk
  -- the range `x = b^{k/μ_g}`, at which the Gaussian is centred on `k`
  set L : ℝ := (k : ℝ) / g.mu with hLdef
  have hkR : g.mu * max 2 L₀ < (k : ℝ) := by
    have h1 : g.mu * max 2 L₀ ≤ (⌈g.mu * max 2 L₀⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : ((⌈g.mu * max 2 L₀⌉₊ : ℕ) : ℝ) + 1 ≤ (k : ℝ) := by exact_mod_cast hk
    linarith
  have hLbig : max 2 L₀ < L := by
    rw [hLdef, lt_div_iff₀ hmu, mul_comm]; exact hkR
  have hL2 : (2 : ℝ) ≤ L := le_of_lt (lt_of_le_of_lt (le_max_left _ _) hLbig)
  have hLL₀ : L₀ ≤ L := le_of_lt (lt_of_le_of_lt (le_max_right _ _) hLbig)
  have hLpos : (0 : ℝ) < L := by linarith
  set x : ℝ := (b : ℝ) ^ L with hxdef
  have hlogbx : Real.logb (b : ℝ) x = L := by rw [hxdef]; exact Real.logb_rpow hb0 hbne
  have hlogx : Real.log x = L * Real.log (b : ℝ) := by rw [hxdef]; exact Real.log_rpow hb0 L
  have hlogxpos : (0 : ℝ) < Real.log x := by rw [hlogx]; positivity
  have hx2 : (2 : ℝ) < x := by
    have h4 : (b : ℝ) ^ (2 : ℝ) ≤ x := by
      rw [hxdef]; exact Real.rpow_le_rpow_of_exponent_le (le_of_lt hb1) hL2
    have hb2' : (b : ℝ) ^ (2 : ℝ) = (b : ℝ) ^ (2 : ℕ) := by
      rw [← Real.rpow_natCast (b : ℝ) 2]; norm_num
    rw [hb2'] at h4
    nlinarith [hb2, h4]
  have hxpos : (0 : ℝ) < x := by linarith
  have hP : (0 : ℝ) < (picount x : ℝ) := by
    exact_mod_cast picount_pos (le_of_lt hx2)
  -- the main term at the peak: the Gaussian factor is `1` and `π_k = π`
  have hmain : mmrMain g x (k : ℤ)
      = (picount x : ℝ) / (Real.sqrt (2 * Real.pi * g.sigSq) * Real.sqrt L) := by
    rw [mmrMain_def, piCong_of_dg_eq_one g hdg, hdg, hlogbx]
    have hmune : g.mu ≠ 0 := ne_of_gt hmu
    have hz : (((k : ℕ) : ℤ) : ℝ) - g.mu * L = 0 := by
      rw [hLdef]; push_cast; field_simp; ring
    rw [hz, Real.sqrt_mul (le_of_lt hWpos) L]
    simp
  -- the error term
  have hexp : (1 : ℝ) - 1 / 4 = (3 : ℝ) / 4 := by norm_num
  have herr : |(countEq g x (k : ℤ) : ℝ) - mmrMain g x (k : ℤ)|
      ≤ C * (picount x : ℝ) / Real.log x ^ ((3 : ℝ) / 4) := by
    have := hC x hx2 (k : ℤ)
    rwa [hexp] at this
  -- main term beats error term
  have hden1 : (0 : ℝ) < Real.sqrt (2 * Real.pi * g.sigSq) * Real.sqrt L := by
    have h1 : (0 : ℝ) < Real.sqrt (2 * Real.pi * g.sigSq) := Real.sqrt_pos.mpr hWpos
    have h2 : (0 : ℝ) < Real.sqrt L := Real.sqrt_pos.mpr hLpos
    exact mul_pos h1 h2
  have hden2 : (0 : ℝ) < Real.log x ^ ((3 : ℝ) / 4) := Real.rpow_pos_of_pos hlogxpos _
  have hcmp : C * Real.sqrt (2 * Real.pi * g.sigSq) * Real.sqrt L
      < Real.log x ^ ((3 : ℝ) / 4) := by
    have h := hL₀ L hLL₀
    have hsplit : Real.log x ^ ((3 : ℝ) / 4)
        = Real.log (b : ℝ) ^ ((3 : ℝ) / 4) * L ^ ((3 : ℝ) / 4) := by
      rw [hlogx, Real.mul_rpow (le_of_lt hLpos) (le_of_lt hlogb)]; ring
    rw [hsplit]
    calc C * Real.sqrt (2 * Real.pi * g.sigSq) * Real.sqrt L
        = (C * Real.sqrt (2 * Real.pi * g.sigSq)) * Real.sqrt L := by ring
      _ < Real.log (b : ℝ) ^ ((3 : ℝ) / 4) * L ^ ((3 : ℝ) / 4) := h
  have hbeat : C * (picount x : ℝ) / Real.log x ^ ((3 : ℝ) / 4)
      < mmrMain g x (k : ℤ) := by
    rw [hmain, div_lt_div_iff₀ hden2 hden1]
    have : C * (picount x : ℝ) * (Real.sqrt (2 * Real.pi * g.sigSq) * Real.sqrt L)
        = (picount x : ℝ)
            * (C * Real.sqrt (2 * Real.pi * g.sigSq) * Real.sqrt L) := by ring
    rw [this]
    exact mul_lt_mul_of_pos_left hcmp hP
  -- hence the count is positive, and a prime with `g(p) = k` exists
  have hlow : (0 : ℝ) < (countEq g x (k : ℤ) : ℝ) := by
    have h := (abs_le.mp herr).1
    linarith
  have hpos : 0 < countEq g x (k : ℤ) := by exact_mod_cast hlow
  obtain ⟨p, hp1, _, hp3⟩ := exists_of_countEq_pos g (le_of_lt hxpos) hpos
  exact ⟨p, hp1, hp3⟩

/-! ### From "every large value is attained" to infinitude -/

/-- If every sufficiently large integer is `g(p)` for some prime `p`, then `g(p)`
is prime for infinitely many primes `p`.

The map sending a prime `k` to a prime `p` with `g(p) = k` is injective, because
`g(p)` determines `k`; this is the paper's argument. -/
theorem infinite_of_exists_prime_eval_eq (g : Weight b)
    (h : ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k → ∃ p : ℕ, Nat.Prime p ∧ g.eval p = (k : ℤ)) :
    {p : ℕ | Nat.Prime p ∧ ∃ q : ℕ, Nat.Prime q ∧ g.eval p = (q : ℤ)}.Infinite := by
  obtain ⟨k₀, h'⟩ := h
  -- turn the statement into a total choice function
  have h2 : ∀ k : ℕ, ∃ p : ℕ, k₀ ≤ k → (Nat.Prime p ∧ g.eval p = (k : ℤ)) := by
    intro k
    by_cases hk : k₀ ≤ k
    · obtain ⟨p, hp1, hp2⟩ := h' k hk
      exact ⟨p, fun _ => ⟨hp1, hp2⟩⟩
    · exact ⟨0, fun hc => absurd hc hk⟩
  choose F hF using h2
  -- the source: primes `≥ k₀`
  set K : Set ℕ := {k : ℕ | Nat.Prime k ∧ k₀ ≤ k} with hK
  have hKinf : K.Infinite := by
    have h1 : {p : ℕ | Nat.Prime p}.Infinite := by
      simpa [Nat.prime_iff] using Nat.infinite_setOfPred_prime
    have h2 : {p : ℕ | Nat.Prime p} \ {k : ℕ | k < k₀} ⊆ K := by
      rintro n ⟨hn1, hn2⟩
      exact ⟨hn1, not_lt.mp hn2⟩
    exact Set.Infinite.mono h2 (h1.sdiff (Set.finite_lt_nat k₀))
  refine Set.infinite_of_injOn_mapsTo (f := F) ?_ ?_ hKinf
  · intro a ha c hc hac
    have h1 := (hF a ha.2).2
    have h2 := (hF c hc.2).2
    rw [hac] at h1
    have : ((a : ℕ) : ℤ) = ((c : ℕ) : ℤ) := by rw [← h1, h2]
    exact_mod_cast this
  · intro a ha
    obtain ⟨hp1, hp2⟩ := hF a ha.2
    exact ⟨hp1, a, ha.1, hp2⟩

/-- **Theorem 1.1** for `d_g = 1`: `g(p)` is prime for infinitely many primes `p`. -/
theorem infinite_prime_eval_prime_of_dg_one (g : Weight b) (hg : g.Coprime₁)
    (hdg : g.dg = 1) (hmu : 0 < g.mu) :
    {p : ℕ | Nat.Prime p ∧ ∃ q : ℕ, Nat.Prime q ∧ g.eval p = (q : ℤ)}.Infinite :=
  infinite_of_exists_prime_eval_eq g (exists_prime_eval_eq_of_dg_one g hg hdg hmu)

/-! ### The headline: OEIS A052034 is infinite -/

/-- **A052034 is infinite.**

There are infinitely many primes `p` such that `S(p)`, the sum of the squares of
the decimal digits of `p`, is again prime.  These are the primes
`11, 23, 41, 61, 83, 101, 113, 131, 137, 173, 179, 191, …` of OEIS A052034. -/
theorem A052034_infinite : {p : ℕ | Nat.Prime p ∧ Nat.Prime (S p)}.Infinite := by
  have h := infinite_prime_eval_prime_of_dg_one wS wS_coprime₁ dg_wS mu_wS_pos
  refine Set.Infinite.mono ?_ h
  rintro p ⟨hp, q, hq, hpq⟩
  refine ⟨hp, ?_⟩
  have : (S p : ℤ) = (q : ℤ) := by rw [← eval_wS p, hpq]
  have : S p = q := by exact_mod_cast this
  rwa [this]

/-- **A052034 is infinite, with `S` written out.**

The same statement as `A052034_infinite`, but with the definition of `S` inlined,
so that nothing but Mathlib's own `Nat.digits`, `Nat.Prime` and `Set.Infinite`
appears.  A reader auditing the claim need not read any definition of ours. -/
theorem A052034_infinite_inlined :
    {p : ℕ | Nat.Prime p ∧
      Nat.Prime (((Nat.digits 10 p).map (fun d => d ^ 2)).sum)}.Infinite := by
  simpa [S_def] using A052034_infinite

/-- **A052034 is infinite**, stated without `Set.Infinite`: beyond every bound
there is a prime `p` for which the sum of the squares of the decimal digits of
`p` is again prime. -/
theorem A052034_exists_gt (N : ℕ) :
    ∃ p : ℕ, N < p ∧ Nat.Prime p ∧
      Nat.Prime (((Nat.digits 10 p).map (fun d => d ^ 2)).sum) := by
  obtain ⟨p, hp, hgt⟩ := A052034_infinite_inlined.exists_gt N
  exact ⟨p, hgt, hp.1, hp.2⟩

/-- **Corollary 1.4 in base ten, for even `r`.**

There are infinitely many primes `p` such that the sum of the `r`-th powers of
the decimal digits of `p` is again prime.  (`r = 2` is `A052034_infinite`.)

Only the even case is available here: for odd `r` one has `d_g = 3`, and
Theorem 1.1 then needs the prime number theorem for arithmetic progressions,
which is outside the axiom base of this development. -/
theorem infinite_prime_powDigitSum_prime (r : ℕ) (hr : 2 ≤ r) (hre : Even r) :
    {p : ℕ | Nat.Prime p ∧ Nat.Prime (powDigitSum 10 r p)}.Infinite := by
  have hb : (2 : ℕ) ≤ 10 := by norm_num
  have hr1 : 1 ≤ r := by omega
  have h := infinite_prime_eval_prime_of_dg_one (powWeight 10 r hb hr1)
      (powWeight_coprime₁ 10 r hb hr1) (dg_powWeight_ten_even r hre hb hr1)
      (powWeight_mu_pos 10 r hb hr1)
  refine Set.Infinite.mono ?_ h
  rintro p ⟨hp, q, hq, hpq⟩
  refine ⟨hp, ?_⟩
  have h1 : (powDigitSum 10 r p : ℤ) = (q : ℤ) := by
    rw [← eval_powWeight 10 r hb hr1 p, hpq]
  have h2 : powDigitSum 10 r p = q := by exact_mod_cast h1
  rwa [h2]

/-- **Corollary 1.5**, for a digit `c ≥ 2`.

There are infinitely many primes in whose base-`b` expansion the digit `c`
occurs a prime number of times.

(For `c = 1` one has `g(1) = 1`, so `d_g` need not be `1` when `b = 2` or
`b = 3`; the argument here covers every `c` with `2 ≤ c < b`.) -/
theorem infinite_prime_digitOccurrences_prime (b c : ℕ) (hb : 2 ≤ b)
    (hc2 : 2 ≤ c) (hcb : c < b) :
    {p : ℕ | Nat.Prime p ∧ Nat.Prime (digitOccurrences b c p)}.Infinite := by
  have hc : 1 ≤ c := by omega
  have h := infinite_prime_eval_prime_of_dg_one (digitCount b c hb hc)
      (digitCount_coprime₁ b c hb hc hcb) (dg_digitCount b c hb hc hc2 hcb)
      (digitCount_mu_pos b c hb hc hcb)
  refine Set.Infinite.mono ?_ h
  rintro p ⟨hp, q, hq, hpq⟩
  refine ⟨hp, ?_⟩
  have h1 : (digitOccurrences b c p : ℤ) = (q : ℤ) := by
    rw [← eval_digitCount b c hb hc p, hpq]
  have h2 : digitOccurrences b c p = q := by exact_mod_cast h1
  rwa [h2]

/-- **Every sufficiently large integer is `S(p)` for a prime `p`** (§6.1). -/
theorem exists_prime_S_eq :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k → ∃ p : ℕ, Nat.Prime p ∧ S p = k := by
  obtain ⟨k₀, h⟩ := exists_prime_eval_eq_of_dg_one wS wS_coprime₁ dg_wS mu_wS_pos
  refine ⟨k₀, fun k hk => ?_⟩
  obtain ⟨p, hp1, hp2⟩ := h k hk
  refine ⟨p, hp1, ?_⟩
  have : (S p : ℤ) = (k : ℤ) := by rw [← eval_wS p, hp2]
  exact_mod_cast this

end DigSq
