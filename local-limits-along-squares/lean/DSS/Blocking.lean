/-
DSS/Blocking.lean

**The elementary heart of the sparse polynomial section (§7.2).**

Lemma 7.6 of the paper: for `b^k > c ≥ 1`, the `k` base-`b` digits of
`b^k − c` are the digitwise complements, with respect to `b − 1`, of the
digits of `c − 1` padded on the left by zeros; consequently, for every
strongly `b`-additive `g`,

  `g(b^k − c) = k·g(b−1) + C_{g,c}`

with an explicit constant `C_{g,c}`.  This generalises the verified digit-sum
complement rule `sb_pow_sub` from `s_b` to arbitrary integer digit weights,
and is the mechanism that makes `G(P(u·b^k + v))` affine in `k`
(Proposition 7.8).  We verify:

* `eval_ofDigits_comp` — the complement identity at the level of digit lists;
* `eval_pow_sub` — Lemma 7.6 itself, with the exact constant and threshold
  (`1 ≤ c ≤ b^k`; the paper's "sufficiently large `k`");
* `eval_add_pow_mul` — block additivity `g(r + b^k·m) = g(r) + g(m)` for
  `r < b^k`;
* `eval_linear_blocking` — the affine identity `g(u·b^k − c) = k·g(b−1) + C`
  for linear arguments with negative shift, i.e. Proposition 7.8(i) in
  degree one; for a nonnegative shift `v < b^k` the value
  `g(u·b^k + v) = g(u) + g(v)` is constant in `k` (`eval_add_pow_mul`).

Not formalised: Lemma 7.7 (the stabilising carries of a general `Q(b^k)`)
and with it Proposition 7.8 in degree `≥ 2`, and the block-additive case
(ii).

Nothing in this file is conditional: it imports no axioms.
-/
import DSS.Weight

namespace DSS

open Finset

variable {b : ℕ} (g : Weight b)

private lemma ofDigits_replicate_zero (b : ℕ) :
    ∀ n : ℕ, Nat.ofDigits b (List.replicate n 0) = 0
  | 0 => by simp
  | n + 1 => by
      simp [List.replicate_succ, Nat.ofDigits_cons, ofDigits_replicate_zero b n]

/-- The complement identity on digit lists: if every entry of `L` is a digit,
then `ofDigits` of the digitwise complement plus `ofDigits L` plus `1` is
`b^{len L}`. -/
lemma ofDigits_comp (hb : 2 ≤ b) :
    ∀ L : List ℕ, (∀ d ∈ L, d < b) →
      Nat.ofDigits b (L.map (fun d => b - 1 - d)) + Nat.ofDigits b L + 1
        = b ^ L.length := by
  intro L
  induction L with
  | nil => intro _; simp
  | cons d tl ih =>
      intro h
      have hd : d < b := h d (by simp)
      have htl : ∀ e ∈ tl, e < b := fun e he => h e (by simp [he])
      have ihtl := ih htl
      simp only [List.map_cons, Nat.ofDigits_cons, List.length_cons]
      have hexp : b ^ (tl.length + 1) = b * b ^ tl.length := by
        rw [pow_succ]
        ring
      rw [hexp]
      have hcomp : (b - 1 - d) + d = b - 1 := by omega
      have hmul : b * (Nat.ofDigits b (tl.map (fun d => b - 1 - d)))
          + b * Nat.ofDigits b tl + b = b * b ^ tl.length := by
        have h5 := congrArg (fun t => b * t) ihtl
        simpa [Nat.mul_add] using h5
      omega

/-- **Lemma 7.6:** for `1 ≤ c ≤ b^k`,

`g(b^k − c) = k·g(b−1) + C_{g,c}`,

where `C_{g,c} = ∑_j g(b−1−δ_j) − h·g(b−1)` over the `h` digits `δ_j` of
`c − 1`.  The digits of `b^k − c` are the `(b−1)`-complements of the digits
of `c − 1`, padded on the left to length `k` by the digit `b − 1`. -/
theorem eval_pow_sub {c k : ℕ} (hc : 1 ≤ c) (hck : c ≤ b ^ k) :
    g.eval (b ^ k - c)
      = k * g.w (b - 1)
        + (((Nat.digits b (c - 1)).map (fun d => g.w (b - 1 - d))).sum
            - (Nat.digits b (c - 1)).length * g.w (b - 1)) := by
  have hb : 2 ≤ b := g.hb
  have hb1 : 1 < b := g.one_lt_b
  obtain ⟨D, hDdef⟩ : ∃ L : List ℕ, L = Nat.digits b (c - 1) := ⟨_, rfl⟩
  obtain ⟨h, hhdef⟩ : ∃ n : ℕ, n = D.length := ⟨_, rfl⟩
  have hDdig : ∀ d ∈ D, d < b := by
    intro d hd
    rw [hDdef] at hd
    exact Nat.digits_lt_base hb1 hd
  -- `h ≤ k`
  have hlen : h ≤ k := by
    have h1 : c - 1 < b ^ k := by
      calc c - 1 < c := by omega
        _ ≤ b ^ k := hck
    have h2 : (Nat.digits b (c - 1)).length ≤ k :=
      (Nat.digits_length_le_iff hb1 (c - 1)).mpr h1
    rw [hhdef, hDdef]
    exact h2
  -- the value of `c − 1`
  have hval : Nat.ofDigits b D = c - 1 := by
    rw [hDdef]
    exact Nat.ofDigits_digits b (c - 1)
  -- the complement list and its value
  obtain ⟨CL, hCLdef⟩ : ∃ L : List ℕ,
      L = D.map (fun d => b - 1 - d) ++ List.replicate (k - h) (b - 1) := ⟨_, rfl⟩
  have hrepval : Nat.ofDigits b (List.replicate (k - h) (b - 1)) + 1
      = b ^ (k - h) := by
    have h0 : ∀ e ∈ List.replicate (k - h) (0 : ℕ), e < b := by
      intro e he
      rw [List.eq_of_mem_replicate he]
      omega
    have h1 := ofDigits_comp hb (List.replicate (k - h) 0) h0
    have h2 : (List.replicate (k - h) (0 : ℕ)).map (fun d => b - 1 - d)
        = List.replicate (k - h) (b - 1) := by
      rw [List.map_replicate]
      simp
    have h3 : Nat.ofDigits b (List.replicate (k - h) (0 : ℕ)) = 0 :=
      ofDigits_replicate_zero b (k - h)
    rw [h2, h3] at h1
    simpa using h1
  have hCLval : Nat.ofDigits b CL + c = b ^ k := by
    rw [hCLdef, Nat.ofDigits_append]
    have h1 := ofDigits_comp hb D hDdig
    rw [hval, ← hhdef] at h1
    have h2 : (D.map (fun d => b - 1 - d)).length = h := by
      rw [List.length_map, hhdef]
    rw [h2]
    have h3 : b ^ h * (Nat.ofDigits b (List.replicate (k - h) (b - 1)))
        = b ^ h * (b ^ (k - h) - 1) := by
      congr 1
      omega
    rw [h3]
    have h4 : b ^ h * (b ^ (k - h) - 1) = b ^ k - b ^ h := by
      have h5 : b ^ h * b ^ (k - h) = b ^ k := by
        rw [← pow_add]
        congr 1
        omega
      have h6 : 1 ≤ b ^ (k - h) := Nat.one_le_pow _ _ (by omega)
      have h7 : b ^ h * (b ^ (k - h) - 1) + b ^ h * 1 = b ^ h * b ^ (k - h) := by
        rw [← Nat.mul_add]
        congr 1
        omega
      omega
    rw [h4]
    have h7 : b ^ h ≤ b ^ k := Nat.pow_le_pow_right (by omega) hlen
    have h8 : c - 1 ≤ b ^ h - 1 := by
      have h9 : c - 1 < b ^ h := by
        rw [hhdef, hDdef]
        exact (Nat.digits_length_le_iff hb1 (c - 1)).mp (le_refl _)
      omega
    omega
  -- the digits of `CL` are digits
  have hCLdig : ∀ d ∈ CL, d < b := by
    intro d hd
    rw [hCLdef, List.mem_append] at hd
    rcases hd with hd | hd
    · rw [List.mem_map] at hd
      obtain ⟨e, _, he⟩ := hd
      omega
    · rw [List.eq_of_mem_replicate hd]
      omega
  -- evaluate
  have hnum : b ^ k - c = Nat.ofDigits b CL := by omega
  rw [hnum, g.eval_ofDigits CL hCLdig, hCLdef, List.map_append, List.sum_append]
  have h1 : (List.replicate (k - h) (b - 1)).map g.w
      = List.replicate (k - h) (g.w (b - 1)) := by
    rw [List.map_replicate]
  rw [h1, List.sum_replicate]
  have h2 : ((D.map (fun d => b - 1 - d)).map g.w).sum
      = ((Nat.digits b (c - 1)).map (fun d => g.w (b - 1 - d))).sum := by
    rw [List.map_map, hDdef]
    rfl
  rw [h2]
  have h3 : (k - h : ℕ) • g.w (b - 1) = ((k - h : ℕ) : ℤ) * g.w (b - 1) := by
    rw [nsmul_eq_mul]
  rw [h3]
  have h4 : ((k - h : ℕ) : ℤ) = (k : ℤ) - (h : ℤ) := by
    omega
  rw [h4, hhdef, hDdef]
  ring

/-- Block additivity: `g(r + b^k·m) = g(r) + g(m)` for `r < b^k`. -/
theorem eval_add_pow_mul : ∀ (k : ℕ) (r m : ℕ), r < b ^ k →
    g.eval (r + b ^ k * m) = g.eval r + g.eval m := by
  intro k
  induction k with
  | zero =>
      intro r m hr
      have h0 : r = 0 := by simpa using hr
      subst h0
      simp
  | succ k ih =>
      intro r m hr
      have hb0 : 0 < b := g.b_pos
      have hd : r % b < b := Nat.mod_lt _ hb0
      have hsplit : r = r % b + b * (r / b) := (Nat.mod_add_div r b).symm
      have hlt : r / b < b ^ k := by
        have h1 : r < b * b ^ k := by
          have : b ^ (k + 1) = b * b ^ k := by rw [pow_succ]; ring
          omega
        exact Nat.div_lt_of_lt_mul (by omega)
      have hgoal : r + b ^ (k + 1) * m = r % b + b * (r / b + b ^ k * m) := by
        have hpow : b ^ (k + 1) = b * b ^ k := by rw [pow_succ]; ring
        have hdist : b * (r / b + b ^ k * m) = b * (r / b) + b * (b ^ k * m) := by
          ring
        have hassoc : b * (b ^ k * m) = (b * b ^ k) * m := by ring
        rw [hdist, hassoc, ← hpow]
        omega
      rw [hgoal, g.eval_add_mul _ _ hd, ih (r / b) m hlt]
      conv_rhs => rw [hsplit, g.eval_add_mul _ _ hd]
      ring

/-- **The affine identity for linear arguments (Proposition 7.8(i), degree
one):** for `u ≥ 1` and `1 ≤ c ≤ b^k`,

`g(u·b^k − c) = k·g(b−1) + (C_{g,c} + g(u−1))`,

which is `Ak + C` with `A = g(b−1)`. -/
theorem eval_linear_blocking {u c k : ℕ} (hu : 1 ≤ u) (hc : 1 ≤ c)
    (hck : c ≤ b ^ k) :
    g.eval (u * b ^ k - c)
      = k * g.w (b - 1)
        + ((((Nat.digits b (c - 1)).map (fun d => g.w (b - 1 - d))).sum
            - (Nat.digits b (c - 1)).length * g.w (b - 1)) + g.eval (u - 1)) := by
  have hb0 : 0 < b := g.b_pos
  have hpow0 : 0 < b ^ k := Nat.one_le_pow k b hb0
  have hsplit : u * b ^ k - c = (b ^ k - c) + b ^ k * (u - 1) := by
    have h1 : u * b ^ k = b ^ k + b ^ k * (u - 1) := by
      have h2 : u = 1 + (u - 1) := by omega
      calc u * b ^ k = (1 + (u - 1)) * b ^ k := by rw [← h2]
        _ = b ^ k + b ^ k * (u - 1) := by ring
    omega
  have hlt : b ^ k - c < b ^ k := by omega
  rw [hsplit, eval_add_pow_mul g k _ _ hlt, eval_pow_sub g hc hck]
  ring

/-! ### The infinitude of prime values along a sparse linear sequence

Theorem 7.5 of the paper couples the affine identity with the prime number
theorem in an arithmetic progression to get the asymptotic count of `k` with
`G(P(ub^k+v))` prime.  The *infinitude* half of that statement needs only
Dirichlet's theorem, which is in Mathlib; we record it in degree one, where
`eval_linear_blocking` supplies the affine identity unconditionally.
-/

/-- The constant `C` of the degree-one affine identity
`g(u·b^k − c) = k·g(b−1) + C` (`eval_linear_blocking`). -/
def blockConst (u c : ℕ) : ℤ :=
  ((((Nat.digits b (c - 1)).map (fun d => g.w (b - 1 - d))).sum
      - (Nat.digits b (c - 1)).length * g.w (b - 1)) + g.eval (u - 1))

/-- `eval_linear_blocking` in the compact form `Ak + C` of the paper. -/
theorem eval_linear_blocking_const {u c k : ℕ} (hu : 1 ≤ u) (hc : 1 ≤ c)
    (hck : c ≤ b ^ k) :
    g.eval (u * b ^ k - c) = (k : ℤ) * g.w (b - 1) + blockConst g u c :=
  eval_linear_blocking g hu hc hck

/-- **Theorem 7.5, the infinitude part, in degree one.**  If the slope
`A = g(b−1)` of the affine identity is positive and coprime to the intercept
`C = blockConst g u c`, then `g(u·b^k − c)` is prime for infinitely many `k`.

Only Dirichlet's theorem on primes in arithmetic progressions enters (the
paper's asymptotic count needs the prime number theorem for progressions,
which is not available at this pin); the affine identity itself is
`eval_linear_blocking`. -/
theorem infinite_prime_linear_blocking {u c : ℕ} (hu : 1 ≤ u) (hc : 1 ≤ c)
    (hA : 0 < g.w (b - 1))
    (hcop : Int.gcd (g.w (b - 1)) (blockConst g u c) = 1) :
    {k : ℕ | ∃ p : ℕ, p.Prime ∧ g.eval (u * b ^ k - c) = (p : ℤ)}.Infinite := by
  obtain ⟨A, hA'⟩ : ∃ t : ℤ, t = g.w (b - 1) := ⟨_, rfl⟩
  obtain ⟨C, hC'⟩ : ∃ t : ℤ, t = blockConst g u c := ⟨_, rfl⟩
  rw [← hA'] at hA
  rw [← hA', ← hC'] at hcop
  -- the modulus of the progression
  obtain ⟨q, hq⟩ : ∃ q : ℕ, (q : ℤ) = A := ⟨A.toNat, Int.toNat_of_nonneg hA.le⟩
  have hq0 : q ≠ 0 := by
    intro h
    rw [h] at hq
    omega
  -- the residue class
  obtain ⟨a, ha⟩ : ∃ a : ℕ, (a : ℤ) = C % A :=
    ⟨(C % A).toNat, Int.toNat_of_nonneg (Int.emod_nonneg _ (ne_of_gt hA))⟩
  have hgcd : Int.gcd A (C % A) = 1 := by
    have hrec : C % A + (C / A) * A = C := by
      rw [Int.emod_def]; ring
    calc Int.gcd A (C % A) = Int.gcd A (C % A + (C / A) * A) :=
          (Int.gcd_add_mul_right_right A (C % A) (C / A)).symm
      _ = Int.gcd A C := by rw [hrec]
      _ = 1 := hcop
  have hcopna : Nat.Coprime a q := by
    have h1 : Nat.gcd A.natAbs (C % A).natAbs = 1 := hgcd
    have h2 : A.natAbs = q := by rw [← hq]; simp
    have h3 : (C % A).natAbs = a := by rw [← ha]; simp
    rw [h2, h3] at h1
    exact Nat.coprime_comm.mp h1
  refine Set.infinite_of_forall_exists_gt fun N => ?_
  obtain ⟨K, hKdef⟩ : ∃ t : ℕ, t = max N c + 1 := ⟨_, rfl⟩
  obtain ⟨p, hpgt, hpp, hpmod⟩ :=
    Nat.forall_exists_prime_gt_and_modEq (A * (K : ℤ) + C).toNat hq0 hcopna
  -- `p ≡ C  (mod A)`
  have hZ : ((p : ℤ)) % ((q : ℕ) : ℤ) = ((a : ℤ)) % ((q : ℕ) : ℤ) := by
    rw [← Int.natCast_mod, ← Int.natCast_mod]
    exact_mod_cast hpmod
  have hdvd : A ∣ ((p : ℤ) - C) := by
    have h1 : ((p : ℤ)) % A = (C % A) % A := by rw [hq] at hZ; rw [hZ, ha]
    have h2 : (C % A) % A = C % A := Int.emod_emod_of_dvd C dvd_rfl
    have h3 : ((p : ℤ)) % A = C % A := by rw [h1, h2]
    exact Int.ModEq.dvd (Int.ModEq.symm h3)
  obtain ⟨k₀, hk₀⟩ := hdvd
  -- `k₀` is large
  have hple : (A * (K : ℤ) + C) ≤ ((A * (K : ℤ) + C).toNat : ℤ) := Int.self_le_toNat _
  have hpgtZ : (((A * (K : ℤ) + C).toNat : ℕ) : ℤ) < (p : ℤ) := by exact_mod_cast hpgt
  have hk₀K : (K : ℤ) < k₀ := by
    have h1 : A * (K : ℤ) + C < (p : ℤ) := by linarith
    have h2 : A * (K : ℤ) < A * k₀ := by
      have : (p : ℤ) = A * k₀ + C := by linarith [hk₀]
      linarith
    exact lt_of_mul_lt_mul_left h2 hA.le
  have hk₀0 : (0 : ℤ) ≤ k₀ := le_of_lt (lt_of_le_of_lt (Int.natCast_nonneg K) hk₀K)
  obtain ⟨k, hk⟩ : ∃ k : ℕ, (k : ℤ) = k₀ := ⟨k₀.toNat, Int.toNat_of_nonneg hk₀0⟩
  have hKk : K < k := by
    rw [← hk] at hk₀K
    exact_mod_cast hk₀K
  have hck : c ≤ b ^ k := by
    have h1 : c < k := by omega
    have h2 : k < b ^ k := Nat.lt_pow_self g.one_lt_b
    omega
  refine ⟨k, ⟨p, hpp, ?_⟩, by omega⟩
  rw [eval_linear_blocking_const g hu hc hck, ← hA', ← hC', hk]
  linarith [hk₀]


end DSS
