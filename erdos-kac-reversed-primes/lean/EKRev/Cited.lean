/-
EKRev/Cited.lean

THE AXIOM BASE of the conditional verification.

This file — and only this file — declares axioms.  Each axiom transcribes a
result quoted from the literature by the paper (or standard background the
paper invokes by name), in the form in which the paper uses it.  Everything
else in this development is proved from these axioms inside Lean.

Axioms:
* `gs_prop3`        — Granville–Soundararajan, "Sieving and the Erdős–Kac
                      theorem", Prop. 3, specialized to `h ≡ 1` (the only case
                      the paper uses: see §2, "We take h ≡ 1").  Quoted as
                      Proposition 2.2.
* `col_thm2`        — S. Col, "Palindromes dans les progressions
                      arithmétiques", Acta Arith. 137 (2009), Thm. 2.
                      Quoted as Theorem 3.1.
* `bsh_thm7`        — W. D. Banks, I. E. Shparlinski, "Prime divisors of
                      palindromes", Period. Math. Hungar. 51 (2005), Thm. 7.
                      Quoted as Theorem 3.2.
* `drs_thm13`       — C. Dartyge, J. Rivat, C. Swaenepoel, "Prime numbers with
                      an almost prime reverse", arXiv:2506.21642, Thm. 1.3.
                      Quoted as Theorem 4.4.
* `brun_titchmarsh` — H. L. Montgomery, R. C. Vaughan, "The large sieve",
                      Mathematika 20 (1973), Thm. 2 (interval form).  Used in
                      Lemma 4.2(ii).
* `pnt`             — the prime number theorem `π(x) ~ x/log x` (standard;
                      used in Lemma 4.2, first part).
* `mertens_regular` — Mertens' second theorem, in the paper's "regularity"
                      form (eq. (1.10)): the set of all primes is regular of
                      density 1 (§1.2, after eq. (1.10)).
* `method_of_moments` — P. Billingsley, "Probability and measure", 3rd ed.,
                      Thm. 30.2 together with the fact that the standard
                      normal law is determined by its moments (ibid., §30);
                      stated for empirical distributions of finite families,
                      which is how the paper applies it (end of proof of
                      Prop. 2.1).

Encoding notes (details in VERIFICATION.md):
* Suprema over real cut-offs `z ≤ x` are encoded by an existentially
  quantified bound function `Bnd` dominating every discrepancy in the range,
  whose sum obeys the stated estimate.  This is equivalent to the quoted
  sum-of-sup statements and is the form in which the sums are consumed.
* `k ≤ σ^{2/3}` is encoded as `k³ ≤ σ²`.
* Residues mod `d` are encoded via `% d`, so the class of `a = d` is `0`;
  real-indexed counting functions are evaluated at integer cut-offs, at which
  all the counts jump.
-/
import Mathlib.Tactic
import EKRev.Defs

namespace EKRev

open Filter

/-- **[GS, Prop. 3] with `h ≡ 1`** (Proposition 2.2 of the paper).
For a finite set `M` of positive integers and a finite set `R` of primes,
with `μ_R = ∑_{ℓ∈R} 1/ℓ`, `σ_R² = ∑_{ℓ∈R} (1/ℓ)(1-1/ℓ)`,
`r_d = #{n ∈ M : d ∣ n} - #M/d`, uniformly for `1 ≤ k ≤ σ_R^{2/3}`:
even `k`:
`∑_{n∈M} (ω_R(n)-μ_R)^k = C_k #M σ_R^k (1 + O(k³/σ_R²)) + O(μ_R^k ∑_{d∈Π_k(R)} |r_d|)`;
odd `k`:
`∑_{n∈M} (ω_R(n)-μ_R)^k ≪ C_k #M σ_R^k k^{3/2}/σ_R + μ_R^k ∑_{d∈Π_k(R)} |r_d|`,
with a single absolute implied constant `K`. -/
axiom gs_prop3 :
  ∃ K : ℝ, 1 ≤ K ∧
    ∀ (M R : Finset ℕ), M.Nonempty → (∀ n ∈ M, 0 < n) → (∀ ℓ ∈ R, ℓ.Prime) →
    ∀ k : ℕ, 1 ≤ k → (k : ℝ) ^ 3 ≤ sigSq R →
      (Even k →
        |∑ n ∈ M, ((omegaR R n : ℝ) - muR R) ^ k
            - Ck k * M.card * sigSq R ^ ((k : ℝ) / 2)|
          ≤ K * (Ck k * M.card * sigSq R ^ ((k : ℝ) / 2) * k ^ 3 / sigSq R
              + muR R ^ k * ∑ d ∈ piProds R k, |rem M d|)) ∧
      (¬ Even k →
        |∑ n ∈ M, ((omegaR R n : ℝ) - muR R) ^ k|
          ≤ K * (Ck k * M.card * sigSq R ^ ((k : ℝ) / 2)
                * (k : ℝ) ^ ((3:ℝ)/2) / sigSq R ^ ((1:ℝ)/2)
              + muR R ^ k * ∑ d ∈ piProds R k, |rem M d|))

/-- **[Col, Thm. 2]** (Theorem 3.1 of the paper).  For every `b ≥ 2` there is
`β = β(b) > 0` such that for all `A > 0`, `0 < η < β`:
`∑_{q < x^{β-η}, (q, b³-b)=1} sup_{z≤x} max_a |#𝒯(z,a,q) - #𝒯(z)/q|
  ≪_{b,A,η} #𝒯(x)/log^A x`  at `x = b^λ`.
The inner `sup`/`max` is encoded by the bound function `Bnd`. -/
axiom col_thm2 :
  ∀ b : ℕ, 2 ≤ b →
    ∃ β : ℝ, 0 < β ∧
      ∀ A η : ℝ, 0 < A → 0 < η → η < β →
        ∃ C : ℝ, 0 ≤ C ∧ ∀ lam : ℕ, 1 ≤ lam →
          ∃ Bnd : ℕ → ℝ,
            (∀ q, 0 ≤ Bnd q) ∧
            (∀ q, 1 ≤ q → Nat.Coprime q (b ^ 3 - b) →
              (q : ℝ) < ((b : ℝ) ^ (lam : ℕ)) ^ (β - η) →
              ∀ z ≤ b ^ lam, ∀ a : ℕ,
                |((palBelowMod b z a q).card : ℝ) - ((palBelow b z).card : ℝ) / q|
                  ≤ Bnd q) ∧
            (∑ q ∈ (Finset.Icc 1 (⌈((b : ℝ) ^ (lam : ℕ)) ^ (β - η)⌉₊)).filter
                (fun q => Nat.Coprime q (b ^ 3 - b)
                  ∧ (q : ℝ) < ((b : ℝ) ^ (lam : ℕ)) ^ (β - η)),
              Bnd q)
              ≤ C * ((palBelow b (b ^ lam)).card : ℝ)
                  / (Real.log ((b : ℝ) ^ (lam : ℕ))) ^ A

/-- **[BSh, Thm. 7]** (Theorem 3.2 of the paper): for every `b ≥ 2`, `ν ≥ 1`,
`d ≥ 1`:  `#{n ∈ 𝒯_ν : d ∣ n} ≪_b #𝒯_ν · d^{-1/2}`. -/
axiom bsh_thm7 :
  ∀ b : ℕ, 2 ≤ b → ∃ C : ℝ, 0 ≤ C ∧
    ∀ ν : ℕ, 1 ≤ ν → ∀ d : ℕ, 1 ≤ d →
      (((palSet b ν).filter fun n => d ∣ n).card : ℝ)
        ≤ C * ((palSet b ν).card : ℝ) / Real.sqrt (d : ℝ)

/-- **[DRS, Thm. 1.3]** (Theorem 4.4 of the paper).  For every `b ≥ 2` there
is `ξ₀ = ξ₀(b) > 0` such that for `0 < ξ < ξ₀` there are `c = c(b,ξ) > 0` and
`λ₀` with, for `λ ≥ λ₀`:
`∑_{d ≤ b^{ξλ}, (d, b(b²-1))=1} sup_{b^{λ-1}≤z≤b^λ} sup_{1≤a≤d}
   |π̄_λ(z,a,d) - π_λ(z)/d| ≪ b^{λ - c√λ}`.
The inner suprema are encoded by the bound function `Bnd`. -/
axiom drs_thm13 :
  ∀ b : ℕ, 2 ≤ b →
    ∃ ξ0 : ℝ, 0 < ξ0 ∧
      ∀ ξ : ℝ, 0 < ξ → ξ < ξ0 →
        ∃ c C : ℝ, 0 < c ∧ 0 ≤ C ∧
          ∃ lam0 : ℕ, ∀ lam : ℕ, lam0 ≤ lam →
            ∃ Bnd : ℕ → ℝ,
              (∀ d, 0 ≤ Bnd d) ∧
              (∀ d, 1 ≤ d → Nat.Coprime d (b * (b ^ 2 - 1)) →
                (d : ℝ) ≤ (b : ℝ) ^ (ξ * (lam : ℝ)) →
                ∀ z, b ^ (lam - 1) ≤ z → z ≤ b ^ lam → ∀ a : ℕ,
                  |((revCount b lam z d a : ℕ) : ℝ) - ((picLam b lam z : ℕ) : ℝ) / d|
                    ≤ Bnd d) ∧
              (∑ d ∈ (Finset.Icc 1 (⌈(b : ℝ) ^ (ξ * (lam : ℝ))⌉₊)).filter
                  (fun d => Nat.Coprime d (b * (b ^ 2 - 1))
                    ∧ (d : ℝ) ≤ (b : ℝ) ^ (ξ * (lam : ℝ))),
                Bnd d)
                ≤ C * (b : ℝ) ^ ((lam : ℝ) - c * Real.sqrt (lam : ℝ))

/-- **Brun–Titchmarsh** [MV, Thm. 2], interval form (used in Lemma 4.2(ii)):
the number of primes in `[x, x+y)` is `≪ y / log y` for `y ≥ 2`. -/
axiom brun_titchmarsh :
  ∃ C : ℝ, 0 ≤ C ∧ ∀ x y : ℕ, 2 ≤ y →
    ((primesIn x (x + y)).card : ℝ) ≤ C * (y : ℝ) / Real.log (y : ℝ)

/-- **The prime number theorem** `π(x) log x / x → 1` (standard background;
used for `π_{λ,i} ∼ b^{λ-1}/((λ-1) log b)` in Lemma 4.2). -/
axiom pnt :
  Tendsto (fun x : ℕ => (pic x : ℝ) * Real.log (x : ℝ) / (x : ℝ)) atTop (nhds 1)

/-- **Mertens' second theorem** in the regularity form (§1.2, after
eq. (1.10)): the set of all primes is regular of density 1. -/
axiom mertens_regular : IsRegular {p : ℕ | p.Prime} 1

/-- **The method of moments** [Bil, Thm. 30.2], together with the fact that
the standard normal law is determined by its moments, for empirical
distributions of finite families (end of proof of Prop. 2.1): if all moments
of `f_λ` over `B_λ` converge to the standard normal moments, then the
empirical distribution functions converge to `Φ` pointwise. -/
axiom method_of_moments :
  ∀ (B : ℕ → Finset ℕ) (f : ℕ → ℕ → ℝ),
    (∀ᶠ lam in atTop, (B lam).Nonempty) →
    (∀ k : ℕ, Tendsto (fun lam => avg (B lam) (fun n => f lam n ^ k))
      atTop (nhds (normalMoment k))) →
    ∀ t : ℝ, Tendsto (fun lam => edf (B lam) (f lam) t) atTop (nhds (Phi t))

end EKRev
