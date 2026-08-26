/-
DigSq/Cited.lean

**THE AXIOM BASE.**  This file — and only this file — declares axioms.

Phases 1 and 2 of the verification need exactly one result from the literature:

* `mmr` — B. Martin, C. Mauduit, J. Rivat, *Propriétés locales des chiffres des
  nombres premiers*, J. Inst. Math. Jussieu **18** (2019), 189–224,
  **Théorème 1**, specialised to `β = 0`.

Everything else in this development is proved from it inside Lean.

## The source statement

Théorème 1 of the authors' preprint reads, verbatim:

> Soit `ε ∈ ]0, 1/2[`, `g ∈ ℱ₊`.  Pour tous `x > 2`, `β ∈ ℝ`, `k ∈ ℤ`, on a
>
> `∑_{p ≤ x, g(p) = k} e(βp)`
>   `= d_g / √(2π σ²_g log_b x) · ( ∑_{p ≤ x, g(1)p ≡ k mod d_g} e(βp) )`
>       `· exp( −(k − μ_g log_b x)² / (2 σ²_g log_b x) )`
>   `+ O( π(x) / (log x)^{1−ε} )`,
>
> la constante implicite ne dépendant que de `ε`, `b` et `g`.

with the standing conventions of §1.1 of that paper:

* `b` is an integer `≥ 2`, fixed throughout;
* `g` is *fortement `b`-additive*: `g(0) = 0` and
  `g(∑_j ε_j(n) b^j) = ∑_j g(ε_j(n))`;
* `ℱ₊` is the set of `g : ℕ → ℤ` fortement `b`-additives satisfying
  `pgcd(g(1), …, g(b−1)) = 1` — **and nothing further**: `σ_g > 0`,
  non-constancy and so on are *not* part of the definition;
* `μ_g = (1/b) ∑_{a=0}^{b−1} g(a)`, `σ²_g = (1/b) ∑_{a=0}^{b−1} (g(a) − μ_g)²`;
* `d_g = pgcd(g(2) − 2g(1), …, g(b−1) − (b−1)g(1), b−1)`;
* `e(t) = e^{2iπt}`, `π(x)` is the number of primes `≤ x`, `log_b` is the
  logarithm to base `b`, and `log` is the natural logarithm;
* the theorem places **no restriction on `k`** (Remarque 1 only observes that it
  is of interest when `(k, d_g) = 1`).

Taking `β = 0` makes `e(βp) = 1`, so both sums become the cardinalities
`countEq g x k` and `piCong g x k` of `DigSq/Counting.lean`.  That specialisation
is the whole of the difference between the axiom below and Théorème 1.

See `SOURCE_AUDIT.md` for the line-by-line comparison, the independent
cross-checks, and the residual caveats.

## Encoding notes

* **Quantifier order.**  The source fixes `ε` and `g` first and is then uniform
  in `x > 2`, `β` and `k`, with the implied constant depending only on `ε`, `b`
  and `g`.  That is exactly `∀ ε, ∃ C, ∀ x, ∀ k` below.  Writing `∀ x, ∃ C`
  would make the axiom vacuous; writing `∃ C, ∀ ε` would make it strictly
  stronger than the quoted theorem.  This single line is the crux of the whole
  development.
* **Real cut-offs.**  `x : ℝ`, matching the source (and needed, since the
  `x_k = b^{k/μ_g}` of the paper's §3 is irrational).
* **`k : ℤ`.**  Values of `g` may be negative when `μ_g = 0`.
* The hypothesis `g ∈ ℱ₊` is `Weight b` together with `Weight.Coprime₁`: the
  structure carries `2 ≤ b` and `g(0) = 0`, `Weight.eval` is the strongly
  `b`-additive extension (`Weight.eval_add_mul`, `Weight.eval_ofDigits`), and
  `Coprime₁` is the `pgcd` condition.  The positivity `σ_g > 0` implicit in the
  displayed formula is *proved*, not assumed (`Weight.sigSq_pos`, Lemma 2.2 of
  the paper) — which is why `DigSq/Weight.lean` sits above this file.
* `d_g ≥ 1` is proved (`Weight.dg_pos`), so the `Int.emod` encoding of the
  congruence in `piCong` is meaningful.
-/
import DigSq.Counting

namespace DigSq

variable {b : ℕ}

/-- The main term of the local limit theorem, eq. (5):

`d_g · π_k(x) / √(2π σ_g² log_b x) · exp(-(k - μ_g log_b x)² / (2 σ_g² log_b x))`. -/
noncomputable def mmrMain (g : Weight b) (x : ℝ) (k : ℤ) : ℝ :=
  (g.dg : ℝ) * (piCong g x k : ℝ)
      / Real.sqrt (2 * Real.pi * g.sigSq * Real.logb (b : ℝ) x)
    * Real.exp (-(((k : ℝ) - g.mu * Real.logb (b : ℝ) x) ^ 2)
                  / (2 * g.sigSq * Real.logb (b : ℝ) x))

lemma mmrMain_def (g : Weight b) (x : ℝ) (k : ℤ) :
    mmrMain g x k =
      (g.dg : ℝ) * (piCong g x k : ℝ)
          / Real.sqrt (2 * Real.pi * g.sigSq * Real.logb (b : ℝ) x)
        * Real.exp (-(((k : ℝ) - g.mu * Real.logb (b : ℝ) x) ^ 2)
                      / (2 * g.sigSq * Real.logb (b : ℝ) x)) := rfl

/-- **Martin–Mauduit–Rivat, Théorème 1** (the paper's Theorem 2.1), at `β = 0`.

For `b ≥ 2` and `g` strongly `b`-additive with `gcd(g(1),…,g(b-1)) = 1`, and for
each fixed `ε ∈ (0, 1/2)`, there is a constant `C = C(b, g, ε)` with

`| #{p ≤ x : g(p) = k} - mmrMain g x k | ≤ C · π(x) / (log x)^{1-ε}`

uniformly for real `x > 2` and all `k ∈ ℤ`. -/
axiom mmr {b : ℕ} (g : Weight b) (hg : g.Coprime₁) {ε : ℝ} (hε₀ : 0 < ε) (hε₁ : ε < 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 2 < x → ∀ k : ℤ,
      |(countEq g x k : ℝ) - mmrMain g x k|
        ≤ C * (picount x : ℝ) / (Real.log x) ^ (1 - ε)

end DigSq
