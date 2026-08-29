/-
DSS/Cited.lean

**THE AXIOM BASE.**  This file — and only this file — declares axioms.

The verification uses exactly two results from the literature — `hhbr`,
documented further below, and:

* `mmr` — B. Martin, C. Mauduit, J. Rivat, *Propriétés locales des chiffres des
  nombres premiers*, J. Inst. Math. Jussieu **18** (2019), 189–224,
  **Théorème 1**, specialised to `β = 0`.

Everything else in this development is proved inside Lean; the entire squares
half of the paper (Theorem 1.8 and its companions) uses no axiom at all.

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
`countEq g x k` and `piCong g x k` of `DSS/Counting.lean`.  That specialisation
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
* **Real cut-offs.**  `x : ℝ`, matching the source (and needed: the paper
  applies the theorem at real heights, e.g. throughout the partial summation
  of Lemma 5.7, and the peak height `b^{k/μ_g}` of a target `k` is generally
  irrational).
* **`k : ℤ`.**  Values of `g` may be negative when `μ_g = 0`.
* The hypothesis `g ∈ ℱ₊` is `Weight b` together with `Weight.Coprime₁`: the
  structure carries `2 ≤ b` and `g(0) = 0`, `Weight.eval` is the strongly
  `b`-additive extension (`Weight.eval_add_mul`, `Weight.eval_ofDigits`), and
  `Coprime₁` is the `pgcd` condition.  The positivity `σ_g > 0` implicit in the
  displayed formula is *proved*, not assumed (`Weight.sigSq_pos`, Lemma 2.2 of
  the predecessor paper) — which is why `DSS/Weight.lean` sits above this file.
* `d_g ≥ 1` is proved (`Weight.dg_pos`), so the `Int.emod` encoding of the
  congruence in `piCong` is meaningful.
-/
import DSS.Counting

namespace DSS

variable {b : ℕ}

/-- The main term of the local limit theorem, eq. (38):

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

/-- **Martin–Mauduit–Rivat, Théorème 1** (the paper's Theorem 3.1), at `β = 0`.

For `b ≥ 2` and `g` strongly `b`-additive with `gcd(g(1),…,g(b-1)) = 1`, and for
each fixed `ε ∈ (0, 1/2)`, there is a constant `C = C(b, g, ε)` with

`| #{p ≤ x : g(p) = k} - mmrMain g x k | ≤ C · π(x) / (log x)^{1-ε}`

uniformly for real `x > 2` and all `k ∈ ℤ`. -/
axiom mmr {b : ℕ} (g : Weight b) (hg : g.Coprime₁) {ε : ℝ} (hε₀ : 0 < ε) (hε₁ : ε < 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 2 < x → ∀ k : ℤ,
      |(countEq g x k : ℝ) - mmrMain g x k|
        ≤ C * (picount x : ℝ) / (Real.log x) ^ (1 - ε)

/-!
## The second axiom: almost primes in short intervals

* `hhbr` — H. Halberstam, D. R. Heath-Brown, H.-E. Richert, *Almost-primes in
  short intervals*, in: Recent progress in analytic number theory, Vol. 1
  (Durham, 1979), Academic Press, 1981, 69–101.

The result, as quoted by the paper's §4 (proof of Corollary 4.6):

> there are `θ < 1/2` and `c > 0` (`θ = 0.455` is admissible) such that every
> interval `(z − z^θ, z]` with `z` large contains at least `c·z^θ / log z`
> integers that are `P₂`'s,

where a `P₂` is an integer `n ≥ 2` with `Ω(n) ≤ 2`.  The axiom below
transcribes this at the admissible exponent `θ = 0.455`, the form in which
the source states it (their Theorem 2 with `R = 2`).

### Encoding notes

* `IsP2 n` is `2 ≤ n ∧ Ω(n) ≤ 2` with `Ω` the number of prime factors with
  multiplicity, encoded as `n.primeFactorsList.length`.
* The interval count is over the integers `n` with
  `z − z^{0.455} < n ≤ z`, collected in the finite set `p2InInterval z`.
* The quantifier order is as in the source: the constants `c` and the
  threshold `z₀` are absolute, and the estimate is uniform in `z ≥ z₀`.
* The threshold `3 ≤ z₀` is a harmless normalisation (any statement with a
  smaller threshold implies this one), included so that `log z > 1` is
  available on the range.
-/

/-- A `P₂`: an integer `n ≥ 2` with at most two prime factors counted with
multiplicity. -/
def IsP2 (n : ℕ) : Prop := 2 ≤ n ∧ n.primeFactorsList.length ≤ 2

instance (n : ℕ) : Decidable (IsP2 n) := by
  unfold IsP2
  infer_instance

open Classical in
/-- The `P₂`'s in the short interval `(z − z^{0.455}, z]`. -/
noncomputable def p2InInterval (z : ℝ) : Finset ℕ :=
  (Finset.range (⌊z⌋₊ + 1)).filter
    (fun n => IsP2 n ∧ z - z ^ (0.455 : ℝ) < (n : ℝ) ∧ (n : ℝ) ≤ z)

/-- **Halberstam–Heath-Brown–Richert** (Durham 1979 proceedings, Theorem 2
at `R = 2`): every short interval `(z − z^{0.455}, z]` with `z` large contains
`≫ z^{0.455}/log z` almost-primes `P₂`. -/
axiom hhbr : ∃ c z₀ : ℝ, 0 < c ∧ 3 ≤ z₀ ∧ ∀ z : ℝ, z₀ ≤ z →
    c * z ^ (0.455 : ℝ) / Real.log z ≤ ((p2InInterval z).card : ℝ)

end DSS
