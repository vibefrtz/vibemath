# Source audit of the axiom `DigSq.mmr`

The whole of Phase 2 of this development — including `A052034_infinite` — is
conditional on one axiom, `DigSq.mmr` in
[`DigSq/Cited.lean`](lean/DigSq/Cited.lean). Its value is exactly the fidelity of
that transcription. This file records the comparison against the source.

**Verdict: the transcription is faithful.** Every hypothesis, every constant and
the quantifier order match the source. No change to the axiom was required. The
only difference between the axiom and the source theorem is the specialisation
`β = 0`, which is documented below and is exactly what the accompanying paper
quotes as its Theorem 2.1.

## 1. The source

> B. Martin, C. Mauduit, J. Rivat, *Propriétés locales des chiffres des nombres
> premiers*, Journal of the Institute of Mathematics of Jussieu **18** (2019),
> 189–224. **Théorème 1.**

Consulted: the authors' preprint,
`https://www-lmpa.univ-littoral.fr/~martin/mmrp3-v7.pdf`, hosted on Bruno
Martin's page at LMPA, Université du Littoral Côte d'Opale.

### Théorème 1, verbatim

> Soit `ε ∈ ]0, 1/2[`, `g ∈ ℱ₊`. Pour tous `x > 2`, `β ∈ ℝ`, `k ∈ ℤ`, on a
>
> ```
> ∑           e(βp)  =  ────────d_g────────  ·  (  ∑              e(βp)  )
>  p≤x                  √(2π σ²_g log_b x)          p≤x
>  g(p)=k                                          g(1)p≡k mod d_g
>
>                          ⎛     (k − μ_g log_b x)²  ⎞      ⎛  π(x)      ⎞
>                    · exp ⎜ − ───────────────────── ⎟  + O ⎜ ────────── ⎟
>                          ⎝     2 σ²_g log_b x      ⎠      ⎝ (log x)^{1−ε} ⎠
> ```
>
> la constante implicite ne dépendant que de `ε`, `b` et `g`.

### Standing conventions (§1.1 of the source)

* `b` is an integer `≥ 2`, fixed throughout the paper.
* `g` is *fortement `b`-additive*: `g(0) = 0` and, for `n ≥ 1`,
  `g(∑_{j≥0} ε_j(n) b^j) = ∑_{j≥0} g(ε_j(n))`, where `ε_j(n)` is the `j`-th
  base-`b` digit of `n`.
* `ℱ₊` is the set of `g : ℕ → ℤ` fortement `b`-additives satisfying
  `pgcd(g(1), …, g(b−1)) = 1`. **Nothing further** — `σ_g > 0`, non-constancy,
  positivity of `μ_g` are *not* part of the definition.
* `μ_g = (1/b) ∑_{a=0}^{b−1} g(a)`, `σ²_g = (1/b) ∑_{a=0}^{b−1} (g(a) − μ_g)²`.
* `d_g = pgcd(g(2) − 2g(1), …, g(b−1) − (b−1)g(1), b−1)`.
* `e(t) = e^{2iπt}`; `π(x)` is the number of primes not exceeding `x`; `log_b`
  is the logarithm to base `b`; `log` is the natural logarithm.
* The theorem imposes **no restriction on `k`**. Remarque 1 of the source only
  observes that it is of interest when `(k, d_g) = 1`.

## 2. Line-by-line comparison

| Théorème 1 | `DigSq` | Verdict |
|---|---|---|
| `b ∈ ℕ`, `b ≥ 2`, fixed | `Weight.hb : 2 ≤ b`, `b` a parameter of `Weight b` | ✅ |
| `g : ℕ → ℤ` | `Weight.w : ℕ → ℤ` | ✅ |
| `g(0) = 0` | `Weight.w_zero` | ✅ |
| `g(∑ ε_j b^j) = ∑ g(ε_j)` | `Weight.eval` (via `Nat.digits`), with the property proved as `Weight.eval_add_mul` and `Weight.eval_ofDigits` | ✅ |
| `pgcd(g(1), …, g(b−1)) = 1` | `Weight.Coprime₁` = `(Finset.Ico 1 b).gcd (fun a => (w a).natAbs) = 1` | ✅ |
| nothing further in `ℱ₊` | no further hypothesis on the axiom | ✅ |
| `μ_g = (1/b) ∑_{a<b} g(a)` | `Weight.mu` | ✅ |
| `σ²_g = (1/b) ∑_{a<b} (g(a) − μ_g)²` | `Weight.sigSq` | ✅ |
| `d_g = pgcd(g(2)−2g(1), …, g(b−1)−(b−1)g(1), b−1)` | `Weight.dg = Nat.gcd (b−1) ((range b).gcd fun a => (w a − a·w 1).natAbs)` | ✅ — the extra terms `a = 0, 1` contribute `\|0\| = 0`, and `Nat.gcd n 0 = n` |
| `ε ∈ ]0, 1/2[` | `hε₀ : 0 < ε`, `hε₁ : ε < 1/2` | ✅ |
| `∀ x > 2`, `x` real | `∀ x : ℝ, 2 < x` | ✅ |
| `∀ k ∈ ℤ`, unrestricted | `∀ k : ℤ` | ✅ |
| `∀ β ∈ ℝ` | specialised to `β = 0` | ⚠ see §3 |
| LHS `∑_{p≤x, g(p)=k} e(βp)` | `countEq g x k` | ✅ at `β = 0` |
| inner sum `∑_{p≤x, g(1)p≡k (d_g)} e(βp)` | `piCong g x k` | ✅ at `β = 0` |
| prefactor `d_g / √(2π σ²_g log_b x)` | `(g.dg : ℝ) * (piCong …) / Real.sqrt (2 * π * g.sigSq * Real.logb b x)` | ✅ — `2π σ²_g log_b x` **under one root, in the denominator** |
| `exp(−(k − μ_g log_b x)² / (2 σ²_g log_b x))` | `Real.exp (-(((k:ℝ) − g.mu * logb b x)^2) / (2 * g.sigSq * logb b x))` | ✅ |
| error `O(π(x) / (log x)^{1−ε})` | `≤ C * (picount x : ℝ) / (Real.log x) ^ (1 − ε)` | ✅ — natural `log`, `rpow` exponent |
| "la constante implicite ne dépendant que de `ε`, `b` et `g`" | `∀ ε, ∃ C, ∀ x, ∀ k`, with `b` and `g` bound in the axiom's signature ahead of `C` | ✅ **the crux** |

## 3. The one deliberate difference: `β = 0`

Théorème 1 carries a factor `e(βp) = e^{2iπβp}` on both sides, uniformly in real
`β`; the axiom takes `β = 0`, where `e(0·p) = 1` and both sums collapse to
cardinalities. This is a *weakening*: the axiom is a consequence of Théorème 1,
not a restatement of it. It is also exactly what the accompanying paper quotes
as its Theorem 2.1, and exactly what the paper's proofs use — the authors
themselves draw only the equidistribution consequence from the `β ≠ 0` case.

Formalising the general `β` would require complex exponentials and a
`Finset.sum` over primes valued in `ℂ`, for no gain: nothing downstream consumes
it.

## 4. How little of the axiom is actually used

Worth knowing for a reader who is prepared to believe some instances of
Théorème 1 more readily than others. The entire development consumes the axiom
at exactly one place, in `exists_prime_eval_eq_of_dg_one`, and only at:

* `β = 0`;
* `ε = 1/4`, so the error exponent is `(log x)^{3/4}`;
* `d_g = 1`, where the congruence is vacuous and `π_k(x) = π(x)` exactly
  (`piCong_of_dg_eq_one`);
* `x = b^{k/μ_g}`, the peak, where `μ_g log_b x = k` and the Gaussian factor is
  exactly `1`.

At that point both the main term and the error term are multiples of `π(x)`,
which cancels. So the only content drawn from Théorème 1 is:

> at the peak, `#{p ≤ x : g(p) = k}` differs from `π(x)/√(2π σ²_g log_b x)` by
> at most `C π(x)/(log x)^{3/4}`.

A reader who grants that much gets `A052034_infinite`, Corollaries 1.4 and 1.5,
and everything else in Phase 2.

## 5. Independent cross-checks on the prefactor

The prefactor is the one place where a transcription slip would be both easy and
fatal, so it was checked three ways.

1. **The source, read twice.** A first pass returned the prefactor garbled as
   `d_g √(2π σ²_g / log_b x)`. A second, targeted pass asking explicitly what
   lies inside the root and on which side of the fraction bar returned
   `d_g / √(2π σ²_g log_b x)`. The two differ by a factor `2π σ²_g`; items 2 and
   3 decide between them.
2. **The `g = s_b` specialisation.** For the digit sum, `d_{s_b} = b − 1` and
   `σ²_{s_b} = (b²−1)/12`, and the source's own examples section gives the
   coefficient `(b−1)/√(2π (b²−1) log_b x / 12)`. Substituting
   `π_k(x) ∼ π(x)/φ(b−1)` returns eq. (1) of the accompanying paper — the
   Drmota–Mauduit–Rivat theorem, with the constant `(b−1)/φ(b−1)` — which is
   also stated independently in B. Martin's habilitation thesis with
   `2π σ²_q log_q N` under a single root in the denominator. Consistent with the
   second reading, not the first.
3. **A sieve to `10^8`.** `validation/check_numerics.py` sums the main term over
   all `k` for `g = S`, `b = 10`, `d_S = 1`. With the prefactor
   `d_g/√(2π σ²_g log_b x)` the total matches `π(x)` to 0.46%, 0.24% and 0.13%
   at `x = 10^6, 10^7, 10^8` — as it must, since summing the Gaussian over `k`
   recovers `√(2π σ²_g log_b x)`. With the first reading it would be off by a
   factor `2π σ²_S ≈ 4530`. The largest pointwise discrepancy also sits a factor
   of about 70 inside the error term the axiom permits.

Items 2 and 3 agree with the second reading, which is what `Cited.lean` encodes.

## 6. Residual caveats

Stated plainly, because they are what a referee would ask.

1. **Preprint, not the published version.** The comparison is against the
   authors' preprint `mmrp3-v7.pdf`, not the Cambridge-published J. Inst. Math.
   Jussieu text, which is paywalled. Version 7 should be the accepted
   manuscript, but this has not been confirmed against the journal.
2. **Machine-assisted reading.** The source PDF was read by a model, not by a
   human eye on the printed page. §5 exists because the first such reading was
   wrong. The three cross-checks make a surviving error unlikely — a wrong
   prefactor would break the mass check in §5.3, a wrong exponent would break
   the error-term check — but a human should still read Théorème 1 once against
   `Cited.lean` before the repository is cited anywhere that matters.
3. **`σ_g > 0` is not in `ℱ₊`.** The source's displayed formula divides by
   `√(2π σ²_g log_b x)`, which requires `σ_g > 0`; that is not part of the
   definition of `ℱ₊` but follows from `pgcd(g(1), …, g(b−1)) = 1`, and is
   proved here as `Weight.sigSq_pos` (Lemma 2.2 of the accompanying paper)
   rather than assumed. The axiom is therefore stated exactly as strongly as the
   source, with no hidden extra hypothesis.
4. **Consistency is not proved and cannot be.** An axiom cannot be shown
   consistent from inside Lean. What §5 establishes is that the axiom is not
   vacuous and not obviously false at accessible heights.

## 7. Effect on `VERIFICATION.md`

Item 1 of the "not machine-checked" inventory in `VERIFICATION.md` previously
read *"it has not yet been checked line-by-line against the 2019 original"*.
That is now done, with the caveats of §6.
