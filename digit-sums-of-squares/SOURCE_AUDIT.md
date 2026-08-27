# Source audit of the axioms `DSS.mmr` and `DSS.hhbr`

Everything conditional in this development — Corollary 1.3 and its two
instances, and nothing else — rests on the two axioms declared in
[`DSS/Cited.lean`](lean/DSS/Cited.lean).  Their value is exactly the fidelity
of the transcriptions.  This file records how each was checked.

The unconditional majority of the development, including the whole of
Theorem 1.10, does not depend on either axiom; the build-time guard
`DSS/Guard.lean` enforces this.

## 1. `DSS.mmr` (Martin–Mauduit–Rivat)

> B. Martin, C. Mauduit, J. Rivat, *Propriétés locales des chiffres des
> nombres premiers*, J. Inst. Math. Jussieu **18** (2019), 189–224,
> **Théorème 1**, specialised to `β = 0`.

**The axiom is identical, character for character apart from the namespace,
to the axiom `DigSq.mmr` of the predecessor repository**
([`prime-values-digital-functions`](../prime-values-digital-functions/)):
the statement, the auxiliary definition `mmrMain`, the verbatim source
quotation and all encoding notes were carried over unchanged, and only the
file's introductory comment differs.  The predecessor's
[`SOURCE_AUDIT.md`](../prime-values-digital-functions/SOURCE_AUDIT.md)
records the line-by-line comparison with Théorème 1 of the authors' preprint
(every hypothesis, every constant and the quantifier order match; the only
difference is the specialisation `β = 0`, a weakening), three independent
cross-checks on the main-term constant, and a numerical validation to `10⁸`.
That audit applies verbatim here and is not repeated.

Its residual caveats also carry over: the comparison was against the authors'
preprint rather than the paywalled published text, and the source was read by
a model rather than by a human eye.

What this paper consumes from `mmr` is again modest: one instance at
`ε = 1/4` and `d_g = 1`, at the `≍ √L` targets of the window — the same
consumption pattern (`π_k = π` exactly, `π(x)` cancelling between main and
error term) documented in the predecessor.

## 2. `DSS.hhbr` (Halberstam–Heath-Brown–Richert)

> H. Halberstam, D. R. Heath-Brown, H.-E. Richert, *Almost-primes in short
> intervals*, in: Recent progress in analytic number theory, Vol. 1
> (Durham, 1979), Academic Press, London–New York, 1981, 69–101.

### What the paper quotes

The accompanying paper (§3, proof of Corollary 1.3) uses the result in the
form:

> By the theorem of Halberstam, Heath-Brown and Richert, there are `θ < 1/2`
> and `c > 0` (`θ = 0.455` is admissible) such that every interval
> `(z − z^θ, z]` with `z` large contains at least `c·z^θ/log z` integers
> that are `P₂`'s.

### The transcription

```lean
axiom hhbr : ∃ c z₀ : ℝ, 0 < c ∧ 3 ≤ z₀ ∧ ∀ z : ℝ, z₀ ≤ z →
    c * z ^ (0.455 : ℝ) / Real.log z ≤ ((p2InInterval z).card : ℝ)
```

with `p2InInterval z` the set of integers `n` with `z − z^{0.455} < n ≤ z`
that are `P₂` (`IsP2 n := 2 ≤ n ∧ Ω(n) ≤ 2`, `Ω` counted with multiplicity
via `n.primeFactorsList.length`).

Point by point:

| Source clause | Transcription | Verdict |
|---|---|---|
| `P₂` = at most two prime factors with multiplicity, `n ≥ 2` | `IsP2` | ✅ |
| the interval `(z − z^θ, z]` | strict lower, weak upper bound in `p2InInterval` | ✅ |
| `θ = 0.455` admissible | the axiom is stated at exactly `0.455` — the *weakest* faithful choice, since the paper needs only some `θ < 1/2` | ✅ |
| absolute constants, uniform in large `z` | `∃ c z₀, … ∀ z ≥ z₀` — constants first, then uniformity | ✅ |
| `z` large | `z₀` with the harmless normalisation `3 ≤ z₀` (any statement with a smaller threshold implies this one) | ✅ |

### Accessibility caveat, and the corroboration

The Durham proceedings volume was **not independently accessible** at audit
time; the transcription is of the statement as quoted by the accompanying
paper.  Two independent corroborations:

1. J. Wu, *Almost primes in short intervals*, Sci. China Math. **53** (2010),
   2511–2524, states the Halberstam–Heath-Brown–Richert result in the same
   form — `(x − x^θ, x]` contains `≫ x^θ/log x` integers `P₂` for
   `θ = 0.455` — as the benchmark its own `θ = 101/232` improves.  Any
   subsequent admissible exponent below `0.455` (Wu's included) *implies* the
   axiom as stated with a different constant, so the transcription is robust
   to the exact provenance of the exponent.
2. `validation/check_numerics.py` counts the `P₂`'s in `(z − z^{0.455}, z]`
   at `z = 10⁶, 10⁷, 5·10⁷`: 141, 375 and 721, i.e. about `4·z^{0.455}/log z`
   — the shape the axiom asserts, with room to spare.  This does not prove
   the axiom; it is the evidence that it was not mis-transcribed into
   something false or vacuous.

A reader who wants full confidence should compare the axiom once against the
proceedings text (their Theorem 2 with `R = 2`) before citing the conditional
results anywhere that matters; the unconditional results are unaffected.

## 3. What the axioms do *not* say

Neither axiom smuggles in the conclusion:

* `mmr` speaks only of the number of primes with `g(p) = k` for a *single*
  `k`; it says nothing about almost-primes, and nothing about more than one
  target at a time.
* `hhbr` speaks only of integers in short intervals; it knows nothing about
  digits or primes `p` with constrained `g(p)`.

Corollary 1.3 arises exactly by the paper's argument: `hhbr` manufactures
`≫ √L/log L` distinct `P₂` targets in the Gaussian window, and `mmr` counts
the primes hitting each.  The proof in `DSS/P2.lean` consumes nothing else,
as the axiom guard certifies.
