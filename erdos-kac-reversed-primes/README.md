# EKRev — a conditional Lean verification of "An Erdős–Kac law for palindromes and for reversed primes"

This repository accompanies the paper *An Erdős–Kac law for palindromes
and for reversed primes*. It contains a Lean 4 formalisation in which

* the results the paper **quotes from the literature** are stated as
  axioms — all of them in the single file [`lean/EKRev/Cited.lean`](lean/EKRev/Cited.lean),
  with documentation of the source and encoding of each; and
* **every argument the paper itself makes** — the Erdős–Kac criterion
  (Prop. 2.1 with Lemma 2.3 and the moment computation), the palindrome
  hypotheses (Lemma 3.3), the reversed-prime hypotheses (Lemmas 4.1, 4.2,
  4.4, 4.5) and the deductions of Theorems 1.1, 1.2, the fixed-order
  moments of Theorem 1.5 and Corollaries 1.3 and 1.6 — is proved in Lean
  from those axioms, with **no `sorry`**.

The Lean kernel therefore certifies:
*if the eight quoted literature results hold as transcribed, then the
paper's theorems hold.*

The paper itself is included as
[`paper_anonymous.pdf`](paper_anonymous.pdf) (with LaTeX source), so that
every claim checked here can be read against its primary source.

See [`VERIFICATION.md`](VERIFICATION.md) for the full paper↔Lean
correspondence, the encoding conventions, a cross-check of the axioms
against the original literature (Granville–Soundararajan and
Dartyge–Rivat–Swaenepoel verified against the originals;
Banks–Shparlinski corroborated via an independent secondary quotation;
Col's theorem not independently accessible), the two places where the
formal proof deviates from the paper's (equivalent) argument, and an
honest list of what is *not* machine-checked (most notably: the
uniform-in-`k` range of Theorem 1.5 is formalised only at each fixed
order `k` — which is all that Theorems 1.1 and 1.2 use).

## Headline statements

All in [`lean/EKRev/Main.lean`](lean/EKRev/Main.lean) (`F_λ(t) → Φ(t)` below means
convergence of the empirical distribution function to the standard normal
law, available both pointwise and uniformly in `t`):

| Lean name | Statement |
|---|---|
| `pal_EK_omega`, `pal_EK_Omega` | Theorem 1.1: E–K law for `ω`, `Ω` on base-`b` palindromes `𝒯_λ` |
| `rev_EK_omega_loc`, `rev_EK_Omega_loc` | Theorem 1.2, localised: E–K law for `ω(R_λ(p))`, `Ω(R_λ(p))` over `p ∈ 𝒫_{λ,i}` |
| `rev_EK_omega`, `rev_EK_Omega` | Theorem 1.2, unlocalised: the same over all of `𝒫_λ` |
| `pal_moments`, `rev_moments_loc` | Theorem 1.5 at each fixed moment order |
| `pal_normal_order_*`, `rev_normal_order_*` | Corollary 1.3: `ω`, `Ω` have normal order `log log n` on both families |
| `*_omegaS*`, `*_OmegaS*` | Corollary 1.6: all of the above for `ω_S`, `Ω_S` with an arbitrary regular set `S` of primes |

## Checking it yourself

Requires [`elan`](https://github.com/leanprover/elan) (the Lean toolchain
manager); the pinned toolchain (`lean-toolchain`: Lean 4 `v4.33.0`) and
Mathlib version (`lake-manifest.json`) are downloaded automatically.

```sh
cd lean
lake exe cache get              # fetch the Mathlib binary cache (recommended)
lake build                      # builds all 17 modules; expect "Build completed successfully"
lake env lean AxiomAudit.lean   # prints the axiom closure of every main theorem
```

The expected audit output is recorded in
[`lean/axiom_audit.txt`](lean/axiom_audit.txt): every theorem depends only on
Lean's built-in axioms (`propext`, `Classical.choice`, `Quot.sound`) and
the declared axioms of `Cited.lean` — and the axiom set of each theorem
matches the paper's citation structure (e.g. Brun–Titchmarsh enters only
the `Ω`-statements for reversed primes, exactly as in the paper).

`lean/EKRev/Sanity.lean` additionally contains compile-time `#guard` checks of
the combinatorial definitions on concrete numbers (e.g. `R₃(149) = 941`,
`#𝒯₃ = 90` in base 10).

## Layout

```
lean/
  EKRev.lean        root module
  lakefile.toml, lean-toolchain, lake-manifest.json   (pinned build config)
  AxiomAudit.lean   #print axioms driver
  axiom_audit.txt   its expected output
  EKRev/
  Digits.lean       base-b digits, the reversal R_λ, Lemma 4.1
  PalCount.lean     palindromes; #𝒯_λ; eq. (3.1)
  PrimeBlocks.lean  𝒫_λ, 𝒫_{λ,i}, 𝒜_{λ,i}, π̄_λ(z,a,d); eq. (4.2)
  OmegaS.lean       ω, Ω, ω_S, Ω_S; Ω−ω = Σ_{m≥2} #{ℓ^m ∣ ·}
  Phi.lean          the normal distribution function Φ
  Defs.lean         L, C_k, r_d, 𝒟(ℰ), regular sets
  Cited.lean        THE AXIOM BASE (the only file with axioms)
  Sums.lean         elementary sum estimates
  CritSetup.lean    Lemma 2.3
  CritMoments.lean  the moment computation (Prop. 2.2 applied to 𝒬)
  Criterion.lean    Prop. 2.1 (incl. uniformity in t)
  PalHyp.lean       Lemma 3.3(ii)
  PalOmega.lean     Lemma 3.3(iii)
  RevHyp.lean       Lemmas 4.2, 4.4
  RevOmega.lean     Lemma 4.5
  Main.lean         Theorems 1.1, 1.2, 1.5 (fixed k), Cor. 1.3, 1.6
    Sanity.lean     executable #guard checks
paper_anonymous.pdf the manuscript (anonymised), with paper_anonymous.tex
VERIFICATION.md     the detailed verification report
```
