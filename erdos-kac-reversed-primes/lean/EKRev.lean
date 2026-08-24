/-
EKRev: a conditional Lean verification of
"An Erdős–Kac law for palindromes and for reversed primes".

Module structure (in dependency order):

* `EKRev.Digits`      — base-`b` digits, the reversal `R_λ`, Lemma 4.1
* `EKRev.PalCount`    — palindromes, `#𝒯_λ`, eq. (3.1)
* `EKRev.PrimeBlocks` — `𝒫_λ`, `𝒫_{λ,i}`, `𝒜_{λ,i}`, `π̄_λ(z,a,d)`, eq. (4.2)
* `EKRev.OmegaS`      — `ω`, `Ω`, `ω_S`, `Ω_S`, the prime-power identity
* `EKRev.Phi`         — the standard normal distribution function `Φ`
* `EKRev.Defs`        — `L`, `C_k`, `r_d`, `𝒟(ℰ)`, regular sets, `𝒬`
* `EKRev.Cited`       — THE AXIOM BASE: the results quoted from the
                        literature (see the file for the exact inventory)
* `EKRev.Sums`        — elementary sum estimates
* `EKRev.CritSetup`   — hypotheses of Prop. 2.1; Lemma 2.3
* `EKRev.CritMoments` — the moment computation (Prop. 2.2 applied to `𝒬`)
* `EKRev.Criterion`   — Prop. 2.1: moments ⇒ Erdős–Kac, `ω_S` and `Ω_S`,
                        pointwise and uniformly in `t`
* `EKRev.PalHyp`      — Lemma 3.3(ii) for palindromes (Col + the sieve set-up)
* `EKRev.PalOmega`    — Lemma 3.3(iii) for palindromes (Banks–Shparlinski)
* `EKRev.RevHyp`      — Lemmas 4.2 and 4.4' for reversed primes (PNT, DRS)
* `EKRev.RevOmega`    — Lemma 4.5 for reversed primes
* `EKRev.Main`        — Theorems 1.1, 1.2, 1.5 (fixed order), Cor. 1.3, 1.6
-/
import EKRev.Digits
import EKRev.PalCount
import EKRev.PrimeBlocks
import EKRev.OmegaS
import EKRev.Phi
import EKRev.Defs
import EKRev.Cited
import EKRev.Sums
import EKRev.CritSetup
import EKRev.CritMoments
import EKRev.Criterion
import EKRev.PalHyp
import EKRev.PalOmega
import EKRev.RevHyp
import EKRev.RevOmega
import EKRev.Main
import EKRev.Sanity
