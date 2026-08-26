/-
DigSq — a conditional Lean verification of
"Prime values of digital functions along the primes".

Module structure (in dependency order):

* `DigSq.Imports`   — the single place Mathlib is imported
* `DigSq.Weight`    — digit weights, `g(n)`, `μ_g`, `σ_g²`, `d_g`; Lemma 2.2
* `DigSq.Examples`  — the power weights, `S`, `μ_S = 57/2`, `d_S = 1`
* `DigSq.Counting`  — `π(x)`, `#{p ≤ x : g(p) = k}`, `π_k(x)` at real cut-offs
* `DigSq.Analytic`  — the elementary inequality `B√L < A·L^{3/4}`
* `DigSq.Cited`     — THE AXIOM BASE (Martin–Mauduit–Rivat)
* `DigSq.Main`      — Theorem 1.1 for `d_g = 1`; `A052034_infinite`
* `DigSq.Sharp`     — §6.2: the sharpness of "sufficiently large"
* `DigSq.Happy`     — §6.3: the happy-number theorem; no prime has all its
                      `S`-iterates prime
* `DigSq.Guard`     — build-time assertions on the axiom closure of each result
* `DigSq.Sanity`    — executable `#guard` checks
-/
import DigSq.Imports
import DigSq.Weight
import DigSq.Examples
import DigSq.Counting
import DigSq.Analytic
import DigSq.Cited
import DigSq.Main
import DigSq.Sharp
import DigSq.Happy
import DigSq.Guard
import DigSq.Sanity
