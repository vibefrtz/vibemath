# DSS — a Lean verification of *Local limits along squares and prime values of digital functions*

This folder accompanies the paper *Local limits along squares and prime values
of digital functions*
([`paper_anonymous.pdf`](paper_anonymous.pdf), source in
[`paper_anonymous.tex`](paper_anonymous.tex)), the sequel to
[*Prime values of digital functions along the primes*](../prime-values-digital-functions/).
It contains a Lean 4 formalisation in which

* **the prescribed-digit-sum theorem — Theorem 1.8, its corollaries, and
  every lemma feeding them — is machine-checked with no axioms at all** beyond
  Lean's three built-in ones.  In particular the theorem of Bose and Chowla on
  dense Sidon sets, which the paper quotes from the literature, is *proved*
  inside Lean (in the field with `p²` elements, via
  [`DSS/BoseChowla.lean`](lean/DSS/BoseChowla.lean)) rather than assumed;
* **the engine of the paper's new square local limit theorem is
  machine-checked**: the two-digit spectral gap (Lemma 2.4) is proved **in
  full, in every base `b ≥ 2`** — the gcd identity (17), a finset Bezout
  combination, the distance estimate (18), the lattice direction, and, in
  base 2, the explicit constant `2/5` — together with the binary-endpoint
  parameter audit of Remark 2.3 as exact rational arithmetic
  ([`DSS/SpectralGap.lean`](lean/DSS/SpectralGap.lean),
  [`DSS/BinaryAudit.lean`](lean/DSS/BinaryAudit.lean));
* **the almost-prime theorem on squares (Corollary 1.3, `P₂` part) is
  machine-checked as an implication**: the statement of Theorem 1.1 is
  transcribed as a *definition* — `SquareLLT`, never an axiom — and
  `SquareLLT g → #{n ≤ x : g(n²) is a P₂} ≫ x/log log x` is proved with the
  short-interval axiom `hhbr` as its **only** axiom
  ([`DSS/SquareP2.lean`](lean/DSS/SquareP2.lean));
* **the output-distribution theorem on squares (Theorem 1.2, unweighted
  form) is machine-checked as an implication that uses no axioms at all**:
  both clauses of Theorem 1.1 are definitions (`SquareLLT`, `SquareTail`),
  and
  `SquareLLT g ∧ SquareTail g → ∑_{m ≤ Q_η(L)} max_a |Δ_{g,□}(x;m,a)| ≪ x L^{−1/2+ε}`
  is proved from them, with **Poisson summation for the Gaussian
  (the paper's Lemma 4.3) proved from Mathlib's Jacobi theta transformation**
  ([`DSS/GaussSum.lean`](lean/DSS/GaussSum.lean),
  [`DSS/OutputLevel.lean`](lean/DSS/OutputLevel.lean));
* **the Fourier assembly of Theorem 1.1 (the paper's §2.4) is
  machine-checked as an implication that uses no axioms at all**: the two
  remaining analytic inputs — the integrated minor-arc estimate
  (Corollary 2.7) and the shrinking major-arc Gaussian expansion
  (Proposition 2.8) — are transcribed as *definitions* (`SquareMinor`,
  `SquareMajor`, never axioms), and
  `SquareMinor g → SquareMajor g → SquareLLT g`
  is proved — Fourier inversion on the circle, the splitting into arcs, the
  Gaussian Fourier transform, the Gaussian tails, and the coefficient
  collection by the identity (37) included
  ([`DSS/SquareAssembly.lean`](lean/DSS/SquareAssembly.lean)).  The
  human-trust surface of Theorem 1.1 is thereby exactly the two named
  square-method estimates (and Proposition 2.10 for the tail clause);
* the almost-prime theorem along the primes (**Corollary 4.6**: `g(p)` is a
  `P₂` for `≫ π(x)/log log x` primes when `μ_g > 0` and `d_g = 1`) is proved
  from exactly **two** results quoted from the literature — the local limit
  theorem of Martin–Mauduit–Rivat and the short-interval almost-prime theorem
  of Halberstam–Heath-Brown–Richert — declared as axioms in the single file
  [`DSS/Cited.lean`](lean/DSS/Cited.lean) and audited against their sources in
  [`SOURCE_AUDIT.md`](SOURCE_AUDIT.md);
* the lattice density `ρ_{g,□}` of eq. (4) together with **the finite
  Fourier identity (37)** that produces it, **the whole of Theorem 5.12's
  local factor theory** — multiplicativity of `N(c,·)` by the Chinese
  remainder theorem, the product formula (60) for an arbitrary modulus, and
  the mean formula (61) — **the `h_g`-scaling reduction of Theorem 2.1 to
  Theorem 1.1**, the digit-weight complement lemma of §7.2 with the
  **infinitude half of Theorem 7.5 in degree one**, and the exact reciprocal
  identity of §8 are verified unconditionally;
* every proof is `sorry`-free, the axiom discipline is **enforced at build
  time** by [`DSS/Guard.lean`](lean/DSS/Guard.lean), and
  [`axiom_audit.txt`](lean/axiom_audit.txt) records the `#print axioms` output
  for all 107 audited results — of which 102 depend on no axiom at all.

## The headlines

**Theorem 1.8, zero axioms.**  Every sufficiently large admissible `q` is the
base-`b` digit sum of at least `2^(√q/(36b))` squares with root coprime to `b`
and at most `3q` digits:

```lean
theorem sq_digit_sum_count {b : ℕ} (hb : 3 ≤ b) {q u : ℕ}
    (hq : 2304 * b ^ 4 ≤ q) (hadm : u ^ 2 ≡ q [MOD b - 1]) :
    2 ^ (Nat.sqrt q / (36 * b)) ≤ (sqSols b q).card

theorem sq_digit_sum_count_two {q : ℕ} (hq : 36864 ≤ q) :
    2 ^ (Nat.sqrt q / 72) ≤ (sqSols 2 q).card
```

where `sqSols b q` is the set of `n` with `(n, b) = 1`, `s_b(n²) = q` and
`n² ≤ b^{3q}`.  Both depend on **no axiom** (`propext`, `Classical.choice`,
`Quot.sound` only): Bertrand's postulate and Dirichlet's theorem come from
Mathlib, and Bose–Chowla is proved here.

**The two-digit spectral gap in every base, zero axioms** — the engine of
the new local theorem (Lemma 2.4), in base 2 with the explicit constant
`2/5`:

```lean
theorem two_digit_gap {b : ℕ} (g : Weight b) (hg : g.Coprime₁) :
    ∃ c : ℝ, 0 < c ∧ ∀ θ t : ℝ,
      ‖digitalFactor g θ t * digitalFactor g θ ((b : ℝ) * t)‖
        ≤ Real.exp (-c * dist01 ((g.dg : ℝ) * θ) ^ 2)

theorem two_digit_gap_two (g : Weight 2) (hg : g.Coprime₁) (θ t : ℝ) :
    ‖digitalFactor g θ t * digitalFactor g θ (2 * t)‖
      ≤ Real.exp (-(2 / 5) * dist01 θ ^ 2)
```

**The Fourier assembly of Theorem 1.1, zero axioms** — the paper's §2.4 as
an implication.  The minor- and major-arc estimates enter as *definitions*
transcribing Corollary 2.7 and Proposition 2.8, and the local limit theorem
follows:

```lean
theorem squareLLT_of_arcs (g : Weight b) (hg : g.Coprime₁)
    (hminor : SquareMinor g) (hmajor : SquareMajor g) : SquareLLT g
```

**Corollary 1.3 (`P₂` part) as an implication, from `hhbr` and nothing
else** — the square local limit theorem enters as the hypothesis
`SquareLLT g`, a transcription of Theorem 1.1's statement, never an axiom:

```lean
theorem square_p2_of_llt {b : ℕ} (g : Weight b) (hg : g.Coprime₁)
    (hdg : g.dg = 1) (hmu : 0 < g.mu) (hllt : SquareLLT g) :
    ∃ c : ℝ, 0 < c ∧ ∃ x₀ : ℝ, 3 ≤ x₀ ∧ ∀ x : ℝ, x₀ ≤ x →
      c * x / Real.log (Real.log x) ≤ ((sqP2Ints g x).card : ℝ)

theorem square_p2_binary : …  -- the s₂-instance
```

**Theorem 1.2 (unweighted form) as an implication, with zero axioms** — both
clauses of Theorem 1.1 enter as definitions, and the whole chain (Poisson
summation, the Chinese remainder splitting of the class, the window
truncation) is proved:

```lean
theorem square_output_level {b : ℕ} (g : Weight b) (hg : g.Coprime₁)
    (hllt : SquareLLT g) (htail : SquareTail g) {η ε : ℝ} (hη : 0 < η)
    (hε : 0 < ε) :
    ∃ C x₀ : ℝ, 0 < C ∧ ∀ x : ℝ, x₀ ≤ x →
      ∑ m ∈ moduli g x η, deltaSqMax g x m
        ≤ C * x * (Real.logb (b : ℝ) x) ^ (-(1 : ℝ) / 2 + ε)
```

**Corollary 4.6**, from `mmr` and `hhbr` and nothing else — with the concrete
instances that the sum of squared decimal digits of `p` (the function of
OEIS A052034), and the binary digit sum of `p`, are almost primes `P₂` for
`≫ π(x)/log log x` primes `p ≤ x`:

```lean
theorem p2_count {b : ℕ} (g : Weight b) (hg : g.Coprime₁) (hdg : g.dg = 1)
    (hmu : 0 < g.mu) :
    ∃ c : ℝ, 0 < c ∧ ∃ x₀ : ℝ, 3 ≤ x₀ ∧ ∀ x : ℝ, x₀ ≤ x →
      c * (picount x : ℝ) / Real.log (Real.log x) ≤ ((p2Primes g x).card : ℝ)

theorem p2_count_S : …        -- S(p) is a P₂ for ≫ π(x)/log log x primes
theorem p2_count_binary : …   -- s_2(p) is a P₂ for ≫ π(x)/log log x primes
```

## Layout

| File | Contents | Axioms |
|---|---|---|
| [`DSS/Digits.lean`](lean/DSS/Digits.lean) | the digit sum `s_b`; block additivity, the complement rule (78), the carry-free representation lemma | none |
| [`DSS/Sidon.lean`](lean/DSS/Sidon.lean) | Sidon sets; closure under translation/dilation; `T ∪ {0}`; the coefficients of `(∑ b^r)²` | none |
| [`DSS/CarryFree.lean`](lean/DSS/CarryFree.lean) | `a_T`; uniqueness of power sums; **Lemma 7.2** for `b ≥ 3` | none |
| [`DSS/CarryFreeTwo.lean`](lean/DSS/CarryFreeTwo.lean) | **Lemma 7.2** for `b = 2` (the parity bookkeeping) | none |
| [`DSS/BoseChowla.lean`](lean/DSS/BoseChowla.lean) | **Bose–Chowla, proved** in `GF(p²)`; + Bertrand: a Sidon set of any size `m` below `4m²` | none |
| [`DSS/Singleton.lean`](lean/DSS/Singleton.lean) | `s_b((2b^k−1)²) = k(b−1)+1`; infinitude of squares with prime digit sum | none |
| [`DSS/Squares.lean`](lean/DSS/Squares.lean) | **Theorem 1.8**, both cases | none |
| [`DSS/PrimeCount.lean`](lean/DSS/PrimeCount.lean) | **Corollary 1.9** in bases 2 and 3, via Bertrand | none |
| [`DSS/FWeight.lean`](lean/DSS/FWeight.lean) | weights that see the length: the split (52), `Z_b`, the zero weight's parameters, **Example 5.13's forcing**, the base-4 example | none |
| [`DSS/Weight.lean`](lean/DSS/Weight.lean), [`Counting.lean`](lean/DSS/Counting.lean), [`Examples.lean`](lean/DSS/Examples.lean) | the framework inherited from the predecessor repository (the `d_g` theory, the counting functions, `S`) | none |
| [`DSS/SpectralGap.lean`](lean/DSS/SpectralGap.lean) | **Lemma 2.4 in full, every base**: the gcd identity (17), the Bezout distance estimate (18), the lattice direction, `1 − cos 2πx ≥ 8‖x‖²`, the general gap `two_digit_gap`, and the binary gap at `c = 2/5` | none |
| [`DSS/SquareAssembly.lean`](lean/DSS/SquareAssembly.lean) | **the Fourier assembly of Theorem 1.1 (§2.4)**: `SquareMinor`/`SquareMajor` as *definitions*, Fourier inversion, the window split, the Gaussian transform and tail, and `squareLLT_of_arcs` | none |
| [`DSS/BinaryAudit.lean`](lean/DSS/BinaryAudit.lean) | **Remark 2.3**: the Mauduit–Rivat parameter audit at `q = 2`, as exact `ℚ` arithmetic | none |
| [`DSS/RhoSquare.lean`](lean/DSS/RhoSquare.lean) | `ρ_{g,□}` of eq. (4): normalisation (40), `κ_ρ = 1`, the restriction equivalence of Thm 1.2 | none |
| [`DSS/KappaM.lean`](lean/DSS/KappaM.lean) | **Theorem 5.12's local factors**: primes, prime powers, CRT multiplicativity, the product formula (60) for every `d`, the mean formula (61) | none |
| [`DSS/RhoFourier.lean`](lean/DSS/RhoFourier.lean) | **the finite Fourier identity (37)**: `∑_j η_j e(−jk/d) = ρ_{g,□}(k)`, from root-of-unity orthogonality | none |
| [`DSS/ShiftSquares.lean`](lean/DSS/ShiftSquares.lean) | `g((bn)²) = g(n²)`; the exact identity `S₀ = S − S(·/b)/b` of §8 | none |
| [`DSS/Blocking.lean`](lean/DSS/Blocking.lean) | **Lemma 7.6** for arbitrary weights; block additivity; degree-one blocking (Prop. 7.8(i)); **the infinitude half of Theorem 7.5** via Dirichlet | none |
| [`DSS/Cited.lean`](lean/DSS/Cited.lean) | **the axiom base**: `mmr` and `hhbr`, with source quotations | — |
| [`DSS/SquareLLT.lean`](lean/DSS/SquareLLT.lean) | the statement of **Theorem 1.1** as the *definition* `SquareLLT` | none |
| [`DSS/SquareGeneral.lean`](lean/DSS/SquareGeneral.lean) | **Theorem 2.1** reduced to Theorem 1.1: the `h_g`-scaling, as an implication | none |
| [`DSS/GaussSum.lean`](lean/DSS/GaussSum.lean) | **Lemma 4.3**, from Mathlib's Jacobi theta transformation: Poisson summation for a shifted Gaussian, with explicit constants | none |
| [`DSS/OutputLevel.lean`](lean/DSS/OutputLevel.lean) | the tail clause (6) as the *definition* `SquareTail`; **Theorem 1.2 (unweighted) as an implication** | none |
| [`DSS/P2.lean`](lean/DSS/P2.lean) | **Corollary 4.6** and its instances | `mmr`, `hhbr` |
| [`DSS/SquareP2.lean`](lean/DSS/SquareP2.lean) | **Corollary 1.3 (`P₂` part)** as an implication from `SquareLLT` | `hhbr` |
| [`DSS/Sanity.lean`](lean/DSS/Sanity.lean) | compile-time `#guard`s: the identities computing on concrete numbers | none |
| [`DSS/Guard.lean`](lean/DSS/Guard.lean) | `#assert_axioms`: the axiom discipline as a build invariant | — |

## Reproducing the check

```sh
cd lean
lake exe cache get
lake build                      # "Build completed successfully", no warnings
lake env lean AxiomAudit.lean   # compare with axiom_audit.txt
cd ../validation
uv run --with numpy python check_numerics.py   # reproduces §5.5 and more; a few seconds
```

Toolchain: Lean 4 `v4.33.0`, Mathlib tag `v4.33.0` (pinned in
`lean-toolchain` and `lake-manifest.json`).

## What is *not* verified

The verification report [`VERIFICATION.md`](VERIFICATION.md) gives the full
paper ↔ Lean correspondence and an honest inventory of what is not
machine-checked: the two shrinking-frequency estimates behind Theorem 1.1
(Propositions 2.6 and 2.8 — its §2.4 assembly and its engine, Lemma 2.4,
*are* now verified), the **`B^{ω(m)}`-weighted** form of Theorem 1.2
(the unweighted form *is* verified; the weighted one needs Mertens'
`∑_{p≤x} 1/p = log log x + O(1)`, absent from Mathlib at this pin), the
weighted-sieve `P₃` statements, the mean-zero asymptotics, the shellwise
Mertens formulas beyond their verified local factors, the Erdős–Kac
composition (§6), the transfer propositions of §8, Proposition 7.8 in degree
`≥ 2`, and Corollary 1.9 for bases `b ≥ 4`.  The two axioms themselves are
assumptions; `SOURCE_AUDIT.md` records how they were checked against their
sources.
