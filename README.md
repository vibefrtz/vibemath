# vibemath

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.22078540.svg)](https://doi.org/10.5281/zenodo.22078540)

A collection of mathematics papers, each accompanied by a Lean 4
formalisation that certifies the paper's deductive content.

## The method

Every paper in this repository follows the same verification discipline:

* the results the paper **quotes from the literature** are declared as
  Lean **axioms**, collected in a single documented file of the paper's
  Lean project, transcribed in exactly the form in which the paper uses
  them;
* **every argument the paper itself makes** is proved in Lean from those
  axioms, with no `sorry`, so that the Lean kernel certifies the
  implication *"if the quoted literature results hold as transcribed,
  then the paper's theorems hold"*;
* an **axiom audit** (`#print axioms` on each main theorem) is committed
  alongside the sources, making the exact logical dependencies of every
  theorem checkable at a glance — and, in each case, mechanically
  comparable with the citation structure of the paper's own proofs;
* a **verification report** (`VERIFICATION.md`) records the paper↔Lean
  correspondence, the encoding conventions, any cross-checks of the
  axioms against the original sources, any places where the formal proof
  deviates from the paper's (equivalent) argument, and an
  inventory of what is *not* machine-checked.

## Structure

Each paper is a top-level folder:

```
<paper-name>/
  README.md            what is proved, headline Lean statements, build steps
  VERIFICATION.md      the detailed verification report
  paper_anonymous.pdf  the manuscript (with its LaTeX source)
  lean/                a self-contained Lean project (pinned toolchain and
                       Mathlib version, axiom-audit driver and its expected
                       output); `cd lean && lake exe cache get && lake build`
                       reproduces the check
```

Each `lean/` directory is an independent Lake project with its own pinned
`lean-toolchain` and `lake-manifest.json`, so every paper's verification
remains reproducible bit-for-bit regardless of when it was added.

## Papers

| Paper | Lean status |
|---|---|
| [An Erdős–Kac law for palindromes and for reversed primes](erdos-kac-reversed-primes/) | all of the paper's own arguments machine-checked (0 `sorry`); 8 quoted literature results as axioms; clean axiom audit |
| [Prime values of digital functions along the primes](prime-values-digital-functions/) | the first two phases machine-checked (0 `sorry`); a single quoted literature result as an axiom, with 32 of the 40 audited results unconditional; the axiom discipline enforced at build time |
| [Prime values of digital functions and prescribed digit sums of squares](digit-sums-of-squares/) | the entire squares half — Theorem 1.10, with Bose–Chowla **proved in Lean** rather than quoted — machine-checked with **no axioms at all** (45 of 48 audited results unconditional); the almost-prime theorem Corollary 1.3 from exactly 2 quoted literature results as axioms; 0 `sorry`; the axiom discipline enforced at build time |

## License

The Lean sources, the axiom audits and this repository's own text are
released under the Apache License 2.0 (see [`LICENSE`](LICENSE)), the
licence used throughout the Lean/Mathlib ecosystem. Each paper's
manuscript — `paper_anonymous.pdf` and its LaTeX source — is released
under [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/).
