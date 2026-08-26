/-
DigSq/Imports.lean — the single place where Mathlib is imported.

We deliberately do **not** `import Mathlib` or `import Mathlib.Tactic`: the whole
development uses about a quarter of Mathlib, and keeping the surface small keeps
the build honest and fast.
-/
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Data.Nat.Digits.Div
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.IntervalCases
