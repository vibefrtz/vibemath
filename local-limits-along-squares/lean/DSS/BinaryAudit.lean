/-
DSS/BinaryAudit.lean

**The binary-endpoint audit of Remark 2.3**, machine-checked.

The paper includes `b = 2` in the square local limit theorem by checking that
the final parameter selection of Mauduit–Rivat (their (73)–(79)) survives at
`q = 2`.  The check is pure arithmetic, and the paper performs it in Remark 2.3
after the exact simplifications `log 2 / (8 log 2) = 1/8` and
`6·(log 2)/(25·log 2) = 6/25` (which are trivial cancellations).  This file
verifies the three resulting rational inequalities:

* the lower-bound bracket equals `(16/9)(1 + 25ξ/8)`, hence exceeds `16/9`
  for `ξ > 0` (`binary_bracket_eval`, `binary_bracket_gt`);
* the quantity to dominate is `ν + ν/25 + 6ν/25 + 3 = 32ν/25 + 3`
  (`binary_sum_eval`);
* `32ν/25 + 3 < 16ν/9` for every `ν > 10`, the standing range
  (`binary_domination`) — indeed already for `ν ≥ 675/112`.

Nothing in this file is conditional: it imports no axioms.
-/
import DSS.Imports

namespace DSS

/-- The bracket of Remark 2.3:
`2(1 + 25ξ/8) / (1 + 1/8) = (16/9)(1 + 25ξ/8)`. -/
theorem binary_bracket_eval (ξ : ℚ) :
    2 * (1 + 25 * ξ / 8) / (1 + 1 / 8) = (16 / 9) * (1 + 25 * ξ / 8) := by
  field_simp
  ring

/-- For `ξ > 0` the bracket exceeds `16/9`. -/
theorem binary_bracket_gt {ξ : ℚ} (hξ : 0 < ξ) :
    (16 : ℚ) / 9 < 2 * (1 + 25 * ξ / 8) / (1 + 1 / 8) := by
  rw [binary_bracket_eval]
  nlinarith

/-- The dominated quantity of Remark 2.3:
`ν + ν/25 + 6ν/25 + 3 = 32ν/25 + 3`. -/
theorem binary_sum_eval (ν : ℚ) :
    ν + ν / 25 + 6 * ν / 25 + 3 = 32 * ν / 25 + 3 := by ring

/-- **The audit:** `32ν/25 + 3 < 16ν/9` for `ν > 10` — so the Mauduit–Rivat
lower bound `2μ > (16/9)ν` dominates the required quantity throughout the
standing range, and their conditions (52) and (63) hold at `q = 2`. -/
theorem binary_domination {ν : ℚ} (hν : 10 < ν) :
    32 * ν / 25 + 3 < 16 * ν / 9 := by
  nlinarith

/-- The sharp threshold recorded in the file comment: the domination already
holds for `ν ≥ 675/112` (and `675/112 < 7`). -/
theorem binary_domination_sharp {ν : ℚ} (hν : 675 / 112 ≤ ν) :
    32 * ν / 25 + 3 ≤ 16 * ν / 9 := by
  nlinarith

end DSS
