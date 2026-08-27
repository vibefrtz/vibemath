/-
DSS/Sanity.lean

Compile-time `#guard` checks: concrete numerical instances of the identities
proved in this development, evaluated by the kernel.  None of these are used
by any proof; they exist so that a reader can see the definitions computing
the right numbers.

Nothing in this file is conditional: it imports no axioms.
-/
import DSS.Digits
import DSS.Sidon
import DSS.CarryFree
import DSS.CarryFreeTwo
import DSS.Singleton
import DSS.FWeight
import DSS.Cited

namespace DSS

/-! ### The digit sum and the complement rule -/

#guard sb 10 361 = 10
#guard sb 10 12321 = 9
#guard sb 2 225 = 4
#guard sb 3 289 = 5

-- the complement rule `s_b(b^k − c) + s_b(c−1) = k(b−1)`, at `b = 10, k = 3, c = 46`
#guard sb 10 (10 ^ 3 - 46) + sb 10 45 = 3 * 9

/-! ### The singleton family `s_b((2·b^k − 1)²) = k(b−1) + 1` (Remark 7.3) -/

#guard sb 10 ((2 * 10 ^ 1 - 1) ^ 2) = 1 * 9 + 1    -- 19² = 361
#guard sb 10 ((2 * 10 ^ 2 - 1) ^ 2) = 2 * 9 + 1    -- 199² = 39601
#guard sb 10 ((2 * 10 ^ 3 - 1) ^ 2) = 3 * 9 + 1    -- 1999² = 3996001
#guard sb 2 ((2 * 2 ^ 3 - 1) ^ 2) = 3 * 1 + 1      -- 15² = 225 = 11100001₂
#guard sb 3 ((2 * 3 ^ 2 - 1) ^ 2) = 2 * 2 + 1      -- 17² = 289 = 101201₃

/-! ### The carry-free square (Lemma 7.2) on a small Sidon set -/

-- `T = {2, 3}` is Sidon, positive, avoids its own sumset;
-- `a_T = 1 + b² + b³`; `s_10(a_T²) = (2+1)² = 9`
#guard aT 10 {2, 3} = 1101
#guard sb 10 (aT 10 {2, 3} ^ 2) = 9
-- shifted: `s_10((a_T·10^k − 1)²) = 9k + 4` for `10^k > a_T² + 2a_T`, e.g. `k = 7`
#guard sb 10 ((aT 10 {2, 3} * 10 ^ 7 - 1) ^ 2) = 7 * 9 + 2 ^ 2

-- the binary case with even exponents `T = {2, 6}`:
-- `s_2((a_T·2^k − 1)²) = k + C(3,2) = k + 3` for `2^k > a_T² + 2a_T`, e.g. `k = 15`
#guard aT 2 {2, 6} = 69
#guard sb 2 ((aT 2 {2, 6} * 2 ^ 15 - 1) ^ 2) = 15 + Nat.choose (2 + 1) 2

/-! ### Pair counts -/

#guard (pairsLT {2, 4, 10}).card = Nat.choose 3 2
#guard (pairsLT ({2, 4, 10, 22} : Finset ℕ)).card = Nat.choose 4 2

/-! ### Admissibility: `s_b(n²) ≡ n² (mod b−1)`; squares mod 9 lie in {0,1,4,7} -/

#guard (List.range 30).all (fun n => [0, 1, 4, 7].contains (sb 10 (n ^ 2) % 9))
#guard (List.range 30).all (fun n => sb 10 (n ^ 2) % 9 = n ^ 2 % 9)

/-! ### The zero counter and the base-3/base-4 examples -/

#guard Zb 10 100 = 2
#guard Zb 10 10203 = 2
#guard Zb 2 8 = 3
#guard exWeight3.dg = 2
#guard exWeight4.dg = 3
#guard (sbWeight 10 (by norm_num)).dg = 9

/-! ### `P₂`'s -/

#guard decide (IsP2 4) = true      -- 2·2
#guard decide (IsP2 6) = true      -- 2·3
#guard decide (IsP2 7) = true      -- prime
#guard decide (IsP2 8) = false     -- 2³
#guard decide (IsP2 1) = false
#guard decide (IsP2 30) = false    -- 2·3·5

/-! ### The number `d_g` of the base-10 digit sum is `9`, so Corollary 1.3
applies to `s_2` (where `d = 1`) but not directly to `s_10` -/

#guard (sbWeight 2 (by norm_num)).dg = 1

end DSS
