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
import DSS.RhoSquare
import DSS.KappaM
import DSS.Blocking

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

/-! ### The number `d_g` of the base-10 digit sum is `9`, so Corollary 4.6
applies to `s_2` (where `d = 1`) but not directly to `s_10` -/

#guard (sbWeight 2 (by norm_num)).dg = 1

/-! ### The square lattice density `ρ_{g,□}` (eq. (4)) for `s_10`: `d = 9`,
and the quadratic-residue counts modulo 9 -/

#guard rhoSq (sbWeight 10 (by norm_num)) 0 = 3
#guard rhoSq (sbWeight 10 (by norm_num)) 1 = 2
#guard rhoSq (sbWeight 10 (by norm_num)) 4 = 2
#guard rhoSq (sbWeight 10 (by norm_num)) 7 = 2
#guard rhoSq (sbWeight 10 (by norm_num)) 2 = 0
#guard rhoSq (sbWeight 10 (by norm_num)) 3 = 0
#guard rhoSq (sbWeight 2 (by norm_num)) 5 = 1

/-! ### The κ_m counts `N(c,d)` of eq. (58): primes, the base-3 example
(`d = 2`: odd shells vanish), and the prime power `9` -/

#guard nboth 0 5 = 4
#guard nboth 3 5 = 3
#guard nboth 0 2 = 1
#guard nboth 1 2 = 0
#guard nboth 6 9 = 6
#guard nboth 1 9 = 3

/-! ### Multiplicativity of `N(c, ·)` (Theorem 5.12) at concrete moduli -/

#guard nboth 3 15 = nboth 3 3 * nboth 3 5
#guard nboth 1 35 = nboth 1 5 * nboth 1 7
#guard nboth 0 12 = nboth 0 4 * nboth 0 3

/-! ### The affine identity of Proposition 7.8(i), degree one: the constant
`C_{g,c}` of `blockConst` is independent of `k` -/

-- `s_10(2·10^k − 7) = 9k − 5`: at `k = 4`, `19993` has digit sum `31 = 36 − 5`
#guard blockConst (sbWeight 10 (by norm_num)) 2 7 = -5
#guard (sbWeight 10 (by norm_num)).eval (2 * 10 ^ 4 - 7) = 4 * 9 - 5
#guard (sbWeight 10 (by norm_num)).eval (2 * 10 ^ 5 - 7) = 5 * 9 - 5

end DSS
