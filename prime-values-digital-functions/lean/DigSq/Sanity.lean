/-
DigSq/Sanity.lean

Executable checks on the definitions (not part of any proof; they provide quick
evidence that the encodings mean what they are supposed to mean).  Each `#guard`
is checked at compile time.
-/
import DigSq.Examples

namespace DigSq

/-! ### `S` is the sum of the squares of the decimal digits -/

#guard S 0 = 0
#guard S 1 = 1
#guard S 123 = 14              -- 1 + 4 + 9
#guard S 10 = 1
#guard S 999 = 243             -- the largest value of `S` on three digits
#guard S 19 = 82
#guard S 28 = 68               -- §6.3: `s(19) = s(28)` but `S(19) ≠ S(28)`
#guard (Nat.digits 10 19).sum = (Nat.digits 10 28).sum

/-! ### The first terms of OEIS A052034

The primes `p` for which `S(p)` is again prime. -/

#guard (List.range 200).filter (fun p => Nat.Prime p && Nat.Prime (S p))
        = [11, 23, 41, 61, 83, 101, 113, 131, 137, 173, 179, 191, 197, 199]

/-! ### The `S`-orbit of §6.3: the eight-cycle of the happy numbers -/

#guard S 4 = 16
#guard S 16 = 37
#guard S 37 = 58
#guard S 58 = 89
#guard S 89 = 145
#guard S 145 = 42
#guard S 42 = 20
#guard S 20 = 4

/-! ### The constants attached to `S` -/

-- `d_S = 1`: the digit differences `g(a) - a·g(1) = a² - a` are `0,0,2,6,12,20,30,42,56,72`
#guard (List.range 10).map (fun a => a ^ 2 - a) = [0, 0, 2, 6, 12, 20, 30, 42, 56, 72]
-- and `gcd(2, 9) = 1`
#guard Nat.gcd 9 2 = 1
-- `10 · μ_S = ∑_{a<10} a² = 285 = 10 · 57/2`
#guard ((List.range 10).map (fun a => a ^ 2)).sum = 285

/-! ### The other digital functions of the paper -/

-- sums of `r`-th powers of the decimal digits
#guard powDigitSum 10 2 123 = 14          -- 1 + 4 + 9
#guard powDigitSum 10 3 123 = 36          -- 1 + 8 + 27
#guard powDigitSum 10 1 123 = 6           -- the plain digit sum
#guard S 123 = powDigitSum 10 2 123

-- occurrences of a digit (Corollary 1.5)
#guard digitOccurrences 10 7 1777 = 3
#guard digitOccurrences 10 7 1234 = 0
#guard digitOccurrences 2 1 0b101101 = 4

-- Corollary 1.5 in action: primes below 200 in which the digit 1 occurs a prime
-- number of times
#guard (List.range 200).filter
        (fun p => Nat.Prime p && Nat.Prime (digitOccurrences 10 1 p))
        = [11, 101, 113, 131, 151, 181, 191]

/-! ### The `binom(a,2)` example of §1 -/

#guard (List.range 10).map (fun a => a * (a - 1) / 2) = [0, 0, 1, 3, 6, 10, 15, 21, 28, 36]
#guard ((List.range 10).map (fun a => a * (a - 1) / 2)).sum = 120   -- mean 12

end DigSq
