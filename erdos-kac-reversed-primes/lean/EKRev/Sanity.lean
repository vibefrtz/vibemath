/-
EKRev/Sanity.lean

Executable sanity checks on the combinatorial definitions (not part of the
proofs; provides quick evidence that the encodings mean what they should).
Each `#guard` is checked at compile time.
-/
import EKRev.Digits
import EKRev.PalCount
import EKRev.PrimeBlocks
import EKRev.OmegaS

namespace EKRev

-- digits of 123 in base 10 (least significant first)
#guard digit 10 123 0 = 3
#guard digit 10 123 1 = 2
#guard digit 10 123 2 = 1

-- reversal of a 3-digit block, base 10
#guard rev 10 3 123 = 321
#guard rev 10 3 100 = 1     -- leading zeros of the reversal are dropped
#guard rev 10 3 321 = 123   -- involution
#guard rev 2 4 0b1101 = 0b1011

-- palindromes with exactly λ digits: #𝒯_λ = (b-1)·b^(⌈λ/2⌉-1)
#guard (palSet 10 1).card = 9
#guard (palSet 10 2).card = 9
#guard (palSet 10 3).card = 90
#guard (palSet 2 3).card = 2
#guard (33 : ℕ) ∈ palSet 10 2
#guard (121 : ℕ) ∈ palSet 10 3
#guard (123 : ℕ) ∉ palSet 10 3

-- cumulative palindrome counts
#guard (palBelow 10 100).card = 18      -- 1..9 and 11,22,…,99
#guard (palBelowMod 10 100 0 3).card = 6 -- 3,6,9,33,66,99

-- 3-digit primes and their reversals
#guard (101 : ℕ) ∈ PLam 10 3
#guard (100 : ℕ) ∉ PLam 10 3
#guard (149 : ℕ) ∈ PLamI 10 3 1
#guard (941 : ℕ) ∈ ALamI 10 3 1        -- 941 = R₃(149)
#guard (PLam 10 2).card = 21            -- two-digit primes
#guard (ALam 10 2).card = 21

-- π̄_λ(z, a, d) and π_λ(z): primes 100 ≤ p < 200 with 3 ∣ R₃(p)
#guard picLam 10 3 200 = 21
#guard revCount 10 3 200 3 3
    = ((primesIn 100 200).filter fun p => 3 ∣ rev 10 3 p).card

-- ω and Ω
#guard smallOmega 12 = 2
#guard bigOmega 12 = 3
#guard smallOmega 1 = 0
#guard bigOmega (2^5 * 3^2) = 7

end EKRev
