"""Numerical validation for *Prime values of digital functions and prescribed
digit sums of squares*.

Reproduces every number quoted in §5.4 of the paper, spot-checks the
carry-free digit-sum identities of §7 (Lemma 7.2 and Remark 7.3) against
direct computation, and sanity-checks the transcription of the
Halberstam–Heath-Brown–Richert axiom (`hhbr` in `DSS/Cited.lean`) by counting
`P₂`'s in short intervals.

Run:  uv run --with numpy python check_numerics.py     (~2 min)
"""
import numpy as np, math

ok_all = True
def report(label, got, expect, exact=True):
    global ok_all
    good = (got == expect) if exact else abs(got - expect) < 1e-4
    ok_all &= good
    print(f"  {'OK ' if good else 'FAIL'} {label}: got {got}  (paper: {expect})")

# ---------------------------------------------------------------- sieve to 1e8
N = 10**8
sieve = np.ones(N, dtype=bool); sieve[:2] = False
for i in range(2, int(N**0.5)+1):
    if sieve[i]: sieve[i*i::i] = False
primes = np.flatnonzero(sieve).astype(np.int64)
print("[0] pi(10^8) =", len(primes))
report("pi(10^8)", len(primes), 5761455)

# ------------------------------------------- [1] zero digits of decimal primes
def zeros_base10(a):
    out = np.zeros_like(a); x = a.copy()
    while x.max() > 0:
        alive = x > 0
        d = x % 10
        out += ((d == 0) & alive)
        x //= 10
    return out

Z = zeros_base10(primes)
small_prime = {2, 3, 5, 7}          # Z_10(p) <= 7 for p < 10^8
zprime = np.isin(Z, list(small_prime))
print("\n[1] Z_10(p) prime, p <= 10^8  (paper §5.4, first computation)")
report("count", int(zprime.sum()), 629304)

recip = (1.0 / primes[zprime]).sum()
print(f"  sum 1/p over these = {recip:.3f}  (paper: 0.051)")
ok_all &= abs(recip - 0.051) < 5e-4

def log3(x): return math.log(math.log(math.log(x)))
for X, expect in ((10**7, -0.99), (10**8, -1.02)):
    mask = (primes <= X) & zprime
    d = (1.0 / primes[mask]).sum() - log3(X)
    print(f"  sum 1/p - log_3 x at x=1e{int(math.log10(X))}: {d:.2f}  (paper: {expect})")
    ok_all &= abs(d - expect) < 5e-3

# shells: proportion with a prime number of zeros vs the binomial model.
# NOTE: the paper's quoted model values 0.11305 / 0.08101 / 0.05220 are the
# binomial with parameters (m-2, 1/10) on the m-digit shell -- the model in
# which the leading digit AND the last digit (1,3,7,9 for a prime) carry no
# zeros.  The parenthetical "(7, 1/10)" in the manuscript's sentence is a slip:
# Bin(7, 1/10) would predict 0.14714, visibly off the data.
from math import comb
print("  shells (proportion with prime zero count | Bin(m-2, 1/10) model):")
for digits, prop_paper, model_paper in ((8, 0.11336, 0.11305),
                                        (7, 0.08126, 0.08101),
                                        (6, 0.05294, 0.05220)):
    lo, hi = 10**(digits-1), 10**digits
    m = (primes >= lo) & (primes < hi)
    prop = zprime[m].sum() / m.sum()
    n = digits - 2
    model = sum(comb(n, k) * 0.1**k * 0.9**(n-k)
                for k in small_prime if k <= n)
    print(f"    {digits}-digit: {prop:.5f} vs model {model:.5f} "
          f"(paper: {prop_paper} vs {model_paper})")
    ok_all &= abs(prop - prop_paper) < 1e-5 and abs(model - model_paper) < 1e-5

# ------------------------------------------------- [2] the base-3 oscillation
print("\n[2] base 3, weights (1,2,-3): F(p) = ell_3(p) + g(p)  (paper §5.4 table)")
M3 = 3**16
sieve3 = np.ones(M3, dtype=bool); sieve3[:2] = False
for i in range(2, int(M3**0.5)+1):
    if sieve3[i]: sieve3[i*i::i] = False
p3 = np.flatnonzero(sieve3).astype(np.int64)

W = np.array([1, 2, -3], dtype=np.int64)
F = np.zeros_like(p3); x = p3.copy()
while x.max() > 0:
    alive = x > 0
    F += np.where(alive, W[x % 3], 0)
    x //= 3
# F <= 2*17 = 34; F prime means F in primes up to 34
Fprime = np.isin(F, [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31])
ell = np.floor(np.log(p3) / math.log(3)).astype(np.int64) + 1
# fix floating rounding at powers of 3
for m in range(1, 17):
    ell[p3 == 3**m] = m + 1

table_prime  = {10: 1220, 11: 696, 12: 7943, 13: 9118,
                14: 64566, 15: 51468, 16: 527820}
table_eq_two = {10: 0, 11: 696, 12: 0, 13: 9118, 14: 0, 15: 51468, 16: 0}
for m in range(10, 17):
    shell = ell == m
    got_p  = int((Fprime & shell).sum())
    got_2  = int(((F == 2) & shell).sum())
    report(f"m={m}: #F(p) prime", got_p, table_prime[m])
    report(f"m={m}: #F(p)=2    ", got_2, table_eq_two[m])

# --------------------------------- [3] the carry-free identities of Lemma 7.2
print("\n[3] Lemma 7.2 and Remark 7.3, against direct digit sums")
def sb(b, n):
    s = 0
    while n: s += n % b; n //= b
    return s

import itertools, random
random.seed(7)
S = [2*s for s in (32, 37, 44, 47, 52)]      # translate+double a Sidon set
for b in (2, 3, 10):
    for t in (1, 2, 3):
        T = random.sample(S, t)
        a = 1 + sum(b**r for r in T)
        k = 1
        while b**k <= a*a + 2*a: k += 1
        got = sb(b, (a * b**k - 1)**2)
        want = k*(b-1) + t*t if b >= 3 else k + t*(t+1)//2
        report(f"b={b} t={t} k={k}: s_b((a_T b^k-1)^2)", got, want)
for b in (2, 3, 10, 16):
    for k in (2, 3, 5, 8):
        if b**k > 4:
            report(f"singleton b={b} k={k}", sb(b, (2*b**k - 1)**2), k*(b-1) + 1)

# ------------------------------ [4] sanity of the hhbr transcription (P2's)
print("\n[4] P2's in (z - z^0.455, z]  (sanity for the hhbr axiom)")
def Omega(n):
    c = 0
    d = 2
    while d*d <= n:
        while n % d == 0: n //= d; c += 1
        d += 1
    return c + (1 if n > 1 else 0)
for z in (10**6, 10**7, 5*10**7):
    lo = z - z**0.455
    cnt = sum(1 for n in range(int(lo)+1, z+1) if 2 <= n and Omega(n) <= 2)
    dens = z**0.455 / math.log(z)
    print(f"  z={z:>9}: {cnt:4d} P2's in an interval of length {z**0.455:8.1f}"
          f"  (z^0.455/log z = {dens:6.1f}, ratio {cnt/dens:.2f})")
    ok_all &= cnt > 0

print("\nALL CHECKS PASSED" if ok_all else "\nSOME CHECKS FAILED")
