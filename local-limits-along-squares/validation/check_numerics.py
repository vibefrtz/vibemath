"""Numerical validation for *Local limits along squares and prime values of
digital functions*.

Reproduces every number quoted in §5.5 of the paper, spot-checks the
carry-free digit-sum identities of §7 (Lemma 7.2 and Remark 7.3) against
direct computation, sanity-checks the transcription of the
Halberstam–Heath-Brown–Richert axiom (`hhbr` in `DSS/Cited.lean`) by counting
`P₂`'s in short intervals, verifies the binary-endpoint arithmetic of
Remark 2.3, the lattice density ρ_{g,□} of eq. (4), the κ_m product formula
of Theorem 5.12 against direct counts, the finite-height portrait of the
square local limit theorem (Theorem 1.1), and the exact reciprocal identity
S₀ = S − S(·/10)/10 of §8.

Also checked, against the Lean statements they mirror:

  [10] the multiplicativity of N(c,·) and the mean formula (61) — the new
       content of DSS/KappaM.lean;
  [11] the finite Fourier identity (37), sum_j eta_j e(-jk/d) = rho(k) —
       DSS/RhoFourier.lean;
  [12] Lemma 4.3 (Gaussian sums in progressions) *against the constants the
       Lean proof supplies*, and the theta bound behind it — DSS/GaussSum.lean;
  [13] the rho/sigma scaling identity in the proof of Theorem 2.1 —
       DSS/SquareGeneral.lean;
  [14] the degree-one affine identity of Proposition 7.8(i) and the
       Dirichlet count behind Theorem 7.5 — DSS/Blocking.lean;
  [15] the output discrepancy of Theorem 1.2 at finite height —
       DSS/OutputLevel.lean.

Run:  uv run --with numpy python check_numerics.py     (a few seconds)
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
# The model values 0.11305 / 0.08101 / 0.05220 are the binomial with
# parameters (m-2, 1/10) on the m-digit shell -- the model in which the
# leading digit AND the units digit (1,3,7,9 for a large prime) carry no
# zeros.  (An earlier draft's parenthetical "(7, 1/10)" was a slip -- it
# would predict 0.14714 -- and the revision states the (m-2, 1/10) model.)
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

# --------------------------- [5] the binary-endpoint arithmetic of Remark 2.3
print("\n[5] Remark 2.3: the Mauduit-Rivat parameter audit at q = 2, exactly")
from fractions import Fraction as Fr
# log2/(8 log2) = 1/8 and 6 log2/(25 log2) = 6/25 are exact cancellations;
# the remaining checks are rational arithmetic (mirrored in Lean by
# DSS/BinaryAudit.lean).
br = Fr(2,1) / (1 + Fr(1,8))
report("bracket 2/(1+1/8) = 16/9", br, Fr(16,9))
report("1 + 1/25 + 6/25 = 32/25", 1 + Fr(1,25) + Fr(6,25), Fr(32,25))
dom_all = all(Fr(32,25)*Fr(nu) + 3 < Fr(16,9)*Fr(nu) for nu in range(11, 200))
report("32v/25 + 3 < 16v/9 for 10 < v < 200", dom_all, True)
report("threshold 675/112 < 7", Fr(675,112) < 7, True)

# ----------------------- [6] the lattice density rho_{g,square} of eq. (4)
print("\n[6] rho_{s_10,square}: quadratic residues mod 9 (eq. (4)); kappa = 1")
rho = {k: sum(1 for r in range(9) if (r*r - k) % 9 == 0) for k in range(9)}
report("rho(0),rho(1),rho(4),rho(7)", (rho[0],rho[1],rho[4],rho[7]), (3,2,2,2))
report("rho vanishes off the residues", all(rho[k]==0 for k in (2,3,5,6,8)), True)
report("normalisation sum rho = 9 (eq. (40))", sum(rho.values()), 9)
phi9 = sum(1 for a in range(9) if math.gcd(a,9)==1)
red = sum(rho[k] for k in range(9) if math.gcd(k,9)==1)
report("sum over reduced classes = phi(9) (kappa_rho = 1)", red, phi9)

# ------------------- [7] kappa_m: N(c,d) against the product formula (60)
print("\n[7] Theorem 5.12: d/phi(d)^2 * N(c,d) vs the product over ell | d")
def nboth(c, d):
    return sum(1 for a in range(d)
               if math.gcd(a,d)==1 and math.gcd((a-c)%d, d)==1)
def phi(d): return sum(1 for a in range(d) if math.gcd(a,d)==1)
def primes_of(d):
    out, x, p = [], d, 2
    while p*p <= x:
        if x % p == 0:
            out.append(p)
            while x % p == 0: x //= p
        p += 1
    if x > 1: out.append(x)
    return out
ok7 = True
for d in (2, 3, 4, 5, 8, 9, 16, 6, 12, 15, 30):
    for c in range(-3, 8):
        lhs = Fr(d) / Fr(phi(d))**2 * nboth(c, d)
        rhs = Fr(1)
        for l in primes_of(d):
            rhs *= Fr(l, l-1) if c % l == 0 else Fr(l*(l-2), (l-1)**2)
        ok7 &= (lhs == rhs)
report("product formula (60) on d in {2,...,30}, -3 <= c < 8", ok7, True)
# the local average identity behind (61)
ok7b = all(Fr(1,l)*Fr(l,l-1) + Fr(l-1,l)*Fr(l*(l-2),(l-1)**2) == 1
           for l in (2,3,5,7,11,13))
report("local average identity (61)", ok7b, True)

# ---------------- [8] the square local theorem at finite height (Thm 1.1)
print("\n[8] s_10(n^2) for n <= 2*10^6: the mod-9 lattice, and the Gaussian")
Nsq = 2*10**6
n = np.arange(1, Nsq+1, dtype=np.int64)
sq = n*n
ssq = np.zeros_like(sq); x = sq.copy()
while x.max() > 0:
    alive = x > 0
    ssq += np.where(alive, x % 10, 0)
    x //= 10
# the lattice: the distribution of s(n^2) mod 9 must converge to rho(k)/9
ok8 = True
print("    k mod 9 : observed proportion vs rho(k)/9")
for k in range(9):
    prop = (ssq % 9 == k).mean()
    tgt = rho[k]/9
    ok8 &= abs(prop - tgt) < 0.01
    print(f"      {k}: {prop:.4f} vs {tgt:.4f}")
report("mod-9 proportions within 0.01 of rho(k)/9", ok8, True)
# illustration (not a gate): the Gaussian at the peak
L = math.log10(Nsq); mu2L = 2*4.5*L; var = 2*8.25*L
kpk = min(range(int(mu2L)-4, int(mu2L)+5),
          key=lambda k: abs(k-mu2L) if rho[k % 9] else 9e9)
obs = int((ssq == kpk).sum())
prd = rho[kpk % 9]*Nsq/math.sqrt(2*math.pi*var)*math.exp(-(kpk-mu2L)**2/(2*var))
print(f"    peak k={kpk}: observed {obs}, Gaussian main term {prd:.0f} "
      f"(ratio {obs/prd:.3f}; illustration only, L = {L:.1f} is small)")

# ------------ [9] the exact reciprocal identity S0 = S - S(./10)/10 (§8)
print("\n[9] S0(N) = S(N) - S(N/10)/10, exactly, at N = 10^5  (mirrors Lean")
print("    DSS/ShiftSquares.lean: recipSum_split)")
def is_prime(m):
    if m < 2: return False
    d = 2
    while d*d <= m:
        if m % d == 0: return False
        d += 1
    return True
def sb10(m):
    s = 0
    while m: s += m % 10; m //= 10
    return s
NN = 10**5
Sfull = sum(Fr(1,m) for m in range(1, NN+1) if is_prime(sb10(m*m)))
Ssub  = sum(Fr(1,m) for m in range(1, NN//10+1) if is_prime(sb10(m*m)))
S0    = sum(Fr(1,m) for m in range(1, NN+1)
            if m % 10 != 0 and is_prime(sb10(m*m)))
report("S0 = S - S(N/10)/10 (exact rational)", S0 == Sfull - Fr(1,10)*Ssub, True)

# --------- [10] Theorem 5.12: multiplicativity, and the mean formula (61)
print("\n[10] Theorem 5.12: N(c,.) multiplicative, and the mean over a period")
ok10 = all(nboth(c, d1*d2) == nboth(c, d1) * nboth(c, d2)
           for d1, d2 in ((3,5), (4,9), (5,7), (8,9), (9,25), (2,15), (16,27))
           for c in range(-4, 9))
report("N(c,.) multiplicative for coprime moduli", ok10, True)
ok10b = True
for d in (2, 3, 4, 5, 6, 8, 9, 12, 15, 30):
    for A in (1, 2, 3, 6, 10):
        mean = sum(Fr(d) / Fr(phi(d))**2 * nboth(A*m, d) for m in range(d)) / d
        prod = Fr(1)
        for l in primes_of(d):
            if A % l == 0:
                prod *= Fr(l, l-1)
        ok10b &= (mean == prod)
report("mean formula (61), d <= 30, A in {1,2,3,6,10}", ok10b, True)

# ---------------- [11] the finite Fourier identity (37) for rho_{g,square}
print("\n[11] eq. (37): sum_j eta_j e(-jk/d) = rho_{g,square}(k), d = d_g = 9")
d9, w1 = 9, 1
def ee(t): return complex(math.cos(2*math.pi*t), math.sin(2*math.pi*t))
eta = [sum(ee(j*w1*r*r/d9) for r in range(d9)) / d9 for j in range(d9)]
ok11 = True
for k in range(-9, 10):
    val = sum(eta[j] * ee(-j*k/d9) for j in range(d9))
    ok11 &= abs(val - rho[k % 9]) < 1e-9
report("Fourier inversion of the arc coefficients, -9 <= k <= 9", ok11, True)

# ------------------ [12] Lemma 4.3: Gaussian sums in progressions (Poisson)
print("\n[12] Lemma 4.3: (2 pi s)^(-1/2) sum_{k = c mod M} exp(-(k-y)^2/(2s))")
ok12 = True
for (sv, M, c, y) in ((330.0, 5, 2, 180.0), (5.0, 3, 1, 7.3),
                      (50.0, 7, 4, -12.5), (12.0, 2, 1, 0.0)):
    assert M*M <= 2*math.pi**2*sv                 # the hypothesis of the lemma
    lo, hi = int(y - 60*math.sqrt(sv)), int(y + 60*math.sqrt(sv))
    tot = sum(math.exp(-(k-y)**2/(2*sv))
              for k in range(lo, hi+1) if (k - c) % M == 0)
    got = tot / math.sqrt(2*math.pi*sv)
    bound = (4.0/M) * math.exp(-(2*math.pi**2*sv/M**2))
    err = abs(got - 1.0/M)
    ok12 &= err <= bound + 1e-13
    print(f"    s={sv:6.1f} M={M} c={c}: |sum - 1/M| = {err:.3e} "
          f"<= proved bound {bound:.3e}")
report("Lemma 4.3 within the proved error bound", ok12, True)

# the theta bound behind it: |sum_n exp(-a(n+b)^2) - sqrt(pi/a)| <= sqrt(pi/a) 2t/(1-t)
ok12b = True
for (al, be) in ((0.5, 0.3), (1.0, 0.0), (0.2, 0.75), (2.0, 0.5)):
    tot = sum(math.exp(-al*(n+be)**2) for n in range(-400, 401))
    t = math.exp(-math.pi**2/al)
    ok12b &= abs(tot - math.sqrt(math.pi/al)) <= math.sqrt(math.pi/al)*2*t/(1-t) + 1e-12
report("theta bound |sum - sqrt(pi/a)| <= sqrt(pi/a) 2t/(1-t)", ok12b, True)

# ------------- [13] Theorem 2.1: the h_g-scaling of the main term (eq. (14))
print("\n[13] Theorem 2.1: sqMain of h*g at k = h*l equals sqMain of g at l")
def sq_main(rho_k, xv, mu, sig2, Lv, k):
    return (rho_k * xv / math.sqrt(4*math.pi*sig2*Lv)
            * math.exp(-(k - 2*mu*Lv)**2 / (4*sig2*Lv)))
xv, Lv, mu10, sig10 = 1e6, 6.0, 4.5, 8.25
ok13 = True
for h in (2, 3, 5):
    for l in (20, 25, 31, 54):
        lhs = sq_main(h*rho[l % 9], xv, h*mu10, h*h*sig10, Lv, h*l)   # eq. (14)
        rhs = sq_main(rho[l % 9], xv, mu10, sig10, Lv, l)             # Thm 1.1
        ok13 &= abs(lhs - rhs) <= 1e-9 * max(1.0, abs(rhs))
report("rho/sigma scaling identity of the proof of Theorem 2.1", ok13, True)

# -------- [14] Proposition 7.8(i) in degree one, and Theorem 7.5 infinitude
print("\n[14] Prop. 7.8(i): s_10(u*10^k - c) = A k + C, and primes among them")
ok14 = all(sb10(2*10**k - 7) == 9*k - 5 for k in range(1, 30))
report("s_10(2*10^k - 7) = 9k - 5 for 1 <= k < 30", ok14, True)
ok14b = all(sb10(3*10**k - 41) == 9*k - 2 for k in range(2, 30))
report("s_10(3*10^k - 41) = 9k - 2 for 2 <= k < 30", ok14b, True)
# Dirichlet: A = 9, C = -5, (A,C) = 1, so 9k - 5 is prime infinitely often
K = 20000
cnt = sum(1 for k in range(1, K+1) if is_prime(9*k - 5))
# the density of primes in the progression -5 mod 9 is (A/phi(A))/log(Ak+C)
pred = sum(1.5 / math.log(9*k - 5) for k in range(2, K+1))
print(f"    #(k <= {K} : 9k-5 prime) = {cnt}, "
      f"sum (A/phi(A))/log(9k-5) = {pred:.0f}, ratio {cnt/pred:.3f}")
ok_all &= abs(cnt/pred - 1) < 0.05

# ------------- [15] Theorem 1.2 at finite height: the output discrepancy
print("\n[15] Theorem 1.2 at finite height: sum over m <= Q_eta(L) of")
print("     max_a |#{n <= x : s_10(n^2) = a mod m} - x/m|, x = 2*10^6")
Lx = math.log(Nsq, 10)
eta_v = 0.1
Qv = math.sqrt(Lx) / (math.log(Lx) ** (0.5 + eta_v))
tot15 = 0.0
for m in range(1, int(Qv) + 1):
    if math.gcd(m, 9) != 1:
        continue
    counts = np.bincount(ssq % m, minlength=m)
    tot15 += float(np.abs(counts - Nsq / m).max())
target = Nsq * Lx ** (-0.5 + 0.1)
print(f"    Q_eta(L) = {Qv:.2f}, sum = {tot15:.1f}, x L^(-1/2+0.1) = {target:.1f}")
ok_all &= tot15 <= target
# Illustration only.  At these heights L = log_10 x is 4.3 to 6.3, so the
# theorem's own error L^(-1/2+eps) is of order 1/2 and the estimate is not yet
# quantitative; what the data show is the slow decrease of the relative
# discrepancy, at roughly the predicted L^(-1/2) rate.
print("    (illustration) sum over all m <= 20 with (m,9)=1, relative to x:")
for Nx in (2*10**4, 2*10**5, 2*10**6):
    sub = ssq[:Nx]
    tot = 0.0
    for m in range(1, 21):
        if math.gcd(m, 9) != 1:
            continue
        counts = np.bincount(sub % m, minlength=m)
        tot += float(np.abs(counts - Nx / m).max())
    print(f"      x = {Nx:>9}: {tot/Nx:.4f} x   (L^(-1/2) = "
          f"{math.log(Nx,10)**-0.5:.4f})")

print("\nALL CHECKS PASSED" if ok_all else "\nSOME CHECKS FAILED")
