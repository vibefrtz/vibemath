import numpy as np, math
N = 10**8
sieve = np.ones(N, dtype=bool); sieve[:2]=False
for i in range(2, int(N**0.5)+1):
    if sieve[i]: sieve[i*i::i] = False
primes = np.flatnonzero(sieve)
print("pi(10^8) =", len(primes), "(known: 5761455)")

# S = sum of squares of decimal digits, for n < 10^8 : max 8*81 = 648
def Sarr(a):
    out = np.zeros_like(a); x = a.copy()
    while x.max() > 0:
        d = x % 10; out += d*d; x //= 10
    return out

M = 649
isprime_small = np.zeros(M+1, dtype=bool); isprime_small[2:]=True
for i in range(2,int(M**0.5)+1):
    if isprime_small[i]: isprime_small[i*i::i]=False
omega = np.zeros(M+1, dtype=np.int64)
for p in range(2, M+1):
    if isprime_small[p]: omega[p::p] += 1

Sp = Sarr(primes.astype(np.int64))
good = isprime_small[Sp]

print("\n[1] first primes p with S(p) prime:", primes[good][:14].tolist())
print("    paper lists: 11 23 41 61 83 101 113 131 137 173 179 191")

# [2] omega(S(p)) over 8-digit primes
mask8 = (primes >= 10**7)
w = omega[Sp[mask8]].astype(float)
print("\n[2] 8-digit primes: count=%d  mean omega(S(p))=%.4f  var=%.4f  (paper 2.055 / 0.480)" % (mask8.sum(), w.mean(), w.var()))

# Gaussian-weighted mean of omega(k): center y = mu*log_b x, V = sigma^2 log_b x
mu = 28.5
sig2 = sum(a**4 for a in range(10))/10 - mu**2
print("    mu_S =", mu, " sigma_S^2 =", sig2)
for L in (8.0, 7.95, math.log10(10**8)):
    y = mu*L; V = sig2*L
    ks = np.arange(1, 4000)
    wt = np.exp(-(ks-y)**2/(2*V))
    om = np.array([omega[k] if k <= M else 0 for k in ks], dtype=float)
    ok = ks <= M
    m1 = (wt[ok]*om[ok]).sum()/wt[ok].sum()
    m2 = (wt[ok]*om[ok]**2).sum()/wt[ok].sum()
    print("    L=%.2f: gaussian-weighted mean omega(k)=%.4f var=%.4f (paper 2.051 / 0.480)" % (L, m1, m2-m1**2))
print("    log_3(10^8) =", math.log(math.log(math.log(10**8))))

# [3] Mertens: sum 1/p over p<X with S(p) prime, vs log(log_2 X + kappa)
kappa = math.log(mu/math.log(10))
print("\n[3] kappa_S = log(57/(2 log 10)) = %.4f  (paper 2.516)" % kappa)
gp = primes[good].astype(float)
for X in (10**4, 10**5, 10**6, 10**7, 10**8):
    s = (1.0/gp[gp < X]).sum()
    main = math.log(math.log(math.log(X)) + kappa)
    print("    X=1e%-2d  sum=%.5f  log(log_2X+kappa)=%.5f  diff=%.5f" % (round(math.log10(X)), s, main, s-main))
L2 = math.log(math.log(10**8))
print("    secondary term log(1+kappa/log_2 X) at X=1e8 : %.4f (paper 0.62)" % math.log(1+kappa/L2))


# ---- MMR main-term validation ----
mu = 28.5; sig2 = 721.05; b=10; dg=1
print("\n=== MMR main term vs reality for g=S, b=10 (d_g=1, so pi_k(x)=pi(x))")
print(" x        k     actual    MMR main   ratio")
for x in (10**6, 10**7, 10**8):
    m = primes <= x
    pix = int(m.sum()); L = math.log(x, b)
    kpeak = int(round(mu*L))
    for k in (kpeak-40, kpeak, kpeak+40):
        actual = int((Sp[m]==k).sum())
        main = dg*pix/math.sqrt(2*math.pi*sig2*L)*math.exp(-(k-mu*L)**2/(2*sig2*L))
        print(" 1e%-2d  %5d  %9d  %10.1f   %.4f" % (round(math.log10(x)), k, actual, main, actual/main if main else float('nan')))
    tot_main = sum(dg*pix/math.sqrt(2*math.pi*sig2*L)*math.exp(-(k-mu*L)**2/(2*sig2*L)) for k in range(0,900))
    print("      total over all k: actual pi(x)=%d, summed main term=%.1f, ratio=%.4f" % (pix, tot_main, pix/tot_main))
    err = max(abs(int((Sp[m]==k).sum()) - dg*pix/math.sqrt(2*math.pi*sig2*L)*math.exp(-(k-mu*L)**2/(2*sig2*L))) for k in range(0,900))
    print("      max_k |actual - main| = %.1f ;  pi(x)/(log x)^{3/4} = %.1f" % (err, pix/math.log(x)**0.75))
