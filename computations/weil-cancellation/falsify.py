"""
Falsification test: is the arithmetic's off-line-zero cancellation reachable at FINITE
truncation, or genuinely infinitary?

Objects (symmetric completions, real on Re=1/2, invariant under s -> 1-s):
  A(s)  = (1/2) s (s-1) pi^{-s/2} Gamma(s/2)
  SUM   Xi_N^S(s) = A(s) D_N(s)   + A(1-s) D_N(1-s),     D_N(s)=sum_{n<=N} n^{-s}
  PROD  Xi_P^P(s) = A(s) E_P(s)   + A(1-s) E_P(1-s),     E_P(s)=prod_{p<=P} (1-p^{-s})^{-1}

Off-line zeros come in quadruples {rho,1-rho,conj rho,1-conj rho}; count
  M(T) = #zeros in {Re>1/2, Im>0} up to height T  (argument principle / winding number)
On-line zeros: sign changes of the real function t -> Xi(1/2+it) on (0,T].
"""
import sys
from mpmath import mp, mpf, mpc, pi, gamma, digamma, log, e, sqrt, arg, floor

mp.dps = 30

PRIMES = [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47]

def A(s):
    return mpf('0.5') * s * (s-1) * pi**(-s/2) * gamma(s/2)

def Alog_deriv(s):   # A'/A
    return 1/s + 1/(s-1) - mpf('0.5')*log(pi) + mpf('0.5')*digamma(s/2)

def make_sum(N):
    ns = list(range(1, N+1))
    def D(s):
        return sum(mpf(n)**(-s) for n in ns)
    def Dp(s):       # D'
        return sum(-log(n)*mpf(n)**(-s) for n in ns)
    return D, Dp

def make_prod(P):
    ps = [p for p in PRIMES if p <= P]
    def E(s):
        r = mpf(1)
        for p in ps:
            r *= 1/(1 - mpf(p)**(-s))
        return r
    def Ep(s):       # E' = E * (E'/E), E'/E = -sum_p log p * p^{-s}/(1-p^{-s})
        ld = sum(-log(p)*mpf(p)**(-s)/(1 - mpf(p)**(-s)) for p in ps)
        return E(s)*ld
    return E, Ep

def build_Xi(D, Dp):
    def Xi(s):
        return A(s)*D(s) + A(1-s)*D(1-s)
    def Xip(s):
        return (Alog_deriv(s)*A(s)*D(s) + A(s)*Dp(s)
                - Alog_deriv(1-s)*A(1-s)*D(1-s) - A(1-s)*Dp(1-s))
    return Xi, Xip

def winding_count(Xi, x0, x1, y0, y1, base_step=mpf('0.25')):
    """#zeros in rectangle [x0,x1]x[y0,y1] via change of arg / 2pi (adaptive)."""
    corners = [mpc(x0,y0), mpc(x1,y0), mpc(x1,y1), mpc(x0,y1), mpc(x0,y0)]
    total = mpf(0)
    for k in range(4):
        a = corners[k]; b = corners[k+1]
        L = abs(b-a)
        nsteps = max(4, int(L/base_step)+1)
        prev = Xi(a)
        prevarg = arg(prev)
        i = 1
        while i <= nsteps:
            t = mpf(i)/nsteps
            z = a + (b-a)*t
            val = Xi(z)
            curarg = arg(val)
            d = curarg - prevarg
            # unwrap to (-pi,pi]
            while d > pi:  d -= 2*pi
            while d <= -pi: d += 2*pi
            if abs(d) > pi*mpf('0.7'):
                # refine this subinterval by bisection sampling
                sub = 8
                pa = prevarg
                for j in range(1, sub+1):
                    tt = (mpf(i-1) + mpf(j)/sub)/nsteps
                    zz = a + (b-a)*tt
                    ca = arg(Xi(zz))
                    dd = ca - pa
                    while dd > pi:  dd -= 2*pi
                    while dd <= -pi: dd += 2*pi
                    total += dd
                    pa = ca
                prevarg = pa
                i += 1
                continue
            total += d
            prevarg = curarg
            i += 1
    return int(floor(total/(2*pi) + mpf('0.5')))

def online_count(Xi, T, step=mpf('0.05'), delta=mpf('0.01')):
    t = delta
    prev = Xi(mpc(mpf('0.5'), t)).real
    cnt = 0
    while t < T:
        t += step
        cur = Xi(mpc(mpf('0.5'), t)).real
        if prev == 0: prev = cur; continue
        if (prev > 0) != (cur > 0):
            cnt += 1
        prev = cur
    return cnt

def census(label, Xi, Xip, Ts, B=mpf('4'), delta=mpf('0.01')):
    row = {'label': label}
    row['online_T'] = online_count(Xi, Ts[-1])
    Ms = []
    for T in Ts:
        M = winding_count(Xi, mpf('0.5')+delta, B, delta, mpf(T))
        Ms.append((float(T), M))
    row['offline_upper_right'] = Ms   # M(T): off-line zeros with Re>1/2, Im>0 up to T
    # first onset height (coarse)
    onset = None
    for (T,M) in Ms:
        if M > 0:
            onset = T; break
    row['onset'] = onset
    return row

def main():
    which = sys.argv[1] if len(sys.argv) > 1 else 'test'
    Ts = [20, 40, 60, 80]
    if which == 'test':
        D,Dp = make_sum(3)
        Xi,Xip = build_Xi(D,Dp)
        s = mpc(mpf('0.5'), 14.13)
        print("reality check Im Xi(1/2+14.13i) =", float(Xi(s).imag))
        print("symmetry check Xi(s)-Xi(1-s) =", float(abs(Xi(mpc('0.3','5'))-Xi(mpc('0.7','-5')))))
        import time
        t0=time.time()
        r = census('SUM N=3', Xi, Xip, [20,40,60])
        print(r); print("elapsed", time.time()-t0)
    elif which == 'run':
        rows = []
        for N in [2,3,5,8,13]:
            D,Dp = make_sum(N)
            Xi,Xip = build_Xi(D,Dp)
            r = census(f'SUM N={N} (AFE~{float(2*pi*N*N):.0f})', Xi, Xip, Ts)
            rows.append(r); print(r, flush=True)
        for P in [2,3,5,7,11,13]:
            E,Ep = make_prod(P)
            Xi,Xip = build_Xi(E,Ep)
            npr = len([p for p in PRIMES if p<=P])
            r = census(f'PROD P={P} ({npr} primes)', Xi, Xip, Ts)
            rows.append(r); print(r, flush=True)
        print("=== DONE ===")

if __name__ == '__main__':
    main()
