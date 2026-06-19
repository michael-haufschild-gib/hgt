#!/usr/bin/env python3.13
"""
The open inch, named: the de Bruijn-Newman constant as the total-positivity ONSET TIME
of the field's secular coefficients.

Secular coeffs  c_n = [w^n] Xi(sqrt w) = xi^{(2n)}(1/2)/(2n)!  (= xi(1/2) e_n(1/gamma^2)).
de Bruijn heat flow:  H_t(z) = int e^{t u^2} Phi(u) cos(z u) du,  H_0 = Xi.
In moments mu_{2n}(t)=int u^{2n} e^{tu^2}Phi,  d/dt mu = shift-up, giving
     c_n(t) = sum_k (t^k/k!) * (2n+2k)!/(2n)! * c_{n+k}.
de Bruijn-Newman:  H_t has ONLY REAL zeros  <=>  t >= Lambda.   RH <=> Lambda <= 0.
Rodgers-Tao 2018:  Lambda >= 0.   Hence (given RH numerically) genuine zeta sits at Lambda = 0:
the secular coefficients are at the EXACT total-positivity boundary -- the no-margin.

Detectors (GORZ Jensen / Turan, scale-free): the Jensen polynomials J_{d,n} hyperbolic <=> RH.
  Turan/J2 margin:  m_n = c_n^2/(c_{n-1}c_{n+1}) - 1   (>=0 = TP2 = J_{2,n} hyperbolic).
  J3 discriminant:  disc of  sum_{j<=3} C(3,j) c_{n+j} X^j   (>=0 = J_{3,n} hyperbolic).

We show: (A) genuine detectors >=0 at t=0 with margins shrinking in n (-> 0 = no-margin);
         (B) forward heat (t>0) strengthens TP, backward heat (t<0) destroys it (complex zeros);
         (C) the TP-onset time t*(N) (where the worst detector among n<=N hits 0) -> 0^- as N grows
             -- a numerical realization of Lambda = 0 as the secular total-positivity boundary.
"""
import mpmath as mp

mp.mp.dps = 60

def xi(s):
    return (s*(s-1)/2) * mp.pi**(-s/2) * mp.gamma(s/2) * mp.zeta(s)

def true_coeffs(M, radius):
    g = lambda z: xi(mp.mpf('0.5') + z)
    tc = mp.taylor(g, mp.mpf(0), 2*M, method='quad', radius=radius)
    return [mp.re(tc[2*n]) for n in range(M+1)]

def heat(c, t, n, Kmax):
    s = mp.mpf(0)
    for k in range(0, Kmax+1):
        m = n + k
        if m >= len(c):
            break
        s += mp.power(t, k)/mp.factorial(k) * mp.factorial(2*n+2*k)/mp.factorial(2*n) * c[m]
    return s

def turan_margin(c, n):
    return c[n]**2/(c[n-1]*c[n+1]) - 1

def jensen_disc3(c, n):
    a0, a1, a2, a3 = c[n], 3*c[n+1], 3*c[n+2], c[n+3]      # J_{3,n}=a3 X^3+a2 X^2+a1 X+a0
    return 18*a3*a2*a1*a0 - 4*a2**3*a0 + a2**2*a1**2 - 4*a3*a1**3 - 27*a3**2*a0**2

def heated_vector(c, t, Ncoef, Kmax):
    return [heat(c, t, n, Kmax) for n in range(Ncoef)]

def main():
    M, Kmax = 16, 6
    radius = mp.mpf(3)
    c = true_coeffs(M, radius)
    Ncoef = M - Kmax + 1                       # heat(.,.,n,Kmax) defined for n <= M-Kmax
    print(f"=== true secular coefficients (M={M}, dps={mp.mp.dps}) ===")
    print(f"  c_0=xi(1/2)={mp.nstr(c[0],12)}  c_1/c_0={mp.nstr(c[1]/c[0],14)}  "
          f"secondzeta(2)={mp.nstr(mp.secondzeta(2),14)}")
    # convergence check of the heat series (Kmax vs Kmax-2) at a sample
    s1 = heat(c, mp.mpf('0.1'), 3, Kmax)
    s0 = heat(c, mp.mpf('0.1'), 3, Kmax-2)
    print(f"  heat-series convergence at (t=0.1,n=3): |K={Kmax} - K={Kmax-2}| = {mp.nstr(abs(s1-s0),4)} (small => converged)")

    print("\n=== (A) genuine detectors at t=0 (RH-consistent; margins shrink in n = no-margin) ===")
    nmaxT = Ncoef - 2
    for n in range(1, nmaxT+1):
        print(f"  n={n:2d}: Turan margin={mp.nstr(turan_margin(c,n),5)}   J3 disc {'>=0' if jensen_disc3(c,n)>=0 else '<0'}")

    print("\n=== (B) heat flow: min Turan margin and #J3-hyperbolic vs t ===")
    grid = ['0.30','0.15','0.08','0.04','0.02','0.00','-0.02','-0.04','-0.08','-0.15','-0.30']
    for ts in grid:
        t = mp.mpf(ts)
        cc = heated_vector(c, t, Ncoef, Kmax)
        margins = [turan_margin(cc, n) for n in range(1, Ncoef-1)]
        j3 = [jensen_disc3(cc, n) for n in range(0, Ncoef-3)]
        minm = min(margins)
        nhyp = sum(1 for d in j3 if d >= 0)
        print(f"  t={ts:6s}: min Turan margin={mp.nstr(minm,5):>12}   J3-hyperbolic {nhyp}/{len(j3)}")

    print("\n=== (C) TP-onset time t*(N): worst detector among n<=N crosses 0 (expect t*->0^- as N grows) ===")
    def min_margin_at(t, N):
        cc = heated_vector(c, t, Ncoef, Kmax)
        return min(turan_margin(cc, n) for n in range(1, N+1))
    for N in range(3, nmaxT+1):
        # bisection for t* in [-0.5, 0]: min_margin_at(0,N)>0, find t where it = 0
        lo, hi = mp.mpf('-0.6'), mp.mpf('0')
        if min_margin_at(hi, N) <= 0:
            print(f"  N={N}: min margin already <=0 at t=0"); continue
        if min_margin_at(lo, N) > 0:
            print(f"  N={N}: t* < -0.6 (detectors still positive)"); continue
        for _ in range(40):
            mid = (lo+hi)/2
            if min_margin_at(mid, N) > 0:
                hi = mid
            else:
                lo = mid
        print(f"  N={N}: t* = {mp.nstr((lo+hi)/2, 6)}   (TP-onset; -> 0 as N grows = Lambda=0 no-margin)")

if __name__ == "__main__":
    main()
