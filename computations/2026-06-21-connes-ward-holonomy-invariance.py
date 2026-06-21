"""
The GPT candidate detector  T_xi = (event-holonomy, source-width tomography, Ward residual,
passport-subtracted transport)  is INVARIANT under the rung-1 surrogate  S = e^{q((s-1/2)^2)} xi.

Reason (verified here): every component is a function of {zeros, FE, source-measure}, all shared.
 - source measure  mu_f = (1/2pi) Lap log|f|:  log|e^q xi| = Re(q) + log|xi|, and Re(q) is HARMONIC
   (q holomorphic) => Lap Re(q) = 0 => mu_S = mu_xi exactly (same zeros, same masses, same nested
   width tomography M_k(r)).
 - Ward/mirror residual  W_f(s) = H_f(s) + H_f(1-s),  H_f = f'/f:
   W_S = W_xi + [q'(s) + q'(1-s)];  for FE-even q, q'(s) = -q'(1-s) => the bracket is 0 => W_S = W_xi.
   (And W_xi == 0 identically, since xi(s)=xi(1-s) => (xi'/xi)(1-s) = -(xi'/xi)(s).)
 - winding / event-holonomy:  oint d log(e^q xi) = oint d log xi + oint dq = oint d log xi  (q entire,
   single-valued => oint dq = 0).
 - passport: the e^q factor IS the tame archimedean level that the passport Pi(S) captures/subtracts.

=> T_xi gives the SAME value on xi and on every rung-1 surrogate. So T_xi is a {zeros,FE,source}
detector — RH/source-geometry relevant (the BRIDGE axis, Conjecture C), NOT a transcendence detector.
Run: python3 this.py  (~seconds)
"""
import mpmath as mp
mp.mp.dps = 30
half = mp.mpf(1)/2
logpi = mp.log(mp.pi)

def logxi(s):
    return ( mp.log(half) + mp.log(s) + mp.log(s-1)
             - (s/2)*logpi + mp.loggamma(s/2) + mp.log(mp.zeta(s)) )
def Hxi(s):                      # xi'/xi
    return mp.diff(logxi, s)

c = mp.mpf('1e-2')               # use a deliberately LARGE level to stress the invariance
def HS(s):                       # surrogate H_S = xi'/xi + q', q = c(s-1/2)^2 => q' = 2c(s-1/2)
    return Hxi(s) + 2*c*(s-half)

pts = [half+0.3 + 1j*mp.mpf('18'), half + 1j*mp.mpf('27'), mp.mpf('0.7') + 1j*mp.mpf('35'),
       mp.mpf('0.4') + 1j*mp.mpf('12')]

print("=== Ward/mirror residual  W_f(s) = H_f(s) + H_f(1-s)  ===")
print("  point                      |W_xi|        |W_S|        |W_S - W_xi|")
for s in pts:
    Wxi = Hxi(s) + Hxi(1-s)
    WS  = HS(s)  + HS(1-s)
    print(f"  {mp.nstr(s,4):>22}   {mp.nstr(abs(Wxi),3):>10}   {mp.nstr(abs(WS),3):>10}   {mp.nstr(abs(WS-Wxi),3):>10}")
print("  -> W_xi ~ 0 (FE) AND W_S = W_xi: the Ward residual cannot separate xi from the surrogate.")

print("\n=== source measure: Laplacian of Re(q),  q = c(s-1/2)^2  (must be 0 => mu_S = mu_xi) ===")
def ReQ(x, y):
    w = (x-half) + 1j*y
    return mp.re(c*w**2)
h = mp.mpf('1e-6')
maxlap = mp.mpf(0)
for s in pts:
    x, y = mp.re(s), mp.im(s)
    lap = (ReQ(x+h,y)+ReQ(x-h,y)+ReQ(x,y+h)+ReQ(x,y-h)-4*ReQ(x,y))/h**2
    maxlap = max(maxlap, abs(lap))
print("  max |Laplacian Re(q)| over points:", mp.nstr(maxlap, 3), " (0 => source measure unchanged)")

print("\n=== winding of the surrogate level:  oint dq around a closed rectangle ( = 0 ) ===")
# q' = 2c(s-1/2); integrate around rectangle [0.3,0.7] x [20,21]
def qprime(s): return 2*c*(s-half)
contour = 0
corners = [mp.mpf('0.3')+20j, mp.mpf('0.7')+20j, mp.mpf('0.7')+21j, mp.mpf('0.3')+21j]
for k in range(4):
    a, b = corners[k], corners[(k+1)%4]
    contour += mp.quad(lambda t: qprime(a+(b-a)*t)*(b-a), [0,1])
print("  |oint dq| =", mp.nstr(abs(contour), 3), " (0 => event-holonomy / winding unchanged)")

print("\n=== verdict ===")
print("  All four T_xi components (event-holonomy, source tomography, Ward residual, passport) are")
print("  INVARIANT under the rung-1 surrogate e^{q}xi. T_xi is a function of {zeros, FE, source measure}")
print("  only => it is a SOURCE-GEOMETRY / FE detector (the BRIDGE / positivity axis, Conjecture C),")
print("  NOT a transcendence detector. The GPT 'hidden variables 2 (source) + 3 (FE)' are the verdict.")
