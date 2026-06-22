"""Dirichlet L-function reciprocal-seam machinery (real primitive characters).
Completed Xi_chi(w)=xi_chi(1/2+w), xi_chi(s)=(q/pi)^{(s+a)/2} Gamma((s+a)/2) L(s,chi),
a=0 (even chi) / 1 (odd chi); real chi => Xi_chi even, zeros = nontrivial zeros of L.
Moments T_k^chi = 2 sum_{gamma>0} gamma^{-2k} = 2(-1)^{k+1} k c_{2k}^chi, where
  c_{2k}^chi = polygamma(2k-1,b)/((2k)! 4^k) + g_{2k}^chi,   b=(a+1/2)/2 (=1/4 even, 3/4 odd),
  g_{2k}^chi=[w^{2k}] log L(1/2+w,chi) via log-of-series recurrence on a_m^chi=L^{(m)}(1/2,chi)/m!.
NO log(1-4w^2) term (L has no pole). Protector trivial zeros at s=-a-2l (l>=0), images
  y_l=-(2l+a+1/2)^{-2}, weight (2l+a+1/2)^{-2}; P_m^chi=4^{-m} zeta(2m,(a+1/2)/2)."""
import mpmath as mp

# real primitive characters: (q, parity a, [chi(1..q-1)])
CHARS = {
 'chi3':  (3, 1, [1,-1]),
 'chi4':  (4, 1, [1,0,-1]),          # L=beta (Dirichlet)
 'chi5':  (5, 0, [1,-1,-1,1]),       # (r/5)
 'chi7':  (7, 1, [1,1,-1,1,-1,-1]),  # (r/7)
 'chi8':  (8, 0, [1,0,-1,0,-1,0,1]), # (2/n)
}

def L_taylor(name, M):
    "a_m = L^{(m)}(1/2,chi)/m!, m=0..M, via L(1/2+w)=q^{-(1/2+w)} sum_r chi(r) zeta(1/2+w, r/q)."
    q,a,chi = CHARS[name]
    half=mp.mpf('0.5'); lq=mp.log(q)
    # exp series e_j = [w^j] q^{-(1/2+w)} = q^{-1/2} (-lq)^j / j!
    e=[mp.power(q,-half)*mp.power(-lq,j)/mp.factorial(j) for j in range(M+1)]
    a_series=[mp.mpf(0)]*(M+1)
    for r in range(1,q):
        c=chi[r-1]
        if c==0: continue
        # h_i = [w^i] zeta(1/2+w, r/q) = zeta^{(i)}(1/2,r/q)/i!
        h=[mp.zeta(half, mp.mpf(r)/q, i)/mp.factorial(i) for i in range(M+1)]
        # convolve e*h, add chi(r)* ...
        for m in range(M+1):
            s=mp.fsum(e[j]*h[m-j] for j in range(m+1))
            a_series[m]+=c*s
    return a_series  # = a_m^chi

def T_moments_L(name, kmax):
    q,a,chi = CHARS[name]
    M=2*kmax+1
    A=L_taylor(name,M)
    g=[mp.mpf(0)]*(M+1); g[0]=mp.log(A[0])
    for m in range(1,M+1):
        s=mp.fsum(n*g[n]*A[m-n] for n in range(1,m))
        g[m]=(m*A[m]-s)/(m*A[0])
    b=(mp.mpf(a)+mp.mpf('0.5'))/2
    T=[None]*(kmax+1)
    for k in range(1,kmax+1):
        c=mp.polygamma(2*k-1,b)/(mp.factorial(2*k)*mp.power(4,k)) + g[2*k]
        T[k]=2*((-1)**(k+1))*k*c
    return T

def Ptriv_L(m, a):
    "P_m^chi = sum_{l>=0}(2l+a+1/2)^{-2m} = 4^{-m} zeta(2m,(a+1/2)/2)"
    return mp.power(4,-m)*mp.zeta(2*m, (mp.mpf(a)+mp.mpf('0.5'))/2)

def Mtriv_L_matrix(d, a):
    P=[None]+[Ptriv_L(m,a) for m in range(1,2*d+2)]
    return mp.matrix([[ (1 if (i+j)%2==0 else -1)*P[i+j+1] for j in range(d+1)] for i in range(d+1)])

def xi_chi(name, s):
    "completed L (real on critical line for real chi); for zero-finding cross-check."
    q,a,chi=CHARS[name]
    L=mp.power(q,-s)*mp.fsum(chi[r-1]*mp.zeta(s,mp.mpf(r)/q) for r in range(1,q) if chi[r-1]!=0)
    return mp.power(mp.mpf(q)/mp.pi,(s+a)/2)*mp.gamma((s+a)/2)*L
