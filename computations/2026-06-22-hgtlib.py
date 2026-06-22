"""Shared library for the gpt/37 reciprocal-seam-squared computations.
All matrices SPD under RH (actual zeros on line). High-precision (mpmath)."""
import mpmath as mp

def load_zeros(path, n=None):
    g=[]
    with open(path) as f:
        for line in f:
            s=line.strip()
            if s: g.append(mp.mpf(s))
    return g[:n] if n else g

def y_atoms(gammas):
    "on-line reciprocal atoms y_n = 1/gamma_n^2 > 0"
    return [1/(g*g) for g in gammas]

def T_moments(ys, kmax):
    "zero moments T_k = 2 sum_n y_n^k from a finite atom list (truncated; for fakes/injection)"
    T=[None]*(kmax+1)
    pows=[mp.mpf(1) for _ in ys]
    for k in range(1,kmax+1):
        for i in range(len(ys)): pows[i]*=ys[i]
        T[k]=2*mp.fsum(pows)
    return T

def T_moments_exact(kmax):
    """EXACT zeta zero moments T_k = 2 sum_{gamma>0} gamma^{-2k} (NO zero-truncation):
    c_{2k}=[w^{2k}] log Xi(w), Xi(w)=xi(1/2+w) has zeros exactly at w=+-i gamma_n.
      [w^{2k}]log(1-4w^2)       = -4^k/k
      [w^{2k}]logGamma(1/4+w/2) = polygamma(2k-1,1/4)/((2k)! 4^k)
      [w^{2k}]log zeta(1/2+w)   = g_{2k} via log-of-series recurrence on a_m=zeta^{(m)}(1/2)/m!
      T_k = 2(-1)^{k+1} k c_{2k}.   (cancellation ~0.6*2k digits; set mp.mp.dps accordingly)"""
    M=2*kmax+1
    a=[mp.zeta(mp.mpf('0.5'),1,m)/mp.factorial(m) for m in range(M+1)]
    g=[mp.mpf(0)]*(M+1); g[0]=mp.log(a[0])
    for m in range(1,M+1):
        s=mp.fsum(n*g[n]*a[m-n] for n in range(1,m))
        g[m]=(m*a[m]-s)/(m*a[0])
    T=[None]*(kmax+1)
    for k in range(1,kmax+1):
        c=-mp.power(4,k)/k + mp.polygamma(2*k-1,mp.mpf(1)/4)/(mp.factorial(2*k)*mp.power(4,k)) + g[2*k]
        T[k]=2*((-1)**(k+1))*k*c
    return T

def add_quartet_moments(T, beta, gamma0, weight=2):
    """T_k += contribution of an off-line FE quartet w in {+-d +- i g0}, d=beta-1/2, g0=gamma0,
    atom y=-w^{-2}, folded weight `weight` per orbit (weight/2 per the 2 conj members per orbit).
    Returns NEW real moment list (imag parts cancel by conjugate symmetry)."""
    d=mp.mpf(beta)-mp.mpf('0.5'); g0=mp.mpf(gamma0)
    ws=[mp.mpc(d,g0), mp.mpc(-d,g0), mp.mpc(d,-g0), mp.mpc(-d,-g0)]
    ys=[-1/(w*w) for w in ws]
    out=[None]*len(T)
    for k in range(1,len(T)):
        out[k]=mp.re(T[k]+(mp.mpf(weight)/2)*mp.fsum(y**k for y in ys))
    return out

def H0_matrix(d, T):
    "Q_0 moment matrix H^0_{ij}=T_{i+j+1}, i,j=0..d"
    return mp.matrix([[T[i+j+1] for j in range(d+1)] for i in range(d+1)])

def Ptriv(m):
    "P_m = sum_{j>=1} (2j+1/2)^{-2m} = 4^{-m} zeta(2m, 5/4)  (exact, Hurwitz)"
    return mp.power(4,-m)*mp.zeta(2*m, mp.mpf(5)/4)

def Mtriv_matrix(d):
    "trivial-zero protector moment matrix; M_{ij}=(-1)^{i+j} P_{i+j+1}"
    P=[None]+[Ptriv(m) for m in range(1,2*d+2)]
    return mp.matrix([[ (1 if (i+j)%2==0 else -1)*P[i+j+1] for j in range(d+1)] for i in range(d+1)])

def gen_eig_sym(A, B):
    """generalized symmetric eigenproblem A x = mu B x, A,B SPD.
       returns (eigvals sorted asc, eigvecs columns in original coords)."""
    L=mp.cholesky(B)                      # B = L L^T
    Linv=mp.inverse(L)
    C=Linv*A*Linv.T                       # symmetric
    C=(C+C.T)/2
    E,Q=mp.eigsy(C)                        # C = Q diag(E) Q^T
    # generalized eigvecs: x = L^{-T} q
    LinvT=Linv.T
    V=LinvT*Q
    # sort ascending
    idx=sorted(range(len(E)), key=lambda i:E[i])
    evals=[E[i] for i in idx]
    Vs=mp.matrix(A.rows, A.rows)
    for c,i in enumerate(idx):
        for r in range(A.rows): Vs[r,c]=V[r,i]
    return evals, Vs

def overlap_with_pole(c):
    "abs cosine between coeff vector c (mp matrix col, length n) and pole u_i=(-4)^i"
    n=c.rows
    u=mp.matrix([mp.power(-4,i) for i in range(n)])
    num=abs(mp.fsum(c[i]*u[i] for i in range(n)))
    den=mp.sqrt(mp.fsum(c[i]**2 for i in range(n)))*mp.sqrt(mp.fsum(u[i]**2 for i in range(n)))
    return num/den
