"""comp82 — boundary-channel completeness (gpt/48 §7e): where does a fake's negative direction live?

comp81 sign-fake: H^0_flip = H^A - H^P has inertia (d,1) — ONE negative square that the rank-one Γ-atom
repair cannot reach (the direction the scalar s_d is blind to). QUESTION: does that negative eigenvector
u_- lie in the span of the prolate/archimedean 4N+1 boundary channels
   v_N = v(y_N),  y_N = -(2N+1/2)^{-2}   (N=0: y=-4 pole; N=1: y=-0.16=y_*; N>=2: protector tail)
or in the finite-place BULK orthogonal to them?
 - fast residual decay in r  => the 4N+1 channel basis is FAITHFUL (finite-rank boundary Weyl catches the fake);
 - slow/no decay            => the defect lives in the bulk, channels are decorative/incomplete.
Control: a REAL off-line quartet fake (push s_d<0), same test.  Outcome unknown a priori."""
import mpmath as mp
A_STAR=mp.mpf('0.16'); Y_STAR=-A_STAR

def cA_cP(kmax):
    M=2*kmax+1
    a=[mp.zeta(mp.mpf('0.5'),1,m)/mp.factorial(m) for m in range(M+1)]
    g=[mp.mpf(0)]*(M+1); g[0]=mp.log(a[0])
    for m in range(1,M+1):
        s=mp.fsum(n*g[n]*a[m-n] for n in range(1,m)); g[m]=(m*a[m]-s)/(m*a[0])
    cA=[None]*(kmax+1); cP=[None]*(kmax+1)
    for k in range(1,kmax+1):
        cA[k]=-mp.power(4,k)/k + mp.polygamma(2*k-1,mp.mpf(1)/4)/(mp.factorial(2*k)*mp.power(4,k))
        cP[k]=g[2*k]
    return cA,cP
def Tfrom(c,kmax): return [None]+[2*((-1)**(k+1))*k*c[k] for k in range(1,kmax+1)]
def vy(y,d): return mp.matrix([[y**i] for i in range(d+1)])
def H(T,d): return mp.matrix([[T[i+j+1] for j in range(d+1)] for i in range(d+1)])

def neg_eigvec(Msym):
    "smallest-eigenvalue eigenvector of a symmetric matrix (the negative direction)."
    E,V=mp.eigsy((Msym+Msym.T)/2)
    idx=min(range(len(E)),key=lambda i:E[i])
    u=mp.matrix([V[r,idx] for r in range(V.rows)])
    nrm=mp.sqrt(mp.fsum(u[r]**2 for r in range(u.rows)));
    return mp.matrix([u[r]/nrm for r in range(u.rows)]), E[idx]

def residual_after_channels(u,d,rmax):
    "||u - proj onto span{v_0..v_r}|| (Euclidean), r=0..rmax, u unit."
    out=[]
    cols=[]
    for N in range(rmax+1):
        yN=-mp.power(2*N+mp.mpf('0.5'),-2)
        cols.append(vy(yN,d))
        Vr=mp.matrix(d+1,len(cols))
        for j,c in enumerate(cols):
            for i in range(d+1): Vr[i,j]=c[i]
        # orthogonal projection P = Vr (Vr^T Vr)^{-1} Vr^T ; residual = ||u - P u||
        G=Vr.T*Vr
        coef=mp.inverse(G)*(Vr.T*u)
        proj=Vr*coef
        res=mp.sqrt(mp.fsum((u[i]-proj[i])**2 for i in range(d+1)))
        out.append(float(res))
    return out

def quartet_T(Tz,beta,g0,w,kmax):
    d=mp.mpf(beta)-mp.mpf('0.5'); g0=mp.mpf(g0)
    ws=[mp.mpc(d,g0),mp.mpc(-d,g0),mp.mpc(d,-g0),mp.mpc(-d,-g0)]
    ys=[-1/(z*z) for z in ws]
    return [None]+[mp.re(Tz[k]+(mp.mpf(w)/2)*mp.fsum(y**k for y in ys)) for k in range(1,kmax+1)]

for d in (8,10,12):
    mp.mp.dps=int(6.5*d)+160; kmax=2*d+1
    cA,cP=cA_cP(kmax)
    cFlip=[None]+[cA[k]-cP[k] for k in range(1,kmax+1)]
    cZeta=[None]+[cA[k]+cP[k] for k in range(1,kmax+1)]
    Tflip=Tfrom(cFlip,kmax); Tz=Tfrom(cZeta,kmax)
    # (1) sign-flip fake: H^0_flip has inertia (d,1); take its negative eigenvector
    H0f=H(Tflip,d); u,lam=neg_eigvec(H0f)
    res_flip=residual_after_channels(u,d,6)
    ov_v1=abs((vy(Y_STAR,d).T*u)[0])/mp.sqrt((vy(Y_STAR,d).T*vy(Y_STAR,d))[0])  # |cos| with v_*
    # (2) real off-line quartet fake (push negative): add quartet to zeta with weight pushing s_d<0
    Tq=quartet_T(Tz,'1.0',8,12,kmax)         # off-line beta=1, low g0, strong weight
    H0q=H(Tq,d); uq,lamq=neg_eigvec(H0q)
    res_q=residual_after_channels(uq,d,6) if lamq<0 else None
    print(f"d={d}:")
    print(f"  sign-fake H^0_flip: min-eig={mp.nstr(lam,3)}, |cos(u,v_*)|={mp.nstr(ov_v1,4)}")
    print(f"    residual after r channels (N=0..6): {[round(x,4) for x in res_flip]}")
    if res_q is not None:
        print(f"  off-line-quartet H^0: min-eig={mp.nstr(lamq,3)}")
        print(f"    residual after r channels (N=0..6): {[round(x,4) for x in res_q]}")
    else:
        print(f"  off-line-quartet H^0: min-eig={mp.nstr(lamq,3)} (>=0, no negative dir at this d)")
print("\nReading: fast residual->0 means the 4N+1 prolate channels capture the fake's negative direction (faithful);")
print("slow/flat residual means it lives in the finite-place bulk (channels incomplete).")
print("DONE")
