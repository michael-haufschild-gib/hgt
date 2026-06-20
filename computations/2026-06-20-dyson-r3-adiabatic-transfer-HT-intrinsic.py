# R3 refinement: same Berry-monopole transport, but z-component INTRINSIC (from the FE), not hand-inserted.
# R(s) = (Re zeta(s), Im zeta(s), log|chi(s)|), chi=zeta(s)/zeta(1-s).  log|chi|=0 <=> Re s=1/2 (THEOREM |chi|=1).
import numpy as np, mpmath as mp
mp.mp.dps=25
sx=np.array([[0,1],[1,0]],complex); sy=np.array([[0,-1j],[1j,0]]); sz=np.array([[1,0],[0,-1]],complex)
def ground(R):
    Hm=R[0]*sx+R[1]*sy+R[2]*sz; w,v=np.linalg.eigh(Hm); return v[:,0]
def field(s):
    z=complex(mp.zeta(s)); z2=complex(mp.zeta(1-s))
    if abs(z2)<1e-300: zc=1e6
    else: zc=float(mp.log(abs(z/z2))) if abs(z)>1e-300 else -50.0
    return np.array([z.real, z.imag, zc])
def berry_loop(center,r,N=600):
    st=[]
    for k in range(N):
        s=center+r*np.exp(1j*2*np.pi*k/N); R=field(s)
        n=np.linalg.norm(R)
        if n<1e-9: return None
        st.append(ground(R))
    prod=1+0j
    for k in range(N): prod*=np.vdot(st[k],st[(k+1)%N])
    return -np.angle(prod)
tests=[("on-line zero rho1",0.5+14.134725j,0.5),("on-line zero rho2",0.5+21.02204j,0.5),
       ("regular 0.5+10i",0.5+10j,0.5),("regular far 2+5i",2+5j,0.5),
       ("on rho1 small r=0.15",0.5+14.134725j,0.15)]
print("INTRINSIC field R=(Re z,Im z,log|chi|); Berry phase around loops (monopole=>+/-pi):")
for nm,c,r in tests:
    bp=berry_loop(c,r)
    print(f"  {nm:22s}: {'degeneracy' if bp is None else f'berry={bp:+.4f}  |bp|/pi={abs(bp)/np.pi:.3f}'}")
