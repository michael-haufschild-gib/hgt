# THE MACHINE R3 (dyson) STEP 7: STRUCTURAL transport of the NODE's Berry-monopole test.
# Node test UNCHANGED: H = Rx*sx + Ry*sy + Rz*sz ; ground eigenstate ; Berry phase = -arg prod<psi_k|psi_{k+1}>.
# Only the FIELD is remapped by metaphor: magnetic field  <->  (object value, distance to symmetry axis):
#     R(s) = ( Re zeta(s), Im zeta(s), Re(s) - 1/2 ).
# Degeneracy R=0  <=>  zeta(s)=0 AND Re(s)=1/2  (on-line zero = Berry monopole).
import numpy as np, mpmath as mp
mp.mp.dps=25
sx=np.array([[0,1],[1,0]],complex); sy=np.array([[0,-1j],[1j,0]]); sz=np.array([[1,0],[0,-1]],complex)
def ground(R):
    Hm=R[0]*sx+R[1]*sy+R[2]*sz; w,v=np.linalg.eigh(Hm); return v[:,0]
def field(s):
    z=complex(mp.zeta(s)); return np.array([z.real, z.imag, s.real-0.5])
def berry_loop(center, r, N=600):
    states=[]
    for k in range(N):
        ph=2*np.pi*k/N; s=center+r*np.exp(1j*ph)
        R=field(s)
        if np.linalg.norm(R)<1e-12: return None  # hit degeneracy
        states.append(ground(R))
    prod=1+0j
    for k in range(N): prod*=np.vdot(states[k],states[(k+1)%N])
    return -np.angle(prod)
tests=[
 ("on-line zero rho1   0.5+14.1347i", 0.5+14.134725j, 0.5),
 ("on-line zero rho2   0.5+21.022i ", 0.5+21.02204j, 0.5),
 ("regular pt (no zero) 0.5+10i     ", 0.5+10.0j, 0.5),
 ("regular pt far       2.0+5i      ", 2.0+5.0j, 0.5),
 ("small loop on rho1 (r=0.2)       ", 0.5+14.134725j, 0.2),
 ("BIG loop 0.5+17.5i r=5 (encl 2 zeros 14.13,21.02 + 15.0?,16.0?)", 0.5+17.5j, 5.0),
]
print("Berry phase of H(s)=(Re z, Im z, Re s-1/2).sigma around loops (monopole => ~ +/- pi):")
for name,c,r in tests:
    bp=berry_loop(c,r)
    if bp is None: print(f"  {name}: hit degeneracy"); continue
    print(f"  {name}: berry={bp:+.4f}  (pi={np.pi:.4f})  |bp|/pi={abs(bp)/np.pi:.3f}")
