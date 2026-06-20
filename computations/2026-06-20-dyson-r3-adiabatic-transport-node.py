# THE MACHINE R3 (dyson). NODE = Adiabatic transport of eigenstates (Berry connection).
# STEP 6: RUNNABLE tests of the adiabatic constraints ON THE NODE (spin-1/2, H(R)=R.sigma).
import numpy as np
sx=np.array([[0,1],[1,0]],complex); sy=np.array([[0,-1j],[1j,0]]); sz=np.array([[1,0],[0,-1]],complex)
def H(R): x,y,z=R; return x*sx+y*sy+z*sz
def ground(R):
    w,v=np.linalg.eigh(H(R)); return v[:,0]   # lowest eigenvalue eigenvector

# T1: adiabatic fidelity vs transport SPEED. Path: tilt field from +z to -z through equator.
def fidelity_vs_speed(Ttot, N=4000):
    ts=np.linspace(0,1,N); dt=(ts[1]-ts[0])*Ttot
    psi=ground((0,0,1.0))
    for t in ts:
        th=np.pi*t                    # polar angle 0->pi
        R=(np.sin(th)*0.0, 0.0, np.cos(th)); R=(0.3*np.sin(th),0.0,np.cos(th))
        # crank-nicolson step
        Hm=H(R); U=np.linalg.inv(np.eye(2)+0.5j*dt*Hm)@(np.eye(2)-0.5j*dt*Hm)
        psi=U@psi
    g=ground((0.0,0.0,-1.0)); return abs(np.vdot(g,psi))**2
print("T1 adiabatic fidelity (->1 as slow):")
for Ttot in [1,5,20,80,200]:
    print(f"  Ttot={Ttot:4d}  fidelity={fidelity_vs_speed(Ttot):.5f}")

# T2: Berry phase around a closed loop = solid angle. Loop = circle at polar angle theta.
def berry_phase(theta, N=2000):
    phis=np.linspace(0,2*np.pi,N); gam=0.0; prev=None; first=None
    for ph in phis:
        R=(np.sin(theta)*np.cos(ph),np.sin(theta)*np.sin(ph),np.cos(theta))
        g=ground(R)
        if prev is not None:
            ov=np.vdot(prev,g); gam+=np.angle(ov)   # discrete parallel transport
        else: first=g
        prev=g
    gam+=np.angle(np.vdot(prev,first))
    return -gam
print("T2 Berry phase vs predicted -(1/2)*solidangle = -pi(1-cos theta):")
for theta in [0.5,1.0,1.5,2.0]:
    pred=-np.pi*(1-np.cos(theta))
    bp=berry_phase(theta)
    # bring to same branch
    d=(bp-pred+np.pi)%(2*np.pi)-np.pi
    print(f"  theta={theta:.2f}  berry={bp:+.4f}  pred={pred:+.4f}  diff(mod2pi)={d:+.2e}")
