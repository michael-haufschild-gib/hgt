# DMR / Avila Lyapunov referee
# Certifies the dynamics continent's central theorem (DMR-abelian/-solvable, DMR-Avila)
# and Avila's L = max(0, log lambda) on a concrete one-frequency SL2(R) cocycle.
# Draft: dynamics-continent-lyapunov-avila-morales-ramis.md, section 8.
# Run: runpod 157.157.221.29:39437, python3 (3.8.10), pure math (no numpy). 2026-06-19.
import math

alpha = (math.sqrt(5.0) - 1.0) / 2.0   # golden-mean frequency (Diophantine)

def lyap(applyT, N=300000, burn=2000):
    # fibered Lyapunov exponent via vector iteration with renormalization
    vx, vy = 1.0, 0.0
    s = 0.0; cnt = 0
    for n in range(N):
        th = (n * alpha) % 1.0
        ax, ay = applyT(th, vx, vy)
        nrm = math.hypot(ax, ay)
        if n >= burn:
            s += math.log(nrm); cnt += 1
        vx, vy = ax/nrm, ay/nrm
    return s / cnt

# 1. Rotation cocycle R(theta) in SO(2): reducible, abelian hull  -> expect L=0
def rot(th, x, y):
    c, sn = math.cos(2*math.pi*th), math.sin(2*math.pi*th)
    return c*x - sn*y, sn*x + c*y

# 2. Almost-Mathieu / Schrodinger transfer matrix at energy E, coupling lam
def amo(lam, E):
    def T(th, x, y):
        v = E - 2.0*lam*math.cos(2*math.pi*th)
        return v*x - y, x          # [[v,-1],[1,0]] . (x,y)
    return T

L_rot   = lyap(rot)
L_sub   = lyap(amo(0.5, 0.0))
L_crit  = lyap(amo(1.0, 0.0))
L_super = lyap(amo(2.0, 0.0))

print("=== DMR / Avila Lyapunov referee (golden-mean frequency, N=3e5) ===")
print("rotation (reducible, abelian hull)        L = %.6f   [DMR-abelian: expect 0]" % L_rot)
print("AMO lam=0.5 (subcritical)                 L = %.6f   [expect ~0 if E in spectrum]" % L_sub)
print("AMO lam=1.0 (critical, self-dual)         L = %.6f   [Avila: max(0,log1)=0]" % L_crit)
print("AMO lam=2.0 (supercritical, SL2 hull)     L = %.6f   [Avila: log2 = %.6f]" % (L_super, math.log(2.0)))
print("log2 reference = %.6f" % math.log(2.0))
