# Marginal infinite-frequency regime (sigma=1/2) value distribution (D5 12.1-12.4).
# Tests the field's characterization of its hardest native dynamical problem:
#  - 2nd moment <|zeta(1/2+it)|^2> ~ log(T/2pi)  (Ingham, = the cocycle's k=1 exponential moment)
#  - mean(log|zeta|) -> 0, Var(log|zeta|) ~ (1/2)loglog T  (Selberg CLT centering + variance order)
# Honest caveats: Selberg variance converges very slowly; discrete sampling near zeros inflates Var.
# Run: runpod 157.157.221.29:39437, python3.13 + mpmath 1.4.1. 2026-06-19.
import mpmath as mp, math
mp.mp.dps = 15

def run(T, N):
    dt = T/N
    s2 = 0.0; logs = []
    for j in range(1, N+1):
        t = j*dt
        z = mp.zeta(0.5 + 1j*t)
        az = float(abs(z))
        if az <= 0: continue
        s2 += az*az
        logs.append(math.log(az))
    n=len(logs)
    mean2 = s2/n
    ml = sum(logs)/n
    vl = sum((x-ml)**2 for x in logs)/n
    print("T=%6g N=%d : <|z|^2>=%.4f (log(T/2pi)=%.4f) ; Var(log|z|)=%.4f ((1/2)loglogT=%.4f) ; mean(log|z|)=%.4f" %
          (T, N, mean2, math.log(T/(2*math.pi)), vl, 0.5*math.log(math.log(T)), ml))

print("=== marginal-regime (sigma=1/2) value distribution: Ingham 2nd moment & Selberg log-variance (D5 12.1-12.2) ===")
run(500.0, 4000)
run(2000.0, 8000)
run(10000.0, 12000)
