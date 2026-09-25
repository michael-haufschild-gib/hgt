import sys
sys.path.insert(0, "/root/precert")
import mpmath as mp
import theta_common as tc
mp.mp.dps = 40

def G(u, t):
    d = tc.c5_point(u, t)
    r = d["r"]; a = d["tq1"]; b = d["t2q2"]
    return (9*r*a + 5*r*a*a + 4*a*a) / (24*r*r + 5*r*b)

for u in (0, 0.5, 1.0, 2.0, 4.0):
    prev = None; mono = True; crossings = []
    vals = []
    ts = [mp.mpf(1)/100 * k for k in range(1, 61)] + [mp.mpf(6)/10 + mp.mpf(k)/10 for k in range(0, 55)]
    for t in ts:
        g = G(u, float(t))
        vals.append((float(t), float(g)))
        if prev is not None and g > prev + mp.mpf(10)**-30:
            mono = False
            crossings.append((float(t), float(g - prev)))
        prev = g
    mx = max(vals, key=lambda p: p[1])
    print(f"u={u}: max G={mx[1]:.6f} at t={mx[0]:.2f}; monotone decreasing: {mono};"
          f" G(0.01)={vals[0][1]:.8f} G(1)={dict(vals).get(1.0, None)} G(6)~{vals[-1][1]:.3e}"
          f"{' viol:' + str(crossings[:3]) if crossings else ''}", flush=True)
