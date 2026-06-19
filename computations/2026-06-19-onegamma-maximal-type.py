"""1/Gamma is entire, order 1, MAXIMAL type: log|1/Gamma(-x+1/2)| ~ x log x.
Supports (T)'s target class = hypertranscendental-growth class (prototype 1/Gamma)."""
import mpmath as mp
mp.mp.dps = 30
print("x   log|1/Gamma(-x+.5)|   x*log(x)   ratio (->1 = maximal type)")
for x in [10, 20, 40, 80, 160, 320]:
    v = mp.log(abs(1/mp.gamma(-x + 0.5)))
    ref = x*mp.log(x)
    print(f"{x:5d}  {float(v):12.4f}  {float(ref):12.4f}  {float(v/ref):.4f}")
print("control e^s (order-1 NORMAL): r/(r log r) -> 0")
for r in [10, 40, 160, 640]:
    print(f"  r={r:4d}  {float(r/(r*mp.log(r))):.4f}")
