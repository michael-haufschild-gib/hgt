"""zeta is order-1 MAXIMAL type, inheriting Gamma's exp(x log x) growth via the FE chi-factor.
log|zeta(-x+.5)| ~ x log x - x(1+log2+log pi); ratio to (x log x) = 1 - 2.84/log x -> 1.
This is CASE (i) of the (T*) split: maximal type via max-modulus = the Holder mechanism."""
import mpmath as mp
mp.mp.dps = 30
print("x     log|zeta(-x+.5)|   x log x     ratio   1-2.838/log x")
for x in [10, 20, 40, 80, 160, 320]:
    s = -x + mp.mpf('0.5')
    v = mp.log(abs(mp.zeta(s))); ref = x*mp.log(x)
    pred = 1 - (1+mp.log(2)+mp.log(mp.pi))/mp.log(x)
    print(f"{x:4d}  {float(v):13.3f}  {float(ref):10.3f}  {float(v/ref):.4f}   {float(pred):.4f}")
print("=> ratio -> 1: zeta order-1 maximal type, leading coeff 1, same as Gamma. Inherited via FE.")
