"""Correction to the case-(ii) framing: the log-enhancement of zeta's zero density is the
Gamma-factor PHASE (Source-A), not the primes. Riemann-von Mangoldt: N(T)=theta(T)/pi+1+S(T),
theta = Riemann-Siegel = arg of the Gamma-factor. Main (T/2pi)log T term = theta/pi (Gamma);
S(T)=O(log T) = prime fluctuation (Source-B). => Gamma-perp-zeta over K is a WELD statement."""
import mpmath as mp
mp.mp.dps = 30
print("T     theta/pi      (T/2pi)log(T/2pi)-T/2pi   diff(->-1/8)")
for T in [50, 100, 500, 1000]:
    th = mp.siegeltheta(T)/mp.pi
    main = (T/(2*mp.pi))*mp.log(T/(2*mp.pi)) - T/(2*mp.pi)
    print(f"{T:5d}  {float(th):12.5f}  {float(main):20.5f}   {float(th-main):+.5f}")
print("T     N(T)   theta/pi+1   S(T)=N-(theta/pi+1)")
for T in [50, 100, 500]:
    nz = int(mp.nzeros(T)); base = mp.siegeltheta(T)/mp.pi + 1
    print(f"{T:5d}  {nz:5d}  {float(base):10.4f}   {float(nz-base):+.4f}")
print("=> main log term = Gamma phase (Source-A); S(T)=O(log T) = primes (Source-B). Weld.")
