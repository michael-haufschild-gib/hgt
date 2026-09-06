# Check C(a) ~ sum_rho X^rho/rho^2 and A(a) ~ (2+gamma-log 4pi) e^a using the first NZ zeta zeros.
import numpy as np, math
from mpmath import mp, zetazero, euler, pi, log, mpf, mpc
mp.dps = 20
NZ = 400
gam = [float(zetazero(k).imag) for k in range(1, NZ+1)]
rows = np.load('fixed_pole_profile.npy')
c0 = float(2 + euler - log(4*pi))
print("2+gamma-log(4pi) =", c0, "  sum_{k<=NZ} 2/|rho|^2 =", sum(2/(0.25+g*g) for g in gam))
for a in [2.0, 3.0, 4.0, 4.02, 5.0, 6.0, 7.0, 8.0]:
    i = int(np.argmin(np.abs(rows[:,0]-a))); a = rows[i,0]; A = rows[i,1]; C = rows[i,2]
    X = math.exp(2*a)
    S = 0.0
    for g in gam:
        rho = complex(0.5, g)
        S += 2*(X**0.5*np.exp(2j*a*g)/rho**2).real
    print(f"a={a:5.2f}  A/e^a={A/math.exp(a): .5f}  C={C: .4f}  sum_rho X^rho/rho^2 (NZ={NZ}) = {S: .4f}  even/e^a={(A+C)/math.exp(a): .5f} odd/e^a={(A-C)/math.exp(a): .5f}")
