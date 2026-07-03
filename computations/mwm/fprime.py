#!/usr/bin/env python3
"""MWM R8 chunk 0 — direct jet measurement: f_dh'(rho) at localized zero centers.

Central difference with h = 1e-8 at dps 30. Prints (beta, t, |f'|, arg f', |f(rho)| residual).
Usage: fprime.py BETA1 T1 [BETA2 T2 ...]
"""
import sys
from mpmath import mp, mpf, mpc, arg, fabs

mp.dps = 30
from engine2 import f_dh

def jet(beta, t):
    s = mpc(beta, t)
    h = mpf("1e-8")
    fp = (f_dh(s + h) - f_dh(s - h)) / (2 * h)
    return s, f_dh(s), fp

if __name__ == "__main__":
    args = sys.argv[1:]
    for i in range(0, len(args), 2):
        s, f0, fp = jet(mpf(args[i]), mpf(args[i + 1]))
        print(f"rho=({args[i]},{args[i+1]})  |f(rho)|={fabs(f0)!s:.12}  "
              f"|f'|={fabs(fp)!s:.10}  arg f'={arg(fp)!s:.10}", flush=True)
