#!/usr/bin/env python3
# MACHINE STEP8 (continuum/differential, per v9) + STEP9 method#5 (VISUALIZE as an orbit-path).
# NODE constraint: an identification map's TWIST (rotational part) is read from the matched geometry.
# Continuum HT transfer: the identification map of an HT function = its functional equation; ITERATE it to
# get an ORBIT-PATH (method#5 visualize), and measure the "twist" = total winding of the value-vector /
# the recurrence factor along the path. Matched DA control (exp) + precision-saturation (Wheeler) => not blind.
import mpmath as mp

def orbit_twist(f, fname, factor, z0, n=12, dps=30):
    mp.mp.dps = dps
    # orbit z0, z0+1, ... ; value path f(z0+k); cumulative turning (winding) of the value vector
    pts = [f(z0+k) for k in range(n)]
    tw = mp.mpf(0)
    for k in range(1,len(pts)-1):
        a = pts[k]-pts[k-1]; b = pts[k+1]-pts[k]
        if abs(a)>0 and abs(b)>0:
            tw += mp.arg(b/a)               # turning angle between successive path segments
    # also: total winding of the recurrence factor product arg(prod factor(z0+k))
    fac = mp.mpf(0)
    for k in range(n-1):
        fac += mp.arg(factor(z0+k))
    return float(tw), float(fac)

z0 = mp.mpc(0.4, 0.9)
print("=== STEP8+9: identification-orbit TWIST (method#5 path-visualization), HT vs DA control ===")
print("  function        | value-path turning | recurrence-factor winding arg(prod) | (twist signature)")
# Gamma (HT): Gamma(z+1)=z*Gamma(z), factor=z (variable -> winds)
tw_g, fac_g = orbit_twist(lambda z: mp.gamma(z), "Gamma(HT)", lambda z: z, z0)
print(f"  Gamma (HT)      | {tw_g:+.5f}          | {fac_g:+.5f}                         | factor=z (winds)")
# exp (DA control): exp(z+1)=e*exp(z), factor=e (constant -> no wind)
tw_e, fac_e = orbit_twist(lambda z: mp.e**z, "exp(DA)", lambda z: mp.e, z0)
print(f"  exp (DA control)| {tw_e:+.5f}          | {fac_e:+.5f}                         | factor=e (const, no wind)")

print("\n=== precision-saturation check (Wheeler instrument): is the twist precision-independent? ===")
for dps in (15,25,40):
    tw_g,_ = orbit_twist(lambda z: mp.gamma(z), "G", lambda z: z, z0, dps=dps)
    print(f"  dps={dps}: Gamma value-path turning = {tw_g:+.8f}")
print("\nREAD (STEP10): the 'twist' = arg-winding of the recurrence factor. Gamma's factor z winds (it has a")
print("zero); exp's constant factor does not. This is the identification's twist for the HT functional equation.")
