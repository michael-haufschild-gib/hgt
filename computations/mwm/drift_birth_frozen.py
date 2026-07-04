#!/usr/bin/env python3
"""Drift-birth fixed point, CORRECTED to the frozen-circle geometry (doc 51 §2-3).

The naive full-tower first-passage (drift_birth_fixed_point.py) is phase-fragile
-> scattered islands, no clean edge (P1/P2 FAILED). Reason: the dip lives in the
FROZEN lattice geometry, where the partial sums S_M = a e^{i beta}(1-w^M)/(1-w)
lie on a CIRCLE through 0 of radius r = a/|1-w| = a/(2|cos 2pi d|). That dip is
SMOOTH, not fragile.

Closed form of the frozen dip (deepest negative excursion of Re S_M):
    S_M = (a/|1-w|) * e^{i psi} * (1 - w^M),   psi = beta - arg(1-w)
    min_M Re S_M = (a/|1-w|)(cos psi - 1)   [1-w^M sweeps circle center 1 radius 1]
    => frozen_dip(d) = (a/|1-w|)(1 - cos psi),   psi = beta(d) - arg(1-w(d)).
with  beta(d) = pi/8 - 2 pi d^2   (doc 50 §5 stationary value),
      w = e^{-i pi(1+4d)},  |1-w| = 2|cos 2pi d|.

Two regimes bracket the truth:
  - FROZEN edge: pair survives if birth depth A*B(d) > frozen_dip(d) at birth phase.
  - DRIFT-WORST edge: drift rotates beta through all values (doc 51 §4); worst dip
    = 2a/|1-w| = a/|cos 2pi d|, survival iff A*B(d) > a/|cos 2pi d|
    <=> F(d) := |cos(pi/8-2pi d^2)|*|cos 2pi d| > a/A.
The census edge d*=0.194 (2 pi d*^2 = 0.236) must sit between these.

Envelope scale: a = a0 = 2/sqrt(N) at the pair (marginal term); birth depth
A*B(d). The one dimensionless knob is rho := A/a0 (birth-depth / envelope ratio).

PRE-REGISTERED (before running):
  Q1 (prior 0.45): the FROZEN edge d_froz(rho) passes through d=0.194 at a rho
     that is O(1) and STABLE across N in {100,300,1000,3000} (a true constant,
     not an N-artifact). Report rho*(N) at d=0.194.
  Q2 (prior 0.50): the DRIFT-WORST edge (F(d)=1/rho) passes through 0.194 at
     rho = 1/F(0.194) = 1/0.342 = 2.92. Report and check F(d) shape.
  Q3 (prior 0.30) THE prize: at the NATURAL scale rho=1 (birth depth = envelope,
     no fine-tuning) one of the two edges lands within [0.17,0.22]. If neither
     does at rho=1, the constant needs a NON-trivial rho -> report which rho and
     whether IT has an independent meaning (e.g. the REACH ratio 1.10-2.11).
  Q4 (prior 0.60): frozen_dip(d) and F(d) are SMOOTH monotone on [0,0.25]
     (no fragility) -> the edge is a clean threshold crossing for every rho.
"""
import mpmath as mp

mp.mp.dps = 40
pi = mp.pi

def pieces(N, d):
    d = mp.mpf(d)
    a0 = 2 / mp.sqrt(mp.mpf(N))
    beta = pi/8 - 2*pi*d*d
    w = mp.e**(-1j*pi*(1+4*d))
    one_minus_w = 1 - w
    absw = abs(one_minus_w)                 # = 2|cos 2pi d|
    argw = mp.arg(one_minus_w)
    psi = beta - argw
    frozen_dip = (a0/absw)*(1 - mp.cos(psi))     # >= 0
    drift_worst_dip = 2*a0/absw                   # = a0/|cos 2pi d|
    B = abs(mp.cos(beta))
    F = B*abs(mp.cos(2*pi*d))
    return dict(a0=a0, B=B, F=F, frozen_dip=frozen_dip,
                drift_worst=drift_worst_dip, absw=absw, psi=psi)

def edge_from_condition(N, rho, which, dgrid):
    """largest d (contiguous from 0) with survival; birth depth = rho*a0*B(d)."""
    dstar = mp.mpf(0); ok_prev = True; island = False; broke = False
    for d in dgrid:
        p = pieces(N, d)
        birth = rho * p['a0'] * p['B']
        dip = p['frozen_dip'] if which == 'frozen' else p['drift_worst']
        ok = birth > dip
        if ok and not broke:
            dstar = d
        if not ok:
            broke = True
        if ok and broke:
            island = True
    return dstar, island

dgrid = [mp.mpf(k)/2000 for k in range(0, 601)]   # d in [0,0.30], step 5e-4

print("=== Q4: smoothness / shape of frozen_dip and F over [0,0.25] (N=300) ===")
for dd in ['0.00','0.05','0.10','0.15','0.194','0.22','0.25']:
    p = pieces(300, dd)
    print(f"  d={dd:>6}  B={float(p['B']):.4f}  F={float(p['F']):.4f}"
          f"  frozen_dip/a0={float(p['frozen_dip']/p['a0']):.4f}"
          f"  drift_worst/a0={float(p['drift_worst']/p['a0']):.4f}")

print("\n=== Q1: rho* such that FROZEN edge = 0.194, vs N ===")
target = mp.mpf('0.194')
for N in [100,300,1000,3000]:
    # birth = rho*a0*B(0.194) must equal frozen_dip(0.194): rho = frozen_dip/(a0*B)
    p = pieces(N, target)
    rho_star = p['frozen_dip']/(p['a0']*p['B'])
    dstar,_ = edge_from_condition(N, rho_star, 'frozen', dgrid)
    print(f"  N={N:>4}  rho*(frozen)={float(rho_star):.4f}  check d*={float(dstar):.4f}")

print("\n=== Q2: DRIFT-WORST edge, rho = 1/F(d); at d=0.194 ===")
p = pieces(300, target)
print(f"  F(0.194)={float(p['F']):.4f}  => rho_drift* = 1/F = {float(1/p['F']):.4f}")
for rho in ['2.92','2.0','1.5','1.0']:
    dstar, island = edge_from_condition(300, mp.mpf(rho), 'drift_worst', dgrid)
    print(f"    rho={rho:>4}  drift-worst d*={float(dstar):.4f} "
          f" 2pi d*^2={float(2*pi*dstar**2):.4f}  island={island}")

print("\n=== Q3: NATURAL scale rho=1, both edges (N=300) ===")
for which in ['frozen','drift_worst']:
    dstar, island = edge_from_condition(300, mp.mpf(1), which, dgrid)
    print(f"  rho=1  {which:>12} edge d*={float(dstar):.4f}"
          f"  2pi d*^2={float(2*pi*dstar**2):.4f}  island={island}")

print("\ncensus target: d*=0.194, 2 pi d*^2 = 0.236")
