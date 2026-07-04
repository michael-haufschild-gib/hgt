#!/usr/bin/env python3
"""Drift-birth fixed point: does the EXACT sweep walk PRODUCE the survival edge
d* ~ 0.194 (2 pi d*^2 ~ 0.236)?  (doc 66 §7 / docs 50 §4-6, 51.)

The walk is the exact deterministic lattice (no randomness), so this is the one
sanctioned computation: the constant lives in a first-passage that reasoning
cannot close (the (DRIFT-dip) realized-fraction f).

EXACT INPUTS (all certified elsewhere):
  - pair born at fractional offset d, height t = 2 pi (N+d)^2 (doc 50 §4, P-L4).
  - birth phase  beta(d) = pi/8 - 2 pi d^2   (doc 50 §5 stationary value; the
    SAME object as the birth amplitude B(d) = cos(beta(d)) = |cos(pi/8-2pi d^2)|,
    so there is NO free birth-phase parameter).
  - per-entry exact rotation  Delta(m) = -t * log((N-m)/(N-m-1))   (doc 50 §4,
    the certified step; encodes the drift dp_eff/dm ~ m/N automatically).
  - envelope  a_m = 2 (N-m)^{-1/2}          (doc 51 §1; grows toward matched level).
  - sweep pushes c_m = a_m cos(Phi(m)),  Phi(m) = beta(d) + sum_{m'<m} Delta(m').
  - birth depth  eta0^2(d) = A * B(d)       (doc 51 §8(4): birth depth prop B(d)).
  - Absorption: pair dies at first partial sum where eta0^2 + S <= 0, entries
    added in PHYSICAL order (marginal term last, m: M_sweep-1 -> 0).
  Survival(d,A) = pair survives the whole sweep.  d*(A) = sup{d : survive}.

PRE-REGISTERED PREDICTIONS (written before running):
  P1 (prior 0.35) THE test: d*(A) is INSENSITIVE to the birth-depth scale A over
     a decade (A in {0.5,1,2,4,8}*a0-ish), landing in [0.17,0.22] (census 0.194).
     If d* slides strongly with A -> constant is NOT intrinsic -> model insufficient,
     REPORT the (d*,A) curve honestly instead of claiming a derivation.
  P2 (prior 0.70): survival set is an INTERVAL [0,d*] (empty middle), for N>=100.
  P3 (prior 0.40): the edge tracks F(d)=|cos(pi/8-2pi d^2)|*|cos 2pi d| crossing a
     level f; report the implied f and whether it is stable across N in {100,300,1000}.
  P4 (prior 0.55): d* is stable across N in {100,300,1000} to within +-0.02
     (a true constant of the matched regime, not an N-artifact).
"""
import mpmath as mp

mp.mp.dps = 30
pi = mp.pi

def survives(N, d, A, M_sweep=None):
    """Exact walk. Return True if pair of birth depth A*B(d) survives the sweep."""
    if M_sweep is None:
        M_sweep = N - 2            # sweep the whole top block down to marginal term
    t = 2 * pi * (N + d) ** 2
    beta = pi / 8 - 2 * pi * d * d
    B = abs(mp.cos(beta))
    eta0 = A * B                   # birth depth (units of the envelope scale)
    # cumulative rotation phases Phi(m), m = 0..M_sweep
    # entries added in physical order marginal-last: m = M_sweep-1, ..., 1, 0.
    # partial depth = eta0 + running sum of c_m in that order; watch for <=0.
    # precompute Delta(m) and a_m
    order = list(range(M_sweep - 1, -1, -1))
    # Phi(m) = beta + sum_{m'=0}^{m-1} Delta(m'); build Phi for all m first
    Phi = [beta]
    for m in range(1, M_sweep):
        j = N - (m - 1)
        Delta = -t * mp.log(mp.mpf(j) / (j - 1))
        Phi.append(Phi[-1] + Delta)
    depth = eta0
    mindepth = depth
    for m in order:
        a_m = 2 * (mp.mpf(N - m)) ** (mp.mpf(-1) / 2)
        c_m = a_m * mp.cos(Phi[m])
        depth += c_m
        if depth < mindepth:
            mindepth = depth
        if depth <= 0:
            return False, mindepth
    return True, mindepth

def edge(N, A, dgrid):
    surv = []
    for d in dgrid:
        ok, _ = survives(N, d, A)
        surv.append((d, ok))
    # d* = largest d that is the top of the initial survival interval [0,d*]
    dstar = 0.0
    for d, ok in surv:
        if ok:
            dstar = d
        else:
            break
    # check interval-ness: any survival ABOVE the first gap?
    seen_gap = False
    island = False
    for d, ok in surv:
        if not ok:
            seen_gap = True
        elif seen_gap and ok:
            island = True
    return dstar, island, surv

dgrid = [mp.mpf(k) / 400 for k in range(0, 141)]   # d in [0, 0.35], step 0.0025

print("=== P1/P3: edge vs birth-depth scale A  (N=300) ===")
for A in ['0.5', '1', '2', '4', '8']:
    dstar, island, _ = edge(300, mp.mpf(A), dgrid)
    Fd = abs(mp.cos(pi/8 - 2*pi*dstar**2)) * abs(mp.cos(2*pi*dstar)) if dstar>0 else mp.mpf('nan')
    print(f"  A={A:>4}  d*={float(dstar):.4f}  2pi d*^2={float(2*pi*dstar**2):.4f}"
          f"  F(d*)={float(Fd):.4f}  island_above={island}")

print("\n=== P2/P4: edge vs N  (A=1) ===")
for N in [100, 300, 1000]:
    dstar, island, surv = edge(N, mp.mpf(1), dgrid)
    print(f"  N={N:>4}  d*={float(dstar):.4f}  2pi d*^2={float(2*pi*dstar**2):.4f}"
          f"  interval(no island above)={not island}")

print("\n=== survival map (N=300, A=1), d : survive? ===")
_, _, surv = edge(300, mp.mpf(1), dgrid)
row = ""
for d, ok in surv:
    if abs(float(d*400) - round(float(d*400))) < 1e-9 and round(float(d*400)) % 4 == 0:
        row += ("#" if ok else ".")
print("  d=0.00 " + row + " d=0.35   (# survive, . absorbed; step 0.01)")

print("\ncensus target: d* = 0.194, 2 pi d*^2 = 0.236")
