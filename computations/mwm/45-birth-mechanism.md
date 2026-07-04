# 45 — The Birth Mechanism, Filmed: Resonant Attraction, Central Repulsion

**Register: SEARCH** (task #130; doc 44 §4 opening (2) executed). Certification:
`computations/mwm/birth_homotopy.py` (P-B1/P-B2/P-B3 pre-registered, ALL PASS).

## 1. The measurement

Homotopy in the marginal term: A_λ = Σ_{n≤34} n^{−s} + λ·35^{−s}, exact-FE
symmetrization at every λ. The two N = 35 mid-band survivors (p = .036, .086,
just above the n = 35 entry at t* = 2π·35² = 7696.9) and a p-central control
(t = 7900, p ≈ .45):

- **P-B1 PASS**: both survivors' pairs are ABSENT at λ = 0, PRESENT at λ = 1 —
  the pairs are created by the marginal term.
- **P-B2 PASS — collision filmed**: the flanking on-line gap shrinks
  monotonically in λ (survivor-1: .295/.246/.187/.101 at λ = 0/.2/.4/.6), the
  on-line count drops by two between λ = .6 and .8, and the pair emerges and
  deepens (η = .059 → .096; survivor-2: η = .037 → .097). Pair birth is an
  on-line zero COLLISION driven by the entering term.
- **P-B3 PASS, stronger than registered**: at the p-central control the SAME
  term REPELS — min-gap grows monotonically in λ (.359 → .440). The marginal
  term is a stabilizer off-resonance, a pair-creator at resonance.

## 2. The mechanism is stationary phase [CONJECTURE, with the frame explicit]

On the line the marginal term perturbs Z by 2λ|γ(1/2+it)|·N^{−1/2}·cos φ(t),
φ(t) = θ_γ(t) − t·log N, and φ′(t) = log√(t/2π) − log N vanishes EXACTLY at
t = 2πN² — the truncation transition IS the stationary phase of the marginal
term's Z-perturbation. Near t* the push acts coherently on consecutive gaps
(attraction → collision → birth); away from t* its sign rotates on the beat
scale and averages to the measured repulsion. **(MID-central) therefore has a
provable shape**: an oscillatory/stationary-phase statement about an EXPLICIT
one-term perturbation of an explicit fixed polynomial — the attraction zone is
confined to |p| ≤ p*, plus a selectivity clause (even at resonance only the
softest gaps collide — 8 births across ~50 transitions in [200, 12000]).
Next measurement: the push-sign profile σ(p) = sign d(min-gap)/dλ across one
full interval p ∈ (0,1) — maps the attraction zone directly and hands the
stationary-phase computation its target boundary.

## 3. The two halves of the program meet here

Pair birth = two on-line zeros colliding and leaving = a local DISCRIMINANT
sign change of the zero configuration — doc 19/20's square-class object, for
the fixed polynomial Φ_N under a one-parameter perturbation. That is EXACTLY
the shape the (SPUR-R) analytic arc was built for: doc 25's tracking clearance
tracks disc signs of perturbed section chains; doc 38's minor chain certifies
them; Theorem B⁗/S″ control the equilibrium march of such configurations. So
(MID-central) — the last arithmetic wall — is a DISC-STABILITY statement in the
native format of the lane's own analytic machinery: show the one-term
perturbation cannot flip the local disc at p-central phases (its push is
sub-stiffness there), by the same energy/margin bookkeeping the SPUR arc
already formalizes. The arithmetic enters ONLY through the explicit phase
φ(t) and amplitude N^{−1/2} of the marginal term — the weld identity in its
barest form.

## 4. Openings

1. σ(p) profile run (one interval, ~20 λ-derivative scans) → the measured
   attraction boundary p*.
2. The stationary-phase write-out: push-sign flip at accumulated beat phase π —
   a classical computation on the explicit φ(t); with it, (MID-central) reduces
   to the selectivity clause (gap-stiffness vs push-amplitude N^{−1/2} — the
   doc-12 small-ball object, now with a mechanism anchoring WHICH gaps are at
   risk).
3. Wire the disc-stability form of (MID-central) into the SPUR arc's Lean
   substrate (the tracking/margin interfaces are already banked; #143's stack).
4. #149 full text: G–M's fixed-N zero counts on the matched slice, now asked
   with the right question (their methods vs the resonant marginal term).
