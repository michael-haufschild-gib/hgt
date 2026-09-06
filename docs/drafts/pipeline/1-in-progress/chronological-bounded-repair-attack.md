# Bounded chronological arithmetic repair — working knowledge

**Frozen target [R], OPEN.** Construct real a_(k,N), one fixed bound C independent
of k,N, and full L²(0,∞) convergence e^(−t)+Σ_(k≤N)a_(k,N)h(kt)→0,
where h(t)=1/t−1/(e^t−1). Derive everything without RH. The target has not changed.
[Classical RH interface](chronological-rh-recovery-interface.md).

**Verified:** six individual Lean leaf builds; 95 public declarations audited,
only propext/Classical.choice/Quot.sound. All six umbrella imports wired.
Current authoritative lint passes with existing file-size warnings. [Proofs and certificate](../3-formalized/chronological-arithmetic-repair-boundary.md).

## What works

**[BRIDGE] Nonlinear response repair.** Put q=e^(−t) and
 g=2h(2t)−h(t)=q/(1+q). The recurrence P₀=0, P_(m+1)=g(1+P_m) has
q−P_m=qg^m and squared L² error ≤4^(−m)/2. Lean proves the actual integral
and its limit. Products of responses are used; this is not [R].

**Exact arithmetic cost.** For a zero-constant formal series F, its unique
Lambert inverse is μ*coeff(F). Every power g^r, r≥2, has inverse coefficient
of absolute value binomial(p−1,r−1) at every sufficiently large prime p.
Lean excludes bounded real Lambert representations. Formal-series impossibility
alone says nothing about L² closure.

**Positive residue: sharp boundary.** P_m=q−q^(m+1)/(1+q)^m. Its exact inverse
A_(k,m) agrees with μ(k) through m, equals μ(m+1)−1 at m+1, and equals
μ(m+2)+m at m+2 for m≥2. Thus |A_(m+2,m)|≥m−1. If a truncation through N
has bound B and m>B+1, then N≤m+1: it is exactly a Möbius prefix, with at
most one final correction −1. All these statements are formalized.

## Independently frozen candidate [A]: damped infinite depth

For 0≤ε≤1/2 define

F_ε(q)=q/(1+εq),
b_(n,ε)=Σ_(d|n) μ(n/d)(−ε)^(d−1).

Candidate arrays are b_(n,ε_N), n≤N, with ε_N→0. Lean now proves their
full L² convergence is equivalent to raw Möbius convergence: [B] below.
Retired as a distinct convergence mechanism, not disproved as an approximation
statement independently of the raw sequence.

**[BRIDGE, proved in Lean]** F_ε is the damped fixed point
F=g(1+(1−ε)F). Its formal Lambert inverse is exactly b, and
|b_(n,ε)|≤1/(1−ε)≤2 for every n. Also q−F_ε=εq²/(1+εq), with full squared
L² error ≤ε²/4. Thus infinite depth removes the finite-product coefficient
obstruction. This does not justify exchanging arithmetic truncation and limits.

**Exact finite remainder, proved in Lean.** Let
R_N(t)=e^(−t)+Σ_(k≤N)μ(k)h(kt), and let D_(N,ε) be [R]'s residual with b.
Then

D_(N,ε)(t)=e^(−t)−Σ_(d≤N)(−ε)^(d−1)e^(−dt)
+Σ_(d≤N)(−ε)^(d−1)R_floor(N/d)(dt).

The exponential part is controlled by a finite geometric sum. The last sum
contains R_N itself with coefficient one. The missing lemma is full L² control
of this sum for a concrete ε_N→0. No bound of that kind has been proved.

## Attacks, limits, and next hard question

- Exact cancellation in chronological degree forces μ. Its bound |μ|≤1 does
  not control error concentrating at t→0.
- Fake proof: rapid nonlinear recovery → bounded arithmetic linearization →
  finite L² recovery. Finite powers fail the middle step. Damped infinite depth
  repairs that step but leaves the last implication entirely open.
- Reversing [A] succeeded: exact full L² equivalence to raw convergence is
  formalized. This is a rigidity result, not an assertion of raw heat divergence.
- Do not transfer the known unsmoothed Nyman–Beurling raw-prefix no-go through
  exponential smoothing without proof: its inverse is unbounded.
- Unproved direct attack on the raw sequence: pair a block (N,λN] with
  √N φ(Nt). Strong Cauchy convergence would force
  Σ_(N<k≤λN)μ(k)K(k/N)=o(√N), K(r)=∫h(ru)φ(u)du.
  The window's Mellin transform should expose 1/ζ without undoing smoothing.
  Real-cutoff interpolation and the boundary-pole argument need a complete
  audit; no raw heat nonconvergence theorem is claimed.
- Unrestricted density via analytic dilation pairing/Blaschke uniqueness is
  another possible [BRIDGE], not yet dependency-closed or formalized. It supplies
  no coefficient budget and does not prove [R].

No numerical result enters Lean. No new RH proof or novelty/priority claim.

## Frozen test [B], now proved: full L² convergence equivalence

For every schedule 0≤ε_N≤1/2 tending to zero,
D_(N,ε_N)→0 in full L² if and only if R_N→0 in full L².
`ChronologicalDampingRigidity.chronologicalDampedHeat_converges_iff_raw`
(namespace RHTower) proves this on the actual half-line measure.

**Positive residue.** If all earlier raw error norms are ≤C, then
||D_(N,ε)−R_N||₂≤2ε(1+C). Only strict earlier indices N/d, d≥2, occur.
If the damped errors tend to zero, strong induction first bounds every raw
error by one C; the perturbation then vanishes. The converse follows from
boundedness of a convergent sequence. All finite errors are proved to belong
to L², with the norm identified as the square root of their squared integral.

## Numerical evidence and next test

Runpod N=16,...,512: retained box-C=1 errors decrease from 1.31e−4 to 4.12e−9;
raw error at N=512 is 8.37e−2. These are feasible-vector measurements, not
certified optima or a convergence theorem. Different quadratures agree; 80-digit
residual spot checks differ from float by at most 1.62e−14. Initial optimizer
failures were exposed by monotonicity checks and corrected by retaining feasible
vectors and comparing active-set and singular-mode constructions.

At N=512, zeroing nonsquarefree coefficients of the C=1 vector raises error to
0.913; resetting its first eight coefficients to μ raises error to 0.140.
Those interventions break this vector's cancellation; they do not rule out
reoptimizing under either restriction. Next hard test: can a coefficient
construction maintain its budget while repairing the small-t error at every
cutoff? Finite fits and damping equivalence do not supply that estimate.
[Results, checks, coefficients, code](../2-fully-proven/computations/chronological-bounded-repair-2026-09-06/REPORT.md).
