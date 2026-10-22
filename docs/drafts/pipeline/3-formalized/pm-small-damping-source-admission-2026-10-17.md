# PM: small-damping admission of the physical source

- **ID:** pm-small-damping-source-admission-2026-10-17
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** read-only PM entry in `docs/reports/rh-current-frontier-map.md`
- **Statement:** [OPEN] Resolve an actual analytic admission obstruction in the physical-model route, retaining the original source and all contact/cross terms.

## Scope and plan

PM only this turn. Earlier thread routes: XN, HF, IRK, EGC, OWU, RN.
The prior RN turn produced verified mathematical evidence but did not meet
the strict positive-contribution criterion. The full objective remains active.

1. Inspect current Lean statements and documented corpus-search results for
   the physical source, small damping, retarded realization, and contact action.
2. Isolate a concrete obstruction; iterate conjecture, proof attempt, failure
   analysis, and positive salvage. No numerical experiments or web search.
3. Complete a dependency-closed paper proof before new Lean code. A better
   bound, new receiver, or changed target does not count as completion.
4. Formalize an unconditional surviving advance; one owned Lean process at
   a time, canonical `lake --old env lean` audit, axiom audit, umbrella wiring,
   formal lint, and owned-scratch cleanup. No full/umbrella builds, heartbeat
   increases, commits, or frontier-map edits.

## Status

- [x] PM selected; documented deep corpus search launched.
- [x] Exact source-admission obstruction isolated.
- [x] Dependency-closed paper proof and exact Lean formalization complete.
- [x] Lean verification and final audit complete.
- [x] User's strict contribution criterion met for PM small-damping admission.

## Corpus audit and conjecture loop

The fixed-input `jointCausalKernel` already admits every positive damping.
That theorem does not cover the forced original response. The current forced
response theorem in `ThetaCuspHawkingBMPhysicalCausalGreenBand` assumes damping
above `principalKernelGrowth q`, which is at least 3/2. The source includes
all three actual principal exponents `2*rho`, `1`, `2-2*rho`, their literal
amplitudes (including the mixed channel), and cutoff commutators.

1. Reuse fixed-input admission: rejected; the time-dependent source remains.
2. Remove poles by a new cancellation hypothesis: rejected. The actual
   connection Gamma factors are already nonzero in the positive half-plane;
   pole absence alone does not establish time-domain admission. Existing
   physical fundamental poles lie in the left half-plane and do not refute
   positive-damping admission.
3. Degree-reflection plus a Legendre derivative estimate: plausible, but
   unnecessary. The original circle representation supplies a more direct
   positive mechanism through its exact height mass.
4. **Selected conjecture:** for every actual Xi copy, branch, amplitude, and
   positive damping, the unchanged `causalJointForcedResponse` belongs to the
   original damped time L2 space. Its Bochner Laplace integral exists and
   equals the original causal frequency response throughout `Re(w)>0`.
   Verdict: **PROVED AND FORMALIZED**. This removes the PM admission
   threshold; an intermediate kernel estimate alone will not count.

Documented searches:

- `research 'FZZ physical source small damping L2 admission retarded Haar target' --mode deep --budget-seconds 300 --json`: partial; filter/judge malformed output, no useful stronger admission theorem.
- `research 'principal causal response positive half plane Dirichlet reflection stability' --mode deep --module ThetaCuspHawkingBM --budget-seconds 300 --json`: nonpartial retrieval; existing fixed-input admission and source-dependent forced admission confirmed. Index refresh deferred to running indexer; source-only candidates require Lean verification.

No external search or novelty claim: the user's corpus-only restriction
overrides the skill's external-literature phases.

## Dependency-closed paper proof

Write P_nu(z) for the corpus's `legendreKernel`, H(d,theta) for its positive
circle height, and A for normalized circle integration. The existing exact
identity is P_{-m}(cosh d)=A(H(d,theta)^m).

**1. Exact height mass.** The existing Legendre differential equation and
actual first two derivatives give
`d/dz ((z^2-1) P'_{-1}(z))=0` for z>0. Its value at z=1 is zero, so
P'_{-1}(z)=0 for z>1. Continuity at 1 and P_{-1}(1)=1 yield
P_{-1}(z)=1 for z>=1. The circle identity therefore gives A(H)=1 for every
real radius d. This is an exact identity, with no spectral assumption.

**2. Uniform derivative on the physical exponent strip.** Fix m with
0<=Re(m)<=2. For d>=0, the explicit chart gives
`exp(-d)<=H<=exp(d)` and `|dH/dd|<=H`: the latter follows from
`denominator^2-radialNumerator^2=sin(theta)^2>=0`.
Consequently `|d(H^m)/dd|<=|m| H^Re(m)`. If H<=1, this last power is at
most 1; if H>=1, it is at most H^2<=exp(d) H. Thus
`|d(H^m)/dd|<=|m|(1+exp(d) H)`.
All integrands and derivatives are continuous on each compact rectangle,
so differentiation under the finite circle integral is justified by a
compact constant majorant. Exact height mass yields
`|sinh(d) P'_{-m}(cosh d)|<=|m|(1+exp(d))`.
For d>=1 the ratio `(1+exp(d))/sinh(d)` is uniformly bounded (use the
explicit exponential formula and exp(-2d)<=exp(-2)). On z in
`[1,cosh(1)]`, P' is continuous by the existing second-derivative theorem
and hence bounded. Combining both regions gives a finite C_m with
`|P'_{-m}(z)|<=C_m` for all z>=1. No asymptotic expansion, pole removal,
or degree-symmetry assumption is used.

**3. Reflection removes the unstable kernel growth.** Let
`Z_+=(cosh(h)+sinh(x)sinh(y))/(cosh(x)cosh(y))` and let Z_- replace y by
-y. Their difference is `2*tanh(x)*tanh(y)`, of absolute value at most 2.
If both causal cones are present, Z_+,Z_->=1, so the mean-value integral
and step 2 bound `|P(Z_+)-P(Z_-)|<=2*C_m`.
If only one cone is present, monotonicity of cosh at the absent reflected
cone gives `1<=Z_present<=3`; compact continuity bounds its kernel.
If neither cone is present the kernel vanishes. Thus the complete
Dirichlet causal kernel, including its factor 1/2, is uniformly bounded
in h,x,y. This retains both characteristic indicators; they must not be
subtracted after dropping a cone boundary term.

**4. Unchanged actual principal time responses.** In the literal retarded
formula for `radialResponse`, the source is odd and supported in |y|<=sigma.
Extend its spatial integral to a symmetric interval containing that support,
then change y to -y in one copy. The result is precisely the reflected
kernel from step 3 times the same odd source. All integrals are finite,
bounded measurable functions on compact intervals; the original extended
kernel is continuous on its causal support. The corpus's uniform physical
source bound therefore gives `|radialResponse(t,x)|<=C*(max(t,0))^2`.
Finite propagation gives support |x|<=max(t,0), hence its L2 norm is at most
`C'*(max(t,0)+1)^3`. The existing exact
`nativePrincipalResponse_eq_principalTimeResponse` transports this bound
to each of the three original principal responses, retaining each amplitude.
Every positive exponential damping is now Bochner L1 (and L2) in time;
polynomials are absorbed by any smaller positive exponential rate.

**5. Complete source admission.** Apply the existing bounded cutoff/spatial
operators to the three admitted responses and sum all three. The remaining
`timeCuspMainVector` already has its original Laplace admission for Re(w)>-2.
Thus the literal `causalCuspSourceVector` is Bochner L1 for every positive
damping. Its actual Laplace transform is holomorphic on Re(w)>0 by the
existing dominated Bochner Laplace theorem; on each Re(w)>=c>0 its norm is
bounded by the c-damped source L1 norm.

**6. Original forced response, not a replacement family.** For any c>0,
compose that admitted source transform with the original positive joint
wave resolvent. Its existing bound gives a Cauchy-bounded Hilbert map on
the shifted half-plane, exactly as in `nativeForcedBoundary` but without
the old growth threshold. The proved Hilbert half-plane theorem constructs
a causal time response damped in L2 at every k>c. Its transform is the
same literal `causalJointFrequencyResponse`. On a sufficiently far-right
line, this equals the transform of the existing `causalJointForcedResponse`.
The existing weighted-L2 Laplace injectivity theorem therefore identifies
the new construction with that unchanged response almost everywhere.
Given any k>0 choose c=k/2, obtaining the required L2 admission. Cauchy-
Schwarz with any smaller positive damping gives absolute Laplace
integrability at every Re(w)>0; transform equality follows from the same
construction and injectivity. No new source or analytic premise is added.

This proof removes an actual admission obstruction. It does not itself
prove the remaining optical magnitude, ordered cap, Haar approximation,
all-divisor extinction, or RH. Final credit depends on verifying the entire
six-step statement in Lean, not merely its intermediate bound.

## Formalized result and contribution assessment

**Status: FORMALIZED. PM receives positive-contribution credit for removing the
small-damping admission obstruction. The full cross-route objective remains active.**

The theorem `RHTower.D4BMForcedSmallDamping.causalJointForcedResponse_memLp_pos`
proves, for every actual `XiZeroCopy`, branch, amplitude, and every real `k > 0`,
that the unchanged `D4BMJointSource.causalJointForcedResponse`, multiplied by
`expRay k`, belongs to the original time `L2` space on positive time. The old
condition `principalKernelGrowth q < k` is removed. There is no RH assumption,
no added analytic premise, and no replacement source or response.

The companion theorems `causalJointForcedResponse_integrable_pos` and
`causalJointForcedResponse_laplace_pos` prove absolute Bochner integrability and
the original frequency-response identity throughout `Re w > 0`.
`causalJointFrequencyResponse_differentiableAt_pos` gives holomorphy there.

This is admission of the literal physical forced response into the required
function space at arbitrarily small positive damping. The reflected-kernel
bound is an intermediate ingredient, not the credited endpoint. The exact
odd-source reflection cancels the growing direct contribution before norms are
taken. All three principal channels, their actual amplitudes, cutoff
commutators, and the native square remainder remain present. Laplace uniqueness
identifies the auxiliary Hardy construction with the previously defined response.

### Lean modules

- `formal/GaloisForLFunctions/RHTower/ThetaCusp/ThetaCuspHawkingBMPrincipalReflectionAdmission.lean`:
  exact height mean, global Legendre derivative control, and complete reflected
  Dirichlet kernel control on the physical exponent strip (4 public theorems).
- `formal/GaloisForLFunctions/RHTower/ThetaCusp/ThetaCuspHawkingBMPrincipalSmallDamping.lean`:
  literal retarded-response and radial `L2` growth, all three actual principal
  responses, and complete original-source Laplace admission (5 public theorems).
- `formal/GaloisForLFunctions/RHTower/ThetaCusp/ThetaCuspHawkingBMForcedSmallDamping.lean`:
  original frequency holomorphy, original forced-response `L2` admission,
  absolute Laplace admission, and exact original transform (4 public theorems).

All three modules are wired into `formal/GaloisForLFunctions/RHTower.lean`.
The read-only frontier map was not edited by this task.

### Verification

Each module passed its final direct check, without warnings, using
`lake --old env lean -j1 -o .lake/build/lib/lean/<module>.olean <module>.lean`
from `formal/`. No full or umbrella build was run. One owned foreground Lean
process ran at a time. No heartbeat limit was raised.

A separate `/tmp` audit imported the completed module and ran `#print axioms`
for all 13 public theorems. Every theorem depends only on `propext`,
`Classical.choice`, and `Quot.sound`. No added axioms or proof holes.
`scripts/formal_tools.py lint` passed with repository large-file warnings.

### Remaining frontier

This result does not assert zero-damping admission or a uniform zero-damping
limit. Haar approximation, optical magnitude, the ordered cap limit, and
all-divisor extinction remain open. No RH conclusion is claimed. The other
routes and route candidates still require their own qualifying contributions.

Owned PM research-search JSON, API scratch, and axiom-audit scratch files were
removed after verification. All owned build, audit, and lint processes exited.
