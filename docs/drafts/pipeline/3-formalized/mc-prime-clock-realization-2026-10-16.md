# Actual-prime realization of compact-clock controls

Status: FORMALIZED. Paper proof, three leaf builds, and axiom audit complete.

Parent goal: `../1-in-progress/cross-route-100-theorems-2026-10-16.md`.
Counted as contribution 1 of 100. Supporting lemmas and modules count once.

## Task and scope

Produce an unconditional structural advance combining the complete Abel-source
clock cone, actual prime-window supply, and terminal divisor-fibre geometry.
Research sources are local Lean only. No external novelty claim, numerical
experiment, full build, added axiom, or assumed RH/source-positivity input.

## Plan

1. Audit existing clock-cone, prime-window, and terminal-source declarations.
2. Prove actual distinct-prime realization with vanishing diagonal cost.
3. Transfer to literal Abel children and integer terminal fibres.
4. Audit leaf modules, axioms, umbrella wiring, lint, and scope of claims.

## Corpus inputs inspected

- `MobiusDivisorCompactClockCone.lean`: arbitrarily late positive mixtures
  uniformly approximate every continuous profile on `[0,a]`.
- Its spectral input was checked through `MobiusDivisorCompactClockSeparation`:
  `exists_simpleCritical_nonzero_of_exponentialType` in
  `FiniteDirichletCriticalNonannihilation.lean` uses the superlinear simple
  critical-zero census in `Zeta23SimpleCriticalDensity.lean`.
- `MobiusDivisorInheritedPrimeInsertionProducer.lean`: `cluster_capacity`
  supplies any fixed multiple of square-root-many primes in every sufficiently
  large proportional window; `cluster_members` retains actual primes.
- `MobiusDivisorAdaptiveTerminalCriticalSource.lean`: exact singleton
  `-sqrt(p) A(M/p)` after child primes are processed; terminal energy is the
  head square plus the sum of literal singleton squares.
- `SuzukiCausalDepthGammaJointCore.lean`: simultaneous source closure highlights
  why a common input must be retained across a continuum of output tests.
- `PaperThetaNativeMeyerCompleteness.lean`: original-source realization and
  full root-block completeness; no claim that this supplies an MC sign.

Searches returned usable local declarations but reported stale coverage
snapshots and unavailable semantic-coverage measurement. Applicability will be
checked by direct Lean compilation. Exhaustive `rg` found clock-profile uses
only in the three existing compact-clock leaves.

## Conjecture and attack

Let `F(t)(u)=exp(-3(t-u)/2) A(exp(t-u))`, `u in [0,a]`, where `A` is the
literal complete Abel source. For every continuous real target `f`, precision
`epsilon>0`, and depth threshold `T`, every sufficiently large integer scale
`N` admits a finite set of distinct actual primes `S` with

`p>sqrt(N)`, `log(N/p)>T` for every `p in S`,

such that

`||sqrt(N) sum_(p in S) p^(-1) F(log(N/p)) - f|| < epsilon`,

and the sum of the squared norms of those individual normalized prime
profiles is less than `epsilon`.

No adjustable weight is attached to an individual prime. Only the common
normalization `sqrt(N)` appears.

Attack: fixed cardinality cannot make diagonal cost vanish while preserving
a nonzero profile. Fixed reciprocal-prime mass is also unavailable in a
bounded proportional window. The surviving scale is `#S ~ sqrt(N)`:
first-order amplitudes stay finite, while quadratic diagonal cost vanishes.
This does not give uniform bounds on the source depths, prime threshold,
window size, or cost of an exhaustive history. No claim of RH follows.

Verdict: SURVIVES PRELIMINARY ATTACK relative to inspected local corpus.

## Dependency-closed paper proof

First approximate `f` within `epsilon/2` by a finite positive mixture
`sum_i c_i F(t_i)`, using the proved compact-clock cone with
`t_i>max(T,0)+1`. Remove zero coefficients and merge equal depths. Put
`r_i=exp(-t_i)>0`; the radii are distinct and strictly below `exp(-T)`.

The map `H(r)=r^(-1) F(-log r)` is continuous, in the uniform norm on the
whole clock interval, on `r>0`. Put `w_i=c_i r_i` and `W=sum_i w_i`.
Fix `delta>0` with `delta(W+1)<epsilon/4`. Choose one sufficiently narrow
common width `eta>0` so the proportional neighborhoods
`[r_i,(1+eta)r_i]` are pairwise disjoint, stay below `exp(-T)`, and satisfy
`||H(x)-H(r_i)||<delta` throughout each neighborhood. Continuity and finite
separation give all these conditions together. For this fixed width, the corpus prime-window theorem
supplies, for every sufficiently large integer `N`, a subset `S_i` of
primes in `(r_i N,(1+eta)r_i N]` with cardinality

`m_i=ceil(c_i r_i sqrt(N))`.

Indeed use `cluster_capacity` with coefficient `c_i sqrt(r_i)` at scale
`r_i N`. Finite intersections preserve the eventual supply. Disjoint windows
give distinct primes across all clusters, and `r_i N>sqrt(N)` eventually.

Ceiling error is between zero and one, so

`m_i/sqrt(N) -> c_i r_i`.

At every sufficiently large `N`, uniformly over every admissible choice of
these subsets, the difference between

`(1/sqrt(N)) sum_i sum_(p in S_i) H(p/N)`

and `sum_i (m_i/sqrt(N)) H(r_i)` has norm at most
`delta sum_i m_i/sqrt(N) < delta(W+1) < epsilon/4`.
The latter vector converges to `sum_i c_i F(t_i)` by the ceiling limit.
Thus their union approximates the original target within `epsilon` at
every sufficiently large scale, not merely along a subsequence.

Continuity bounds `||H||` on the finitely many neighborhoods by one finite
constant `C`. The total quadratic cost is bounded by

`C^2 sum_i m_i/N -> 0`.

This proves the exact conjecture, with no unproved analytic or arithmetic
input beyond the three named corpus theorems.

The all-sufficiently-large-scales form is stronger than the initial
arbitrarily-large-scales formulation. It was separately re-audited above:
fixing the neighborhoods after fixing the tolerance, before varying `N`,
is what proves the stronger quantifier.

The literal source relation is exact:

`sqrt(N)/p * F(log(N/p))(u)`
` = exp(3u/2)/N * sqrt(p) * A(N exp(-u)/p)`.

At integer cutoffs `M=N exp(-u)`, the negative of the unnormalized term is
the actual terminal singleton fibre. Since all selected primes exceed
`sqrt(N)`, they stay terminal throughout the whole cutoff interval.
Processing a canonical small-prime core retains the exact singleton law;
additional already-processed large primes outside the selected block do not
change those singleton values.

## Scope limits

- No paid exhaustion, monotonicity of every prime prefix, global energy
  control, or RH proof has been established by this construction.
- The target profile is fixed before the scale varies. There is no uniform
  realization threshold over arbitrary scale-dependent targets or inherited
  histories. The common normalization is essential; no bounded unnormalized
  synthesis cost is asserted.

## Completed implementation

- `MobiusDivisorPrimeWindowSynthesis.lean`: generic positive Banach-vector
  synthesis by one finite prime set; the proof retains both the first moment
  and quadratic diagonal from the same subsets of disjoint prime windows.
- `MobiusDivisorPrimeClockRealization.lean`: specialization to the compact
  Abel-source cone, exporting actual normalized prime atoms.
- `MobiusDivisorPrimeClockTerminalControl.lean`: exact Abel evaluation,
  one canonical small-prime core, freshness, and simultaneous control of
  literal singleton fibres at every integer cutoff in the clock interval.
- All three targeted `lake --old env lean -j 1 -o ...` builds exit 0 with
  empty output. No full or umbrella build was run; no heartbeat was raised.
- Existing Lean source changes are the three imports in `RHTower.lean`.
  Serena cannot address this ignored Lean tree; edits used precise patches.
- Whole-corpus search for the exact realization mechanism was run after the
  statement became precise. Closest inspected hits:
  `PrimeCoShiftRowGraph.exists_prime_uniform_vector` dilutes a constant
  coefficient sum over arbitrary primes; it does not realize an entire
  literal source profile at common cutoffs.
  `WeilLagPrimeQuadraticMesh.quadraticLagMesh_actual_primes` supplies a prime
  interpolation mesh, not joint source synthesis.
  `PrimeArchFiniteKMSLocalMomentClosure` defines a missing positive moment
  closure and receives it as a hypothesis; this construction does not claim
  to discharge that RH-strength hypothesis.

## Final audit

- The final `/tmp` audit imports the terminal leaf, checks the used mathlib
  names against this toolchain, and prints axioms for all eight public
  declarations. Exit 0. Every declaration uses only `propext`,
  `Classical.choice`, and `Quot.sound`; no new axiom or admitted proof.
- The main exports are
  `PrimePreparation.eventually_exists_prime_vector_synthesis`,
  `eventually_exists_criticalPrimeClock_realization`, and
  `eventually_exists_terminalPrimeClock_control`, under `RHTower`.
- All three imports appear once in `formal/GaloisForLFunctions/RHTower.lean`.
- `scripts/formal_tools.py index` exits 0. Global
  `scripts/formal_tools.py lint --check-generated` exits 1: ten concurrently
  added, unrelated modules are unwired and generated API/overview files
  changed after indexing. No error names any of these three leaves. The
  failing modules are `CHMDDeficitPrimitiveConjugatedTransportAndMobiusDilationInjection`,
  `FiniteWeilNodalAdjacentCoupling`, `FiniteWeilNodalMixtureTransport`,
  `ThetaCuspHawkingBMPWRetardedRegularity`, `ThetaCuspHawkingBMPWRetardedTriangle`,
  `ThetaCuspHawkingBMPWTwoResponseAction`, `ThetaCuspHawkingBMPWTwoResponseActionLimit`,
  `OneChannelPowerSolvability`, `OneChannelRootObservability`, and
  `OneChannelRootProjection`. Their work is preserved. Global lint is not
  claimed clean; formalization status records the successful leaf audits.
- Audited SHA-256 values:
  - window synthesis: `09796e1d7c31bb6a202e236ca4ddcea7eeb98c2c6ec56e5294fa63ec22020457`
  - clock realization: `fc4f59675c8311c139fbb0030dd3d87d39af9fdb092c23d9619292b6ceaea5cf`
  - terminal control: `3c31fba2dd042735148e47efc160ed800b69b9d89f1768497fe6699e21853cd6`

## Significance decision

COUNT ONCE. The earlier cone theorem allowed independently chosen positive
real weights. This theorem removes that relaxation: at every sufficiently
large common scale, distinct actual primes produce any prescribed compact
clock target, while the same prime block has arbitrarily small normalized
quadratic diagonal. The terminal theorem places this control in the literal
divisor geometry under one common processed core. Thus discrete availability
and diagonal cost are jointly removed as obstructions to prescribed finite
window control. No additional positivity or RH-strength source premise is
assumed. The scale-dependent and exhaustive-history problems remain open.
