# Maximal literal domain of the critical prime-log Laplace synthesis

- **ID:** prime-log-maximal-laplace-domain-2026-10-17
- **Stage:** 3-formalized
- **Type:** THEOREM (paper proof and exact Lean proof complete)
- **Source:** whole local Lean corpus; next independent lead in the 100-theorem goal
- **Statement:** The closed finite-prime cubic Laplace synthesis has exactly
  the maximal literal L2 domain, with a canonical damping semigroup that
  admits every damped prime-l2 source and gives a graph core.

## Goal

Replace an abstract graph-closure admission condition by an exact condition
on the actual infinite Dirichlet-Laplace source. The closed domain has no
additional boundary condition at time zero. Counted once as contribution 4.
A generic
closed-operator wrapper, another unboundedness statement, or an assumed graph
approximation would not meet the significance requirement.

Let T be `primeLogCriticalLaplaceSynthesis` and let a belong to the actual
prime l2 source. For t > 0, put

`F_a(t) = 2 t sum_p a_p (log p)^2 p^(-1/2-t)`.

Positive-time evaluation is already a bounded source functional in the corpus.
The proved exact theorem is

`a in domain(closure T) iff F_a in L2((0,infinity),dt)`,

with `closure T(a)` equal to the literal L2 class of F_a. For epsilon > 0,
`M_epsilon(a)_p = p^(-epsilon) a_p` maps the entire source l2 into the
closed domain, with a Hilbert-Schmidt synthesized output. On the closed graph,
it intertwines with the contraction

`R_epsilon(F)(t) = t/(t+epsilon) F(t+epsilon)`.

All these conclusions count together as one structural contribution.
There is no RH assumption or missing arithmetic cancellation premise.

## Gates

- [x] 0 → 1: precise source-pure candidate and explicit endpoint mechanism.
- [x] 1 → 2: dependency-closed paper proof and complete local novelty/significance audit.
- [x] 2 → 3: exact Lean theorem, targeted single-job builds, axioms and wiring.
- [ ] 3 → 4: publication audit if authorized.

## Source evidence

- `PrimeLogCubicLaplaceGraphFormation.lean` defines the literal columns
  `2 t (log p)^2 / sqrt(p) * exp(-t log p)`, proves their exact cubic Gram
  identity, bounded positive-time evaluation, density of the finite-prime
  source, and closability. It does not state the proposed maximal-domain law.
- `PrimeLogCongruenceLaplaceSynthesis.lean` connects this synthesis to actual
  finite congruence deformations and the obstruction to a bounded synthesis.
  Its complete scope was inspected; bounded subcritical synthesis alone does
  not identify the original critical closed domain.
- `PrimeLogThetaLowerClosedGraphLanding` and its four-level extension retain
  finite-core theta reporters. Every reference to the critical synthesis was
  inspected; these do not supply maximal-domain admission.
- Whole-corpus searches returned `partial=false`; all candidate-lemma and
  source-argument hits were inspected. Relevant additional mechanisms include
  `HTGeometry.HilbertSchmidtOperator`, half-line translation/causal semigroups,
  and Burnol graph cores. These are leads; exact applicability is not assumed.
- Existing Hardy first-trace no-escape and bounded-completion saturation laws
  were inspected while closing contribution 3. They concern a different
  source topology and do not themselves construct this maximal Laplace domain.

## Paper mechanism

1. The cubic Gram diagonal gives squared column norm `log(p)/p`. Damping by
   `p^(-epsilon)` makes the sum of squared column norms finite for every
   epsilon > 0, using the existing logarithmic Dirichlet summability result.
   Thus damped synthesis is Hilbert-Schmidt on all prime l2. Finite-prime
   truncations converge in both source and output norms after damping.
2. Check the literal identity
   `p^(-epsilon) feature_p(t) = t/(t+epsilon) feature_p(t+epsilon)`.
   Bounded positive-time evaluation extends it from finite packets to all
   prime-l2 sources, without exchanging a conditionally convergent series.
3. R_epsilon is an L2 contraction and tends strongly to the identity as
   epsilon decreases to zero. Use half-line translations and the bounded
   multiplier t/(t+epsilon). M_epsilon also tends strongly to the identity.
4. If F_a is L2, the damped graph pairs converge to (a,F_a); hence the pair
   lies in the closure of the finite-prime graph. This removes any additional
   endpoint boundary condition and any unproved core premise.
5. Conversely, graph convergence and bounded pointwise evaluations identify
   every closed-graph output with F_a almost everywhere, using the same L2
   subsequence mechanism already used for closability.

The completed audit below checks norm/measure normalizations, pointwise
representatives, Hilbert–Schmidt synthesis, strong weighted translation and
the distinction from an abstract completion wrapper. Lean verification below
discharges the final counting gate.

## No-go closure

No new route is retired. The existing obstruction to a bounded critical
synthesis remains valid. Its positive survivor is the exact maximal closed
domain and unconditional damped source class proved here on paper and in Lean.

## Completed paper and source audit

The exact normalization is ordinary complex `lp` at exponent 2 on `Nat.Primes`
and `Lp` at exponent 2 for Lebesgue measure restricted to `(0,infinity)`.
No frequency weight is silently moved into the source norm. The pointwise
profile is the inner product against `primeLogCriticalEvaluationVector` at
positive time; it agrees with the absolutely convergent displayed series.
Define it to be zero outside the positive half-line.

For each epsilon > 0 take the existing congruence synthesis with d=epsilon,
u=0, divided by sqrt(8 epsilon). Its columns are exactly
`p^(-epsilon) feature_p`. The existing summability iff theorem supplies its
Hilbert–Schmidt property with all hypotheses discharged. The source multiplier
is a contraction diagonal; `PaperDiagonalStrongConvergence` proves strong
convergence of these diagonals to the identity. For every finite packet its
damped source and bounded synthesized output form a literal graph point.
The continuous map sending a to this pair takes the dense finite-prime source
into the closed graph, so every damped l2 source is admitted.

The output contraction is exactly `burnolWeightedShift`. On each
`burnolDepthFeatureL2 ell n` its eigenvalue is `exp(-epsilon (n+1) ell)`,
which tends to 1. Linearity gives convergence on `burnolDepthSpan`; its
proved density and the norm bound 1 extend convergence to every L2 vector
by `StrongConvergenceDense.tendsto_of_dense_of_uniform_bound`.
This proves the required strong zero-time limit without any boundary trace.

For every finite packet the literal exponential identity gives
`F_(M_epsilon a)(t) = t/(t+epsilon) F_a(t+epsilon)` for t>0.
Both sides are continuous source functionals at fixed t, so source density
extends the identity to all l2. If F_a is L2, the admitted damped output equals
`burnolWeightedShift epsilon` applied to its L2 class: forward graph
identification proves this equality almost everywhere, and the existing
quasi-measure-preserving positive translation validates the shifted
representative. Both coordinates converge as epsilon tends to zero, hence
closedness admits (a,F_a).

For the converse, approximate any closed-graph point by literal finite graph
points. Continuous positive-time evaluation identifies the pointwise limit
as F_a. The existing L2 almost-everywhere subsequence theorem identifies that
same limit with the output. Thus the output equals F_a almost everywhere,
and F_a is L2. This also proves output uniqueness and the exact domain iff.

Adversarial checks: an L2 representative cannot be evaluated at a fixed time,
so evaluation is always performed on the source and only compared to outputs
almost everywhere. Positive translation preserves the needed null-set
identity. No bound uniform as epsilon tends to zero is asserted for damped
synthesis. The original critical synthesis remains unbounded; real-axis
theta readers remain obstructed. This result imposes no trace at t=0 and
assumes neither RH nor arithmetic cancellation.

Exhaustive source search found six files referring to the actual critical
synthesis; every call site was inspected. They establish formation,
closability, the bounded/Hilbert–Schmidt threshold, finite-core injectivity,
lower-half-plane reporters and real-axis reader obstructions. None supplies
this maximal-domain classification. `BurnolGraphActionFiltration` concerns
an already bounded primitive synthesis and its large-time action, so does
not prove critical-domain admission. Whole-corpus hybrid searches inspected
both candidate lemmas and source arguments; the latest completed search
reported partial=false, 73,081 files, 61,409 Lean files, 1,081,856 declarations.
Compiler metadata is mixed; targeted Lean checking remains mandatory.

Significance: this joins the unbounded critical congruence boundary to the
Burnol output action and diagonal completion mechanism, removing a genuine
source-admission premise. It constructs the full damped l2 source class and
classifies every undamped admissible source by its literal profile. All
domain, damping, intertwining and core conclusions count together once.

## Exact formal result and verification

Primary declarations in `RHTower/PrimeLogLaplaceMaximalDomain.lean`:

- `primeLogCriticalLaplaceClosure_domain_iff`: for every actual prime-l2
  source a, membership in the original closed domain is equivalent to
  `MemLp (primeLogCriticalLaplaceProfile a) 2 (volume.restrict (Ioi 0))`.
- `primeLogCriticalLaplaceClosure_graph_iff`: the graph consists exactly of
  pairs whose output equals the literal source profile almost everywhere.

The profile is defined through the existing source evaluation vector, and
`primeLogCriticalLaplaceProfile_tsum` proves the literal infinite-prime
series identity at every positive time. The unconditional class is supplied
by `primeLogLaplaceDamped_pair_mem_closureGraph`: every positive damping
of every actual prime-l2 source lies in this same closed graph. Its actual
synthesis is Hilbert–Schmidt by
`primeLogLaplaceDampedSynthesis_isHilbertSchmidt`. No RH, bounded critical
extension, assumed source admission or graph approximation occurs in these
signatures. The weighted-shift identity and strong zero-time limits are
proved, not additional hypotheses.

Four final targeted `lake --old env lean -j 1 -o ...` builds exited 0 with
empty logs. Every new module is imported exactly once by its area umbrella.
All four output oleans were newer than their unchanged source files.
A separate `/tmp` audit checked the two primary signatures, both unconditional
damping signatures and 12 supporting/primary axiom closures: only
`propext`, `Classical.choice`, `Quot.sound`. `scripts/formal_tools.py index`
exited 0; `scripts/formal_tools.py lint --check-generated` exited 0 with
`formal lint passed` and existing large-file warnings. No umbrella build,
heartbeat increase or frontier-map edit was performed.

Final source SHA-256:

| Module beneath `formal/GaloisForLFunctions` | SHA-256 |
| --- | --- |
| `HTGeometry/BurnolWeightedShiftStrongContinuity.lean` | `da2f5de2ad5326568be9bc5268153a315cd336569e937d8d902ae791ae1930bf` |
| `RHTower/PrimeLogLaplaceClosedGraphLiteral.lean` | `1d483d983bfc03b5c8ea471ff5fbd85b76a10a8fd784279c6555130978f7c92b` |
| `RHTower/PrimeLogLaplaceDamping.lean` | `015a3e8385217218fc021d67a3d6443b6e3da4d660361d08a149923a4010e5b3` |
| `RHTower/PrimeLogLaplaceMaximalDomain.lean` | `63930d0851d91e72813b2769b3c0edb76183b76d31fa15921215bb02396ae39a` |

## Log

- 2026-10-17: all final gates passed; counted once as contribution 4/100.
  Rechecked all four final source hashes, then deleted 20 exact owned search,
  scratch, diagnostic and build/audit temporary files. No owned Lean job remains.
- 2026-10-17: `PrimeLogLaplaceDamping.lean` compiles with an empty log.
  The entire damped l2 source is admitted to the original closed graph;
  its actual output is Hilbert–Schmidt. The final maximal-domain leaf is
  under verification. The three finished leaves are wired.
- 2026-10-17: paper proof and whole-corpus source/significance audit complete.
  `BurnolWeightedShiftStrongContinuity.lean` and
  `PrimeLogLaplaceClosedGraphLiteral.lean` compile with empty logs under
  targeted single-job Lean. Damping and the maximal-domain converse are
  drafted and under verification. Candidate remains uncounted.
- 2026-10-17: two whole-corpus hybrid searches and initial exact source reads;
  no new Lean code for this candidate. Compiler metadata is mixed/stale.
- `docs/reports/rh-current-frontier-map.md` remains read-only.
