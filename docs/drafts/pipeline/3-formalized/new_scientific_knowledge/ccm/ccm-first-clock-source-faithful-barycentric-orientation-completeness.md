# CCM first-clock source-faithful barycentric orientation completeness

- **ID:** `ccm-first-clock-source-faithful-barycentric-orientation-completeness`
- **Stage:** 3-formalized
- **Type:** THEOREM (paper) / ROUTE-A POSITIVE-TRANSPORT COMPLETENESS
- **Source:** Hostile audit of the aperture-dependent positive-mixer survivor left by
  `ccm-first-clock-phase-natural-transport-rigidity`
- **Statement:** A finite nonnegative source packet admits a column-stochastic matrix that fixes
  the source and makes every transported dual phase coordinate nonnegative if and only if the
  original source--phase scalar is nonnegative. For the completed literal CCM first-clock packet,
  universal existence is exactly RH.
- **RH used:** no
- **Computation used:** no

## Goal

Close the strongest positive aperture-dependent matrix transport that does not already require
phase naturality. A candidate may choose a new nonnegative column-stochastic matrix at every
aperture, fix the literal source vector, and demand only coordinatewise nonnegativity of the dual
transported phase. This is substantially more permissive than a fixed intertwiner.

The hard question is whether existence of such positive mixers can create a new proof-producing
predecessor for the scalar first-clock floor. The theorem below gives an exact answer: no. The
source scalar is the invariant weighted average of the transported phase, while a canonical
rank-one barycentric collapse exists whenever that scalar already has the target sign.

## Gates

- [x] 0 → 1 in-progress: exact source-pure statement, hostile conjecture tournament, complete
  dependency-closed paper proof
- [x] 1 → 2 fully-proven: hostile proof and novelty audits complete
- [x] 2 → 3 formalized: Lean module, umbrellas, direct check, axioms, final SOTA module build
- [ ] 3 → 4 publication-ready: not proposed; generic barycentric parent is elementary

## Exact abstract theorem

Let `I` be finite. Let `w,s : I -> R`, assume

```text
w_i >= 0 for every i,       W := sum_i w_i > 0.             (1)
```

Call `M : I x I -> R` an oriented source-faithful Markov transport when

```text
M_ij >= 0,                         for every i,j,
sum_i M_ij = 1,                    for every column j,
M w = w,
(M^T s)_j >= 0,                    for every j.              (2)
```

Then

```text
there exists an M satisfying (2)  <->  0 <= w dot s.         (3)
```

The reverse implication has the explicit rank-one witness

```text
P(w)_ij = w_i / W.                                          (4)
```

It is column-stochastic, fixes `w`, and sends `s` under the dual action to the constant
nonnegative vector

```text
(P(w)^T s)_j = (w dot s)/W.                                 (5)
```

Thus `(3)` is both an obstruction and a classification, not merely a no-go.

## Completed literal first-clock packet

Fix `L>0` and a frequency `xi` satisfying `xi L=2 pi`. Use the finite index set

```text
J_L = Option {k : N | 2 <= k <= floor(exp L)}.
```

The extra `none` coordinate is the continuous Gamma--polar half-wave anchor. Define

```text
w_hat(none)   = C(L,xi),
s_hat(none)   = 1,
w_hat(some k) = k^(-1/2) Lambda(k),
s_hat(some k) = sin(xi log k),                               (6)
```

where `C(L,xi)` is `ccmFirstClockContinuousHalfWaveBudget L xi`. Existing unconditional source
identities give

```text
C(L,xi) > 0,
w_hat(j) >= 0,
w_hat dot s_hat
  = C(L,xi) + ccmFirstClockPrimeSineMass L xi
  = pi * ccmPublishedSourceSineCoefficient (L/2) xi.         (7)
```

Apply `(3)` to `(6)`. Since `pi>0`, at the physical frequency `xi=2 pi/L`,

```text
completed oriented source-faithful Markov transport exists at L
  <-> 0 <= ccmPublishedSourceSineCoefficient (L/2,2 pi/L).  (8)
```

Consequently

```text
for every L >= pi/2, such a transport exists
  <-> CCMFirstClockPublishedSourceNonnegative
  <-> RiemannHypothesis.                                    (9)
```

The last equivalence uses the already formalized first-clock completeness theorem; it does not
assume RH.

## Dependency-closed paper proof `[PROVED HERE]`

### Necessity — source scalar is an invariant weighted average

Assume `M` satisfies `(2)`. Since `w_i>=0` and every `(M^T s)_i>=0`,

```text
0 <= w dot (M^T s).
```

Transpose adjointness and source faithfulness give

```text
w dot (M^T s) = (M w) dot s = w dot s.                      (10)
```

Hence `0<=w dot s`. Notice that neither entrywise positivity nor stochasticity is used in this
direction: source faithfulness plus dual coordinate orientation already forces the target scalar
sign.

### Sufficiency — canonical barycentric collapse

Assume `0<=w dot s` and define `P(w)` by `(4)`. From `(1)`, every entry is nonnegative. Every
column has sum

```text
sum_i P(w)_ij = (sum_i w_i)/W = 1.
```

For each row `i`,

```text
(P(w) w)_i = sum_j (w_i/W) w_j = (w_i/W) W = w_i,
```

so the source is fixed. Finally `(5)` follows by the same finite-sum calculation, and it is
nonnegative because `W>0`. Thus `P(w)` satisfies all of `(2)`, proving `(3)`.

### CCM specialization

The anchor weight in `(6)` is strictly positive by the midpoint-reflection theorem. Every
critical-Mellin atom weight is nonnegative because `Lambda(k)>=0` and `k^(-1/2)>=0`. Therefore
`sum_j w_hat(j)>0`. Expanding the finite `Option` sum gives the first equality in `(7)`; the
formalized half-wave budget law gives the second. The abstract equivalence `(3)`, positivity of
`pi`, and the formalized first-clock completeness theorem prove `(8)--(9)`.

No analytic limit, numerical evidence, zero-location input, or unproved spectral statement enters
the proof.

## Heavy-conjecture tournament and hostile audit

### C0 — fixed phase-natural source-faithful mixer

Dead by phase-natural transport rigidity: the only such mixer is the identity. A nontrivial fixed
cross-prime mixer necessarily creates a phase-connection defect at an explicit aperture.

### C1 — arbitrary aperture-dependent positive Markov mixer

Exactly classified by `(3)`. It always exists after the target scalar has the desired sign, via
`P(w)`, and cannot exist before that sign, by `(10)`. Therefore existence is logically identical
to the scalar target and supplies no independent positivity mechanism.

### C2 — optimize over positive mixers or impose strict positivity

No gain. When all source weights are positive, the canonical witness `(4)` is entrywise strictly
positive. Optimization over a class already containing `P(w)` still has feasibility boundary
`w dot s=0`. For the literal packet, zero von Mangoldt coordinates can be removed by restricting
to prime powers, but that changes neither scalar nor boundary.

### C3 — nonlinear source-faithful map

Not classified here. Merely naming a nonlinear map is not a mechanism: it must expose a new
source-defined monotone quantity whose proof does not use the target sign. Any differentiable
family whose linearized dual phase is coordinatewise oriented remains subject to `(10)` at that
linearization.

### C4 — aperture connection current with signed intermediate coordinates

Survives as a genuinely different mechanism. It must retain and orient the nonzero connection
defect forced by phase-natural rigidity. It is not a positive Markov repackaging of one aperture's
source scalar and therefore must be tracked as a successor route, not as an unfinished part of
Route A.

## No-go closure

- **Exact killing theorem/mechanism:** the source scalar is the `w`-weighted average of every
  source-faithful dual transport. Coordinatewise orientation forces its sign; canonical
  barycentric collapse proves this is the only feasibility obstruction.
- **Strongest positive survivor:** the explicit rank-one matrix `P(w)` is the universal positive
  source-faithful orienter, and its output is exactly the normalized scalar source. This gives a
  sharp classification and a canonical certificate when the sign is already known.
- **New insight:** allowing unrestricted aperture dependence does not rescue positive transport.
  Fixed natural transports collapse to identity; arbitrary positive Markov transports collapse to
  the target scalar. A non-theatrical successor must introduce an oriented connection current,
  signed intermediate geometry, or another source-first invariant absent from `(2)`.
- **Status:** dependency-closed paper proof. Generic finite barycentric algebra is elementary;
  novelty claim is limited to the sharp CCM completed-packet connector, joint closure with
  physical-phase naturality rigidity, and exact identification of the remaining mechanism class.

## Anti-theatre boundary

The existential transport statement is not evidence for RH: by `(9)` it is literally an
RH-equivalent reformulation. Constructing `P(w)` after assuming source nonnegativity creates no new
knowledge. The new knowledge is the completeness classification: every positive
source-faithful coordinate-orientation attempt, including aperture-dependent ones, has exactly
the original scalar sign as its feasibility obstruction.

This theorem does not disprove RH and does not prove the source floor. It closes a mechanism class.
Connection-valued or signed nonlinear successors remain open only after being separated into a
new route with their own source-first theorem.

## External priority audit

Exact-term searches over current arXiv primary literature found no source-faithful Markov or
barycentric-transport formulation of the CCM first-clock source. Connes--Consani--Moscovici
(`arXiv:2511.22755`) construct finite self-adjoint operators but leave convergence to the zeta
zeros, and determinant convergence to Xi, unproved. Suzuki's screw-function and operator-limit
papers (`arXiv:2206.03682`, `2209.04658`, `2606.09096`) supply RH-equivalent positivity or
convergence targets, not this finite completed-packet transport classification. Groskin's exact
finite Guinand--Weil dictionary (`arXiv:2607.02828`) explicitly does not prove global positivity.

No novelty is claimed for the generic finite identity `(3)`, which is elementary barycentric
linear algebra. Scoped new content is `(7)--(9)` and its joint terminal interpretation with the
physical-phase transport-rigidity theorem.

## Falsifiers

- a nonnegative finite source vector of positive total mass and an oriented source-faithful matrix
  with negative source--phase scalar;
- a nonnegative source vector with nonnegative source--phase scalar for which `(4)` fails any
  condition in `(2)`;
- a literal completed CCM packet whose dot product differs from the budget-plus-prime source in
  `(7)`;
- universal completed transport existence without the RH-equivalent first-clock source floor.

## Lean certificate

`RHTower/CCM/CCMFirstClockBarycentricOrientationCompleteness.lean` defines finite oriented
source-faithful column-stochastic transport, formalizes invariant necessity and explicit
barycentric sufficiency, defines the completed CCM `Option` packet, proves its exact scalar
identity, and closes aperturewise and universal equivalences.

Audited endpoints:

```text
ccmBarycentricSourceTransport_mulVec
ccmBarycentricSourceTransport_transpose_mulVec
ccm_orientedSourceFaithfulMarkovTransport_iff_dotProduct_nonnegative
ccmFirstClockCompletedPacket_dotProduct
ccmFirstClockCompletedMarkovOrientationAtFrequency_iff_source_nonnegative
ccmFirstClockAllCompletedMarkovOrientations_iff_rh
```

The module is wired into `RHTower.lean` and `RiemannHypothesisSOTA2026.lean`.
`lake build GaloisForLFunctions.RHTower.RiemannHypothesisSOTA2026` passed 9,960 jobs. Scratch
`#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound`.

## Log

- 2026-08-01 — frozen after the fixed-intertwiner classification exposed aperture-dependent
  positive transport as the strongest surviving Route A predecessor class.
- 2026-08-01 — paper proof formalized through universal completed-packet `↔ RH`, both umbrellas
  wired, direct check and SOTA build passed; promoted to Stage 3.
