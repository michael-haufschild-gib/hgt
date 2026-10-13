# Polynomial graph reconstruction and scalar tilted marginal

Status: formalized and audited (2026-10-12); repository lint has six unrelated errors.

## Objective and prior corpus

Construct a continuous polynomial graph recovering the actual finite joint
law from its first-coordinate marginal, for every real quadratic tilt. Reduce
the tilted marginal to an explicit scalar polynomial exponential tilt, and
prove that its equality detects equality of the full joint laws.

Local Lean only. The existing `WeilLogShiftJointLift` already reconstructs the
untilted joint law by a finite measurable lift, defined to vanish away from
the nodes. Its complete five-declaration indexed scope and source were read.
The new target is a continuous globally injective polynomial graph, arbitrary
real tilts, and the scalar exponential-family reduction; the old measurable
reconstruction is not claimed as new. A broad polynomial/marginal query was
exploratory, not an exhaustive novelty audit.

The previous increment supplies the unique first-coordinate polynomial
representative of every observable. The local `KLFactorizationSufficiency`
lemma `map_withDensity_comp` gives the pushforward of a factored density.
Its object is stale relative to source and direct dependency and must be
rebuilt before use; its direct dependency object is fresh.

## Dependency-closed paper proof

Let `P` interpolate the second coordinates of the `r+1` support points at
their distinct first coordinates. Then `degree P < r+1`. Set
`Γ(x) = (x, P(x))`. This graph is continuous and globally injective because
its first coordinate is `x`, and it recovers every support point exactly.
Therefore `Γ(π(z)) = z` almost everywhere for the base law and every real
quadratic tilt, where `π` is the first-coordinate map.

Map composition and almost-everywhere congruence give
`Γ_* (π_* μ) = μ` for every actual tilted law. The same graph works for every
tilt at fixed `r k`, so equality of the first marginals is equivalent to
equality of the full joint measures.

Define the scalar polynomial
`U = a*X^2 + 2*b*X*P + d*P^2`. Evaluation gives
`U(x) = Q(a,b,d)(Γ(x))`; hence the joint quadratic potential equals `U ∘ π`
almost everywhere under the base law. Exponential tilting respects such
almost-everywhere equality. For any measurable observer and measurable real
potential, pushing forward a tilt by the pulled-back potential equals tilting
the pushforward. This follows from the factored-density map theorem and the
change-of-variables identity for the exponential normalizer, including the
nonintegrable case where both normalizers yield the zero tilted measure.

Thus the first marginal of the actual joint tilt is exactly the first base
marginal tilted by `U`, and mapping that scalar tilted law through `Γ`
recovers the full joint tilt. Every measurability premise is discharged by
continuity at the concrete roots; no subcriticality or depth schedule is used.

## Plan and working log

1. Refresh the required stale density-map dependency; verify all native APIs.
2. Formalize polynomial graph, degree, continuity, injectivity and support recovery.
3. Formalize actual reconstruction and the marginal equality criterion.
4. Formalize pushforward/tilt compatibility and the explicit scalar tilt root.
5. Sequential native builds, umbrella wiring, complete declaration/axiom/index
   audits, source/object freshness, whitespace, and one lint snapshot.

## Native verification

Four new leaves are written: `RHTower/WeilLogShiftPolynomialGraph`,
`RHTower/WeilLogShiftPolynomialGraphRecovery`, `HTGeometry/TiltedPushforward`,
and `RHTower/WeilLogShiftPolynomialMarginalTilt`. They contain 18 declarations
(15 theorems, three definitions). All four leaves compiled cleanly, and all 16
API checks plus two concrete API examples passed. Full declaration index
coverage is 18/18 (10 + 3 + 1 + 4). Freshness, all 5 direct project edges,
8 total imports, 7 incoming imports, unique declarations, umbrella wiring,
and whitespace passed. The final native scratch audit imports the actual
scalar-tilt root and verifies 20 axiom reports: all 18 new declarations and
both edited dependency theorems. Only `propext`, `Classical.choice`, and
`Quot.sound` occur; all 16 API checks and both concrete examples passed, with
no residual diagnostics. All owned native processes are terminal.

The recovery leaf also proves that first projection recovers every scalar
measure after graph lifting. After a continuation invalidated its tool handle, the
graph build was recovered through an absent compiler process, empty log, and
fresh object; it was not restarted.

`KLFactorizationSufficiency` was rebuilt from current source. Two linter
warnings were repaired without changing logical statements: remove unused
`Set.indicator_apply` simp argument; rename unused `hcs` to `_hcs` in
`esscherLaw_eq_withDensity_comp`. All five current call sites were checked;
they pass that argument positionally. The rebuild now has an empty log.
Final audit must include both touched theorems as well as all new declarations.

The first API scratch attempt encountered a missing object for
`RHTower.WeilFullConeWindowPinning` in the existing import chain. An external
native compiler was confirmed live for exactly that module and published the
missing object. No duplicate build or source edit was made. API imports were
narrowed to the required local helper and installed Lean libraries so that
independent checks can proceed. Artifacts use `/tmp/hgt-weil-polynomial-graph-`;
the refreshed dependency log is `/tmp/hgt-polynomial-graph-KLFactorizationSufficiency.log`.

Potential later premise discharge: `_hcs : 0 ≤ cs` appears unnecessary in the
Esscher factorization theorem. It is retained in this increment for API
compatibility; removing it needs its own proof and caller audit.

The final lint snapshot has 367 warnings and six unrelated unreachable
RHTower modules: `JointAncestryRealAmplitudeCapstone`,
`JointAncestryRealAmplitudeDetection`, `PaperWoldMovingPrefix`,
`PaperWoldMovingRectangle`, `PaperWoldObservationClock`, and
`PaperWoldObservationScale`. No new or edited leaf has a lint error.

No web searches, external papers, or numerical experiments were used.

## Boundary

No bounds on the graph away from support, no uniform degree in `r`, no new
Gaussian limit interchange, and no claim that graphs coincide across depths.
