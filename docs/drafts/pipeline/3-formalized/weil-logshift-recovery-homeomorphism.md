# Fine-mesh histories as exact coefficient coordinates

Status: FORMALIZED. Dependency-closed paper proof, final leaf compile/export,
and all public axiom audits passed on 2026-10-09.

Source policy: our Lean corpus only. No external papers, web searches, or
numerical experiments. Previous cutoff-reconstruction increment is verified.

## Corpus audit

- `WeilLogShiftCutoffReconstruction.lean`: finite triangular sample-difference
  formula, strictly positive diagonal, finite-prefix equality equivalence, and
  full visible-coefficient injectivity.
- `WeilLogShiftFirstProbeInterpolation.lean`: staged exact corrections and a
  stabilized diagonal sequence, previously for sparse integer-cutoff lifts.
- `HTGeometry/GammaBellSubstitution.lean`: finite triangular back-substitution
  proof pattern; it is not an existing inverse for this infinite recovery map.
- `HTGeometry/TailCoefficientLinearSolve.lean`: finite polynomial triangular
  dependence, not the present infinite linear sequence transform.
- `HTGeometry/TriangularSolveContinuity.lean`: a constant complex diagonal
  solver and continuity proof. The current real, row-dependent diagonal is
  handled directly by the existing probe correction and prefix identities,
  avoiding a complex conversion and unrelated imports.

## Conjecture and paper proof

Every real sequence h_k is the recovery history Q(L_(k+2)) of exactly one
coefficient sequence with lambda(0)=lambda(1)=0. The correspondence and its
inverse are continuous for coordinatewise convergence.

Begin with zero coefficients. At stage k change only coefficient k+2 by
(h_k-Q_current(L_(k+2)))/w_(k+2,k+2). Positive diagonal makes the new sample
exact. Tail vanishing leaves all prior samples unchanged, and each coordinate
stabilizes. The diagonal of the stages realizes the entire target sequence.
The previous finite-prefix theorem proves uniqueness, including the two fixed
invisible coordinates separately.

The forward coordinate map is a constant plus a finite weighted sum of input
coordinates, by the existing difference formula relative to zero. It is
continuous. Every stage coordinate is a finite composition of coordinate
evaluation, such a probe, addition, subtraction, and division by a fixed
nonzero scalar. Hence each inverse coordinate, a fixed-stage coordinate, is
continuous. Assemble a homeomorphism between the zero-head coefficient
subspace and arbitrary real sequences, each with product topology.

The topology claim is coordinatewise. No uniform-norm stability or coefficient
growth bound is claimed.

## Formal result

Leaf: `formal/GaloisForLFunctions/RHTower/WeilLogShiftRecoveryHomeomorphism.lean`.
Three definitions and nine public theorems. The two affine-probe lemmas now live
in imported `WeilLogShiftRecoveryAdaptive.lean`, retaining their names and statements:

- `weilLogShiftRecoveryProbe_affine`,
  `continuous_weilLogShiftRecoveryProbe`: finite affine coordinate formula and continuity.
- `weilLogShiftRecoveryHistory`: reindexes sample n=k+2 as history coordinate k.
- `weilLogShiftRecoveryHistory_eq_iff`,
  `continuous_weilLogShiftRecoveryHistory`: exact visible-coefficient equality
  criterion and forward product-topology continuity.
- `weilLogShiftRecoveryInverse`, `weilLogShiftRecoveryInverse_head`: explicit
  stabilized inverse, with coordinates zero and one equal to zero.
- `weilLogShiftRecoveryHistory_inverse`: every real sequence is realized exactly.
- `weilLogShiftRecoveryInverse_history`: reconstruction of any coefficients is
  exactly their normalization at the two invisible coordinates.
- `existsUnique_weilLogShiftRecoveryHistory`: every history has exactly one
  zero-head coefficient representative.
- `continuous_weilLogShiftRecoveryInverse`: inverse product-topology continuity.
- `weilLogShiftRecoveryHomeomorph`: the packaged homeomorphism between the
  zero-head coefficient subspace and arbitrary real history sequences.

## Verification

- Final leaf compile/export: exit 0, no diagnostics on its first compilation.
- All twelve public declarations: exactly `[propext, Classical.choice, Quot.sound]`.
- Umbrella wired; index refreshed after final compilation; all twelve API entries inspected.
- Global lint: exit 1, one unrelated module unreachable from its umbrella:
  `RHTower.PaperMaassFourierReconstruction`. No error concerns this leaf;
  the out-of-scope module was not modified.
- Scratch API checking replaced deprecated `continuous_finset_sum` with
  `continuous_finsetSum`. A recursive simplification of the affine formula was
  replaced by one whole-function rewrite; no recursion/heartbeat limit was raised.
- No external sources, numerical experiments, new analytic premises/axioms,
  umbrella builds, commits, pushes, or subagents.

## Follow-up proved: bounded samples, divergent moments

`exists_bounded_recovery_with_divergent_excess_and_deficit` now proves the
previous next conjecture: every recovery sample can have absolute value 1 while
both one-sided moments and the signed series diverge. Its stronger intermediate
theorem forces every absolute potential term at n≥2 to be at least 1/2.
The adaptive positive survivor generalizes this leaf's former private builder;
the homeomorphism now specializes it. All twelve original declarations and nine
new declarations passed compilation and standard-axiom audits. See
[the formalized follow-up](weil-logshift-bounded-recovery-no-go.md) for the exact
proof, declarations, and newer global lint snapshot.
