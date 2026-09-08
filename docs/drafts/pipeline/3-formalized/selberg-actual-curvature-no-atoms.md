# No point atoms in actual Maass curvature

- **ID:** selberg-actual-curvature-no-atoms
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** [Active Selberg research loop](../1-in-progress/selberg-quarter-conjecturing-loop.md), cycle 35; [actual curvature measure](selberg-actual-curvature-measure.md).
- **Statement:** For every original principal-congruence Maass source at every real eigenvalue, its constructed positive curvature measure assigns zero mass to every singleton and every countable subset of the upper half-plane.

## Goal and limits

Remove point-charge uncertainty before descending actual curvature through modular identifications. No nonvanishing assumption at the point is needed. This does not remove charge carried by nodal curves or modular seam curves. A quotient total budget and the source-derived quarter comparison remain open; Selberg is not proved.

## Gates

- [x] 0 → 1: original source and constructed measure, precise point-mass assertion.
- [x] 1 → 2: dependency-closed paper proof below, [PROVED HERE].
- [x] 2 → 3: complete scratch/source proofs, both final targeted builds, all 27 declaration axiom audits, and repository formal lint passed.
- [ ] 3 → 4: independent novelty/publication audit.

## Complete paper proof [PROVED HERE]

Let a(z)=sqrt(D(z)) be the actual finite-trace amplitude and b(z)=a(z)/y². The existing source theorems prove that both are continuous on the upper half-plane H, including every common source zero. The constructed positive regular measure mu has the exact identity

integral_H phi dmu = integral_C Delta(phi) a + lambda integral_C phi b

for every C² compact planar test supported inside H. Each source product and restricted measure test is genuinely integrable under those already checked support and continuity conditions.

Fix c in H. Choose the literal planar smooth bump chi with inner radius one and outer radius two. It is nonnegative, equals one at zero, and has compact support in the radius-two closed disk. For r>0 define chi_r(z)=chi(r^(-1)(z-c)). Composition with the affine homeomorphism preserves compact support and C² regularity. Its support is contained in the closed disk of radius 2r about c, hence lies in H whenever 2r<Im(c).

The existing complex C² holomorphic chain rule, together with the checked real-to-complex Laplacian identity, gives

Delta(chi_r)(z)=r^(-2) Delta(chi)(r^(-1)(z-c)).

The actual additive Haar change-of-variables theorem in real dimension two gives integral F(r^(-1)(z-c)) = r² integral F. Consequently

integral |chi_r| = r² integral |chi|,
integral |Delta(chi_r)| = integral |Delta(chi)| = C < infinity.

For every sufficiently small r the local Green identity applied to the constant function one proves integral Delta(chi_r)=0. Therefore, with genuine integrability on both sides,

integral Delta(chi_r) a = integral Delta(chi_r)(a-a(c)).

Continuity of a at c implies that, for every delta>0, |a(z)-a(c)|<=delta on every sufficiently small chi_r support. The support of Delta(chi_r) is contained in that same support. The norm-integral inequality now bounds the last pairing by delta*C. Taking delta=epsilon/(C+1) proves that the Laplacian pairing tends to zero.

Continuity of b at c bounds |b| by B=1+|b(c)| on sufficiently small supports. Its pairing has absolute value at most B r² integral |chi|, which also tends to zero. The exact actual source identity therefore gives integral_H chi_r dmu -> 0. Here r is a spatial radius; the measure was constructed earlier using its own regulator limit. No two limits are interchanged.

Since chi_r is nonnegative and chi_r(c)=1, positivity and the measure/integral inequality give

mu({c}) <= ofReal(integral_H chi_r dmu)

for every sufficiently small positive r. The positive-radius filter is proved nontrivial. Continuity of ENNReal.ofReal and closedness of order let r tend to zero, yielding mu({c})<=0. Thus mu({c})=0. As c was arbitrary, the actual measure has NullSingletonClass. Every countable subset has measure zero by countable subadditivity.

## Conjecture/proof/pivot record

The initial proposal sought regulator-uniform gradient estimates and a small-ball flux bound. Corpus inspection exposed a weaker sufficient input for point atoms: zero total Laplacian plus exact two-dimensional scaling. The completed proof needs only continuity of the original amplitude, so it also covers its nodal points. This is a proved positive replacement for that intermediate route, not a falsification of the stronger local-growth conjecture.

The cutoff-scaling mechanism came from HTGeometry.ScaledCutoff. Bottcher.Brolin.RieszLogIBP.integral_laplacian_eq_zero links constant-mode cancellation to the already inspected ball-flux identity. The formal implementation reuses the lighter existing SelbergLocalTestGreen identity with constant source, and reuses SelbergMaassCurvatureCovariance.laplacian_ofReal for the affine scaling proof. Current-toolchain Haar scaling supplies the exact area factor.

All alternative corpus searches used --any. Local-growth/flux/scaled-cutoff search: 150 declarations in 72 modules. Cancellation/continuous-potential search: 6 in 6. Elliptic/proper-action/overlap-weight search: 32 in 20. Weighted-descent/orbit-sum search: 185 in 66. These describe indexed coverage, not inspection of every result.

For the next quotient step, inspected ThetaCuspHawkingBMCompactTestUnfolding proves finite translate support on the entire modular cell, including seams and elliptic points. Its integral unfolding still uses the hyperbolic-volume fundamental-domain theorem, which does not automatically transfer to the curvature measure. ThetaCuspHawkingBMCompactModularPeriodization.modular_orbit_height_le provides actual orbit-height control. WeightedOrbitInvariantExistence normalizes weighted orbit problems on group carriers, but its injective orbit parametrization does not apply unchanged to the modular action with stabilizers. These are mechanisms for a new proof, not supplied descent hypotheses.

## Lean and verification

- formal/GaloisForLFunctions/RHTower/SelbergPlanarTestScaling.lean: 17 public declarations.
- formal/GaloisForLFunctions/RHTower/SelbergMaassCurvatureNoAtoms.lean: 10 public declarations including the NullSingletonClass instance.
- Complete scratch proofs and needed source olean checks passed without warnings. Modules wired into RHTower.lean; no umbrella build ran.
- Serialized final single-module builds passed, rebuilding only their named target: scaling (28s), atomlessness (10s). Logs: /tmp/selberg_planar_scaling35_build.log and /tmp/selberg_curvature_noatoms35_build.log. Both replayed the existing informational EvenL2LogUnitary tactic suggestion; neither new module emitted a warning.
- /tmp/selberg_curvature_noatoms35_axioms.lean audits all 27 public declarations, including the NullSingletonClass instance. All report only standard Lean axioms; no added axioms, admissions, or audit warnings. Log: /tmp/selberg_curvature_noatoms35_axioms.log.
- Generated indexes refreshed; all 27 declarations verified in /tmp/selberg_curvature_noatoms35_corpus_audit.json. Task-source/card/umbrella whitespace checks passed.
- **Repository formal lint passed**, with existing large-file warnings. Full stdout/stderr log: /tmp/selberg_curvature_noatoms35_lint.log. This supersedes the previous turn's unrelated wiring failure.
- Every task-owned process handle is terminal. Final inspection found no Lean or Lake process (/tmp/selberg_curvature_noatoms35_processes.log). No numerical experiments, full builds, task commits, or pushes.
