# WP07: exact spatial defect checkpoint

Goal remains ACTIVE and OPEN. Previous memory: `mem:research/weil-work-07-poisson-quarter-2026-10-07`. Current cycle is PROGRESS, classical BRIDGE / REDISCOVERED, not a scientific novelty or full-rigidity claim. No subagents used.

## Verified work

Owned modules under formal/GaloisForLFunctions/RHTower/:
- WeilWorkHigherDenominatorWeightedIntegral.lean: added hasDerivAt_weighted_compact_parameter, complex dominated differentiation with a compact parameter range and fixed real integrable weight.
- WeilWorkHigherDenominatorPoissonAnalytic.lean: four public theorems establish positive real part of the complexified quadratic denominator, derivative of its negative-half power, exact real restriction, and horizontal real analyticity of every actual polynomial mode.
- WeilWorkHigherDenominatorSpatialDefect.lean: maass_defect_eq_poisson_packet and degreeThree_infiniteDeficits_or_spatialDefect. The latter uses only the original ZetaPowerDatum 3 g E and E(1) != 0. It derives coefficient growth and all uniqueness premises, retains every nonzero residue polynomial, and identifies the finite packet throughout the upper half-plane.

Each final foreground direct lake --old env lean -o ... check passed without diagnostics. All seven new public theorem axiom audits print exactly propext, Classical.choice, Quot.sound. Both new modules are wired into RHTower. No umbrella/full build, numerical experiment, resource-limit increase, commit or push. SpatialDefect's first compile had only an empty-sum simplification error; fixed using quarterDefect_const_mul with scalar zero.

Latest lint exits 1 on eight unrelated unreachable modules: RHTower WeilWorkDeficitRepairCost, WeilWorkSettledPhaseForwardRegularPart, WeilWorkSingularArithmeticCanonicalGaussian; HTGeometry ApertureConeCalculus, ApertureConeWinding, ApertureLogTranslation, ApertureOpenHistoryIdeal, BoundaryCoronaCStarAlgebra. All error lines inspected; no WP07 error. Owned whitespace and forbidden-source scans pass. Anti-theatre five and anti-laziness four answers posted.

## Next exact proof

The first unpaid Lean step is the moving-point polynomial boundary limit:
polynomialPolarMode(rho,P)(x+i*y)/(sqrt(y)*log(y)) -> -2*x0^(-rho)*P(log(x0)) as x->x0>0 and y->0+, with no rate coupling.

PROOF.md now records a dependency-closed proof using positive dilation. At x=1, subtract P(0) times the known scalar singularity; the corrected weight vanishes at 1, is locally Lipschitz, and has an integrable tail by LogMoments plus norm_polarKernel_boundary_tail. Its integral is uniformly bounded in 0<y<=1. Divide by log(y) to obtain -2*P(0).

For moving x use the already checked integral_polynomial_polarKernel_dilate in AxisPolynomial. Expand P(log(x)+log(abs(t))) as a finite binomial sum of fixed logarithmic weights. Apply the fixed-point theorem to each monomial at height y/x; coefficients converge, and log(y/x)/log(y)->1. Reflection handles negative points. This is shorter than a fresh uniform two-variable estimate.

Useful read sources: PoissonBoundary.lean (entire 270-line module); AxisPolynomial.lean lines 103-128 for exact dilation; FiniteBoundary.lean finitePoleBoundary_contDiffOn gives C1 polynomial times exp(-rho log t), useful for local Lipschitz control; PeriodDefect.lean has actual inversion and three-term identities and a compact-derivative-to-Lipschitz proof pattern. Avoid re-proving these receivers.

The complete datum has positive FE sign by CentralExclusion.degreeThree_functional_equation. Do not assume that sign for the bare cubic datum used by SpatialDefect. Once moving-boundary transport gives both period identities, finitePoleBoundary_eq_zero_of_period kills all interior polynomials. Then reuse Multiplicity.eq_vonMangoldt_of_xi_multiplicity_le; do not rebuild degree-two classification. Infinite-deficit branch and full WP07 remain OPEN.

## Sources and logs

Owned card: docs/drafts/pipeline/1-in-progress/weil-work-07-denominator-three.md. RESULT.md, EVIDENCE.md, PROOF.md under docs/reports/weil-work/results/07-denominator-three are updated. The shared frontier-map row is older than the owned checkpoint.

Current corpus searches: holomorphic weighted integral (partial=false); quarter eigenfunction finite axis packet (partial=true); Poisson logarithmic polynomial boundary dilation (partial=true). All candidate/source statements and ingredient sets inspected. Coverage has substantial pending/stale compiler evidence; semantic retrieval unavailable/timed out; no absence claims. Narrow lexical polarKernel boundary returned the useful existing own-module declarations. Exact coverage and warnings recorded in EVIDENCE.md.

Primary sources reopened: Bruggeman-Lewis-Zagier projective Poisson model, section 2.3 and Theorem 2.1; arXiv 1910.02821v5 Theorem 3.1. The Poisson mechanism is classical. The latter converse requires twists and stronger coefficient bounds unpaid by the cubic datum, so it is not imported.

Final next-step API scratch passed with exit 0 and no diagnostics. Polynomial.hasDerivAt, HasDerivAt.ofReal_comp/scomp, Real.hasDerivAt_log, both Convex norm-image derivative bounds, ContDiffOn.continuousOn_deriv_of_isOpen, polynomial continuity/evaluation/sums, Complex.cpow_def_of_ne_zero/ofReal_log, and finitePoleBoundary_contDiffOn were verified. hasDerivAt_ofReal_cpow_const is global, not in Complex. For unused polymorphic have := @Name probes inside an example, explicit universe levels avoid unresolved universe errors. No polynomial-boundary production module exists yet. All owned processes are terminal and exact scratch files are cleaned after recording this checkpoint.

Continue hgtl7 every turn and foreground targeted Lean checks only. No goal-complete claim until exact WP07 closes.