# Exact finite Weil power covariance threshold

User restriction: mathematical evidence ONLY local Lean corpus, including checked installed Lean dependencies. NO web, external papers, literature/training novelty claims, or numerical experiments.

Formalized card: docs/drafts/pipeline/3-formalized/finite-weil-finite-power-threshold.md.

For all finite r,k, all real a,b,d, and n, actual tilted first-coordinate power covariance matrix (powers 1..n) is PosDef iff n≤r; determinant>0 iff n≤r; determinant=0 iff r<n. Exact support has r+1 points, injective first coordinate. All coefficient/depth assumptions discharged at roots. Arbitrary depth and real coefficient sequences yield eventually positive determinant for each fixed n, starting at r≥n. This removes canonical-depth and subcritical assumptions for positivity; earlier Gaussian limit still has its original assumptions.

Four leaves, 11 theorems:
- HTGeometry/FinitePowerSumNodes: finite_power_sum_succ_constant_iff for n≤r and injective r+1 nodes; exists_ne_zero_finite_power_sum_constant for r<n, no injectivity needed. First uses polynomial degree/evaluation uniqueness; second uses kernel of node-difference matrix, domain Fin n, codomain Fin r.
- HTGeometry/PowerCovarianceKernel: powerCovarianceMatrix_mulVec_eq_zero_of_ae_const; powerCovarianceMatrix_det_eq_zero_of_ae_const. Constant power sums give covariance null vectors under L2; nonzero vector forces determinant zero.
- RHTower/WeilLogShiftFinitePowerCovariance: finiteWeilCanonicalJointQuadraticTilt_power_sum_variance_zero_iff (n≤r), ..._powerCovarianceMatrix_posDef_of_le, ..._powerCovarianceMatrix_det_zero_of_lt. Uses existing unconditional finite support AE characterization, all-observable MemLp2, and first-coordinate injectivity.
- RHTower/WeilLogShiftFinitePowerThreshold: ..._powerCovarianceMatrix_det_pos_iff; ..._powerCovarianceMatrix_posDef_iff; ..._powerCovarianceMatrix_det_zero_iff; eventually_finiteWeilCanonicalJointQuadraticTilt_powerCovarianceMatrix_det_pos_arbitrary. Handles n=0 and r=0.

All four leaf native builds empty logs and fresh objects. Final native scratch audit terminal0, 11 axiom reports only propext/Classical.choice/Quot.sound, 20 checked APIs, no residual diagnostics. Full index coverage 11/11 (2+2+3+4), exact declaration uniqueness, 6 project edges, 12 total imports, 7 incoming imports, four fresh objects, clean whitespace, umbrellas wired. Artifacts /tmp/hgt-weil-finite-power-rank-. Audit script cloned previous and fixed inherited incoming count display to compute actual value. First node build handle lost through compaction; exact process absent, empty log and fresh object recovered before dependent work. All native jobs now terminal.

Final lint snapshot: 1 unrelated error, 367 warnings; RHTower.JointAncestryRealAmplitudeDetection unreachable from umbrella. Do not treat this as current status next turn or modify unrelated active work.

Native proof fix: integral_eq_zero_of_ae goal uses zero function, so simp [F,hy] resolves 0 = 0 y; restricted simp only without function-zero simplification left goal unsolved.

Boundary: exact rank=min(n,r) and determinant factorization NOT yet formalized here. Those are potential followups requiring local corpus search and closed paper proof first. Overall ongoing research goal remains active, not complete.