# HB — metric-dependent cubic bulk pairing

Goal ACTIVE; RH and fixed-clock extinction UNPROVED. This goal turn made concrete progress after a previous no-progress turn. No external blocker. No agents or computations.

User requires every turn opening: literal theta-cusp source → Xi occurrence → retained spin-two source → physical causal radial/left-QNM action → fixed Hawking-clock extinction → RH; state hardest mathematical obstacle and direct attack. Hardest remains extinction of full physical radiative pairing 2Ω(B(p,p)/2,B(m,m)/2). Only work directly serving this obligation. No more computations, analytical work and Lean verification only. Frontier READ ONLY (its pre-existing modifications belong elsewhere). One foreground Lean/Lake process; scratch first; exact individual leaf final builds only; no umbrella/full builds; audit axioms only new declarations; clean owned scratch/processes.

Installed and audited three new leaves:
- HTGeometry.CoordinateMetricPathDensity (namespace GaloisForLFunctions.HTGeometry.MetricPathDensity)
- HTGeometry.CoordinateEinsteinPairedCubicSource (namespace GaloisForLFunctions.HTGeometry.ComplexCoordinateMetricTwoJet.CubicSource)
- RHTower.ThetaCuspHawkingBMActionCubicCoefficient (namespace RHTower.D4BMActionSource)
335 total lines (145/87/103); 23 public declarations. All scratch checks and three exact canonical leaf builds passed warning-free. 23 new-only axiom prints use only propext/Classical.choice/Quot.sound. Nine installed .lean/.olean/.ilean SHA matches; three unique imports in owning umbrellas. Index and lint --check-generated passed (141 existing large-file warnings); diff --check passed. Frontier SHA remained ca874852aafed78ab12eb9e7f44cb6eb070d392a1c3e8b7c89dd9db46eb4291c. No Lean/Lake process at final inspection. Owned root /tmp/hb-action-density.a_3scrw6, marker /tmp/hb-action-density-current, helper /tmp/hb_action_setup.py DELETED. Do not rebuild/re-audit these leaves without new work justifying it.

Exact mathematical result:
g(t)=G+tH+t²K+t³L complete metric path; E(t) literal covariant cosmological Einstein residual. v(t)=exp(log(det g(t)/det G)/2), v(0)=1, C³ near0, v²=det ratio at nondegenerate points. D(G,H) is exact determinant derivative proved from permutation/column replacement, no determinant-trace identity asserted.
W(t)=v(t) g(t)^(-1) M (g(t)^(-1))^T, fixed covariant M. Transpose matters for arbitrary nonsymmetric jets.
W0=G^-1 M (G^-1)^T.
W1=D/(2detG)*W0 -(G^-1 H G^-1)M(G^-1)^T -G^-1 M(G^-1 H G^-1)^T.
P(t)=sum_ij W(t)ij E(t)ij. When E0=E1=0,
P'''(0)/6 = sum_ij [W0ij E3ij + W1ij E2ij],
E2=Lop K+B(H,H)/2,
E3=Lop L+B(H,K)+C(H,H,H)/6.
Every derivative is of the original rational source. Full E2=0 eliminates the changing-weight term exactly. Partial angular cancellation does not justify dropping it. Bulk densitization thus supplies no separate cubic cancellation once the full quadratic equation is solved.

RHTower pairedSource_eq identifies actual field jets, pairedSource_cubic has explicit full linear premise, literal_pairedSource_cubic discharges it for both actual fundamental branches with arbitrary scalar/vector amplitudes, corrections k,l require only C² at exterior point. literal_affine_pairedSource_cubic sets corrections0 and has no equation/regularity premises. literalField Bool uses true=plus,false=minus.

SCOPE: no complete Einstein action-variation formula, integrated cyclicity, physical retarded/advanced adjoint or left-QNM landing, boundary extinction, or RH proved. No mixed ++- extraction from this new weighted contraction yet. The next direct attack should address actual mixed action coefficient and retained boundary contribution. Do not claim the bare Einstein B is cyclic under a fixed pairing or that the new bulk identity proves action cyclicity.

Docs: docs/drafts/pipeline/3-formalized/hb-action-source-density.md complete proof/audit/scope; 1-in-progress/hb-action-source-density.md current card. Generic Must-differentiate-testing-map rule added atop universal-law-field/STATUS.md. Previous two card edits correcting chain remain untouched; concurrent SQB cards/frontier edits preserved. No commits.

Implementation lessons: Matrix has no canonical NormedAddCommGroup here, so MetricPathDensity.path is an explicit matrix polynomial, not ComplexCubicPath.path instantiated on Mat. Scalar derivative diamonds resolved with convert!. Use ContDiffAt.sum (not .fun_sum); specify basepoint when binding ContDiffAt terms. Matrix.add_zero doesn't exist (use add_zero). For ordered matrix derivative proofs use simp only [Matrix.transpose_apply,Matrix.mul_apply,...] to avoid simp reversing transpose products and reordering nested sums. Explicit Pi.mul_apply evaluates product lambdas. Generic complex det smoothness via det_apply', ContDiff.sum, contDiff_prod. Density definition exp(log ratio/2) uses Complex.contDiffAt_log/hasDerivAt_log at slitPlane ratio1. iteratedDeriv_fun_mul and iteratedDeriv_fun_sum provide exact third product/finite sums. Parenthesize summed additions so both terms remain under both binders.

Prior stages still valid: fundamental scalar radial source moment, effective angular source, physical Laurent residue all audited in previous memories; these support physical action but do not replace retained spin-two/full-causal extinction.
