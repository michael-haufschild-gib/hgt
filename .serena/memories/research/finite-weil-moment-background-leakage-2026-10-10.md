# Moment-preserving finite Weil duals — formalized

Card: docs/drafts/pipeline/3-formalized/finite-weil-moment-background-leakage.md. Classification: local-corpus structural bridge, no external priority claim. Only local Lean/mathlib research; user forbids web/papers, see `mem:research/local-lean-corpus-only-2026-10-10`.

## Finding and exact results
Existing normalized moment annihilator uses rank-nullity, with no coefficient size profile. A square-root off-weight bound is NOT established. Its exact moments were being discarded by the analytic/geometric envelopes. They are now preserved through the cutoff dual producer.
`finiteWeilCenteredLog k j = log((j+2):Real)-log((k+2):Real)` lives in GramCoordinateObstruction.
`exists_finiteWeilGram_exponential_moment_dual_witness` (same file line182): exists B>0,K>=2, forall N>=2K, with q=N/K, exists i,d, normd1, |di|1, sumoff|dj|<=q-1, forall p<=q-2 sum_j dj*finiteWeilCenteredLog(N-q)j^p=0, and forall actual w, |form_N w d|*2^q <= B*cost1w.

New `WeilLogShiftGramBackgroundLeakage.lean`:
- line13 `finiteWeilLogBackground k m b j = sum_{p:Fin m} b_p*finiteWeilCenteredLog k j^p`.
- line18 `exists_finiteWeilGram_log_background_cost_leakage`: choose B,K,i,d before w AND b:Fin(q-1)->Real. For z=V_Nw-background_b, both E|zi|<=BC+E sumoff|dj||zj| and <=BC+E(q-1)||z-single_i(zi)||. Exact moments included in returned witness.
- line48 `exists_finiteWeilGram_log_background_isolation_cost`: exists c>0,K>=2, forall largeN exists i, forall b,a, target=background_b+single_i(a) has an ACTUAL realizing test; every realizing test costs >=c*2^q*|a|. Realizability comes from existing unconditional surjective_finiteWeilGramCoefficientVector.

## Refactoring / details
AllOrderCancellation: new pairedLogKernel_cluster_envelope_with_moments, old envelope API preserved as corollary. ExponentialClusterCost: geometric_cluster_envelope_with_moments, old API preserved. CoordinateObstruction: cluster_dual_of_coefficients retains the chosen c through explicit lets e,d; old cluster dual wrapper preserved; new cluster_moment_dual_witness transports moments; exponential_moment_dual_witness strengthens old exponential_dual_witness wrapper.
GramLeakageAlgebra adds extend_pairing, pairing_sub_background (finite sum interchange), and cost_leakage_of_pairing. Existing GramCostLeakage now uses the shared helper.
Lean details: annotate wrapper lambda j : Fin(r+2) explicitly when constructing the extension; annotate target background lambda j : Finset.range N before adding Pi.single. Otherwise Nat-valued arguments force the wrong domain. Erased-finset generic helpers retain explicit DecidableEq parameters.

## Verification
All 10 affected native leaves compile: AllOrderCancellation, AllOrderClusterCost, SuperpolynomialGramCost, ExponentialClusterCost, GramLeakageAlgebra, GramCoordinateObstruction, GramCostLeakage, GramUnitResponse, GramIsolationSeparation, GramBackgroundLeakage (WeilLogShift prefix).
All 39 public declarations audited in /tmp/hgt-moment-final-audit.lean; exact expected-name coverage and only propext, Classical.choice, Quot.sound. Dedicated /tmp/hgt-moment-api.lean checks sum_comm, sum_sub_distrib, sum_const_zero. No heartbeat changes. Final build logs /tmp/hgt-moment-<leaf>.log all empty.
Guarded metadata script /tmp/hgt-moment-metadata.py recomputes exhaustive dependency closure (10), checks every source/direct-dependency artifact and exactly-once imports: no failures.
Index refreshed; roots in LEAN_API; local exact receiver search confirms isolation root line48.
Lint /tmp/hgt-moment-lint.log exit1 only four unrelated missing umbrella imports: RHTower.JointAncestryLagAggregatePositivityAbscissa; RHTower.PaperCriticalFeatureEntropy; RHTower.PhotonicLosslessProductPortDensityLaw; HTGeometry.QKrawtchoukCompanionTriangular. No unrelated repairs.
All owned jobs terminal; no stale affected artifacts. Goal remains active.

## Next local question
Can distinct logarithmic nodes identify a unique annihilator LINE and canonical divided-difference functional? Sup-norm normalization determines coefficients only up to sign, not uniquely. Inspect actual local Vandermonde/interpolation lemmas before conjecturing/proving. This could expose coefficient structure relevant to sharper off-weight bounds; none currently claimed.
