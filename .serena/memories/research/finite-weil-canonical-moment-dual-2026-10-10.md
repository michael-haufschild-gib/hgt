# Canonical finite Weil moment dual — formalized

Card: docs/drafts/pipeline/3-formalized/finite-weil-canonical-moment-dual.md.
Only local Lean/mathlib; no external novelty claim. User explicitly forbids web and external papers, see `mem:research/local-lean-corpus-only-2026-10-10`.

## Exact algebra
New WeilLogShiftMomentBarycentric.lean (12 declarations): for injective h:Fin(n+1)->Real, finiteWeilMomentWeights h = Lagrange.nodalWeight univ h, i.e. reciprocal node-difference products. Moments p<=n equal if n=p then1else0. Every c annihilating p<n equals (sum_i ci hi^n) • weights. Thus every nonzero annihilator has full support.
finiteWeilNormalizedMomentDual h = norm(weights)^-1 • weights. Norm1, each entry nonzero, moments p<n zero. Every unit-norm annihilator equals this vector or its negative (classification line116). Pairing with arbitrary y equals coeff_n(Lagrange.interpolate univ h y)/norm(weights) (line93).
Key sources: Lagrange.coeff_eq_sum plus Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero. Existing corpus already has divided differences and moment uniqueness; new value is the real sup-norm classification and bridge into actual Weil clusters, not novelty of interpolation.

## Unconditional Weil roots
New WeilLogShiftCanonicalCluster.lean (8 declarations), imports pure new leaf and existing GramCoordinateObstruction; existing sources unchanged.
finiteWeilClusterLogNodes r k i = finiteWeilCenteredLog k(k+i) = log(k+2+i)-log(k+2), injective for all natural r,k.
finiteWeilCanonicalCluster r k is normalized moment dual at these r+2 nodes.
- line40 finiteWeilCanonicalCluster_spec: all r,k, norm1, every entry nonzero, moments p<=r zero, and every normalized moment witness equals +/- canonical cluster.
- line57 finiteWeilCanonicalCluster_pairing: arbitrary y pairing is top interpolation coefficient (degree r+1) divided by unnormalized weight norm.
- line65 exists_pairedLogKernel_canonical_cluster_envelope: same existing B>0,L>=1 and width4L(r+1)<=k+2 give geometric paired-kernel envelope for EXPLICIT canonical coefficients. Transfer uses uniqueness up to sign and absolute value, with unchanged constants.
- line83 exists_finiteWeilGram_canonical_cluster_sensitivity: exists B,L, forall arithmetic clusters contained in finite support with that width budget, the explicit zero-extension d of canonical coefficients has norm1, is nonzero at every cluster label, and for every actual test |form_s(w,d)|*((k+2)^2*2^r)<=B*cost1w. Produced by the existing chosen-coefficient cluster helper and cost scaling; no unknown analytic premise.

## Verification / Lean details
Both native leaves pass with empty logs /tmp/hgt-canonical-WeilLogShift{MomentBarycentric,CanonicalCluster}.log. /tmp/hgt-canonical-final-audit.lean audits all20 public declarations plus24 mathlib API terms; exact source-name coverage, only propext/Classical.choice/Quot.sound.
Fresh source/direct-dependency artifacts and exactly-once umbrella imports. Incoming-import search confirms only these two leaves affected. Index refreshed; exact receiver search gives one hit line83. Lint /tmp/hgt-canonical-lint.log exits1 for two unrelated missing umbrella imports: RHTower.SuzukiScrewBeurlingDenyAperture; HTGeometry.QKrawtchoukCompanionTriangular. No unrelated repairs, heartbeat changes, numerical experiments, commits, or full builds. All owned jobs terminal.
Use `Polynomial Real`, not `Real[X]` without opening Polynomial notation. norm_smul_inv_norm needs Mathlib.Analysis.Normed.Module.RCLike.Basic. For Real.log_injOn_pos, positivity tactic does not unfold Set.Ioi membership: give `show 0 < ... by positivity` explicitly.

## Next frontier
The annihilator-line question is CLOSED, including full support and normalized divided-difference interpretation. Sup-norm normalization gives two orientations, not a unique signed vector. The old q-1 off-weight bound is still unsharpened. Next local questions: sign alternation and adjacent coefficient-ratio estimates for the explicit logarithmic node-difference products, then possible sharper absolute-sum control. No square-root profile or optimality claim yet. Whole indefinite goal remains active.
