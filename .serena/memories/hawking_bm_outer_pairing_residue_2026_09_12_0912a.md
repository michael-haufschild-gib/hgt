# HB actual outer pairing — completed 0912a

Full chain: literal theta-cusp source → Xi occurrence → retained spin-two source → physical causal radial/left-QNM action → fixed Hawking-clock extinction → RH. RH unproved; goal active. This goal turn is progress: two new audited native leaves close uniform outer control and actual outer pairing residue. Do not mark goal complete/blocked.

## User constraints
No computations/experiments, no raised heartbeats or resource limits, no #print axioms or other axiom checks, no Git or launch.sh, no full/umbrella builds. One owned foreground Lean/Lake invocation at a time. Only lake env lean scratch and exact lake build Module audit. Wire finished leaves without building umbrellas. Frontier map read only. No subagents spawned. Universal STATUS unchanged because findings route-specific.

## Installed and verified (do not rerun unchanged checks)
1. formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMReducedGreenUniformBound.lean —200 lines, warning-free scratch and exact cached-import leaf audit67sec/2jobs/4326 cached project imports. Source+olean/ilean/hash/trace installed and RHTower umbrella import wired.
- Reuses actual existing clearedReducedGreen, including both source moments and explicit gradient lift.
- New clearedReducedGreenFirst, analytic first jet, original clearing equality; denominator cancellation in small scalar lemmas.
- clearedReducedForcing=-connection(w,chi)*reducedCoefficient(s,w,a,clearedOnset(s,w),t).
- clearedReducedGreen_hasDerivAt proves actual U'=V and V'=w²U+z(1/4+chi²)U-Fclr off source/connection denominator zeros.
- clearedReducedGreen_compact_bound for arbitrary independent chi,s,a: any compact Omega in nonreal Re>-2 gives C≥0 with |U(w,t)|≤C exp(-|Rew|t), w in interiorOmega,t<0. Uses corpus reducedCoefficient_family_norm_le_exp and HTGeometry.SymmetricHorizonGrowth.forcedSecondOrder_horizon_bound_symmetric. Extends bound through both source and connection zeros by analytic numerator continuity.
- clearedReducedGreen_outer_uniform_bound, physicalClearedReducedGreen_outer_uniform_bound: every actual Xi q,branch,side,a and finiteT has R>0,C≥0 bounding full reduced numerator for u in ball(w0,R),T≤t<0. No supplied source/growth/ODE/initial/regularity premise.

2. formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMReducedOuterPairing.lean —255lines, warning-free scratch and exact cached-import leaf audit34sec/2jobs/4332 cached project imports. Source+5artifacts installed,wired.
- D4BMLaplaceRadial.normalizable_outer_uniform_bound derives common bound on actual normalizable family through z=1; uses outerGauss_uniform_bound and compact joint positive-radius powers.
- D4BMJointSource.tortoiseNormalizable_outer_uniform_bound: uniform freqball/finiteinterval T<t<0. Coordinate lower bound via z(t)=(exp(t)*(1+radialUnit(t)))²≥exp(2t)≥exp(2T).
- clearedReducedGreen_continuousAt including denominator zeros via actual moment spatial derivatives from JointSourceClearedRadialAdmission.
- clearedReducedOuterPairing chi s a T w = integral_{Ioo T 0} clearedReducedGreen(w,chi,s,a,t)*normalizable(w,chi,z(t)).
- clearedReducedOuterPairing_integrable proves actual density absolutely integrable for nonreal Rew>-2,T<0.
- clearedReducedOuterPairing_analyticAt and physicalClearedReducedOuterPairing_analyticAt prove genuine outer integral analytic in frequency through source and connection zeros, with common majorant derived. Cauchy dominated theorem used on indicator density. Two complex module-instance diamonds resolved with using!; no resource adjustments.
- continuedReducedOuterPairing=integral_{Ioo T0} continuedReducedGreen(w,chi,s,a,1,t)*normalizable(w,chi,z(t)).
- clearedReducedOuterPairing_eq gives R_T(w)=D(w)*Q_T(w) on actual denominator-nonzero germ, D=-(w-2s)C.
- physicalClearedReducedOuterPairing_value: R_T(w0)=fundamentalSourceMoment(w0,s,a)*clearedOnset(s,w0)*integral_{IooT0} normalizable(w0,chi,z(t))².
- physicalReducedOuterPairing_residue (line217) proves limit_(u→w0,punctured)(u-w0)*Q_T(u) equals that numerator divided by physicalFundamentalDenominatorSlope(q,branch,side). Outer integration precedes limit; exact full reduced response/lift retained. Same amplitude as incoming restoration. Final scalar cancellation uses mul_div_cancel_left₀, no expanded field normalization.

## Next hardest mathematical attack
Join actual incoming and opposite restored horizon blocks to this outer integral at matching b=horizonCoordinate(T); then assemble complete temporal source/contact current.
Specific next joining conjecture at physical fundamental w0:
incomingNormFinitePart(chi,b,w0) + integral_(T,0) n(w0,t)² dt = D4BMFundamentalNorm.normFinitePart(w0).
Kernel at fundamental: incoming H=sqrt(1-z), so incoming M=H²/(2sqrt(1-z))=sqrt(1-z)/2, linear coefficient -1/4. Use original coordinate substitution and uniqueness of two-counterterm cutoff limit. Already source-read actual PhysicalRadialNorm.mode_square_integral and mode_square_cutoff_tendsto, normFinitePart_eq_gamma, normFinitePart_ne_zero. Joining identity not yet proved. Do not claim full-current residue interchange or source/onset nonvanishing. Full four source channels, both Einstein contacts, unprojected/angular/multiplicity/Peierls survival, Hawking extinction and RH still open.

## Search/proof loop
Broad/deep forced, normalizable; OR bound uniform; deep natural-language complex forced ODE method. All candidate/source-method/ideas/ingredientsets inspected. Found existing JointSourceClearedUniformBound principal-family bound and its symmetric ODE method; pivoted from recreating a local forced Gronwall proof to applying that stronger existing mechanism at independent angular frequency. Uninstalled exploratory connectionClearedTortoiseGreen scratch was discarded, not part of corpus.
Normalizable deep retrieval completed over56998 inventoried files; pending compiler44553, stale snapshots and unavailable semantic coverage. Forced query complete; bound/method queries partial. Do not regard search suggestions as proofs. Broad arxiv Volterra/impedance included actual June16 2026 arxiv2606.18071 Volterra Generative Models; approximate stochastic lifts supplied no theorem used here. No numerical computation.

## Docs/lint/cleanup
Updated working and formalized docs/drafts/pipeline/{1-in-progress,3-formalized}/hb-physical-mode-action-contact.md with proofs, audits, exact gap and next joining conjecture. Frontier and universalSTATUS untouched.
Repository lint completed exit1 with five outside-edit unreachable modules: RHTower.DeningerOriginalGreenPoleCalculus; RHTower.ThetaCuspHawkingBMHorizonCoordinateJets; HTGeometry.ElementaryHorizonJets; HTGeometry.SecondEndpointMellinLaurentInterchange; HTGeometry.UniformSecondOrderJet. New leaves wired, no error names ours. Global lint not passed; do not rerun unchanged or fix other agents' pending modules blindly.
All owned processes completed, no owned Lean/Lake remains. All20 explicit /tmp/hb-*0912a* items deleted including scratch, logs, searches and cache-only audit package. Sources/artifacts retained in repository. No live 0912a handle to poll. Previous0911n incoming/opposite leaves remain audited; no need recheck.
