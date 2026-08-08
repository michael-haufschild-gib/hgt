# Constitutive Lawstack Geometry checkpoint — 2026-08-09

Goal remains active. Do not mark complete. User wants GR-scale new field explaining all HGT/RH/HT routes; no Lean writes/builds; own Pipeline1/2 cards; novelty gate explicitly waived.

## Field pivot
Working candidate: Constitutive Lawstack Geometry (CLG), geometry of source laws under lossy observation.
- Routes are native observer charts; only invertible overlaps are gauges.
- No-gos are typed: isotropy, nonseparation, nonproperness, missing maps, derived thickness, holonomy. Not all curvature.
- Bare lawstack is kinematics, not dynamics.

## Exact paper theorems added and hostile-ACCEPTED
All under `docs/drafts/pipeline/2-fully-proven/nomological-geometry-and-dynamics/`:
1. `native-observer-descent-effectivity-and-constitutive-nondetermination-law.md`
   - Coim(q)=|Cech(q)|; full descent + extension across effectivity cell; serial adds identifications; parallel intersects kernel relations; pointed fibre LES.
   - Native q determines native effectivity.
   - Bare q does not determine metric, inertia, DA depth, normalization; forgotten Set data do not determine Top/Banach enrichment.
2. `restricted-history-completion-and-robust-polynomial-saturation-law.md`
   - direct-sum dense/nonclosed in compact product completion; fixed observers stabilize while support grows.
   - robust additive-grid theorem: deleting any D columns still spanning kills every degree-D polynomial.
   - Hurwitz exact DA matroid is equality partition q_i=exp(-2pi i s_i), not orbit dimension/rankR.
   - full marked R_q plus coordinate characters computes partition; branch-history support realizes analytic proof.
   - finite local monodromy can coexist with full DA rank.
   - positive radial data do not determine phase periodicity/holonomy; recurrence does not bound lifted cost.
3. `weighted-history-action-and-infinite-completion-boundary-law.md`
   - proper integer local lengths + weights tending infinity => finite action sublevels.
   - lsc relaxation on compact product equals A on source direct sum and +infinity on every new completion-boundary history.
   - minimal typed laws D (Cech/Bianchi coherence), S_D (vertical-symbol conservativity), P (relative inf-compact action) are logically independent.
   - no nonzero polynomial scalar rank law couples HT/inertia/recurrence.

## Important dead claims
- HT is NOT local holonomy noncompactness/density. s=(3/2,4/3) has finite orbit, Hurwitz DA rank2.
- Full marked holonomy is not useless: R_q and coordinate characters compute exact Hurwitz partition. Only scalar dimension/rank/recurrence shadows fail.
- Positivity is phase quotient only in determinant-holonomy sector, not general Hodge/Witt/coarea positivity.
- Native effectivity is determined by native q; only forgotten-category enrichment is undetermined.
- One heterogeneous scalar field equation impossible.

## Exact local symbol parent
`docs/drafts/pipeline/3-formalized/graded-principal-symbol-characteristic-arrangement.md`: triangular free filtration HT iff every graded raising symbol nonzero; characteristic locus union kernels.

## Stage1
Main:
`docs/drafts/pipeline/1-in-progress/nomological-geometry-and-dynamics/constitutive-lawstack-geometry.md`
Research log:
`.../RESEARCH_LOG.md`
Status remains conjectural field schema.

## Open core / next theorem
Construct before target specialization a Morita-natural source transgression
  tau_s: Theta_s -> Z^1(N(q); E_s)
whose named comparison functors realize at least two nonisomorphic corpus symbols (target: Hurwitz branch increments and Stokes vertical polarity or recurrence deck displacement) and whose source polarization derives action, proving S_D and P. Without this, CLG is a typed recipe, not a field.

## Verification
Three new Stage2 cards passed hostile re-review after repairs. git diff --check and display-math delimiter counts pass. No Lean written or built. Preserve unrelated dirty Lean/user changes.
