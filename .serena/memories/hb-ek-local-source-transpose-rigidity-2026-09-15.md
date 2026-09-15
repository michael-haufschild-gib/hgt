# HB local source-transpose classification (EK)

Goal remains active; RH and general temporal/metric/QNM matching NOT solved. Exact module audited:
`formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMLocalSourceTransposeRigidity.lean` (277 lines), namespace `RHTower.D4BMLocalTranspose`.

## Mathematical facts
- `exists_sourceContact_ne_zero`: actual contact C=((7λ−2)Q−2ΔQ)/8 nonzero somewhere at every Xi copy. If identically zero, all its two-jet entries vanish; SourceContactRigidity identity forces scalar S=0 everywhere since (λ−2)(λ−6)(3λ−2)≠0. Contradicts EI original scalar nonvanishing.
- `PreservesSource q br W`: full literal opposite-branch source-transpose identity, all amplitudes a,b, original onset v, radial x<0, actual angular points. Uses actual half-square Q and ΔQ, not independent test jets.
- `source_weight_derivative`: actual contact at one nonzero point, actual fixed onset at v=2, source amplitudes one force W'=(u−1)(1−4/u)W, u=radialUnit x=−tanh x. Exact weighted defect is −2(1−u²)u³ seed_s seed_opposite C times this ODE residual after multiplying source-identity defect by u−1.
- `source_weight_classification`, `preservesSource_iff`: for differentiable W on x<0, preserves full identity iff W=c D, D=(1+u)^5/u⁴. Quotient derivative zero on connected Iio0 proves necessity; linearity + original density-dual identity gives converse for all original times/amplitudes.
- `preserving_weight_boundary_charge`: u⁴ W seed_t(a,v,x,Q) tends to c*a²*timeOnset(2t,v)*Q at AdS boundary, t=opposite physical rate.
- `not_exists_admitted_source_weight`: no nonzero preserving differentiable W gives a finite AdS limit of W seed_t(1,2,x,Q) at EVERY angular point. Nonzero S somewhere ensures nonzero Q and boundary charge there.
- `not_exists_physicalQNM_source_weight`: no such W equals any fundamental physical QNM radial profile, allowing independent target Xi copy, either side, either radial normalization, arbitrary angular coefficient B(z). Actual fundamental modes have zero AdS limit.

Scope: rules out the entire radial MULTIPLICATION repair of exact pointwise full-source transpose. Does NOT rule out projected-action equalities, angular differential/integral operators, time-integral transmutations, changed clock, boundary-source modifications, or general physical matching. Target tortoiseMode is exactly profile used in LeftQNMMetricEquation (read definition there). No spin-two-current global nonvanishing theorem was proved; do not claim it.

## Files/status
- Own fact log DN44–DN46 added: docs/drafts/pipeline/1-in-progress/hb-dn-source-resolvent-facts.md.
- Closed option and complete positive survivor/paper proof: docs/drafts/pipeline/5-failed/hb-local-source-transpose-matching.md. Former in-progress card moved; absent there.
- Universal STATUS added route-independent boundary-domain constraint. Frontier map untouched.
- Umbrella wired RHTower.lean line18050; no umbrella build.
- Scratch check4 passed. Isolated exact-module lake build passed 53.67 seconds, 2 jobs; no heartbeat/transparency change, no axiom printing. Logs /tmp/hb-ek-local-check4.log and /tmp/hb-ek-exact-audit.log retained. Installed olean confirmed.
- Global formal lint ran; failed only on SEPARATE unwired `ThetaCuspHawkingBMOnsetTransgressionHorizon`; own leaf no errors. Separate module untouched. /tmp/hb-ek-formal-lint.log retained. Do not claim global lint passed.
- All owned Lean/Lake checks terminal; no owned process left. Private exact audit package and EK scratch inputs/search JSON removed; leftover EJ search JSON also removed.

## Discovery/verification
Deep broad OR matching, single-word intertwiner, OR derivative/connected/integrating-factor; inspected candidate lemmas, source method arguments and ingredient_sets. First two complete, third partial, snapshot 58,236 inventoried files with1failure; most compiler metadata source-only. Retrieved candidates verified through Lean or not used. Mathlib IsOpen.exists_is_const_of_deriv_eq_zero supplied ratio constancy. Broad arxiv searches transmutation/observability found arxiv2601.03616 (Jin–Ma–Zuazua, Jan2026); opened primary HTML. Its auxiliary-time Gaussian wave-to-diffusion transmutation assumes self-adjoint nonnegative factorization, not HB fixed-clock matching. Used only to distinguish nonlocal time averaging from scalar multiplier. No numerical computations.

Proof implementation: open HTGeometry.ScalarTwoJet for coordDeriv. Explicit typed derivative of lambda W(y)*seed avoids simp failing to match Pi.mul. In converse unfold dualSeed in BOTH equality and goal before linear_combination; no heartbeat increase needed. One harmless final unnecessarySimpa warning remained.
