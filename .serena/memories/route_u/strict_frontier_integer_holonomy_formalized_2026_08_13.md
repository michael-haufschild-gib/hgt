# Route U strict-frontier integer holonomy (2026-08-13)

Formalized module:
- `formal/GaloisForLFunctions/RHTower/XiShiftedStrictFrontierIntegerHolonomy.lean`
- umbrella import added to `formal/GaloisForLFunctions/RHTower.lean`
- Stage-3 card: `docs/drafts/pipeline/3-formalized/new_scientific_knowledge/shifted-xi-strict-frontier-integer-holonomy-law.md`
- frontier map appended.

Exact new Lean result:
At occupied strict frontier `y=T_(n+1)`, newborn degree `m=n+2`, first finite Padé contact order `d>0`:
- `u * logDeriv (fun v => N_m(y+v)) u -> d` as `u -> 0+`.
- `u * E_m(y+u) -> -d`.
Same `d` has existing positive all-contact arithmetic source-wall residue. Packaged as `XiShiftedStrictFrontierIntegerHolonomyLaw` and cofinal false-RH phase. Premise-free capstones:
- `riemannHypothesis_iff_not_xiShiftedCofinalIntegerHolonomyPhase`
- `riemannHypothesis_or_xiShiftedCofinalIntegerHolonomyPhase`.

Critical honest pivot:
Existing effectivity theorem required positivity through block `m+2`, unavailable at newborn face. New theorem
`hasDerivAt_xiShiftedCanonicalAdmissionNorm_eq_neg_effectivityRate_mul_of_succ_posDef`
needs only `H_(m+1)>0`, using division-free norm flux and Schur positivity. This exact hypothesis is available right of terminal frontier.

Generic infrastructure:
`AnalyticAt.tendsto_sub_mul_logDeriv_of_analyticOrderAt_eq_natCast` proves arbitrary finite analytic order equals logarithmic residue without computation. Newborn determinant order follows from existing lower-jet vanishing and positive first live jet; Schur quotient transfers order to actual norm.

Audit:
- `lake env lean GaloisForLFunctions/RHTower/XiShiftedStrictFrontierIntegerHolonomy.lean` passes clean.
- `lake build GaloisForLFunctions.RHTower.XiShiftedStrictFrontierIntegerHolonomy` passes 11826/11826.
- 11 public declarations depend only on `[propext, Classical.choice, Quot.sound]`.
- no sorry/admit/axiom/opaque/unsafe/native_decide/#eval/#reduce.
- repo-wide lint attempted once, externally terminated 143 with no diagnostics; not claimed pass.
- direct umbrella lean encountered unrelated missing olean for RouteRCartierHermitianPolarizationNoGo before target; targeted build passes and import is wired.

Scientific interpretation:
Regular projective curvature is norm-gauge flat/coboundary. Arithmetic information survives at singular gauge boundary as pair (positive real amplitude, positive integer holonomy). False RH forces cofinal charges d>=1. Remaining open core is global: construct common arcsine-vacuum-renormalized determinant line / trace-class sum rule with finite total holonomy budget. Local charge alone is not RH contradiction.

Novelty:
Generic order-residue theorem and Lax parent theory are classical. Exact shifted-Xi amplitude/contact/effectivity synthesis is corpus-new, external novelty unverified. Related primary sources: Bertola-Eynard arXiv:nlin/0311033; Killip-Simon arXiv:math-ph/0112008; Romik arXiv:1902.06330.
