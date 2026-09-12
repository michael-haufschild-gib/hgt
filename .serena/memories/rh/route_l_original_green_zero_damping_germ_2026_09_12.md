# Route L C52: exact original Green zero-damping germ

Date 2026-09-12. RH remains UNPROVED; persistent RH goal ACTIVE. Latest user steering: optimize Lean, no heartbeat hacks. No heartbeat/recursion increases, no #print axioms, no numerical experiments, no full/umbrella builds, no agents or commits performed by this task.

Proof chain: complete original Green/BV source → fixed physical-reader agreement → conormal vanishing → RH. Reader agreement remains open. C51 fixed-damping full-Xi admission is completed; see `mem:rh/route_l_original_green_full_xi_admission_2026_09_12`.

## Completed C52
Formal module: formal/GaloisForLFunctions/RHTower/DeningerOriginalGreenZeroDampingGerm.lean.
Card: docs/drafts/pipeline/3-formalized/route-l-original-green-zero-damping-germ.md (moved from 1-in-progress).
17 public declarations, wired once into RHTower.lean, all indexed in formal/LEAN_API.md.

For original prime p and actual Xi support rho, define H(a)= [G(rho)/(1-p^(-rho))]/[zeta(a+rho)*zeta(a+1-rho)], with the original reflected Gaussian Mellin transform G. Proved meromorphic on the entire complex damping plane and equal to the actual admitted original Green Mellin integral for real a>1.

At a=0, H has exact meromorphic order -(2*m), m=xiSupportMultiplicity rho. Its exact nonzero trailing coefficient is [G(rho)/(1-p^(-rho))]/[c(rho)*c(1-rho)], where each c is the actual first nonzero zeta Taylor coefficient. Proved c=iteratedDeriv m zeta/(m!). Reflection preserves m; no simplicity or RH premise.

Public results: deningerOriginalPrimeGreenDampingContinuation_{meromorphicOn,meromorphicAt,order,trailingCoeff,normalized_limit,no_finite_limit,finite_limit_iff,nonzero_limit_iff,eq_literal}; exists_deningerOriginalPrimeGreen_zeroDamping_unit; deningerOriginalPrimeGreenZeroDampingCoefficient_{ne_zero,eq_native_jets}; deningerOriginalPrimeGreenZeroDampingRegularization_{analyticAt,zero}; three definitions.
Power normalization a^k*H(a) admits a finite limit iff 2*m<=k; it admits a finite nonzero limit iff k=2*m. At k=2*m, the limit is the exact coefficient above. Filling this value at zero gives an analytic SCALAR germ. This does not construct a zero-damping source vector or physical-reader agreement.

## Optimization and checks
Reusable translated analytic-unit helper; shared one-sided Leibniz collapse instead of derivative expansion. Explicit typed function equalities avoid failed simplifier matching. For integer-to-WithTop addition, use direct term `(WithTop.coe_add (k : Int) (-(2*m : Int))).symm` instead of rewrite search. WithTop.coe_neg is not the right name (actual namespace WithTop.LinearOrderedAddCommGroup); direct term is simpler. Do not start field-notation dots on a new line after a parenthesized expression: Lean parsed that as an extra argument. Explicit MeromorphicAt.comp_analyticAt worked.

Complete scratch `lake env lean /tmp/route_l_zero_damping.lean` passed. Small global-meromorphic scratch passed. Final `lake build GaloisForLFunctions.RHTower.DeningerOriginalGreenZeroDampingGerm` passed, only new leaf built (131s; 11993 jobs mostly cached), exec session 58063 terminal exit0. Index session 84675 terminal exit0. Lint session 15306 terminal exit1: six unrelated unreachable modules: RHTower.ThetaCuspHawkingBMHorizonModeOuterUniformBound; HTGeometry.AnalyticJetGerm, ElementaryHorizonJets, JetCoefficientUniqueness, SecondEndpointMellinLaurentInterchange, UniformSecondOrderJet. Global lint is NOT passed. No owned Lean/Lake/search/index/lint processes remain. Owned workspace scratch duplicate removed after formalization. All card links checked. Relevant scoped git diff check passed.

Logs and five search JSONs moved beside stage3 card. Frontier map and universal STATUS updated. Another task rewrote frontier into a committed snapshot audit while this work ran; preserved that audit and added explicit C52 working-tree verified evidence, replacing its now-superseded scratch-only paragraph. Shared worktree was also committed externally during work; this task did not commit. Preserve concurrent work.

## Research and next hard gap
All 20 candidates and 20 method entries inspected for each of five corpus searches (boundary trace, damping collision, germ calculus, reciprocal coefficient norm, inverse-jet hybrid). Coverage partial; snapshots inventoried about 47,420 Lean files, compiler mostly pending. No claim of exhaustive theorem absence. Trace templates lack original-source incidence. Gaussian zero counting and envelope nonvanishing do not bound inverse native jets. All-complex-time heat bounds require unproved summability. Broadened hybrid found inverse-zeta bounds in zero-free regions near Re=1 and derivative UPPER bounds, not inverse first-nonzero-jet bounds at actual zeros.

Broad newest-first arXiv query reciprocity found Camacho et al., Temporal Localisation of Waves from Imaginary Line-Gap Topology, submitted Sep10 2026: https://arxiv.org/html/2609.11577v1. Inspected E9-E12 and model/supplement: requires two-mode Hamiltonian, spectral gap, symmetry, specified initial overlap and phase switch. Finite-time localization only. No Route L identification/gap/overlap producer; no transfer to RH.

Next obstacle: the exact normalized coefficient contains reciprocals of BOTH native zeta leading jets. C51's original-prime reciprocal bound and Gaussian envelope do not control those additional factors. A complete zero-damping source-domain passage needs actual uniform control or a source-forced coupled mechanism, followed by complete original BV-to-fixed-physical agreement. Separate scalar Laurent limits alone do not admit an original full-Xi vector or justify reader transport. Preserve original p, Tate depth, every multiplicity copy, Xi coefficient, Gamma normalization, horizontal anchor. Do not replace unknown jet bounds with simplicity, separation, RH, or an assumed source-domain limit.
