# Original quadratic source pairing closed locally; next target is full causal metric reconstruction

Goal remains ACTIVE and RH UNPROVED. Previous goal turn and this turn are progress, not blocked. Chain: literal theta-cusp source → Xi occurrence → retained spin-two source → physical causal radial/left-QNM action → fixed Hawking-clock extinction → RH.

User rules: analytical only; no computations/Git/launch.sh/subagents/#print axioms/resource-limit increases. One owned foreground Lean/Lake process. Scratch lake env lean; exact new leaf lake build only; no umbrella/full/dependency rebuilds. Wire umbrellas without building. Frontier READ ONLY; universal STATUS route-independent only. Assess each result across entire chain, conjecture/proof-or-fail/pivot, broad/deep/method corpus searches directly, no research help/source prep.

Prior verified action identity: `mem:d4bm_original_action_cyclicity_boundary_2026_09_12_0912s`. Prior physical reflection: `mem:hawking_bm_literal_source_reflection_and_physical_cyclicity_2026_09_12_0912r`.

## New checked modules — do not repeat audits

1. formal/GaloisForLFunctions/HTGeometry/CoordinateEinsteinOnShellPairing.lean, namespace GaloisForLFunctions.HTGeometry.EinsteinOnShellPairing (315 lines).
Imports CoordinateEinsteinCyclicAction.
- weighted_second_of_residual_zero: C³ scalar f,g with g0=∂i g0=∂j g0=0 imply ∂i∂j(fg)0=f0∂i∂j g0. All four Leibniz terms retained before using residual equations.
- variationMap: fixed CLM a ↦ Σ a_k toSpace(Uk), k:Fin3.
- residual: original cosmological Einstein component of complete family G(a)=J+ΣaUk.
- residual_first: ∂k E_rs(a)=DEinstein_rs(G(a))[Uk]+Λ Uk.metric_rs.
- residual_second: ∂i∂j E_rs(0)=secondVariation(toSpace J)rs(toSpace Ui)(toSpace Uj); affine Λ term contributes no second derivative.
- testCoefficient: original varying determinant density times both inverse metrics contracting Uk.
- bulk_second_eq_hessian: given actual E0=0 and Linearization.cosmological J Uk Λ=0, second derivative of ORIGINAL volume-weighted bulk pairing equals frozen raised-test contraction with actual Einstein Hessian.

Geometric premises explicit; physical module below discharges them. No changed observable/model source. Private determinant/adjugate/inverse smoothness helpers copied from existing action proof because matching complex helpers are private; corpus SmoothMatrixDeterminantCalculus public helpers are real only.

2. formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMOnShellCyclicSource.lean, namespace RHTower.D4BMOnShellCyclicSource (117 lines).
Imports new core + ThetaCuspHawkingBMCyclicActionBoundary.
- private linear_source_zero: uses actual source_eq and cosmological_hasDerivAt, then physicalPerturbation_first_source_zero; every first-residual premise discharged.
- hessianPairing line48: full sum of actual raised test times Einstein Hessian on actual full physical jets.
- quadraticPairing line57: hessianPairing / 2. CRUCIAL Taylor normalization, independent of causal half-jump convention.
- physical_bulk_second_eq_hessian line62: actual physical weighted source second derivative equals hessianPairing, no supplied equations/regularity/symmetry/nondegeneracy.
- quadraticPairing_diag_eq_sourceCoefficient line74: diagonal equals contraction with iteratedDeriv 2 of LITERAL D4BMActualMetricSource.source /2, using existing source_quadratic. Normalization independently fixed.
- physical_quadratic_cyclicity_defect line93:
  B_ijk−B_ikj=(∂i∂j boundary_k−∂i∂k boundary_j)/2.
- physical_quadratic_with_boundary_cyclic line106:
  B_ijk−∂i∂j boundary_k/2 = B_ikj−∂i∂k boundary_j/2.
All use three independent Xi occurrences, both branches, independent scalar/vector amplitudes. No supplied field/flux premises.

Both scratch checks passed default Lean limits. Exact isolated leaf audits passed, core13s and physical54s, each one new Lean leaf (2jobs incl config). Cached dependencies only (26 core,3954 physical). Sources + five matching .olean/.ilean/hash/.trace artifacts installed. HTGeometry/RHTower umbrellas appended, not built. Formal lint passed with pre-existing large-file warnings. Frontier and universal STATUS unchanged. All owned sessions terminal; end-of-turn cleanup removes 0912t scratch/search/audit paths.

## Current hard mathematical target — do NOT retreat to an abstract conditional lemma

The new theorem applies to homogeneous linearized directions. A forced response is not automatically one. Need ACTUAL full metric corrections k_ret,k_adv satisfying ORIGINAL component equations
L(k_ret)=L(k_adv)=−B(h,h),
including contacts, all independent source channels, same causal source/domain. Then their actual difference is homogeneous and new source-pairing reduction applies.
Do not spend a turn merely proving abstract L(Rret−Radv)=0 under supplied inverse axioms. The hard producer is metric reconstruction and original equation verification, followed by physical current/QNM/common-cutoff identification.

Potential next concrete attack: converse sourced Kodama–Ishibashi reconstruction from the source-compatible master solution. Current inspected source:
formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMScalarStreamMasterIdentity.lean
namespace RHTower.D4BMScalarStream:
- harmonicTT/TR/RR/T/R/TF/L, plus T1/TF1/TF2, functions of s,r,μ,F0,F01,F02,F1,F11,F12,F2,F21,F22,H,H1,H2.
- masterVar/1/2 lines75/80/85.
- masterOp163 = masterVar2 + (2r/(r²−1))*masterVar1
   +(μ/(r²(r²−1))−4s²/(r²−1)²)*masterVar.
- master_identity173 has hs:s≠0, hr:r≠0, hf:r²−1≠0; masterOp is explicit combination of seven Einstein rows and formal derivatives. For E_A=−τ_A this yields sourced master equation. It is ONE-WAY identity, not construction of correction solving every row.
- Need source compatibility from original Bianchi identities, converse reconstruction of full rows, and actual causal boundary choices. Full source may require angular operator treatment beyond one harmonic. Inspect current source/cache freshness before relying; this file was only read this turn, not rebuilt/audited.

## Broader searches and whole-chain checks

Research CLI queries: Green; second variation product residual vanishes retain boundary (deep120s); matrix inverse smooth determinant (deep90s); integrate parameter variations of a current retaining all boundary flux (deep90s). Inspected candidate_lemmas, source_arguments, method views, ingredient_sets; deep results partial. Actual candidates used checked in Lean. Some generated ingredients generic, no assumed applicability.

1. ThetaCuspHawkingBMEisensteinActualGreenBoundaryCancellation.lean:
d4BM_completedPoincare_nonCuspPairedGreenDefect_eq_zero387,
d4BM_completedPoincare_pairedBoundaryGreenCurrent_eq_cuspCurrent396.
These retain cusp top after paired modular sides/arcs cancel.
BUT parameter structure in ThetaCuspHawkingBMEisensteinPoincareAbsoluteConvergence.lean has s:ℂ and re_gt_one:1<s.re. Cannot directly instantiate physical Xi parameters; needs continuation or direct full-field producer. This is an applicability failure, not a no-go theorem.

2. ThetaCuspHawkingBMQuarticTestedNativeCurrent.lean (namespace RHTower.D4BMQuarticTestedNativeCurrent) is a distinct physically specialized boundary candidate:
- weightedCovariance166: full TFG period minus the two means times tested linear moments plus product of means times test mean.
- physicalTest349: complete scalar(physicalAngularParameter q)(angularCoordinates z), parameter=(rho−1)/2; NOT center(q)=rho−1/2.
- testedPairCurrent372 = weightedCovariance(T, ∂y response_a, response_b).
- testedPairDensity378 retains six terms: derivative-test*∂yFa*Fb, T∂yFa∂yFb, T∂xFa∂xFb, derivative-x-test*∂xFa*Fb, λa/y²*T Fa Fb, and forcing_a/y²*T Fb, all weighted covariances.
- testedPairCurrent_hasDerivAt398, finite_balance483, decomposition496.
- decomposition restores ORIGINAL tested triple moment and BOTH original response means, uncentered test, two tested linear moments.
- weighted_tendsto_zero991 and cpow_tendsto_zero1002: upper trace zero for every complex height weight, proved from actual source energy/forcing.
- testedPairDensity_integral_tendsto1017: improper integral is NEGATIVE LOWER testedPairCurrent. Do not discard lower endpoint.
Potential comparison is antisymmetric tested current J_ab−J_ba (symplectic/Wronskian structure), but this comparison with full Einstein boundary is NOT proved. Do not fabricate equivalence or treat centered scalar current as full nine-channel action.

GlobalAngularForcing102 defines parameter q branch=branchParameter rho branch (doubled-rate), source forcing=(parameter/2)*scalar(center q)^2 − (Δ−parameter)(cutoffResponse).
Actual normalized physical left reader parameter remains different. Causal metric/current identification, oriented/nonzero full incidence, and fixed-clock extinction all remain unproved.

Read-only frontier current HB section1628ff confirms metric correction solutions, complete independent-channel action, QNM-level transfer/global current identification remain open; time-Hilbert/scalar operator results alone do not supply original metric equations.

Broad arxiv own terms corner/interface/gluing/cobordism. Opened official abstracts:
https://arxiv.org/abs/2608.05071 Jia–Tan generalized defect tube algebras (Aug5/revised12);
https://arxiv.org/abs/2608.07788 Bais–Kjuchukova dihedral branched-cover cobordism (Aug7).
No theorem about Einstein pairing obtained; no external claim enters Lean.

## Lean efficiency lessons

- Avoid rewrites between definitionally equal lambda/Function.comp/pointwise function operations when Matrix aliases cause instances-transparency failures. First 'change HasFDerivAt (explicit function) _ point at h', then evaluate h.fderiv; use explicit typed function derivatives.
- residual_first simplification needed toSpace in simp to identify (toSpace Uk).1 with Uk.metric.
- Do not invent ContinuousLinearMap.fst_apply; not present. simp handles projection after typed change.
- Keep chained dot syntax on same expression line or name intermediate hE; newline-leading .differentiableAt was parsed as anonymous projection and generated misleading Nat/LE errors.
- ContDiffAt.eventually here preserves finite order n; don't demand C² from eventual C³ without .of_le. In pd2_sum, eventual C³ plus differentiableAt suffices.
- literal_contDiffAt(p FIRST)(omega,u,aS,aV)(r,s).
- cosmological_hasDerivAt(J,K,hdet,Λ,r,s), hdet BEFORE Λ.
- Matrix.sum_apply, not Finset.sum_apply on matrix-valued sums.
- Source equation normalization: source_quadratic already gives E''/2=Hessian/2. Do not silently conflate Hessian with coefficient B.

Research card updated: docs/drafts/pipeline/1-in-progress/hb-physical-mode-action-contact.md, section 'Original on-shell quadratic pairing and boundary assembly'. Do not modify frontier. No need reread entire large card or previous checked modules.