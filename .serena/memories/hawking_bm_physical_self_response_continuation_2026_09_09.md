# HB: complete original physical response continued to its own fundamental QNMs

Goal RH ACTIVE and UNPROVED. Previous and current goal turns are PROGRESS. This stage closes pointwise meromorphic continuation of the original same-copy physical response, after last stage closed its complete-source endpoint Green identification. No subagents or numerical experiments. Frontier map READ ONLY; hash preserved. All owned Lean/Lake sessions terminal, scratch/audit directory /tmp/hb-reduced-resolvent.5koylm5n and marker /tmp/hb-reduced-resolvent-current removed.

## Authoritative artifacts
- docs/drafts/pipeline/3-formalized/hb-physical-self-response-continuation.md: exact proof, scope, audit.
- docs/drafts/pipeline/1-in-progress/hb-physical-response-radial-equation.md: current closed chain and remaining physical residue.
- universal-law-field/STATUS.md: new F20i-ac, route-independent rule about deriving nonvanishing before canceling auxiliary factors; their nonvanishing is not pole survival.
Earlier endpoint/classical/Dirichlet cards updated to link current same-copy continuation. Preserve unrelated concurrent Selberg files, umbrellas, generated indexes and STATUS edits.

Ten installed RHTower leaves, prefix ThetaCuspHawkingBM:
ReducedGreenResponse, ReducedGreenContinuation, ReducedGreenBounds,
BoundedRadialUniqueness, PhysicalResolventAssembly, PhysicalSelfAngularGaps,
PhysicalResolventEquation, PhysicalResolventBounds,
PhysicalResolventIdentification, PhysicalSelfResponseContinuation.
29 public theorems +15 definitions =44 declarations, 583 lines; largest72.

## Exact mathematics
Let P be original physical profile for source q, target r; F=continuedAngularSourceProjection=M A+sum_i h V_i C_i, retaining actual residual period A and all three cutoff periods C_i. V_i=continuedPrincipalDifference, amplitude A_i=principalAmplitude, eigenvalue lambda_i=m_i(m_i-1), m_i=[2rho_q,1,2-2rho_q]. Physical target lambda=-(1/4+physicalRadialFrequency(r)^2).

New reducedGreen and continuedReducedGreen at independent target chi use native tortoiseGreen/continuedTortoiseGreen with J, K=(-(1/4+chi²)/2-(s+1)(s+2))*J, minus the original radialLift*J. Actual jets, equation L_lambda U(J)=M J, overlap equality, boundedness and zero outer trace are proved. MeromorphicAt for Rew>-2, Imw≠0 at every fixed t<0 is proved from existing native continuation. reducedGreen_eq_principalDifference connects all original principal coefficients.

Define delta_i=physicalAngularGap(q,r,i)=lambda_i-lambda, D=physicalAngularGapProduct=prod delta, E_i=physicalAngularGapCofactor=prod_(j≠i) delta_j. Define
R=clearedPhysicalGreen=D U(A)+sum_i E_i C_i [V_i-U(A_i)].
Exact cofactor identity E_i delta_i=D holds even at zero gaps. Actual equations give L_lambda R=D F. All value/jet/boundary estimates are derived. BoundedRadialUniqueness derives its first-jet bound internally from bounded value and bounded homogeneous potential using the backward unit-interval estimate, then applies original Wronskian uniqueness. Therefore physicalCuspProfile_mul_gapProduct proves D P=R on 3/2<Rew<2, Imw≠0 for EVERY q,r, with no angular noncollision premise. It does not recover P where D=0.

Crucial new source-specific noncollision: when r=q, physicalAngularParameter=(rho-1)/2, lambda=rho(rho-2)/4. Gaps factor as
 delta0=3rho(5rho-2)/4,
 delta1=rho(2-rho)/4,
 delta2=(3rho-2)(5rho-4)/4.
All factors have only real roots; xi_divisor_support_im_ne_zero gives every gap and D nonzero unconditionally for each actual Xi copy. physicalAngularGap_self_factors, physicalAngularGap_self_ne_zero, physicalAngularGapProduct_self_ne_zero are installed.

continuedPhysicalSelfResponse=R/D for r=q. Capstones:
- physicalCuspProfile_eq_continuedPhysicalSelfResponse
- physicalCuspResponse_ae_continuedPhysicalSelfResponse (original Hilbert class on overlap)
- completePhysicalGreenProfile_self_eq_continued (literal all-four-source endpoint integral on overlap)
- continuedPhysicalSelfResponse_meromorphicAt (pointwise t<0, nonreal Rew>-2)
- allXi_fundamental_physicalSelfResponse_meromorphic (both original fundamental QNMs for EVERY actual copy, no supplied noncollision/continuation/RH premise).
Meromorphy is pointwise in the original interior radial coordinate, NOT radial-L2-valued or operator-valued at QNMs. Arbitrary cross-copy recovery at zero delta remains a confluent problem. No residue, nonzero principal part, pole survival, spin-two reconstruction or extinction yet.

## Next hard step: actual complete-source pole coefficient
First prove scalar-amplitude linearity of native continuedReducedGreen: U(J)=J U(1), with the original integrals/finite-part normalization retained. All source profiles and gradient coefficients are scalar multiples of J, so the existing unconditional integral_mul_const should suffice; no new numerical or source estimate. This yields P_self=Aeff U(1)+sum_i (C_i/delta_i)V_i, Aeff=A-sum_i C_i A_i/delta_i. This reduction is proposed, not yet Lean proved/evaluated.

Then derive regularity of every principal V_i and original onset at target same-copy fundamental QNMs before discarding their principal parts. Parameter evidence to use: BMLaplaceParameters connection=Gamma(gaussC w) Gamma(1/2)/(Gamma(gaussC-gaussA) Gamma(gaussC-gaussB)); gaussA=1/4+w/2+Ichi/2, gaussB=1/4+w/2-Ichi/2, gaussC=1+w. For principal chi_i=I(m_i-1/2), denominator arguments are 1/2+w/2+m_i/2 and 1+w/2-m_i/2. At physical same-copy QNMs w=-1-rho/2 or -2+rho/2, their imaginary parts are nonzero rational multiples of Imrho (±1/4, ±3/4, ±5/4 depending i). This suggests all principal connections are nonzero; CHECK exact QNM normalization against current definitions and formalize, not an existing theorem. Complex.Gamma_ne_zero is used elsewhere via exclusion of negative integers; nonreal arguments exclude them. Nonzero connection plus native horizonFirstMellin_analyticAt and analytic outer moment should give AnalyticAt, stronger than existing meromorphy. Also exclude w=2*physicalRate q branch for the original onset; distinguish D4BMJointSource physicalRate (fundamental rho-2 or -rho-1) from a separate doubled physicalRate in BMCuspIndicialSelection namespace. Do not confuse definitions.

The target physical connection is zero at its QNMs; retain its actual Laurent normalization and the native full source moment in the residue. Aeff needs actual residual angular period continuation/evaluation (frontier's Fourier-Mellin source problem), all three cutoff terms, nonzero principal-part incidence, physical adjoint/left-QNM identification, then spin-two/AIME and independent extinction. Meromorphy and auxiliary gap nonvanishing cannot substitute for this. a=0 would trivially kill source; any nonzero-source claim must retain actual amplitude choices.

## Verification and efficiency
All10 scratch lake env lean checks passed. Each canonical leaf final-audited separately by lake build exactModule in private cache-backed audit project; all10 warning-free. Scratch-only #print axioms on44 NEW declarations: all exactly propext, Classical.choice, Quot.sound, no other diagnostics.30 installed .lean/.olean/.ilean hashes matched audited files.10 unique umbrella imports; no umbrella/full build. One index refresh; lint --check-generated EXIT0 with141 existing large-file warnings. git diff --check EXIT0. All owned processes cleaned.
Private audit uses local dependency stubs with empty roots/globs; own exact leaf targets need roots=[module], globs=[module]. Link new audited .olean/.ilean into private cache before axiom scratch. This turn hardlinked68586 cached artifacts (unnecessarily broad, ~20sec); future setup should compute needed own-module import closure and link only that, as earlier ~4k-module stage did. Never rebuild all old imports.
Lean pitfalls resolved: norm bound add_le_add_right adds common LEFT term (name counterintuitive); use explicit Complex.continuous_ofReal.comp horizonCoordinate_continuous, fun_prop doesn't infer it. Fin.sum_univ_succ expansion needs Fin.succ_zero_eq_one and Fin.succ_one_eq_two before linear_combination, otherwise opaque function arguments Fin.succ0 versus1 remain unmatched atoms. Use current tendsto_finsetSum (old tendsto_finset_sum deprecated). Numeric imaginary parts: norm_num, not nonexistent Complex.ofNat_im.
