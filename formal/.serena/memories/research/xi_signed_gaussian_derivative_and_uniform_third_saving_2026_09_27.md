# Signed Gaussian derivative and second positive uniform H3 saving

Goal remains ACTIVE. No RH proof/refutation; domination rho_D <= 1 unproved. User requires unconditional actual providers, no new axioms/holes, no computations, foreground leaf audits with lake --old env lean, no umbrella/full builds, no resource hacks. No subagents authorized. Corpus search required via python3 ../scripts/formal_tools.py research; direct Lean only, no cards.

Continuation of `mem:research/xi_cofactor_relative_phase_and_positive_third_saving_2026_09_27`.

## New verified mathematics
A_q=Q(alpha_q^2) exp(-t alpha_q^2/2), K=sum |A|^2, J=sum(Re A)^2, I=sum(Im A)^2, H=J-I=K-2I. Complete H3=a²mu0+2abmu1+(b²+2ac)mu2+2bcmu3+c²mu4 retained.

Define D_t Q=Q'-(t/2)Q, coefficient (j+1)a_(j+1)-(t/2)a_j. Exact complex amplitude derivative proved. Vertical segment Re z -> z keeps real part and norm <= |z|. Complex mean value theorem gives |Im(Q(z)exp(-tz/2))| <= |Im z| exp(-t Re z/2) sum_j |(D_tQ)_j| |z|^j, all real t and complex z. Cancellation occurs before absolute value.

B_j(s)=(2j+4)!(2/s)^(2j+4), s>0. T_Q=sum |(D_tQ)_j|sqrt(B_j). Actual full imaginary channel bound I(Q,t) <= exp(-(t-s)G_F) U_F T_Q², t>=s>0; G_F actual residual gap, U_F actual residual orientation budget. No analytic/RH premise.

For Q=a+bX+cX²: T=|b-ta/2|sqrt(B0)+|2c-tb/2|sqrt(B1)+|tc/2|sqrt(B2). Previous root envelope R=|a|sqrt(A0)+|b|sqrt(A1)+|c|sqrt(A2). PROVED T²+(a²t²/4)B0 <= R², all t>=0 and all real a,b,c. /4 is current strong version; earlier /64 superseded. Constant direction recovers exact old-new gap. Exact root helper adds |a|(sqrt(A0)-(t/2)sqrt(B0)); proof retains nonnegative mixed contributions.

For actual distinct positive critical nodes x_i=gamma_i², V_ij=x_i^j, Delta=det(V)², P_i(X)=sum_j adj(V)_ji X^j. New cofactor R_D=sum_i exp(tx_i)T_Pi². Exact adjugate reconstruction and weighted CS, with paired reserve 2sum Q(x_i)²exp(-tx_i)<=J, gives I<=rho_D J, H_N>=(1-rho_D)J where rho_D=exp(-(t-s)G_F)U_F R_D/(2Delta). ALL finite N and ALL t>0 via s=t/2, actual nodes chosen unconditionally before F/coefficient/time. No generalN comparison to prior rho claimed.

H3 extra saving S_D=(t²B0/4)sum_i adj(V)_0i² exp(tx_i)>0: constant adjugate row cannot vanish for invertible V. R_D+S_D<=R_x; sigma_D=exp(-(t-s)G_F)U_FS_D/(2Delta)>0; rho_D+sigma_D<=rho_x. Previous cofactor saving rho_x+sigma_C<=rho_sep. FINAL actual theorem simultaneously proves sigma_D>0, sigma_C>0, H3>=(1-rho_sep+sigma_C+sigma_D)J for same actual three nodes, arbitrary F,a,b,c,t>0. rho_sep=xiGaussianOrientationPhaseBudget F 3 (t/2) t / xiCriticalSamplingHeatFloor gamma t. All same nodes/reserve/anchor, not comparison against every alternate anchor/budget. Independent previous floor K>=J>=F_gamma(t)sum a_j², F_gamma>0 forN>=1 still available. Missing: rho_D<=1, alltime positivity, RH/witness.

## Six new modules, final audits
All formal/GaloisForLFunctions/RHTower/*.lean, each imported exactly once by RHTower.lean; current oleans; 29 new theorems,8defs.
- XiGaussianDerivativePhase (5thms,1def), audit97006 exit0 warning-free.
- XiGaussianDerivativeOrientation (5,2),50130 exit0.
- XiGaussianThirdDerivativeSaving (5,1),STRONG23666 exit0.
- XiGaussianDerivativeCofactorTransfer (4,1),12463 exit0.
- XiGaussianDerivativeNodalBudget (4,1),47736 exit0.
- XiGaussianDerivativeRelativeSaving (6,2),STRONG57219 exit0.
Required missing dependency GaussHodgeWeilEntireDetection restored audit77284 exit0; source unmodified.
Each audit: lake --old env lean <leaf>.lean -o .lake/build/lib/lean/<leaf>.olean. No full/umbrella build. Final 70918 axiom audit exit0 checks29new+5providers=34: only propext/Classical.choice/Quot.sound. Scoped proof-hole/forbidden-computation/resourcehack/trailingwhitespace and git diff --check pass. Index89730 exit0. Metadata56375 exit1:10 unrelated unreachable modules: LatticeMasksDeepPair, MoebiusMollifiedCriticalMoment, MoebiusMollifiedErrorThreeLines, MoebiusMollifiedZetaField, ThetaPrimePowerBernsteinGauge, ThetaTranslationGaugeFlux, ZetaZeroDensityPowerSaving, HTGeometry.CompletedPseudoDiffOpAdicCompleteness, CompletedPseudoDiffOpVectorArtinian, CompletedPseudoDiffOpVectorLattice. No new-scope errors or stale generated metadata. Do not claim repo-wide lint clean. No owned live process remains.

Artifacts at /Users/michael/Documents/Codex/2026-09-26/new-chat-3:
- outputs/xi-signed-derivative-phase.md final report, linked from prior cofactor report.
- work/xi-signed-derivative-phase-manifest.json (exact names).
- work/xi-signed-derivative-phase-verification.json (final checks, errors).
- work/xi-signed-derivative-phase-axioms.lean and .log.
- work/xi-signed-derivative-phase-lint.log.
- work/xi-curvature-rh-loop.md appended.

Useful final theorem: XiGaussianDerivativeRelativeSaving.lean:108 exists_xiHeatThirdQuadratic_two_positive_relative_savings. FullN XiGaussianDerivativeNodalBudget.lean:84 exists_xiHeatHankelForm_allTime_derivative_relative_lower; detailed nodal statement at32.

## Conjecture frontier / search evidence
Search2064 established no existing signed Gaussian derivative phase bound. Search28242 read XiGaussianPolynomialTimeControl and XiHankelPolynomialTimeRegion: existing all-degree region is t(d+3)^5=2pi exp(2tau), not fixed allpositive time; cannot infer all-degree semigroup/Taylor propagation automatically. Search24600 firstcriticalzero momentratio: XiWardSourceWindowMultiplicity firstFourSineMoment barrier near730-802 is CONDITIONAL abstract squareenergy/momentidentity, not actual lowcriticalzero capture. ThetaCuspCalibratedPowerReciprocalMomentLaw/SecondMomentLaw give theta measure ratios, not actual lowcriticalnode location. Do not mistake these for closure. Next meaningful conjecture needs actual threshold control: lowcritical source capture, residual rate/gap, or justified degree/time propagation. Another equivalent reformulation or mere positive correction does not close RH. Unimplemented possibility: adaptive gap rank1 forFempty from quartetcost; no proof yet, do not claim.

## Local Lean lessons
HasDerivAt.congr_deriv normalizes exact derivative; convert hp.mul he produced wrong-level goal. exp_ofReal identifier unavailable: use heatPhaseAmplitude_im and evalRealPolynomial_ofReal. Complex.ext explicit. Segment subtype projection change w.re=z.re before rw. abs_sub_le here is three-point triangle; use abs_add_le b (-ha). natDegree_add_le_of_degree_le/natDegree_C_mul_X_pow_le, natDegree_derivative_le and natDegree_C_mul_le handle polynomial truncation. Fin3 normalization broad simp [xiGaussianFiniteRootEnvelope,Fin.sum_univ_three]. Square comparisons use (sq_le_sq₀ nonneg nonneg).mp plus nlinarith only on explicit nonnegative squares. Positivity denominator annotate (show (0:Real)<=4 by positivity) to avoid inference ambiguity. Root helper now exact root gap; dsimp only local variables before nlinarith, avoid change with wrong association. No new norm_num/decide/native_decide/#eval/#reduce. Do not rerun completed audits without source change.
