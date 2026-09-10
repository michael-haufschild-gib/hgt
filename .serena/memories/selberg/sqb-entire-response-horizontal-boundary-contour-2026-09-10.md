SQB52 positive analytical progress; RH goal ACTIVE/unproved. Full chain: literal theta source -> normalized packets with vanishing native residual retaining mass -> entire Xi occurrence -> critical line -> RH. Hardest still native scalar source cancellation with mass. User: frontier READ ONLY, no numerical computations, no Git/launch/services, one owned foreground Lean process; scratch lake env lean FILE; final only leaf lake build MODULE --old after --no-build preflight; wire umbrellas, no full builds. No subagents.

Three new modules fully checked, leaf-built, wired, axiom-audited:
1 formal/GaloisForLFunctions/RHTower/SelbergThetaCommonForcingTransform.lean (238 lines). Namespace RHTower.SelbergThetaCommonForcingTransform.
   mode_integrable q w at every complex w, mode_transform_equation (alpha+w)*T_alpha(w)=-XiC(w).
   profile_transform_equation q w line112: (alpha^2-w^2)*profileTransform q w=XiC w, literal integral of common profile p.
   profileTransform_eq_entire identifies ALL points with (dslope XiC (-alpha) w-dslope XiC alpha w)/(2alpha).
   profileTransform_analytic line231 actual integral entire. tiltedProfile q a x=p_q(x)*exp(a*x); integrable, continuous, profileTransform_eq_fourier at frequency w.re/(2pi) with tilt w.im.
   Proof uses global sourceRatio_bounded, existing all-complex Phi integral, integral_eq_zero_of_hasDerivAt_of_integrable. Entire join via horizontal Fourier continuity + volume.ae_ne of two real coordinates. Do not rebuild all-plane Phi theorem or J continuity.

2 SelbergThetaHorizontalBoundary.lean. Namespace matching.
   symbol=H(z)/z; H=xi(z+3/2)*(z+(z+2)*xi(z+1)/xi(z+2)).
   source_hasMellin for Re z>0 literal J(a^2); H analytic Re z>=-1; symbol analytic except 0.
   mainTerm=H0=xi(3/2)/xi2.
   norm_scatteringCore_le via safe Lagarias half-shift endpoint from unconditional critical strip.
   xi_strip_decay line188: for .5<=Re z<=2, |Im z|>=2, C |t|^N exp(-pi|t|/4). xi_line_integrable for every line in that strip.
   boundaryPhase(t)=((1+it)/(-1+it))*xi(it)/xi(1+it); modulus1, conjugates on reflection.
   boundaryWeight=1+Re phase = half norm(1+phase)^2, bounds[0,2], even, zero at0.
   symbol_boundary M(-1+it)=XiC(t)*(1+phase(t)).
   This is analytic symbol, not a physical inverse Mellin theorem.

3 SelbergThetaNativeContour.lean. Namespace RHTower.SelbergThetaNativeContour.
   profileTransform_strip_bound q uniformly |Im w|<=2 via sum of L1 tilts +/-2.
   responseNumerator q z=H(z)*pHat_q(-I*(z+1)); responseSymbol=that/z, equals M(z)*pHat.
   Entire response removes spectral poles, sole pole0. Uniform decay, line L1, horizontal limits and bounded mean principal-part remainder all proved.
   responseSymbol_contour_shift V_(1/4)-V_(-1)=responseNumerator q0.
   responseNumerator_zero = C*xi(3/2)/(1+alpha^2); uses existing CommonForcing.mean_denominator_ne_zero.
   responseSymbol_boundary_integrable literal XiC(t)*(1+phase(t))*pHat_q(t).
   MAIN responseSymbol_spectral_boundary line237:
   V_(1/4)(R_q)=C*xi(3/2)/(1+alpha^2)+(1/(2pi))*integral XiC(t)*(1+phase(t))*pHat_q(t)dt.
   Unconditional at every actual Xi copy. Still NOT native scalarResponse equality.

Audits: /tmp/sqb52_{response,boundary,native}_audit.lean and .log all exit0; all selected source/main/decay theorems only [propext,Classical.choice,Quot.sound]. Final leaf logs /tmp/sqb52_{response,boundary,native}_build.log: only respective new leaf actually Built (16s,30s,122s); all other jobs replayed. /tmp/sqb52_lint.log exit0 formal lint passed, existing large-file warnings. Scratch final native /tmp/sqb52_native_contour.lean exit0 session86289. Final audit session55332 terminal0. ALL owned Lean/Lake/search processes collected, no stale owned processes.

Current card updated docs/drafts/pipeline/1-in-progress/sqb-native-spectral-source-comparison.md. Frontier and universal STATUS not edited.

NEXT hardest join: prove scalarResponse(q)=2*V_(1/4)(R_q) directly via Plancherel, not J pointwise inverse Mellin.
F_q(x)=exp(-5x/4)*p_q(x), G(x)=exp(x/4)*J(exp(2x)).
Native height substitution y=exp(2x) gives scalarResponse=2 integral F_q G.
G exactly logIntegrand P(-2x) for P.s=9/8. SelbergThetaHorizontalTransform.logIntegrand_integrable, integral_logIntegrand public. Generic P.s=1+z/2 yields its complex Fourier value M(z) via integral_comp_mul_left(-2).
Fourier(F_q)(u)=pHat_q(2pi*u-5I/4); Fourier(G)(-u)=M(1/4+2pi*u*I).
Fhat L1: response equation denominator has norm>=9/16 because |alpha.im|<1/2; bound by 2*norm xi(7/4+it), already line integrable. Need formalize this short bound and pairing.
Retrieved HTGeometry.ConductorPlancherelPairing.plancherel_pairing, sesq_fourier_pairing, and mathlib VectorFourier.integral_fourierIntegral_smul_eq_flip (all exact signatures read). Generic nonconjugate version follows flip plus Fourier inversion and x->-x.
Mathlib Measure.integral_comp_mul_left g a = abs(a^-1) smul integral g. Integral exp substitution via integral_image_eq_integral_abs_deriv_smul as private helper in HorizontalTransform lines473.
VerticalIntegral' is Zeta23/FromPNTPlus/ResidueCalcOnRectangles: (1/(2pi I)) smul (I smul integral f(c+it)); all imported through contour.
Then parity of actual p permits replacing 1+phase by boundaryWeight in full integral. Retrieve HedenmalmPrimeTranslation.sourceModeU_neg (file HedenmalmPrimeTranslationAnomaly line625), sourceModeU_thetaSource_eq_hedenmalmCausalVolterra, Xi spectral reflection: gives actual mode_reflect(-x)=-mode_q(x), hence p even and pHat even.
Mean normalization C=sourceMass/nativeVolume remains to join explicitly; sourceMass=2 integral exp(-x)Phi(x)=2xi(3/2), expected nativeVolume=2xi2=pi/3. Current searches found only finite-volume/bounding results in ModularFundamentalDomainVolume and SelbergModularHyperbolicArea, NOT absence proof.
After joins expected m(q)=1/(4pi) integral XiC(t)^2*w(t)/(t^2-alpha^2), for nonreal alpha^2. Sign agrees native self-adjoint Gram law. Extra source cancellation still required, no RH implication from w bounds alone.

Broad full-corpus searches this turn:
 /tmp/sqb52_cancellation_search.json (deep natural OR all views2rounds120sec);
 /tmp/sqb52_pairing_search.json (hybrid broad quoted OR all views);
 /tmp/sqb52_native_volume_search.json (deep OR all views2rounds);
 /tmp/sqb52_actual_response_comparison.json (hybrid broad OR allviews).
All candidates and source_arguments inspected, ideas/groups empty in these four. Earlier SQB52 xi-decay deep query had one inspected Gamma+smoothWeight ingredient set; source-specific Gamma match proved here. Index partial: inventoried55962 complete but compiler pending43720; vectors2171548/2331584 expected; refresh background indexer. No absence inference. Norm comparison query first nativeSource_ne_zero is UNCENTERED; centered U mass still different. AIME cancellation results have RH-equivalent premises; old NativeEnergy centeredEnergy is different centering. Do not repeat no-go searches. Seek constructive comparison for actual newly explicit source-response boundary.