# SQB53: exact native scalar Cauchy formula

Active unbudgeted RH/SQB goal remains UNPROVED. Hardest: native source cancellation with retained mass. Chain literal theta -> normalized native residual packets retaining mass -> entire Xi occurrence -> critical line -> RH. User: frontier READ ONLY; analytical only; no computations, Git, launch.sh, subagents. One owned foreground Lean/Lake process, lake env lean scratch/source, targeted final leaf build with --old and preflight --no-build, no umbrella/full builds. All SQB53 processes terminated normally and collected.

## Completed, checked module
`formal/GaloisForLFunctions/RHTower/SelbergThetaNativeScalarBoundary.lean` (409 lines), namespace `RHTower.SelbergThetaNativeScalarBoundary`. Imports NativeContour and CommonForcingPairing; wired into RHTower.lean immediately after NativeContour. Complete scratch `/tmp/sqb53_native_pairing.lean` passed. Final leaf `lake build GaloisForLFunctions.RHTower.SelbergThetaNativeScalarBoundary --old` passed: only this leaf Built24s, other jobs replayed. Log `/tmp/sqb53_native_build.log`. Preflight `/tmp/sqb53_build_preflight.log` only leaf missing. Axiom audit `/tmp/sqb53_native_audit.lean` + `.log` exit0: seven main theorems only propext, Classical.choice, Quot.sound. `scripts/formal_tools.py lint` passed `/tmp/sqb53_lint.log`, existing large-file warnings. No need repeat.

Public results:
- safeSource x=exp(x/4)*J(exp(2x)); integrable, Fourier at -t/(2pi) equals M(1/4+it).
- tiltedProfile_fourier_integrable q for tilt -5/4. Actual pHat on t-5i/4 bounded by2normxi(7/4+it); denominator norm>=9/16, weakened to1/2.
- scalarResponse_eq_log_pairing: S(q)=2 integral p_q(x)exp(-5x/4)*safeSource(x). Direct y=exp2x substitution.
- scalarResponse_eq_contour: S(q)=2 VerticalIntegral'(R_q)(1/4). Bilinear Fourier duality with actual Fourier inversion, exact2pi frequency scale.
- scalarResponse_spectral_boundary and scalarResponse_real_boundary: join previous one-pole contour; reflection turns 1+phase into real w.
- profileTransform_even_real q t: pHat_q(-t)=pHat_q(t), at removed points too. From transform equation a.e. away from re(alpha),-re(alpha), then continuity.
- real_boundary_integrable and boundary_integral_eq_real: absolute admission retained under reflection averaging.
- sourceMass_eq_xi: (sourceMass:complex)=2xi(3/2), actual all-plane Phi transform at -i.
- native_cauchy_integrable q: integral of Xi(t)^2*w(t)/(t²-alpha²) absolutely converges for EVERY actual copy (no off-axis hypothesis). Totalized real removed values irrelevant by ae equality.
- scalarResponse_cauchy (around387): S(q)=2*C*xi(3/2)/(1+alpha²) -(1/pi) integral Xi(t)^2*w(t)/(t²-alpha²).
- sourcePairing_cauchy (around396): m(q)=-1/4*(2*C*xi(3/2)/(1+alpha²)-sourceMass²/((1+alpha²)*inner constant constant)) +1/(4pi)*integral Xi(t)^2*w(t)/(t²-alpha²).

C=xi(3/2)/xi2, w=1+Re beta=norm(1+beta)^2/2 already proved previous turn; w in[0,2] even. This sign agrees with native SA Gram law. Formula does NOT prove cancellation/reality or RH. Remaining normalization V=inner constant constant=2xi2=pi/3 would cancel mean terms. Source mass join is now done.

Card `docs/drafts/pipeline/1-in-progress/sqb-native-spectral-source-comparison.md` updated current math/status. Frontier and universal STATUS untouched (no route-independent new law).

## Searches and prospective source attacks
Deep broad OR queries all retrieval views/max-rounds2/budget120: pairing Fourier/Mellin, even/reflection/divided difference, theta source cancellation/spectral measure/scattering/retained mass, entire response/deBranges/kernel, modular area/covolume/GaussBonnet. Hybrid uncapped module RHTower: half shift/deBranges/Hardy/orthogonality. Lexical OR exact module Modular: volume/area/measure. JSON files `/tmp/sqb53_{pairing,even,cancellation,kernel,hardy,area,modular_area}_search.json`. Inspected candidates, source_arguments, declarations/exploration and prose summaries; deep ideas/groups empty. Partial true, interrupted text/source/filter deadlines; semantic ~2172668/2331703; source_only compiler metadata, not compilation evidence. No absence inference.

Directly read verified source candidates: CauchyTransformHardy.integral_cauchyTransform_eq_zero requires actual Hardy membership. SoninBurnolConductorBounded.fourier_pairing_eq_zero requires opposite physical halfline supports. SuzukiDeBrangesRepresentation.suzukiDeBrangesSeries_div_ae explicitly requires RH. No premise supplied for native source; no new generic conditional receiver/no-go added.

Exact volume join producer retrieved by lexical exploration: `RHTower.D4BMModularCore.integral_measure_chart` in `ThetaCuspHawkingBMModularWeakDerivative.lean`44, read. (integral_upper F(z) dmeasure) = integral_cellChart chartDensity(z) smul F(z). Density=(1/norm im)^2, cellChart=coe '' ModularGroup.fd. map_measure_eq25 gives exact pushforward. Native constantVector_coe + inner_constantVector already public in SelbergNativeConstantMode. `SelbergModularHyperbolicArea.inverse_square_integral` for positive lower endpoint gives1/a. Full area integral using lower arc sqrt(1-x²), x∈[-.5,.5], expected arcsin boundarypi/3. Current area modules only bound area; no absence claim. mathlib riemannZeta_two in NumberTheory/LSeries/HurwitzZetaValues.lean226.

Additional actual-source producer from declaration/exploration views (not yet joined to SQB): `XiCTaylorThetaTailCompletedDensityTransversePick.lean`356 proves thetaCuspTailSecondDensityDeBrangesE_ne_zero on WHOLE upper half-plane. Read definitions and proof. E(z)=(z²+1/4)*F(z)-1/4 where F is actual one-sided completed second-density transform; Esharp uses F(-z). `XiCTaylorThetaTailCompletedDensityDeBranges.lean`31 proves E+Esharp=4z²XiC(z) for|Im z|<1, actualsharp identity also proved. Upper endpoint zero-freeness comes from transverse cone Im(z)*normF(z)<=Im(zF(z)); on imaginary axis sourcepositive mass<=1. `XiCTaylorThetaTailCompletedDensityProjectiveCollision.lean`109 gives Wronskian at Xi zero=4z²XiC'(z)E(z). Native connection / contraction of Esharp/E still unproved; zero-free E alone not enough. Could examine this source-defined split for native pairing identity, not assume Suzuki RH-dependent expansion. No new formal theorem from this candidate.

## Lean syntax lessons
- integral_neg_eq_self takes explicit measure: `(integral_neg_eq_self f volume)`.
- rw integral_comp_mul_left may fail under composed lambda even defeq: explicit calc equality supplied by `Measure.integral_comp_mul_left (fun t=>...) (2*pi)` works.
- sq_sub_sq expands (a+b)*(a-b), so factors h2 thenh1.
- Fourier inversion equality `hFc.fourierInv_fourier_eq hF hFT`; doubleFourier=reflection via Real.fourierInv_eq_fourier_neg.
- Change Real Fourier Circle smul explicitly before rw Real.fourierChar_apply.
- For integrable.neg under lambda, simp under Integrable may not eta-expand; use h.neg.congr (Eventually.of_forall fun t=>by simp only[Pi.neg_apply,neg_neg]).
- Annotate quotient equality before `(eq_div_iff hn).mpr`; otherwise metavariables fail productcommutativity.
- All tmp source checks current toolchain in formal cwd; no owned Lean processes left.
