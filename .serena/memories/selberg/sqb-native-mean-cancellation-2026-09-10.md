# SQB54: exact native mean cancellation (proved; RH open)

Goal ACTIVE: literal theta source -> normalized full-native residual packets retaining mass -> entire Xi occurrence -> critical line -> RH. Hardest remains source cancellation strong enough to orient the actual native scalar. No unconditional RH/occurrence theorem has been obtained.

## Finished module
formal/GaloisForLFunctions/RHTower/SelbergThetaNativeMeanCancellation.lean (165 lines), namespace RHTower.SelbergThetaNativeMeanCancellation. Wired immediately after NativeScalarBoundary in RHTower.lean.
Imports SelbergThetaNativeScalarBoundary, SelbergModularHyperbolicArea, Mathlib InverseDeriv and HurwitzZetaValues.

Six public, closed results:
- full_weight_integral_eq_pi_div_three: actual planar fullDomain integral of 1/y² = pi/3.
- native_volume_fd: original UpperHalfPlane volume fd = ENNReal.ofReal(pi/3).
- constantVector_inner: native constant-vector self inner product = complex cast pi/3.
- two_xi_two: 2*xi(2)=complex cast pi/3.
- mean_residue_cancel(q): exact equality of 2*C*xi(3/2)/(1+alpha²) and M²/((1+alpha²)*V), every actual Xi copy.
- sourcePairing_eq_cauchy(q):
  m(q)=(1/(4*pi))*integral_R Xi(t)^2*boundaryWeight(t)/(t²-alpha_q²) dt.
Here m is SelbergThetaCommonForcingGram.sourcePairing, alpha=xiSpectralPoint q, C=HorizontalBoundary.mainTerm, M=NativeSource.sourceMass, V=inner constant constant.
Uses previously proved sourceMass_eq_xi and mainTerm_eq. Previous NativeScalarBoundary.native_cauchy_integrable proves absolute convergence for every copy, including real removed points. No extra cancellation/volume/admission hypotheses.

## Actual proof joins
Existing SelbergModularHyperbolicArea.full_weight_integrable supplies full-domain integrability. Fubini via indicator(fullDomain), then existing inverse_square_integral along each vertical ray gives 1/arcHeight x. Real.hasDerivAt_arcsin on [-1/2,1/2] integrates to pi/3 (arcsin_sin and sin_pi_div_six).
Complex.measurableEquivRealProd preimage of fullDomain equals UpperHalfPlane.coe '' fd; fd uses normSq>=1 and |re|<=1/2. Existing arcHeight_sq/pos and nlinarith prove equality.
HTGeometry.volume_eq_lintegral_ofReal plus volume_preserving_equiv_real_prod.setLIntegral_comp_preimage_emb transports nonnegative integral; ofReal_integral_eq_lintegral_ofReal joins Bochner area.
inner_constantVector + constantVector_coe + integral_const gives V.
riemannZeta_two, GammaR(2)=pi^-1, and xi_two give 2xi2=pi/3.
NativeScalarBoundary.sourcePairing_cauchy then cancels exact mean terms.

## Verification complete: do not repeat
Scratch /tmp/sqb54_native_mean.lean passes lake env lean.
Name scratch /tmp/sqb54_native_names.lean passed.
Preflight: lake build GaloisForLFunctions.RHTower.SelbergThetaNativeMeanCancellation --old --no-build required ONLY new leaf.
Final same targeted command without --no-build passed; sole Built marker new leaf (78s). Log /tmp/sqb54_native_build.log. Do not cat whole logs: dependency warnings are replayed; rg '^✖|^error:|^✔|^Build completed'.
/tmp/sqb54_native_audit.lean checked all six public results with #print axioms: only propext, Classical.choice, Quot.sound. lake env lean exit0; log /tmp/sqb54_native_audit.log.
formal_tools.py lint passed (/tmp/sqb54_lint.log).
All owned Lean/Lake and research sessions terminal results collected. No live owned processes.
Card docs/drafts/pipeline/1-in-progress/sqb-native-spectral-source-comparison.md updated, with exact mean cancellation and remaining candidate. Frontier and universal STATUS untouched; no new route-independent law.

## Hardest obstacle / analytical search
The remaining Cauchy density Xi(t)^2*w(t) is nonnegative; its imaginary sign agrees with native self-adjoint Gram displacement. Do not call positivity alone a cancellation/RH proof.
Broad/deep OR searches:
 /tmp/sqb54_source_search.json, positive_source, rh, oscillation, native_orientation, area, division, gauge_order, theta_interlacing (all same prefix/suffix _search.json).
Candidate/source arguments and other views inspected (truncated sections reread). Deep requests partial/deadline and no proof_ideas/ingredient_sets; hybrid inventories complete but semantic/compiler coverage incomplete. Failure is not absence.
Area search found exact existing integrability and ray producer, reused successfully.

Tested completed-theta one-sided E candidate: XiCTaylorThetaTailCompletedDensityDeBrangesNoGo.not_forall_thetaCuspTailSecondDensityDeBrangesGap_pos already refutes global positive HB gap in 0<Imz<1/2. E upper-zero-free/Pick cone does NOT establish needed native orthogonality. Do not reprove obstruction.
XiPolynomialDensity.ae_eq_zero_of_orthogonal_polynomial_XiC needs all Xi-weighted polynomial pairings zero; no actual source orthogonality supplied.
Likelihood search found thetaCuspHigherLikelihoodSpectralMasterLaw (actual all-order positive Hankel in intrinsic positive Laplace B coordinate); this is NOT oscillatory-response positivity.
Latest candidate: ThetaCuspReflectedLikelihoodInterferenceFactorization.lean READ entire 157 lines. Actual source normalized reflected product =
 thetaCuspSingleAtomReflectedNormalizedModel(A,z) * thetaCuspReflectedLikelihoodInterference(u,t), for 0<=t<=u.
Interference = Z(B(u+t))*Z(B(u-t))/Z(Bu)^2 with complete positive likelihood partition. All unequal-index contributions remain. Exact action additive, cocycle positive/even/normalized.
SingleAtomReflectedRiccatiContraction has literal atom Riccati margin >0 at line621; only headers/signatures read, not full625 lines. Full-interference control under native pairing remains unproved; no transfer theorem constructed.
Common-interlacing search with module Theta had no lexical declarations; semantic results do not supply atom interlacing. Don't infer interlacing from positive Hankel. Literal individual atoms lack full modular seam cancellation.

## Rules
No numerical work, Runpod, Git, launch.sh, service management, subagents. Frontier READ ONLY. Foreground one Lean/Lake owned process, collect before next. lake env lean scratch; final targeted leaf build --old and no umbrella/full builds. Umbrella wiring allowed/required.
Every new turn opening: full proof chain + hardest mathematical obstacle + concrete attack. Keep goal active, never mark complete on this partial result.

## Lean gotchas fixed
Set.indicator_of_mem hy can infer wrong set if hy merely inequality: give show y in Ici arcHeight from hy. Same neg.
integral_zero' handles Pi.zero; or exact MeasureTheory.integral_zero (Real) (Real) works where rw fails.
Explicit measure type for hc.integrableOn_Icc.
For setLIntegral transport change h's integrand to explicit z.im before rw; then simp_rw [<-one_div] under binder.
ENNReal.toReal_ofReal needs explicit pi/3 nonneg.
After zeta algebra field_simp gives h: pi=6*xi2, use linear_combination -h.
