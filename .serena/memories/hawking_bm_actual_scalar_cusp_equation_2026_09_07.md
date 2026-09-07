# HB actual scalar harmonic equation — verified progress

Goal ACTIVE, unbounded, RH neither proved nor falsified. Previous goal usage2,588,082 no budget. This turn made verified progress, not no-progress: new 301-line leaf ThetaCuspHawkingBMAngularScalarEquation closes full literal scalar cusp equation with actual derivatives for arbitrary complex u and all Y>0. Next turn opening must state full chain and significant target. Chain: literal theta-cusp → Xi occurrence → retained spin-two source → physical causal radial/left-QNM action → fixed Hawking-clock extinction → RH.

## New audited leaf
formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMAngularScalarEquation.lean; namespace RHTower.D4BMAngularSeries; imports CuspJointSmooth and HTGeometry.ScalarTwoJetCalculus. Uses actual ScalarTwoJet.coordDeriv i f z = fderiv R f z (Pi.single i 1), matching metric source calculus.
16 public theorems:
1 value_coordDeriv_zero
2 value_coordDeriv_one
3 value_coordDeriv_zero_zero
4 value_coordDeriv_one_hasFDerivAt
5 value_coordDeriv_one_one
These differentiate existing actual first-family derivatives on the open Y>0 chart. SecondYY formula: a(a-1)F(nu,a-2,d)-2a*pi*(F(nu+1,a-1,d+1)+F(nu-1,a-1,d+1))+pi²*(F(nu+2,a,d+2)+2F(nu,a,d+2)+F(nu-2,a,d+2)). SecondXX=horizontalRate² F(nu,a,d+2).
6 bessel_second_order_relation: s²/4*(K(nu+2)-2Knu+K(nu-2))-s/2*(K(nu+1)+K(nu-1))=nu²Knu, s>0. Derived from corpus modifiedBesselKOrder_add_one at nu,nu+1,nu-1 and field_simp. Linear combination (s/4)*hp-(s/4)*hm+(nu/2)*h0.
7 term_hyperbolic_equation: per-weighted signed summand at a=1/2, any index degree d, all positive heights. Real rpow half shifts via common Y^(-3/2).
8 value_hyperbolicLaplacian: full infinite F(a=1/2) obeys actual Lap equation with nu²-1/4, any d/sign. HasSum linear combinations and uniqueness pass exact term identity, then actual second derivative formulas.
Definition hyperbolicLaplacian f z=(z1:C)^2*(coordDeriv0(coordDeriv0 f)z+coordDeriv1(coordDeriv1 f)z).
9 hyperbolicLaplacian_congr (local eventual equality)
10 hyperbolicLaplacian_add (C2 fields)
11 hyperbolicLaplacian_const_mul (C2 field, complex amplitude)
12 signedTail_hyperbolicLaplacian (pre-existing signed sqrt tail, any index degree, heightDegree0)
13 height_cpow_hasFDerivAt: gradient0(w*Y^(w-1)), from GaloisForLFunctions.RHTower.hasDerivAt_cpow_ofReal in PrimeLogJumpMellinTrace.
14 height_cpow_hyperbolicLaplacian: w(w-1)Y^w.
15 cuspConstantTerm_hyperbolicLaplacian: literal scalar Weyl terms each eigenvalue u²-1/4.
16 scalarCusp_hyperbolicLaplacian: literal full d4BMCompletedEisensteinCuspLeg .scalar u satisfies Y²(E_xx+E_YY)=(u²-1/4)E for every u:C and Y>0. Both Weyl terms +2*(both full signed infinite tails), no supplied jet/higher-derivative or Y>=1 premise. This is actual scalar chart equation; metric connection interpretation/vector reconstruction still next.

## Validation
Scratch lake env lean passed without warnings. Exact source cache-only isolated final lake build leaf passed5.2s, only new leaf compiled. Byte checked copies, installed only new olean/ilean to main cache, no dependency trace/hash copied. Wired once RHTower.lean (was14680; shared file shifts). One scratch#print axioms of16NEW public theorems only: propext, Classical.choice, Quot.sound. Index, scoped diff check, formal lint passed;132 existing size warnings. All owned Lean/Lake ended; scratch /tmp/hb-bm-angular-equation.OJV2R6 removed safely file-by-file. No numerical computations. Do not re-audit/rebuild this leaf or prior leaves.

## Next actual coexact-vector task
Source inspection confirmed d4HyperbolicHodgePairedVectorEigenvalue in ThetaCuspHawkingTeukolskyBackreactionReturnDeterminant:230 merely defines q+1; adjacent effectiveQ equation ring algebra. Need actual covector from scalar and literal horizon connection, THEN first-order Einstein equation/full source. Current source card contains paper-derived coordinate calculation (LEAN OPEN): for g=Y^-2 diag1, Gamma^x_xy=Gamma^x_yx=-1/Y, Gamma^y_xx=1/Y, Gamma^y_yy=-1/Y, other symbols0. CoordinateCovectorD_i V_j=partial_i V_j-sumGamma^k_ij V_k. RoughLap includes BOTH lower-slot terms in second derivative: g^ij*(partial_i D_j V_k-Gamma^l_ij D_l V_k-Gamma^l_ik D_j V_l). Expands to:
rough Vx=Y²(Vx,xx+Vx,YY)+2Y(Vx,Y-VY,x)-Vx;
rough VY=Y²(VY,xx+VY,YY)+2Y(VY,Y+Vx,x)-VY;
div V=Y²(partial_x Vx+partial_Y VY).
For coexact S=(S_Y,-S_x), C3 derivative symmetry yields div=0 and rough(coexact S)=coexact(Delta S)-coexact S. If Delta S=-qS, rough V=-(q+1)V. Derive these from actual metric derivatives/connection; no merely assigned spectral shift. Source ScalarTwoJetCalculus private partial_hasFDerivAt/partial_second show how to get actual ordered derivatives and derivative symmetry. Mathlib FDeriv/Symmetric ContDiffAt.isSymmSndFDerivAt (hf)(minSmoothness R2≤n); use C3 to commute third derivatives. No actual coexact vector/nonzero normalized harmonic yet; do not claim completed Einstein source from scalar equation alone.
Existing ScalarTwoJet.ofField_add/mul/constant used for actual Lap linearity; coordDeriv is abbrev. CoordinateCurvatureTwoJet.christoffel generic finite-d matrix jet and CoordinateCurvature.coordinateChristoffel actual smooth metric available. Literal fixed horizonScale Y^-2 and block equality in FundamentalMetricSource already audited. Need geometry weld and then full reconstructed linearized Einstein equation, B/C reduction, higher-order/gauge corrections, exceptional sectors, spectral/spatial jet interchange if needed, causal support/boundary terms, response domain/left-QNM projection/extinction.

## Proof efficiency / docs
Lean main scratch checks sometimes took2-3min wall but only~16sCPU; tracked same live handle, no restarts. Final isolated cached leaf5.2s. Cast issue: after push_cast, linear_combination coefficient must use ((N:C)+1)^d, not fresh ((N+1:N):C)^d. Before linear_combining HasSum equality with family formulas, simp only[value] at heq and goal, norm_num both (normalizes negative rational exponents), then linear_combination. EventualEq.fderiv needs (k:=R spelled 𝕜:=ℝ) explicitly if inference stuck. Use fderiv_const_apply, not fderiv_const, for a lambda constant at a point. generic zero_apply, no deprecated CLM.zero_apply. Use .hasFDerivAt.comp for R→C functions followed by coordinate CLM, not comp_hasFDerivAt (same scalar-field codomain restriction).
Research card updated closed scalar equation, paper covector derivation, validation. Frontier current HB row, full source paragraphs and Open core updated (shared dynamic lines); Universal STATUS F20i-k now distinguishes actual all-parameter eigen-equation from selection. Rules: one owned foreground Lean process, scratch lake env lean, final leaf lake build, no full/umbrella builds, new axioms only. Numerical experiments ONLY RunPod ssh root@157.157.221.29 -p27094 -i ~/.ssh/id_ed25519; multicore, unpredictable only, no hourslong, download/document computations dir. No subagents authorized. Previous background/radial/smooth leaves in mem:hawking_bm_joint_angular_smoothness_2026_09_07 and mem:hawking_bm_fundamental_metric_source_2026_09_07, do not repeat audits.
