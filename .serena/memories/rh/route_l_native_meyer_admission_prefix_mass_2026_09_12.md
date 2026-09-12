# Route L C65 — actual source admission and horizontal prefix mass

RH and full-source fixed Gamma/BV reader agreement remain UNPROVED. Goal ACTIVE. Latest user target “establish full-source reader agreement.” Chain: complete original source → fixed-reader agreement → conormal vanishing → RH.

## Closed new mathematics
Two new leaves, 420 lines total:
- formal/GaloisForLFunctions/RHTower/MobiusThetaNativeMeyerAdmission.lean (237).
- formal/GaloisForLFunctions/RHTower/MobiusThetaNativePrefixMass.lean (183).
Wired RHTower.lean 6276–6277. Existing higher umbrella chain retained; no umbrella build.

C64 exact h_(k,m)(t)=exp(-mt/2)(-i(-mt))^k Phi(-mt), m positive native depth.

Admission leaf:
- exp_mul_abs_thetaCuspPolynomialAtom_le_at_rate (34): for x≥0,n>0,A≤N+1, bound exp(Ax)|atom(P,n,x)| by existing Gaussian constant for X^N P times exp(-π n²/2). Key exp(x)≤n exp(x).
- thetaCuspFullSource_derivative_exp_bound_pos (64), whole-line (94): choose monomial N>A, sum already admitted derivative atoms, use exact derivative reflection.
- thetaCuspSchwartz_mem_deningerExpSchwartz (106) CLOSED actual theta all-rate/all-order membership. Complexification uses iteratedDeriv_smul_const; no heavy SchwartzMap.iteratedDeriv_ofReal import.
- deningerExpSchwartz_smulLeftCLM_mem (123): temperate multiplier closure from HasTemperateGrowth.norm_iteratedFDeriv_le_uniform, norm_iteratedFDeriv_mul_le, (1+|x|)^K≤exp(K|x|).
- thetaCuspHalfTilt_mem_deningerExpSchwartz (171).
- mobiusThetaNativeCollarSource_mem_deningerExpSchwartz (185), actual k,m no source premise. Uses existing deningerExpMul and schwartzDilate_mem_deningerExpSchwartz on unchanged native source.
- mobiusThetaNativeMeyerSource (199), exact toSource theorem (203).
- summable_norm_mobiusThetaInternalJetRawHeadSource_all_depths (208).
- mobiusThetaNativeCollarSource_preimage_at_anchor_all_depths (222).
These remove m≥3 only from POINTWISE admission/reconstruction. Do NOT enlarge prior Fourier–Laplace/Dirichlet-series convergence chambers.

Prefix leaf:
- actual radial tail A_(k,p,m)(y)=Σ_j μ(p+j) h(log((p+j)|y|)) (def27).
- at_log_coordinate (31): A(exp(-x/m))=exp(x/2)*RawResidual(k,p,m,x), exactly C64 original source.
- integrable (71): a.e. original even preimage minus finite prefix; n0 μ0=0, keep every positive prefix term.
- integral_eq_prefix_mass (115): ∫ℝ A = -2*(Σ_{n<p} μ(n)/n)*PullMass(h).
- massParameter (133): v_m=i(1/2-1/m).
- source_pullMass (137): PullMass(h)=Xi^(k)(v_m)/m. Exponential change of variables to whole-log line; C64 native Mellin point m*s(v_m)=1, |Im v_m|<1 proved for every m>0. Native Jacobian retained.
- fourier_zero (173): F(A)(0)=-(2/m)(Σ_{n<p} μ(n)/n)Xi^(k)(v_m).
No assertion of nonvanishing for arbitrary k,p,m. All-integer zero mass cannot simply be transferred across original prime cutoff. Exact source-derived prefix mass is positive salvage, not arbitrary counterterm.

## Hard remaining operation / next attack
Original second collar J h(t)=(-1)^k exp((m-1)t)h(t). Its radial inverse carries BOTH n^(m-1) and |y|^(m-1); cannot keep only arithmetic weight. Next reconstruct full original second radial collar, then compare the complete Fourier boundary plus finite prefix with existing Gamma transgression. Exact horizontal mass alone does not cancel fixed Gamma/BV reader at a selected Xi zero. Existing fixed-reader equality iff boundary zero is only equivalence, not producer.
Analytic thought, not coded: M_(Jh)(1)=M_h(0)=Xi^(k)(i/2)/m by reflection; first mass reads Xi^(k)(v_m)/m. Do not confuse these points or original selected zero rho.
L1 radial representation does not itself identify all boundary/contact terms with fixed BV source.

## Verification / processes
Scratch base /tmp/MobiusThetaNativeMeyerAdmission.lean exit0 no warnings after last additions (49601).
Tree narrower imports (SecondaryCollarDefect, MeyerTopology instead of AdiabaticTransgression) passed needed olean with lake env lean (35605).
Prefix scratch /tmp/MobiusThetaNativePrefixMass.lean exit0 no warnings (22951); tree exact proof plus header.
Final lake build GaloisForLFunctions.RHTower.MobiusThetaNativePrefixMass exit0 (50842): new admission44sec, prefix34sec;12350 jobs dependency replay. Log /tmp/route-l-native-prefix-mass-build.log.
Global scripts/formal_tools.py lint exit1 (84443), sole error untracked concurrent foreign ThetaCuspHawkingBMNonstationaryMomentAlgebra not wired. Read its distinct nonstationary-moment header, did not modify. Log /tmp/route-l-native-prefix-mass-lint.log. Own new leaves wired/no lint errors. Tracked umbrella/map diff --check passed.
NO owned Lean/build/search process remains. No heartbeat/recursion raises, numerical experiments, extra premises, full/umbrella build, commits or pushes. No #print axioms calls.

## Research/docs
Card docs/drafts/pipeline/1-in-progress/route-l-native-fourier-collar.md RH-L-C65 updated with paper proof, checked status, searches/literature and exact residual obstacle.
Map comparison scope line872 appended C65 results. Universal-law-field/STATUS unchanged: new facts route-specific.
Four deep whole-corpus search artifacts all audited 20 candidates+20 method statements/assumptions each (80+80), all proposed groups:
native-fourier-collar-admission gen881197 snap881205:57114files47483Lean735926decl; pending44643.
meyer-polynomial-scale-method gen881205 snap881207:57115/47483/735926 pending44643.
coordinate-meyer-closure gen881228 snap881241 current881242:57116/47484/735935 pending44644.
native-prefix-mass-method gen881339 snap/current881354:57119/47487/735963 pending44647.
All partial/source-only; complete inventory not compiled correctness. All zero proof ideas/one unverified group. First ordinary Schwartz vs strong-log definition mismatch; second Gaussian carrier not theta; third weighted algebra not exponential closure; fourth Poisson theorem assumes actual cap membership. Existing dilation/zero-mass lemmas verified applicable after new admission.

Broad recent arxiv intertwining newest-first search. Hou–Popescu2609.10483v1Sep9 read entire theorem proofs/chamber checks: actual normalized induced rep and invariant period required, opposite real characters can pair, no forced center. Referenced period theorems not independently verified/imported.
Karlin2609.09548v1Sep8 section4.2+AppendixB read: normalized Laguerre common-core intertwiner, actual self-adjoint spectral domain; similarity does not provide Gamma/BV equality. No paper result added as premise.

## Useful verified APIs / avoid repeat errors
- deningerMobiusRay_summable hh hx and its norm; summable_mul_left_iff to cancel nonzero exp(x/2), summable_nat_add_iff to shift original prefix.
- deningerEvenPreimage_integral_zero, deningerEvenPreimage_integrable, deningerLogPull_dilation_integral, deningerAdiabaticEvenLogPullDilation_integrable.
- To get x≠0 from deningerCompl_zero_ae_univ, type intermediate hxmem : x∈({0}ᶜ:Set ℝ) := hx.mpr(Set.mem_univ x); then simpa using hxmem.
- change of variable exact proof pattern: rw [deningerPullMass,←Real.range_exp,←Set.image_univ,integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ (fun x _ =>(Real.hasDerivAt_exp x).hasDerivWithinAt) Real.exp_injective.injOn,setIntegral_univ].
- Fourier at zero needs both mul_zero and zero_mul in simp.
- ThetaCarrierHassePacket.lean371 XiC_imaginary_pos {a:ℝ}(ha:|a|≤1):0<(XiC(I*(a:ℂ))).re; source read C65 but not imported/used. No all-jet positivity or all-prefix nonzero theorem found by bounded rg; do not claim corpus absence.
- Restrict rg to -g '*.lean' to avoid huge .ilean data. Filter JSON fields, not entire records. Use rg before unknown filenames. No assumptions from names alone.
