# HB native radial endpoint — 2026-09-10

RH goal ACTIVE. This turn made verified progress; do NOT mark goal complete. Full native joint form-domain admission, complete native/physical inverse identification and full physical-current cancellation remain UNPROVED.

## Mandatory working rules
Start each goal turn with full chain, hardest obstacle, last verified progress and next direct attack:
literal theta-cusp source → Xi occurrence → retained spin-two source → physical causal radial/left-QNM action → fixed Hawking-clock extinction → RH.
Ultimate target is complete physical-current cancellation 2 Ω(B(p,p)/2,B(m,m)/2)=0 with independent SS/SV/VV amplitudes and every onset/horizon/AdS/temporal/cusp current.
NO Git commands, launch.sh, numerical computations, full/umbrella builds, or frontier-map edits. Frontier map READ ONLY. One owned foreground Lean/Lake at a time; observe actual terminal exit_code before another. Scratch: lake env lean <file>. Final: lake build <exact module>. Check axioms only NEW public theorems. Do not re-audit these installed results. No subagents were authorized/spawned.
Use corpus research CLI (broad/single terms plus deep mechanism queries), inspect candidate_lemmas, source_arguments/methods, proof_ideas, ingredient_sets and partial/coverage/freshness. No search implementation/help/launcher inspection. Own arXiv terms, examples are not prescribed.

## Newly installed and audited
formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMNativeJointEnergy.lean now 1223 lines. Existing global native energy result remains at 795/871; do not reprove it.
New actual angular energy family nativeTimePrimitiveAngularEnergy at1051: cusp-cutoff CoreField frameGraph element of ORIGINAL D4BMModularCore.energyDomain.
Five new public theorems:
- nativeTimePrimitiveAngularEnergy_continuous1057: actual radial family C⁰ in angular energy norm.
- nativeTimePrimitiveAngularEnergy_boundary1087: whole energy-family value at0 is0, via original embedding injectivity.
- nativeTimePrimitiveAngularEnergy_compact1094: compact radial support from literal finite propagation.
- nativeTimePrimitiveAngularEnergy_value_hasDerivAt1188: after ORIGINAL angular value embedding J, actual derivative is nativeTimePrimitiveAngularRadial1175 (L² class of eta_n times literal W_x).
- nativeTimePrimitiveAngularEnergy_value_contDiff1211: JH is C¹ in ORIGINAL angular L² space.
No mixed angular derivative of W_x was used or assumed.

New formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMNativeRadialEndpoint.lean261 lines:
nativeDirichletCutoff m x = 1-scaledCuspCutoff (1/((m:ℝ)+1)) (-x).
Six new public theorems:
- nativeDirichletCutoff_profile27: smooth∞, 0≤beta≤1, beta0 for x≥-2epsilon, beta1 for x≤-3epsilon.
- nativeDirichletCutoff_weighted_derivative_bound56: exists C≥0, allm x |x*deriv beta_m x|≤C.
- nativeDirichletCutoff_eventually_one71: at each x<0 beta_m eventually has whole constant-one germ.
- nativeTimePrimitiveAngularEnergy_endpoint_error_tendsto_zero85: allm Integrable ||beta'_m JH||² in original radialMeasure and integral→0.
- nativeTimePrimitiveAngularEnergy_endpoint_value_convergence180: allm Integrable ||beta_m H-H||² in angular energy norm, radial integral→0.
- nativeTimePrimitiveAngularEnergy_endpoint_radial_convergence222: allm Integrable ||deriv(beta_m JH)-nativeTimePrimitiveAngularRadial||², radial integral→0.
The three native convergence results hold for every q,s,amplitude,t,n without frequency chamber, native-domain or energy assumptions.

Proof: compact C¹ JH gives derivative boundD≥0. JH0=0 gives ||JH(x)||≤D|x| by vector mean value. Existing scaledCuspCutoff_derivative_bounds gives |x beta'_m|≤C, so ||beta'_m JH||≤DC. On radial half-line it is zero below-3 uniformlym and eventually zero at each negative x; DCT with indicator[-3,0](DC)². Main beta differences dominated by ||H||² and ||(JH)'||². Exact product rule plus norm-square triangle bound proves full radial derivative convergence.

## Validation and cleanup COMPLETE
Family full scratch passed. Exact family leaf build:2jobs,18s. Five NEW theorem axiom checks only: propext,Classical.choice,Quot.sound.
Endpoint iterated in full scratch; final single chain-rule correction passed focused scratch using actual CuspCutoffProfile. COMPLETE exact endpoint leaf build:2jobs,127s. Six NEW theorem axiom checks only: same three foundations, no sorryAx.
Isolated audit reused4135 cached local modules and11cached packages. No dependency/umbrella build. Both audited sources +five artifacts each installed byte-identically with source guards.
RHTower.lean endpoint import added adjacent existing NativeJointEnergy, latest observed17103. No umbrella build.
scripts/formal_tools.py lint PASSED, existing large-file warnings only.
All process handles terminal, no owned Lean/Lake remains.
REMOVED /tmp/hb-native-admission.PXFiWgMj and all8 hb-native-admission-* search JSONs. Do not try to resume old sessions or access removed root.
Frontier map and universal STATUS unchanged. No numerical experiments.

## Next direct proof — radial convolution then ORIGINAL graph admission
Active construction card: docs/drafts/pipeline/1-in-progress/hb-native-radial-form-admission.md.
Audited report: docs/drafts/pipeline/3-formalized/hb-native-radial-form-approximation.md.
Inverse card hb-native-cusp-inverse-identification.md step5 updated; global energy report now points to current family/endpoint work.

For fixed cusp indexn and endpoint indexm:
1. Let H_m=beta_m H_n. It is C⁰_c in angular energyE, JH_m C¹_c in original angularL² F, support≤-2epsilon_m.
2. Convolve in E with normalized bump width delta_k=epsilon_m/(k+2). delta<epsilon, support convolution≤-epsilon, hence strictly original Iio0. Smooth∞ in E by compact smooth kernel convolution.
3. ORIGINAL J commutes Bochner integral. Classical convolution derivative AFTER J gives kappa_delta*(JH_m)' in F. Do not demand E-valued derivative convergence (would add mixed-derivative requirements).
4. Shrinking normalized-bump pointwise convergence for H_m(E) and (JH_m)'(F). Uniform norm bounds and a common enlarged compact radial support give squared-integral convergence in those spaces.
5. Assemble four ORIGINAL joint graph slots: value, radial derivative, sech-weighted angular derivatives1,2. Existing RadialEnergyFamily.graph_mem admits each smooth approximant. Closedness admits fixed m,n graph.
6. Endpoint limit (now audited) admits fixedn cusp graph.
7. Cusp n→∞ uses audited GLOBAL native gradient energy for (eta_n-1)gradW and NativeAngularLocalization cutoff-error→0 for Wgradeta_n. Closedness admits complete actual native graph.
These are THREE successive closed-set limits; no diagonal/uniform rate acrossindices needed. No separate angular smoothing: each actual cusp cutoff already CoreField.
8. Extend compact Green identity in first-derivative graph. For original joint embedding Jjoint derive W_graph=Jjoint.adjoint(W+G), hence W=JjointJjoint.adjoint(W+G).
9. Native/physical difference obeys B u+(I-B)W=0 with B=JjointJjoint.adjoint. Bounded conserved energy yields inverse equality. Full physical-current cancellation still separate.

Critical source:
JointRadialFamilyLift: angularEnergySlot i:E→LℂF; radialFamilySlot i = bochnerL2ProductEquiv ∘ (angularEnergySlot i).compLpL. familyPacketLift_apply is WithLp.toLp2[value slot0, radial slot0, weighted slot1, weighted slot2]. Only original F projection of radial derivative enters graph; avoid convergence of whole FamilyPacketSpace.
JointRadialFamilyData: RadialEnergyFamily has fieldℝ→E,smooth∞,compact,tsupport⊆Iio0.
JointRadialFamilyAdmission63: RadialEnergyFamily.graph_mem via finite Hilbert projections and closed jointDomain.

## Source/API findings already read
HTGeometry/L2DominatedContinuity continuous_toLp_two_of_dominated; L2DominatedDerivative hasDerivAt_toLp_two_of_dominated; L2PairingEnergy norm_l2_sq_eq_integral_norm_sq (generic normed E).
BumpMollifierFamily: widthBump hε(rInε/2,rOutε), bumpMollifier=(widthBump hε).normed volume, nonneg, integral1, continuous,compact. (widthBump hε).contDiff_normed gives smooth∞.
Mathlib Analysis/Calculus/ContDiff/Convolution:
HasCompactSupport.contDiff_convolution_left L hcf hf∞ hgLoc.
HasCompactSupport.hasDerivAt_convolution_right L hfLoc hcg hgC1 x.
Mathlib Analysis/Calculus/BumpFunction/Convolution98:
ContDiffBump.convolution_tendsto_right_of_continuous hφrOut→0 hgContinuous x.
Mathlib Analysis/Convolution529: HasCompactSupport.convolution hcf hcg.
631: support_convolution_subset L.
770: dist_convolution_le hε≥0 hsupport hnonneg hint1 hmg hgBound, generic E; with z0=0 gives uniform norm bound.
327: HasCompactSupport.convolutionExists_left_of_continuous_right L hcf hfLoc hgContinuous.
Bochner/ContinuousLinearMap69: L.integral_comp_comm hi; restrictScalars ℝ available for original complex J. Need exact integrability of kernel-smul integrand.
SuzukiHlogMollifiedFormCore support proof pattern: support_convolution_subset, compact sum, closure_minimal; do not import its form-aperture hypotheses.
YoungConvolutionL2 generic lintegral_enorm_sq_le_of_convolution_bound found in broad convolution source-method search, not used yet. WignerSmithFiniteResolutionLawEscape202 has scalar compact-averaging derivative via IBP, alternative pattern; generic classical derivative sufficient.

API pitfalls verified:
PiLp.continuous_toLp, notWithLp.continuous_toLp.
memLp_indicator_const p hs c (c=0 OR μs≠∞).
IntegrableOn.integrable_indicator makes global Integrable indicator; .indicator instead retains IntegrableOn and is WRONG here.
HasCompactSupport.exists_bound_of_continuous, .comp_left (map_zero J), .deriv verified.
memLp_two_iff_integrable_sq_norm, squeeze_zero, HasDerivAt.smul verified.
HasDerivAt.smul output order is c(x) • f' + c' • f(x).
Function-valued sub/smul and lambda forms do NOT rewrite automatically in this toolchain. In endpoint cutoff proof h has function ((fun_=>1)-scaledCuspCutoff ε ∘ Neg.neg), not lambda. Explicit function equality to lambda by funext;rfl, rw that in h, then h.deriv works. For smul likewise nativeDirichletCutoff m • f = funx=>beta_mx • fx; rewrite h before its derivative. Use abel for swapped add order. This last correction passed scratch and final audit.
For L² continuity of huge native formulas, first construct explicit typed Continuous map z↦(x,z), compose, dsimp Function.comp_def, then change expected function. Direct expected-type comp can hit200k whnf timeout.
Avoid norm absolute syntax |* without a space.
No not_mem_Icc.mp; split on lower bound.
New theorem axioms now AUDITED; do not check them again.

## Search and literature
Eight own broad/deep research requests inspected; partial/pending/stale compiler/source metadata and some runtime deadlines. No ingredient groups accepted as proof. Broad convolution found genuine source arguments and generic Young bound. JSON method may be null: use (method or{}).
Newest-first own arXiv term Mosco: Stange25Aug2026 https://arxiv.org/html/2608.24647v1, Sections4.1–4.2 bulk-surface evolution, recovery sequences and subdifferential graphs. No paper result is Lean premise.
