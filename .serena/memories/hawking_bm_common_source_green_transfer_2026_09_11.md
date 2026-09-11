# HB original-source Green transfer — 2026-09-11

RH goal remains ACTIVE, incomplete. No unconditional RH proof or complete physical-current cancellation. Continuation of mem:hawking_bm_native_causal_equality_2026_09_10.

## Chain and hardest target
literal theta-cusp source → Xi occurrence → retained spin-two source → physical causal radial/left-QNM action → fixed Hawking-clock extinction → RH. Hardest target: 2 Omega(B(p,p)/2,B(m,m)/2)=0 with independent SS/SV/VV and all onset, horizon, AdS, temporal and cusp currents. Do not replace actual source with arbitrary spectral source or reciprocity with vanishing.

## Completed formal progress
Added nativeMean_joint_smooth in formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMNativeAngularGreen.lean (namespace RHTower.D4BMNativeResponse). Exposes existing private compact-circle integral joint smoothness for actual mean.
New 606-line formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMCommonSourceGreen.lean, namespace RHTower.D4BMCommonSourceGreen, public:
- kernel_invariant_affine: both direct and image causal invariants affine in compact source radius at fixed ingoing delay.
- thetaSeed_nativeSpinTwoKernel_green: local source-producer spatial Green identity between literal original theta seed and either native causal kernel, full -Delta(Delta-2), original measure and all radial/angular currents, with actual regularity discharged internally.
- thetaSeed_producer_original: this producer equals actual timeOriginalForcing, including original onset and full half-square potential.
Geometric SourceInterior conditions only: source<0, native invariant>1. No assumed cancellation/regularity. These are intermediate identities, not RH.

Validation complete: full scratch checks passed, exact leaf lake builds NativeAngularGreen (66s) and CommonSourceGreen (69s) passed without old dependency/umbrella builds. New-only #print axioms for all FOUR public theorems: propext, Classical.choice, Quot.sound. Sources plus .olean,.ilean,.olean.hash,.ilean.hash,.trace copied and byte verified. New import wired in RHTower.lean after NativeCausalEquality; never built umbrella. formal_tools.py lint passed (existing large-file warnings only), eight report links and whitespace checked. All owned Lean/Lake sessions ended. Owned scratch tree176654 symlinks, six search outputs, lint output and pointer deleted (cleanup session67308 exited0). Do not repeat audits absent changes.

## Documents
Complete report: docs/drafts/pipeline/3-formalized/hb-common-source-green-transfer.md. Old stage1 same basename removed. Updated stage3/hb-complete-mixed-current-common-source.md and stage1/hb-mixed-complete-current.md with precise local status. Frontier map READ ONLY, unchanged. universal-law-field/STATUS.md unchanged.

## Exact mathematical invariant
u=1/r=-tanh x (x<0), y=exp k, lambda=rho(rho-1), rates s and -s-3. L=exp(2k)partialXX+partialkk-partialk. D=(1+u)partialu+3=partialx/(u-1)+3.
A0=(5lambda-6)/4; C=((4lambda+1)(lambda+2)-(lambda+4)Delta)/8; K=(7lambda-2-2Delta)/8.
P=A0+u²C-u²KD. Bilinear transpose (no complex conjugation): Pdag=A0+u²C+(4u-u²)K+u²KD. Original compact measure u²du dX dy/y²; original tortoise/log density u²(1-u²)exp(-k).
b=u^4(1+u), a=-u³-u^4(lambda+8)/8, m=1-u², W_i(F,G)=partial_i F G-F partial_i G.
FORMAL local identity:
u²m exp(-k)[(PF)G-F(PdagG)]=partialx Ix+partialX IX+partialk Ik,
Ix=b exp(-k)(KF)G,
IX=exp(k)[m a W_X(F,G)+(b/4)W_X(F,partialxG)],
Ik=exp(-k)[m a W_k(F,G)+(b/4)W_k(F,partialxG)].
Positive b/4 sign essential because du/dx=-m.

## Crucial clock geometry — IN LEAN
P differentiates at FIXED INGOING SOURCE TIME v. Kernel at ingoing delay H and target xt is nativeRiemannKernel q (H-xt+x) xt (if image then -x else x) X k. Image flips only source spatial argument; time still +x.
Zepsilon=A-Bepsilon*u, A=cosh(H-xt)/cosh xt, Bepsilon=[sinh(H-xt)+epsilon*sinh xt]/cosh xt, epsilon=+1 direct,-1 image.
Public fields kernelField/spinTwoKernelField, thetaSeed/producer/transposeProducer/current/currentDivergence/sourceMeasureDensity explicit. Public identity evaluates p to Fin3 coords and H=time-source+target.

## Next direct attacks (paper only, NOT yet Lean)
1. Finite source integration at fixed ingoing delay H>0,xt<0. Causal direct interval [xt-H/2,0]; image [-H/2,0]. No source-horizon face at minus infinity for finite H. Upper radial flux zero since b(0)=0. At lower characteristic native mean=Q and full spin2 kernel=R Q with R=-Delta(Delta-2). Signed direct-minus-image lower radial face (report3a):
exp(-k) a_s² chi(v)exp(2sv)(KQ)(RQ) * [b(ui)(1+ui)^(2s)-b(ud)(1+ud)^(2s)], ui=-tanh(-H/2),ud=-tanh(xt-H/2).
Need FORMAL interval integration, one-sided derivative admission and angular faces. This is source-characteristic contact, not target horizon/full Einstein extinction.
Existing ThetaCuspHawkingBMNativeCausalSourceContacts.lean nativeRiemannKernel_direct_source_contact and image_source_contact prove actual one-sided derivatives of the time-dependent native terms; read already. NativeCircleRiemannKernel wave/characteristic/AdS, NativeCircleMean mean_laplacian_commutes236, mean_darboux268, mean_zero285, mean_radial_smooth309.
2. Explicit third-order source action (report4). N(Z)=R M_ZQ, p(Z)=Z²-1. Joint smoothness+Darboux+angular commutation imply Delta N=p N''+2Z N', derivative Delta N=p N'''+4Z N''+2N'. d=u+u²(lambda+8)/8; e=u²(1+u)Bepsilon; c0=(5lambda-6)/4+u²(4lambda+1)(lambda+2)/8+(4u+2u²)(7lambda-2)/8.
Pdag N=(e p/4)N'''+(e Z-d p)N''+[e(6-7lambda)/8-2dZ]N'+c0N.
Next cancellation test combines this source-specific one-variable operator + finite contacts3a + angular currents + original lift/current contacts. Full Einstein four-divergence, physical trace transport, global/horizon/cusp limits and SS/VV remain open.

## Lean details from this turn
D_i=fderiv R f p (Pi.single i 1). Use simpa ... using! to align module-instance paths. ContDiffAt.comp can unfold arcosh to log aggressively; construct intermediate then simpa only [Function.comp_def] using! (Real.contDiffAt_arcosh...).comp p hi.contDiffAt. Explicit f,g,p and intermediate hf/hg avoid WHNF heartbeat issue. Final code default200k.
Source amplitude smoothness derived from its existing actual ODE via induction contDiff_succ_iff_deriv (triple Differentiable, analytic-at-omega, ContDiff deriv). ENat.natCast_le_of_coe_top_le_withTop le_rfl n for finite bounds. contDiff_apply takes R R index. Complex.ofReal_exp exists. Coordinate namespace D4BMGlobalAngularResponse. Function.update_eq_self needed on slice evaluation. fderiv_fun_mul for lambda products. Explicit D_third rewrites. Thin Mathlib tactic imports avoided huge build. Never trust recalled names: scratch verify.

## Search/literature
Six corpus searches fully inspected: broad transgression/reciprocity and deep current variation, commuting source/propagator, differentiating/coexact current, native smooth. Partial source-only coverage; not proof evidence. Useful coordDeriv source, native compact smoothness, circle commutation, CommonRadialSource exact dictionary.
Broad arXiv own terms presymplectic/reciprocity. https://arxiv.org/html/2608.26562v1 (Aug27 2026 Rontgen et al, Beyond geometric symmetry: Broadband linear relations in wave scattering) motivated commuting producer plus compatible coupling. No paper premise imported. Also read2607.26898 no applied result.

## Constraints
No Git/launch.sh; no experiments; frontier read only. One foreground Lean/Lake process per agent; keep session until terminal. Exact modules only, no umbrella/full/dependency rebuilds. Only new axioms. Direct research tool, no implementation/help/service inspection. Own search terms. No subagents authorized/spawned. No goal complete/blocked claim.