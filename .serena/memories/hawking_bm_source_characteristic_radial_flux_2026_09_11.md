# HB original-source radial characteristic transfer — verified 2026-09-11

RH goal remains ACTIVE and incomplete. Full physical-current cancellation and RH are NOT proved. This turn made verified progress, not a blocked/no-progress turn. Continue mem:hawking_bm_common_source_green_transfer_2026_09_11; earlier causal time-class equality is in mem:hawking_bm_native_causal_equality_2026_09_10.

## Chain and hard target
literal theta-cusp source → Xi occurrence → retained spin-two source → physical causal radial/left-QNM action → fixed Hawking-clock extinction → RH.
Hardest target remains 2 Omega(B(p,p)/2,B(m,m)/2)=0 with independent SS/SV/VV and all onset, horizon, AdS, temporal and cusp currents. This turn closes the original source's radial characteristic transfer and fixed-source-time cancellation of that signed face. It does NOT close the full Einstein action pairing.

## Installed, audited result
Extended formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMCommonSourceGreen.lean to 1184 lines. Original 606-line source prefix unchanged (byte checked). Existing umbrella import verified, unchanged; no umbrella build.
Nine NEW public theorems in RHTower.D4BMCommonSourceGreen:
- nativeSpinTwoTrace_eq_interior, line659
- nativeSpinTwoTrace_characteristic,758
- sourceCharacteristic_causal_interval,838
- sourceRadialTraceCurrent_signed_faces,855
- sourceRadialCurrent_characteristic_limit,884
- sourceRadialTransfer_integral,1016
- sourceRadialTransfer_characteristic_integral,1054
- sourceRadialTransfer_signed_characteristic_integral,1093
- sourceRadialTraceCurrent_signed_faces_tendsto_zero,1164

New public definitions: nativeSpinTwoTrace (freeze source radius before angular differentiation), thetaSpinTwo, sourceCharacteristic (image? -h/2 : target-h/2), thetaAngularCoupling, sourceRadialTraceCurrent (actual Green current's radial component using continuous angular trace), sourceCharacteristicWeight, radialTransferDensity.

## Exact mathematics now in Lean
u(y)=-tanh y, b(u)=u^4(1+u), lambda=scalarParameter q, s=physicalRate q branch. Original producer P and bilinear transpose Pdagger from previous memory retained unchanged; original density mu=u²(1-u²)exp(-k); full angular weight R=-Delta(Delta-2).
At fixed ingoing delay H and target x, direct kernel uses invariant(H-x+y,x,y), image invariant(H-x+y,x,-y). For H>0,x<0 the exact original source intervals are [x-H/2,0] and [-H/2,0]. Their characteristic invariants equal1.
K=(7lambda-2-2Delta)/8; Q=actual fullSquarePotential. Angular coupling is (KQ)(RQ), implemented thetaAngularCoupling q X k with actual scalarLaplacian and angular-log coordinate R, no eigenvalue replacement.
W_s(y)=b(u(y))*power(2s)(1+u(y)) (implementation b*sourceAmplitude s 0 1 1).
C_s(v,X,k)=exp(-k)*a²*timeOnset(2s)(v)*(KQ)(RQ).
Actual radial trace at either source characteristic e equals C_s W_s(e); upper face y=0 is0.
Signed direct-minus-image face exactly C_s*[W_s(-H/2)-W_s(x-H/2)].

Define D(y)=mu[(PF)G-F(Pdagger G)]-partial_X I_X-partial_k I_k for actual thetaSeed F and full spinTwoKernelField G. Both angular divergences stay INSIDE this combined integrand.
For every cut in (e,0), Lean proves integral_cut^0 D(y)dy = -sourceRadialTraceCurrent(cut).
The original smooth-interior radial current has its derived characteristic limit. Hence the truncated integrals have a proved improper limit as cut→e+, equal -C_s W_s(e), without any assumed endpoint integrability. The direct-minus-image integrals with cuts x-H/2+d and -H/2+d converge as d→0+ to C_s[W_s(-H/2)-W_s(x-H/2)]. These are actual source/transpose integrals, not an abstract boundary assignment.
Finally W_s(y)→2*power(2s)(2) as y→-infinity. Both characteristic locations tend to minus infinity as H→+infinity. Their signed radial face therefore tends to0 at FIXED original source time, target radius, angular point and amplitude. This does not assert uniform domination, a source-time integrated result, target horizon limit, or full physical extinction.

## Correct characteristic trace mechanism
The old Green field uses full Frechet derivatives on the smooth cone interior. Do not evaluate these across the characteristic without admission. New sourceSlice freezes the source radius before taking angular derivatives. D_sourceSlice and L_sourceSlice prove agreement on interior; both angular Laplacians retained.
The slice trace equals a globally smooth circleSpinTwo evaluated at (arcosh Z,X,k). Near Z=1, arcosh is continuous, so this gives the required actual interior-current limit. Real.arcosh here is log(x+sqrt(x²-1)); there is NO globally continuous_arcosh theorem. Prove local continuity where Z>0 with log/sqrt and positivity (characteristic Z=1). No fictitious transverse differentiability is used.

## Validation / no repeat needed
Scratch checks passed (temporary Prelude exposed private helpers only to speed iteration; that temporary public variant was NEVER installed). Complete final module built with lake build GaloisForLFunctions.RHTower.ThetaCuspHawkingBMCommonSourceGreen in15s,3jobs, no Lean warnings. Exactly this leaf compiled; 4133 existing own-corpus dependency modules and 12 package caches frozen. All nine NEW-only #print axioms reports are exactly [propext,Classical.choice,Quot.sound]. No old theorem axioms audited. Source and five artifacts .olean,.ilean,.olean.hash,.ilean.hash,.trace installed and byte verified.
formal_tools.py index refreshed API/GAPS/OVERVIEW and indexed1 changed file. Whole-corpus formal_tools.py lint passed, existing large-file warnings only. Eleven local report links and scoped whitespace passed.
All owned Lean/Lake sessions terminal. Owned /tmp/hb-source-characteristic-0911 (including20518 frozen links), six search JSONs, and lint output deleted; cleanup session24910 exited0. Do not kill other tasks' processes.

## Documentation
Moved new report to docs/drafts/pipeline/3-formalized/hb-source-characteristic-radial-flux.md; old stage1 same basename removed. Updated stage3/hb-common-source-green-transfer.md and stage1/hb-mixed-complete-current.md with precise current status. Frontier map READ ONLY, unchanged by this task. universal-law-field/STATUS.md unchanged (results route-specific).

## Next direct attack
The radial signed face now has a proved value and fixed-v decay. Next candidate: integrate this actual face in original source time by proving uniform boundedness of W_s on u∈[0,1], then use original onset L1 admission and dominated convolution convergence. Existing verified source signature in ThetaCuspHawkingBMJointSourceOnsetLaplace.lean:29:
timeOnset_integrable (v w:C) (hw:v.re<w.re): IntegrableOn (fun u:R=>Complex.exp(-w*(u:C))*timeOnset v u) (Ioi0).
With w=0 and actual negative source rates this is the relevant source-time input; rate negativity and exact original time-domain matching must be checked in Lean. Time-convolution cancellation is NOT yet proved.
Still open: angular integration retaining cusp/seam currents, differentiated full Einstein four-divergence, physical Green/current trace transport, full source-contact/lift assembly, target horizon/cusp/time limits and independent SS/VV. Previous report's explicit third-order Pdagger N expression remains analytical and is another direct kernel-action attack. Do not substitute the solved radial face for complete pairing.

## Lean efficiency lessons
- Wrong equality direction caused enormous WHNF expansion of native trace versus kernel (arcosh/log/theta source). Diagnose and use explicit congrArg on scalar values, rather than rw searching through huge fields. radialTrace_eq helper closes this. Tendsto.congr' requires old function = new function; improper limit uses radialTrace_eq.symm under Neg.neg.
- ContinuousAt.comp uses (f := inner curve), not (g := inner curve). Explicit sourceCurve_smooth and using! fix instance-path/eta mismatch; include id_eq when needed.
- Fin.succ0 vector evaluations need Matrix.cons_val_succ, not cons_val_one. Numeric complex1+1 sometimes needs norm_num at the intermediate limit.
- Final proofs use default200000 heartbeats; temporary increases were removed after fixing equality orientation.
- Efficient final audit: enumerate own import closure from source (4134 including target), symlink only its cached artifacts; 12 path-only stub dependency packages with existing caches, ClassFieldTheory default/lib/lean fallback. Main Galois lean_lib roots=[] globs=[]; target leaf lean_lib MUST have globs=[exact module]. roots=[module] with globs=[] yields an empty library success, no artifact: do not count it. Corrected exact-glob build actually compiled module15s; target artifact existence and bytes explicitly checked. No Git commands or launcher invoked.

## Search and constraints
Used own broad corpus terms bispectral/concomitant; deep source-kernel intertwining and kernel-moment mechanisms; OR angular-slice and radial-limit searches. All six results inspected incl candidates/source arguments, methods, proof ideas, ingredient sets, coverage/freshness. Partial coverage with311–317 pending source files, largely source-only compiler metadata. Proposed ingredient groups requiring vanishing were NOT adopted. Useful sources: NativeCircleMean slice calculus, NativeAngularGreen compact joint smoothness, native characteristic theorem, JointSourceHorizonFactor.radialUnit_one_sub.
Broad arXiv own terms bispectral/intertwining (preferred2026 dates yielded no useful newer hit); verified1306.0857 revisedJune2025 and re-opened prior2608.26562v1. No external theorem used as premise.
No numerical experiments, no Runpod jobs, no Git/launch.sh, no subagents. One foreground Lean/Lake process at a time, no full/umbrella builds. Keep RH goal active; do not mark complete or blocked.