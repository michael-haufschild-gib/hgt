# HB spin-two double primitive and full-source clock transfer, 2026-09-10

RH and complete extinction UNPROVED; active goal. This turn made actual progress: new analytical full-source representation removes explicit source-delay characteristic boundary terms, with diagonal control and retained terminal Wronskian; five scalar-kernel identities formally proved. Frontier map READ ONLY, no Git/launch.sh/computations/subagents. No route-independent STATUS addition: result is HB-specific.

Chain: literal theta-cusp source → Xi occurrence → retained spin-two source → physical causal radial/left-QNM action → fixed Hawking-clock extinction → RH. Hard target 2 Ω(B(p,p)/2,B(m,m)/2)=0 with independent SS/SV/VV amplitudes and all physical boundaries.

## New direct mathematical attack
Card docs/drafts/pipeline/1-in-progress/hb-spin-two-kernel-transfer.md contains complete analytical derivation, not a formal extinction claim. Source current comparison remains open. Use this representation to test actual cancellation rather than resume five characteristic-period coefficients by default.

M(Z)=native circle mean of full Q; p=Z²−1; Δ remains actual angular operator. Darboux/commutation give
F=p² M''=p ΔM−2Zp M'; F'=p(Δ−2)M'; F''=Δ(Δ−2)M; R M=−F''.
Here primes on M,F are Z-derivatives. F(1)=F'(1)=0. Native right smoothness/commutation supplied analytically by hb-native-circle-green-kernel.md eq4–6 (read this turn); all-orders version not formalized. F=∫1^Z(Z-r)Δ(Δ−2)M(r)dr gives uniform compact O((Z−1)²), F'=O(Z−1).

At fixed inverse radii u,w and same finite INGOING cutoff V, retain exact original reduced source:
s,t=−s−3; α=(2s+1)(2s+2),γ=(2t+1)(2t+2), b=2ks u(3+δu)/(1+u),d=2kt w(3−δw)/(1+w),δ=2s+3.
D_V(h)=∫0^(V−h)e^(−6v)[αχ(v+h)−bχ'(v+h)][γχ(v)−dχ'(v)]dv; W=e^(2sh)D_V, χ=Real.smoothTransition.
W is smooth and W(V)=W'(V)=0 from actual earlier factor at zero. No onset or terminal factor removed on transition interval.

Zε=(1−uw)cosh h+(u−w)sinh h+εuw; A=Z_h; B=Z_hh=Z−εuw; A'=B,B'=A. Lower a+=2max(atanhw−atanhu,0),a−=2atanhw. A>0 on cone interior.
T W=W''/A²−3B W'/A³+(3B²−A²)W/A⁴.
C=−W F_h/A²+(W'/A²−WB/A³)F.
∫ W R M=[C]−∫F T W.

Lower C→0, INCLUDING direct u=w where a=0,k=1−u²,Z=1+k(cosh h−1),A=k sinh h,F=O(h⁴),F_h=O(h³),C=O(h),F T W bounded. Uniform on 0≤u,w≤r<1 from exact A²=d0²+2B0(Z−1)+(Z−1)²≥2(1−r²)(Z−1), B0=1−εuw, d0=|u−w| oru+w. Constants deteriorate at horizon; no horizon limit inferred. Upper C(V)=0 by W,W' actual zeros. Thus ∫a^V e2shD_V R M=−∫a^V F T[e2shD_V]. Empty a≥V intervals zero.
Restore original factor−a_s²a_t²uw fsft/2, outerQ, direct−image, subtract reversed branch: new reduced bulk has positive prefactor times F T W. All angular Green boundaries, physical lift crosscurrents, C contact correcting B=ω+C, temporal physical response face, horizon/cusp/infinite-time limits and SS/VV remain. Source-delay upper boundary zero DOES NOT remove physical terminal current.

## Exact surviving terminal piece (next concrete comparison)
Define g_s(v)=e2sv[αχ(v)−bχ'(v)],g_t analog, c=V−h, I_j=∫0^c g_s^(j)(v+h)g_t(v)dv.
W=I0, W'=I1−g_s(V)g_t(c), W''=I2−g_s'(V)g_t(c)+g_s(V)g_t'(c).
T W=I2/A²−3B I1/A³+(3B²−A²)I0/A⁴
 +[g_s(V)g_t'(c)−g_s'(V)g_t(c)]/A² +3B g_s(V)g_t(c)/A³.
Both terminal Wronskian and geometric product correction remain inside integral. Match these with actual physical response/lift/source-contact currents; do not assign them zero. No cancellation of remaining bulk proved.

## Formal result, DO NOT rebuild or re-audit
formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMSpinTwoKernelPrimitive.lean, namespace RHTower.D4BMSpinTwoKernel, ~100lines. Imports original CausalRiemannKernel and Mathlib FTC. Five publictheorems:
primitive_derivatives23, primitive_eq_weighted_second43, primitive_characteristic50, primitiveFirst_integral55, primitive_volterra72.
For everycomplexν andpositiveZ, ell=ν(ν+1), F=p[ell P−2ZP']; F'=p(ell−2)P'; actualF''=ell(ell−2)P; F=p²P''. Bothjetszeroat1. Twoexactfiniteintegral formulas onZ≥1. No eigenvalue denominator; includesell0,2.
Proof uses actualfirst/secondP jets andODE, thenFTC onF(r)+(Z−r)F'(r). No4thderivativeassumption/computationcertificate. This scalarformal result is not a replacement of full native Q by eigenfunction. Full-native and h-transfer statements remain paper.

Scratch lake env lean passed clean; final exactleaf lake build used frozen2623owncachedmodules+11packagecaches, builtnewleaf80sec3jobs. Only5newaxiomaudits standard[propext,Classical.choice,Quot.sound]. Installedsource/olean/ilean byteidentical. Uniqueumbrellaimport17032, noitsbuild. Globalformal_toolslint PASSED with141existinglargefilewarnings. Lexicalmodulefiltersearchall8decls5publicfound. Report docs/drafts/pipeline/3-formalized/hb-spin-two-kernel-primitive.md. Addedlinkinfiniteclockcard.
One exploratoryscratchprocess interrupted for overly broad dsimp; replacingwith simp only[Pi.pow_apply,id_eq,Complex.ofReal_one]passed. Never use unconstraineddsimp onkerneldefs. AllownedLean/Lake/searchprocesses terminal; scratch/audit cleanup at close.

## Search evidence
Used documentedtool directly, noimplementationinspection. Bispectral search found only existing Casimir scalarcomparison amonguseful exacthits; readBispectralAdjointCasimir (FEblindness vsadjointGram, notnewproducer). ReadProlateCommutationKernel1–175 actualoperatoridentitybeforeSturmboundaryproof. Squared-eigenfunctionOR67resultsmostlySymmetricSquareMatrix, noactualHBsourceintertwiner; deepwavequery methodgroup generic/unverified. Rodrigues/Gegenbauer total0lexical butpartialsemantic returnedShiftedLegendre etc; notabsenceclaim. Flat-onset deepquery identified actual private transition_deriv_zero inCubicArithmeticRectangleSource27: useIsLocalMin.deriv_eq_zero andsmoothTransition.nonneg toproveχ'=0 evenat0. Thismethodwasreadbutnotnewformalleaf. No need reread broad Fokas/Higgs/horizon/Einasto searches from previouspass.