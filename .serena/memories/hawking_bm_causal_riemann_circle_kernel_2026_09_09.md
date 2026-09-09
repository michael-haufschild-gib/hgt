# HB: explicit causal kernel and source-only horizon pairing

Goal remains ACTIVE: RH and physical extinction unproved; no external blocker. Frontier map READ ONLY; concurrent edits there belong to other work. No computations; analytical work plus Lean checks only. No agents. Full chain: literal theta-cusp source → Xi occurrence → retained spin-two source → physical causal radial/left-QNM action → fixed Hawking-clock extinction → RH. Hard target remains complete physical 2 Ω(B(p,p)/2,B(m,m)/2), including independent SS/SV/VV polarization coefficients, onset, horizon, AdS, cusp.

## Installed and audited — DO NOT repeat checks/builds

New module formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMCausalRiemannKernel.lean, 369 lines, namespace RHTower.D4BMCausalKernel. Imports HTGeometry.HypergeometricSpatialJets, RHTower.ThetaCuspHawkingBMLaplacePowerJets, Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp. Fifteen public theorems, all axiom reports only propext, Classical.choice, Quot.sound. All derivative assertions are actual HasDerivAt/iterated deriv, not assigned jet values.

Pν(Z)=((Z+1)/2)^ν * 2F1(-ν,-ν;1;(Z-1)/(Z+1)), Z>0. Gauss argument strictly inside unit disk, ν any complex. Actual first/second derivatives, Legendre ODE (Z²-1)P''+2ZP'-ν(ν+1)P=0, P(1)=1.

Z(h,x,y)=(cosh h+sinh x sinh y)/(cosh x cosh y). Actual time/space jets, Z_h²-Z_x²=(Z²-1)/cosh²x; Z_hh-Z_xx=2Z/cosh²x. Causal |x-y|≤h implies Z≥1. Characteristic Z=1, AdS reflection at x=0.

ν=-1/2+iχ gives original BM R_hh-R_xx+(1/4+χ²)R/cosh²x=0 at every causal point, any complex χ. Dirichlet causal kernel 1/2[1_(h≥|x-y|)R(h,x,y)-1_(h≥|x+y|)R(h,x,-y)] vanishes for h<0 and at x=0, retaining support indicators.

Public theorem names: legendreKernel_derivatives, legendreKernel_equation, legendreKernel_one, invariant_time_derivatives, invariant_space_derivatives, invariant_wave_geometry, invariant_causal, invariant_characteristic, invariant_AdS, riemannKernel_wave, riemannKernel_characteristic, riemannKernel_AdS, bmRiemannKernel_wave, dirichletCausalKernel_boundary, dirichletCausalKernel_before.

Scratch lake env lean passed. Exact leaf lake build GaloisForLFunctions.RHTower.ThetaCuspHawkingBMCausalRiemannKernel passed in isolated audit, 10 sec/3 Lake jobs, only new leaf. Existing closure 2622 own cached modules frozen; no dependency or umbrella build. Installed source/olean/ilean byte-matched audited copies; RHTower umbrella import added without build.
SHA256 source 0e71c6dd5a07935695208b169947e729f5aa3fb19dd7c165c22e5991d9f057ee; olean f4c098856d810d873d9f84f73330066b73e79df406c2da10d6f7772f0078aa24; ilean 3f4b455de98cd12047093dc4a28f6a163b0412c56baf33a20df94f12c2652ae6.
Formal lint passed (141 existing size warnings). Index generated; lint --check-generated twice reported only stale generated catalogs amid concurrent source edits. Do not claim freshness check passed. All owned Lean/Lake/Python checks completed. Scratch /tmp/hb-riemann-kernel.tCBLUpSp removed at end.

## Analytical positive construction — precise scope

Cards: docs/drafts/pipeline/3-formalized/hb-causal-riemann-kernel.md; docs/drafts/pipeline/1-in-progress/hb-causal-horizon-circle-kernel.md. Updated hb-causal-onset-contact-cancellation.md and hb-radiative-source-period-attack.md to point here. STATUS unchanged (new facts route-specific).

Full angular actual wave L=∂τ²-∂x²-sech²x Δ, x<0. Construct M_Z as actual hyperbolic geodesic circle average, retaining literal full angular Q, not eigenprojection. For Z=cosh d, C=cosh d, S=sinh d, Dθ=C-S cosθ>0: Xθ=X0+Y0 S sinθ/Dθ, Yθ=Y0/Dθ. Pulled-back metric dd²+sinh²d dθ² gives Darboux (Z²-1)M''+2ZM'=MΔ. If Xθ=X0+Y0 A, Yθ=Y0 B, 1+A²-B²=-2A', 2AB=-2B'. Thus Δbase integrand-Δtarget integrand=-2Y0 ∂θ Q_X; circle integral zero proves ΔM=MΔ. M1=Id. Intrinsic circle means preserve modular invariance and finite circle averages exist for full smooth cusp-growing Q. Full angular Darboux/commutation/admission not yet Lean formalized.

For physical rate s, w=2s, k=s(s-1)/4, A=(5s²+15s+4)/4, B=(s+2)(2s+3), original scalar angular factor [A+k u²(B-Δ/2)]Q. Q=fullSquarePotential=S²/2. Uses actual ΔQ=2(s+1)(s+2)Q+fullGradientEnergy.

For delay q≥0, E=e^q, b=(E-1)/(E+1):
K_s(q)Q=-a²∫_0^1 u(1+u)^w M_(E-(E-1)u)([A+k u²(B-Δ/2)]Q)du +a²∫_0^b u(1+u)^w M_(E-(E+1)u)([A+k u²(B-Δ/2)]Q)du.
Candidate scalar horizon U_s(v)=∫_0^v χ(t)e^(wt)K_s(v-t)Q dt; stream covector coexact U_s.
Finite exterior η=e^(2x)=(r-1)/(r+1): direct endpoint aη=(E-η)/(E+η); image b unchanged. Zdη=[E(1-u)+ηE^-1(1+u)+(1-η)u]/(1+η); Ziη same with minus final term. Both arguments1 at upper endpoints, η0 horizon, η1 exact AdS cancellation. Compact integrals for finite v. Formal smooth extension in Z at1, forced integral identity, actual causal uniqueness/admission still needed.

## Exact pulse bridge including moving image endpoint

Known particular f_s(u)=a²(1+u)^w u[c_s-k u²], c_s=α_s/(λ-α_s), diagnostic Δ value λ; full angular uses actual H and Q. Pulse I=-∫_0^1 f'P(Zd)+∫_0^b f'P(Zi). I(0)=-f(1), so integration by parts in actual χ' pulse cancels particular horizon and gives χ convolution of I'-wI.
For direct c=E-1,d=E+1; image c=E+1,d=E-1. Z=E-cu, Qc=(1-u)(cu-d)/2, J=w f'P-E(1-u)f'P', kden=-(1-u²)f''/2+(u+w)f'-λf/2, Flux=(1-u²)f'P/2+Qc fP'. Qc'=Z, -cQc=(Z²-1)/2, hence J-kden P=∂u Flux. Literal source equation gives kden=-a²u(1+u)^w[A+k_su²(B-λ/2)]. Direct u1 flux0; u0 fluxes cancel because f0=0. At image b: Flux=(1-b²)f'(b)/2=b'(q)f'(b), exactly cancels moving endpoint. Thus I'-wI=K. Full angular proof uses Darboux/commutation instead of λ substitution. Denominator-free flux algebra and endpoint coefficient checked in Lean scratch with standard3 axioms. Differentiated integrals themselves not formalized.

## Exact clock reduction of actual remaining horizon expression (analytical)

Equation (8) in circle card attacks complete SV horizon current, not full all-sector extinction. Put t=-s-3, w=2s=-3+δ, z=2t=-3-δ, δ=2s+3. g(v)=e^-3v χ(v), zero v≤0. h_s=e^δv g, h_t=e^-δv g. Fixed clock T_V(q,r)=∫_0^V h_s(v-q)h_t(v-r)dv=e^δ(r-q)C_V(q,r), C_V=∫_0^(V-max(q,r))g(u+|r-q|)g(u)du. E_V=h_s(V-q)h_t(V-r), (∂q+∂r)T=-E_V; B_V=(∂r-∂q)T/2.
For k_s=coexact K_sQ, A=D-2, Bst=<k_s,A k_t>, Bts=<k_t,A k_s>, their difference is actual angular Green boundary bΩ. Finite time integrated horizon current equals double integral [B_V(Bst+Bts)+E_V bΩ/2] plus single integral [(∂q T)(q,0)<k_s(q),S_t>-(∂r T)(0,q)<k_t(q),S_s>]. This follows directly from finite-domain convolution differentiation/Fubini; keeps original-source contacts and terminal/cusp corner.
Clock alone has C(d)=∫_0∞g(u+|d|)g(u)du even, C0=Cχ, C'0=0. βδ=(e^δd C(d))', βδ0=δCχ. Exact tail |d|≥1: C=Jχ e^-3|d|, Jχ=∫e^-6uχ(u)du. βδ(d)=wJχ e^wd for d≥1; -zJχ e^-zd for d≤-1. Transition |d|≤1 is explicit compact integral in card. Infinite pairing substitution remains unproved because response/cusp transport needed; retain finite formula. No branch-exchange cancellation obtained yet. Next attack exact radial/angular identity in (8) and other tensor sectors; do not re-audit local χ'^2 cancellation or kernel normalization.

See previous mem:hawking_bm_causal_onset_contact_cancellation_2026_09_09, mem:hawking_bm_mixed_radial_action_current_2026_09_09, mem:hawking_bm_full_source_onset_reduction_2026_09_09.

## Build lessons

Isolated stub buildDir must be PACKAGE-LEVEL before [[lean_lib]], not a lean_lib option. globs=[] on new leaf is empty build: set roots/globs=[full module]. No need rebuild now. Real.hasDerivAt_tanh missing; derive quotient using sinh/cosh. Complex.enorm_real missing. push_cast may rewrite real cosh to complex cosh; use exact_mod_cast typed identities. Avoid simp[invariant_AdS] globally (reflection rewrite loop). Bool branch scratch: cases image <;> simp <;> ring, not dsimp only.
