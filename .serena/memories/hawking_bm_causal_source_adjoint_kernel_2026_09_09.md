# HB: actual source-kernel angular action evaluated radially

Goal ACTIVE, RH and full physical extinction unproved. Previous goal turn classified PROGRESS (explicit Riemann kernel and source-only horizon/clock formula installed). This turn also changes authoritative state with an exact integral evaluation, not a no-go. No external blocker. No computations or agents. Frontier map READ ONLY; other tasks' modifications preserved. STATUS unchanged: results are route-specific.

Full chain: literal theta-cusp source → Xi occurrence → retained spin-two source → physical causal radial/left-QNM action → fixed Hawking-clock extinction → RH. Hard target still full 2 Ω(B(p,p)/2,B(m,m)/2), with all independent SS/SV/VV source polarizations, onset, horizon, AdS and cusp terms.

## New installed module — do NOT rebuild/re-audit

formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMCausalSourceAdjoint.lean (~452 lines), namespace RHTower.D4BMCausalSourceKernel. Imports previously audited BMCausalRiemannKernel, BMLaplaceSourceProfile, and Mathlib interval FTC. Five public theorems, all checked only propext/Classical.choice/Quot.sound:
- original_source_integral_eq_adjoint (line208)
- adjointDensity_eq_cubic (line260)
- original_source_integral_eq_cubic (line271)
- sourceKernel_action (line430)
- originalDensity_sourceRemainder (line441)
All integral proofs use actual derivatives, continuity, absolute integrability and FTC. No supplied flux values or Green/source assumptions. Delay is the geometric subtype E>1; strict-positive-delay only, not a zero-delay or infinite-time admission theorem. Complex s,nu,a unrestricted.

Scratch lake env lean clean. Exact leaf lake build GaloisForLFunctions.RHTower.ThetaCuspHawkingBMCausalSourceAdjoint PASSED 8.7s/3 jobs, only new module. Isolated audit froze3972 existing own cached modules, reused external caches, no dependency/umbrella build. Installed source/olean/ilean matched audited copies byte-for-byte. New import appended to RHTower.lean, no umbrella build. Five new-only axiom checks passed. Index refreshed; ordinary formal lint passed; scoped diff check passed.
Hashes: source 3a89c8a3c6384863b00c5006dfd7208de2b5298fab710e6c81624ce3ed5cf83c; olean735e6e86b2df3429ee743bd561806ec7e251c11759ac3108a33a7690eb7ad7e7; ileane37828c6e5a6c00aa54f99cdd696aaf71252a458f5225b847ca4513132a105f1.
All owned Lean/Lake/Python checks finished. Owned /tmp/hb-causal-source-adjoint.g6BucceZ removed at turn end.

Card: docs/drafts/pipeline/3-formalized/hb-causal-source-adjoint-kernel.md. Updated docs/drafts/pipeline/1-in-progress/hb-causal-horizon-circle-kernel.md (new Source-specific radial adjoint evaluation section, equations9/10). Read them before extending, not old no-go cards.

## Exact positive result

E=e^q>1. Direct c=E-1,d=E+1,upper1; image c=E+1,d=E-1,upper b=(E-1)/(E+1). D=d/c, Z=E-cu, p_D=(1-u)(D-u). c²p_D=Z²-1, -cp_D'=2Z, so actual Legendre Pν(Z) obeys L_D P=λP, L_D f=(p_D f')', λ=ν(ν+1).

A=(5s²+15s+4)/4; k=s(s-1)/4; B=(s+2)(2s+3). Original density u(1+u)^(2s)[A+k u²(B-λ/2)]P. Formal source linkage: equals u*sourceRemainder s 0 1 1 (λ/2-(s+1)(s+2)) 1 (1-u²)*P at u≥0. Thus tied to original mixed-source remainder, not merely a similar polynomial. This is scalar/eigenvalue representation; full angular source application below remains analytical.

First adjoint transfer: h=u³(1+u)^2s. Flux h p_D P'-h' p_D P vanishes at both endpoints (h0=h'0=0; p_D upper0). Therefore exact original integral becomes ∫g_(s,D)P, where g=u(1+u)^(2s-2)C, C=c0+c1u+c2u²+c3u³:
c0=A-3kD;
c1=2A+9k/2-3kD(4s+1)/2;
c2=A+k[2s²+14s+9-D(2s²-2s-6)];
c3=k(2s+3)[6s+3+D(2s+3)]/2.
The literal B cancels the fourth radial power. Formal cubicDensity uses equivalent u*power(2s)(1+u)/(1+u)²*C*P; cubicWeight uses power(2s-2), equivalence proved by cpow_sub/two.

Second adjoint transfer evaluates actual Einstein-current factor λ-2. g0=0, g'0=c0, so unlike first transfer it retains D*c0*Pν(E). Define K sourceKernel as -a²∫direct originalDensity+a²∫image originalDensity. Main theorem sourceKernel_action:
(λ-2)K=-a²∫direct (L_Dd-2)g_d P+a²∫image (L_Di-2)g_i P+Γ_s,a(E)Pν(E),
Γ=-4a²E/(E²-1)[A-6k(E²+1)/(E²-1)].
Γ evaluated from a²[Di(A-3kDi)-Dd(A-3kDd)], Dd=(E+1)/(E-1), Di=inverse Dd. actionDensity uses explicitly proved actual first/second cubicWeight jets; not unspecified derivatives.

## Application to hardest pairing, still analytical full angular

Use actual circle means M_Z Q from mem:hawking_bm_causal_riemann_circle_kernel_2026_09_09 and circle card. Replace Pν(Z) by M_Z Q, λ by actual Δ. The first transfer carries original ΔQ source onto g, retaining full Q. Equation9 gives (Δ-2)K_s by the displayed radial action densities plus Γ_s,a(E)M_E Q. Under coexact, this is exactly (D_covector-2)k_s in the actual SV Einstein horizon current. Γ is the AdS-origin term created by this adjoint manipulation; DO NOT claim it is the complete4D physical AdS action flux.

The separate terms in equation9 have rational singular factors as q→0. Keep their assembled identity; do not independently integrate Γ over delay or assert termwise zero-delay admission. Original finite-source formula supplies combined candidate value; formal admitted Green/limit transport still needed.

Actual local horizon source from MΨ=2current is S_s=2a²2^(2s)[A+kB-(k/2)D_covector]J, J=coexactQ. Uses full source ΔQ relation; no angular inverse remains. Equation10 on finite angularΩ:
<k_s,S_t>=2b²2^(2t)[(A_t+k_t B_t-k_t)<k_s,J>-(k_t/2)<(D-2)k_s,J>-(k_t/2)bΩ(k_s,J)].
This retains actual angular Green boundary bΩ. Equation10 is analytical, not in new Lean module.

Next hard test: substitute equation9+10 into finite clock/source pairing equation8, evaluate assembled radial+circle+contact terms with all cusp/terminal corners, and complete independent remaining tensor sectors. No branch-exchange extinction proved. Full angular circle-mean Darboux/commutation, integrated forcedGreen equality/admission, horizon/cusp/infinite-time transport and completeSS/SV/VV response/pairing remain open. Do NOT repeat χ'^2 onset cancellation, first Riemann-kernel normalization, sourceKernel_action or their axiom audits.

## Lean/build notes

Use convert! (not convert) for these real→complex HasDerivAt compositions; plain convert left metavariables. gt_mem_nhds proves an upper neighborhood, lt_mem_nhds a lower one. Correct continuity congruence is ContinuousAt.congr_of_eventuallyEq, not he.continuousAt_iff. fun_prop quotient denominators needed explicit pow_ne_zero2 hn. Real casts need push_cast after Bool slope cases. Keep package-level buildDir in frozen stubs, roots/globs=[] there, and exact module roots/globs in audit package. No build now necessary.
