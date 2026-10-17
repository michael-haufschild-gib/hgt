# Hyperbolic multiplier lifting — active research goal
Read user brief each turn: /Users/michael/.codex/attachments/88558842-9142-47a9-bda1-a9d243d1a408/pasted-text-1.txt.
Independent BiScaleUncertainty, not RH; no hgtl7, no numerical experiments/computations. Explicit goal: 100 significant contributions, not declaration count. Goal ACTIVE/incomplete. Last turn: progress.

Master paper/card: docs/drafts/pipeline/1-in-progress/hyperbolic-multiplier-lifting-2026-10-17.md.
Facts: docs/reports/BiScaleUncertainty/HyperbolicMultiplierLifting-FACTS.md.
Full field README read earlier; no docs/architecture.md or docs/testing.md. Preserve concurrent work (including both README copies). Serena ignores Lean paths; use rg + inspected source/apply_patch. update_plan and multi_tool_use.parallel unavailable; plan in card; independent reads Promise.allSettled. No subagents authorized.

COUNT 3/100:
1. HyperbolicMultiplierGramTransfer.lean: compensated secant/signed-kernel Gram transfer, exact hyperbolic Gram difference, measured defect penalty, compact collar integral. 13 public theorems. SHA256 12ec9a1f19c416d8d0601c1c1e133880318a69cb43d84e3a133034fd8b387444.
2. HyperbolicJumpEnergyTransfer.lean: signed-sinh squared-jump identity, source-support envelope, UNCOMPENSATED finite clique penalty and full global secant receiver. 19 public theorems. SHA256 56fb077bbe28fbae0d143d8a62f68db8bbcc87c5c3c941c2e0b43feea856e2b4.
3. PlasticCrossoverGramReceiver.lean: exact secant + positive remainder + signed moment decomposition of ACTUAL plastic crossover, full-Gram receiver, canonical odd sources, arbitrary origin coefficient. 18 public theorems. SHA256 c34e886a83d099242571f9bdcb2b4e49fd3841608fad2448b9615e2ee49cd923.
Each actual source compiled with lake --old env lean ... -o .lake/build/lib/lean/... without warnings. All 50 public theorem #print axioms audits (/tmp) only propext, Classical.choice, Quot.sound. All 3 umbrella imports and index refresh completed. No full/umbrella builds.

Latest lint --check-generated FAILED (concurrent unrelated work):
unreachable RHTower.NonTemperedShiftedZetaPairCountermodel, RHTower.WeilConeMismatchWitnesses, RHTower.ZeroCountRemainderNotIntegrable, BiScaleUncertainty.LogarithmicPathKernel, BiScaleUncertainty.PairedCosetSphereDuality, BiScaleUncertainty.SignedCosetProductCoupling; stale generated LEAN_API.md, LEAN_OVERVIEW.md. Existing large-file warnings. No owned module flagged. Don't repair others' unfinished modules. No owned running processes; /tmp/hml_plastic_api.lean, hml_plastic_axioms.lean, hml-plastic-lint.log cleaned.

Exact facts:
C=C_(1/2)f,S=S_(1/2)f,R=h_f(0),RS=h_S(0).
h_f sech=(h_C-h_S)sech², RC=R+RS. Correct alpha1/2 (formerly wrong README1/4 fixed).
Source zero gives h_C=h_S, NOT multiplier zero.
G_C-G_S=sum vi vj cosh((tj-ti)/2)h_f(tj-ti); source clique gives R sumvi², not G_S diagonal.
Delta_f sech=R(sech-sech²)+(Delta_C-Delta_S)sech². Cannot drop companion using this identity alone.

Signed jump identity (any C_c f, real alpha,x):
∫sinh(alpha u)sinh(alpha(u+x))(f(u)-f(u+x))²du
=2(cosh(alpha x)h_(S_alpha f)(0)-h_(S_alpha f)(x)).
Choose B>0 from actual compact support; K_B(x)=sinh(B/2)sinh((B+|x|)/2)>0.
cosh(x/2)RS-h_S(x) ≤ K_B(x)(R-h_f(x)). No companion/additive commutator error.
xi=ti-y, vi=bi² sech(xi/2)/K_B(xi), G=sum vi vj hS(tj-ti), A=sumvi²,D=G-RS A:
sum bi² Delta_f(xi)sech(xi/2) ≥ RS sumvi cosh(xi/2)-sqrt(RS G)
≥ RS(sumvi cosh(xi/2)-sqrt A)-sqrt(RS max(D,0)).
Actual data, no grid/parity/clique assumptions.
Secant F≥0, F≤4R exp(-x/2), integrable C_c without derivatives.
For d=|delta|, nodes tk=kd,k<n,bi=1, integrate full-Gram bound at offset -y over0..d.
Tiling gives L(f;delta,n)≤J_sech(f). delta=log2 gives dyadic nodes.

NEW ACTUAL PLASTIC receiver:
c*=screwSignThreshold>0, k=levyCoshKernel c*, V=levyCoshPotential c*.
E=∫f(u)cosh(u/2), O=∫f(u)sinh(u/2).
P=V R+∫_(u,v)f(u)f(v)[2cosh((u-v)/2)-k(|u-v|)].
Exact P=2∫x>0 k(x)Delta_f(x)+2(E²-O²)
=J_sech+R_plastic+2(E²-O²).
R_plastic integrates Delta_f against2k-sech; weight is4cosh(x/2)-sech(x/2) on x≤c*, dual Lévy weight beyondc*. Strictly positive weight, nonnegative energy.
All pair/jump integrability discharged from actual C_c source using exists_bddSupp_of_hasCompactSupport.
Thus L+R_plastic+2(E²-O²)≤P, also L+2(E²-O²)≤P.
Canonical odd source F=(f(u)-f(-u))/2 is compact continuous odd, E(F)=0, S_(1/2)F even.
Odd receiver L(F)-2O(F)²≤P(F).
Full original expression incl ANY origin coefficient a:
a R +2(E²-O²)+L≤(a+V)∫f²+signed residual pair. Includes gamma-origin constant.
The new receiver is NOT a positivity theorem; negative odd moment, actual multiplier leakage, source-support dependence remain.
Do not say plastic receiver still open; it is verified with precise moment retained.

Next mathematical work:
Control actual Gram leakage under logarithmic source zeros and compare odd sine moment with positive secant/remainder energies. Support-independent domination unproved. Six-packet no-inheritance candidate still UNFORMALIZED:
even smooth phi supported(-eps,eps),2eps<d; coefficients(-1,1,1) at(d,2d,3d), opposite at negatives.
Predicted h_f(d)=0,R=6∫phi²; h_(S_alpha f)(d)=[cosh(5alpha d)-cosh(3alpha d)]∫cosh(2alpha u)phi²>0.
Move positive centers byT, reflect negatives: source R/zero fixed, multiplier factor cosh(2alpha T+5alpha d)-cosh(2alpha T+3alpha d) unbounded. ONE lag, not infinite grid.
Existing EvenSectorSmoothBlindInterpolationObstruction.lean supplies smooth even compact packet/mass.
No no-go theorem claimed before actual proof and positive-survivor audit.

Novelty: classical Hilbert Cauchy–Schwarz, ground-state method, existing corpus plastic jump/moment identities; field-specific bridges only, no literature priority claim. Frank–Seiringer arxiv0803.0503 background. New focused lexical search levyCoshKernel archSechHalfWeight excluding PlasticCrossoverGramReceiver: no declarations. Broad hybrid had relevant existing jump/crossover hits, semantic coverage unmeasured.
Current both READMEs updated for all3; module row34 (other concurrent rows already duplicate IDs28–30; preserve others).

Lean details:
- HasCompactSupport.mul nonexistent; mul_left/mul_right valid. Type-ascribe HasCompactSupport(fun u=>f u*f u):=f.hasCompactSupport.mul_left, then simpa only[sq].
- integral_sub_shift_sq is RHTower.ArchimedeanAnomaly, compact then continuity.
- Explicit (f := (f : ℝ→ℝ)) on exists_bddSupp_of_hasCompactSupport and autocorr integral lemmas avoids C_c.toContinuousMap coercion rw failures.
- abs_add_le twoargs; abs_sub_le three(distance triangle).
- Unconstrained intervalIntegral.integral_mono_on requires(μ:=volume); comp functions may need simp only[Function.comp_def].
- if_pos rewrite only first occurrence; simp only[if_pos hx] for both.
- integral_neg_eq_self f volume; HasCompactSupport.comp_homeomorph(Homeomorph.neg ℝ); integral_prod_cosh_eq_sq; exp_half_div_sinh_eq.
One owned foreground Lean process at a time, final audit actual source, axioms only/tmp, long Python through finite run_guarded timeout. No heartbeat hacks. Clean owned scratch via apply_patch (rm auto-review rejected earlier).