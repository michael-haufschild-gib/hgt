# HB native time-primitive elliptic equation — 2026-09-10

Goal ACTIVE. RH, physical inverse comparison, joint energy-domain admission, and complete physical-current extinction UNPROVED. No blocker. No subagents. Analytical only.

## Chain and hard obstacle
literal theta-cusp source → Xi occurrence → retained spin-two source → physical causal radial/left-QNM action → fixed Hawking-clock extinction → RH.
Hard target remains 2 Ω(B(p,p)/2,B(m,m)/2)=0 with independent SS/SV/VV amplitudes and every onset/horizon/AdS/temporal/cusp current. This turn constructed the ACTUAL pointwise elliptic equation required for native/physical inverse identification, not a generic conditional wrapper.

## New verified result
Extended existing formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMFullNativeWave.lean from 1026 to 1692 lines. Added IntegrationByParts import; original public statements unchanged. Existing unique area-umbrella import in formal/GaloisForLFunctions/RHTower.lean remains wired (observed line17056; concurrent other agents add unrelated imports). No umbrella builds.
Definitions:
- nativeResidualTimePrimitive1425: W(q,s,amp,t,x,X,k)=∫0^t (t-u) fullNullResidual(q,s,amp,u+x,u-x,X,k)du.
- nativeResidualStaticForcing1633: F= squareResidual(q,[X,exp k])*oddSource(s,amp,u,x) + (Σ i:Fin3 principalNullResponse(q,s,amp,i,u+x,u-x)*cutoffCommutator(principalExponent q i,[X,exp k]))/cosh²x.
A=-∂xx-sech²x*(exp(2k)∂XX+∂kk-∂k).
FOUR new public theorems, universal q:XiZeroCopy, arbitrary s/amplitude and all REAL t,x,X,k; no extra analytic assumptions:
- nativeResidualTimePrimitive_radial_equation1450: Wxx=v(t)-∫0t(t-u)[squareResidual*oddSource +(Delta_H v+Σ P_i comm_i)/cosh²x]du.
- nativeResidualTimePrimitive_boundary1474: W(t,0)=0.
- nativeResidualTimePrimitive_second_time1496: Wtt=v(t).
- nativeResidualTimePrimitive_elliptic_equation1679: A W=∫0t(t-u)F(u)du-v(t).
Actual global HasDerivAt proofs are private: these are NOT default derivative values for nondifferentiable fields. Every source-cone edge is included. All original principal amplitudes and cutoff commutators retained.

## Proof mechanism (new positive construction)
Continuous Vp=P, Vr=R, Pr=Rp=G suffice; pure Vpp/Vrr not assumed. For JP=∫0t(t-u)P(u+x,u-x)du, reparametrize a=u+x, so JP=∫x^(t+x)(t+x-a)P(a,a-2x)da. Differentiating only the available second-argument derivative gives JP_x=∫P-2∫(t-u)G-tP(x,-x). Reflect x and exchange arguments for R. Then Wxx=V(t+x,t-x)-V(x,-x)-t(P+R)(x,-x)-4∫(t-u)G.
Private calculus helpers scalarCLM, chain, movingIntegral, weighted, characteristic_derivative, weighted_first, weighted_second appended after old source. chain uses hasStrictFDerivAt_uncurry_coprod; movingIntegral differentiates a variable upper endpoint plus parameter with existing ClockParametricDerivative.
Actual nullSource zero outside positive quadrant follows oddSource onset and continuity to characteristic edges. Every responseJet and actual principal scalar response vanishes there. residualEffective=G also zero. residual_global_primitive extends original residual Goursat identity to ALL REAL p,r. residualNullP/R are single integrals of G; global FTC and rectangle_swap supply continuous first null derivatives and both mixed derivatives. Initial P/R/V terms vanish by actual support.
Original angular jets pass through bounded time integration: nativePrimitive_x/xx, nativePrimitive_k/kk, nativePrimitive_angular_action prove Delta_H W=∫weight residualAction. effective_time_split retains F plus angular action. Final elliptic equation is the exact combination.

## Remaining direct attack
Prior turn proved joint-L2 native residual and modular closed-cell germ compatibility. New pointwise A W equation closes the next actual-field identity. Still need ADMISSIBLE TESTING AND ENERGY FORM ADMISSION on original radialMeasure.prod modular measure. Difference u between literal and constructed physical evolution should yield AW=-u after same forcing is identified. For B=J J* actual unit resolvent, desired B u+(I-B)W=0. Candidate cutoff testing gives ∫η²|grad_A W|²≤2||u||₂||W||₂+4∫|grad_Aη|²|W|², then bounded graph approximants/weak closure. Need actual local test regularity, radial/Dirichlet approximation, modular cusp cutoff limits and graph closure. Do NOT state these are proved or infer admission from L2 and interior PDE. Full unintegrated V global classical static wave regularity also not claimed.

## Searches this turn
Used direct scripts/formal_tools.py research extensively; never read implementation/help or launched service. Broad OR energy/graph; Caccioppoli/elliptic/coercivity; extrapolation/transposition/duality. Deep mechanism searches: double primitive static wave; moving-endpoint parametric derivative; smooth invariant elliptic field admission to Friedrichs form. Inspected declarations/candidate_lemmas/source_arguments (method search)/proof_ideas/ingredient_sets/coverage. Last deep inventory56004 complete, semantics partial, compiler mostly pending/source-only. No absence claim.
Useful corpus: ClockParametricDerivative, mathlib FDeriv.Partial, endpoint FTC, interval translation, rectangle_swap. UnitWaveEllipticRange.unitWaveDuhamel_wave_graph denotes theorem in that FILE (namespace HTGeometry): Fourier KG elliptic inverse, NOT actual joint operator, so not directly applied. Form admission deep suggestions friedrichsFormOperator_represents_form, boundedPerturbedFriedrichsOperator_represents_form, modular Green identities and constructed response smoothness do NOT admit native W; ingredients proposed/unverified. Source arguments recovered PlanarChartTest.core_green in GlobalDistributionEquation67 and frameEnergy_periodize in ModularDirichletUnfolding67; their premises remain to construct for native field.

## New user steering on searches
Every turn state full chain, hard obstacles, previous progress, next direct attack. Use broad/single-word arXiv searches for distant methods, prioritize June–September2026. User explicitly clarified examples Hawking/commutator/etc are NOT prescribed terms. Choose your OWN search terms. This turn independently chose duality/localization/memory, read recent primary-source papers and methods. Do not simply collect papers; conjecture/prove/pivot on actual hard obstacle.
External candidates (all links/dates verified on arXiv; no results adopted as axioms):
1. https://arxiv.org/abs/2609.09921 Hirvonen–Jüngel–Pollino, Sept9, nonlocal population diffusion. Sec4 backward adjoint turns difference equation into ∫|u|²=0; potential alternative uniqueness route. Their bounded nonlocal generator does NOT match our unbounded joint operator. Read exact adjoint existence via contraction.
2. https://arxiv.org/abs/2609.09202 Ramírez-Uribe et al., Sept5, threshold matching vacuum amplitudes. SecII angular v↔1-v averaging removes individual imaginary threshold contributions, but a simultaneous double residue restores squared imaginary part. Potential positive mechanism: evaluate joint contact terms together, no HB cancellation established.
3. https://arxiv.org/abs/2609.10203 Wang–Zhu, Sept9, nonlinear Hawkes. Sec2.2 zero-resolvent corrector g=∫P_sf, discount gε=∫e^-εsP_sf; growth/increment bounds admit extended generator and controlled limit. Transfer requires native infinite-time tail estimates not available; finite-time W avoids that requirement.
4. https://arxiv.org/abs/2609.07642 Czaja–Kania, Sept7, Duhamel sum of mappings. Sec5 extrapolated domain E^-1 uses dual graph of adjoint; positive sectorial operator framework, not proved realization of wave operator.
Initial example-word queries also read Bru–Metraud–Pedra2608.28208 (unbounded double-commutator error bounds, no direct transfer) and Zeng2608.26078 (reflection parity + surviving regulator term); not used as proof. Don't keep repeating these searches without new reason.

## Validation CLOSED — do not repeat old axiom checks
Scratch lake env lean /tmp/.../native.lean passed without warnings. Final isolated lake build GaloisForLFunctions.RHTower.ThetaCuspHawkingBMFullNativeWave passed105sec,2jobs,no warnings. Reused4091 old project modules and11 existing package caches; no old dependency or umbrella builds. ONLY FOUR NEW PUBLIC AXIOM CHECKS above, all exactly [propext,Classical.choice,Quot.sound]. Source+5artifacts byte-identical installed with original-source concurrency guard. Formal lint PASS, large-file warnings including1692line changedmodule. Lexical discovery finds all4public and3matchingprivate/defs,total7hits. All owned sessions finished; no owned Lean/Lake/search/lint processes remain. Scratchroot /tmp/hb-native-weak.fxDtuRHC and nested audit REMOVED. Other agents' unrelated Lean processes were observed and untouched.

## Documents changed
- NEW docs/drafts/pipeline/3-formalized/hb-native-time-primitive-elliptic-equation.md: actual theorem, complete paper mechanism, analytical loop, search/paper method applicability, final validation/limits.
- docs/drafts/pipeline/1-in-progress/hb-native-cusp-inverse-identification.md: inserted current formal pointwise primitive equation before remaining admission conjecture.
- docs/drafts/pipeline/3-formalized/hb-native-cutoff-residual-wave.md: updated remaining comparison paragraph with new result link.
FRONTIER MAP READ ONLY, untouched. Universal STATUS untouched: no new route-independent rule established. No Git commands, launch.sh, mathematical computations, subagents, commits, pushes or external messages. Standard axioms only, no computational oracle.

## Efficient final audit recipe
Own workroot audit/lakefile.toml name nativePrimitiveAudit,11 path requires to deps stubs. Empty GaloisForLFunctions lean_lib roots/globs; NativeAudit lean_lib roots/globs EXACT target. Copy only targetsource and toolchain. Recursively parse own project imports from source; symlink old .olean,.ilean,.hash,.trace,.olean.private,.olean.server into audit .lake/build/lib/lean. Stubpackage lean_lib names Mathlib,Aesop,Plausible,LeanSearchClient,ImportGraph,ProofWidgets,Qq,Batteries,Cslib,Zeta23,ClassFieldTheory, roots/globs empty. Each stub cache symlink original .lake/build/lib/lean; CFT original .lake/build/default/lib/lean. Manifest1.2.0 pathentries fullconfigfile/manifestFile/inheritedfalse. Run only targetlakebuild. Axiom scratch via lakeenvlean auditcwd. Install actual produced5artifacts (.olean,.ilean,.olean.hash,.ilean.hash,.trace), guarded originalsourceunchanged. Existing areaumbrella alreadywired, don'tbuild it. Helper removed with root; reconstruct only when needed.

Lean details learned: `convert!` and `using!` avoid Complex instance-defeq explosions; plain expected-type `.comp` with actual full residual can exceed200kheartbeats, fix via `convert!`. Set typed Continuous hX/hK/hJ and hsum functions before rewriting integrals; function-pointwise add may not match under rw transparency. intervalIntegral.integral_div (NOT integral_div_const). intervalIntegral.integral_interval_sub_left takes integrability of0..b BEFORE0..a for (∫0b)-(∫0a). EventualEq for HasDerivAt.congr_of_eventuallyEq expects NEW function = OLD function. Add-neg normalization uses sub_eq_add_neg, no add_neg_eq_sub. rectangle_swap signature f hf a b c d.

Prior memories: mem:hawking_bm_native_modular_transport_2026_09_10; mem:hawking_bm_native_residual_joint_admission_2026_09_10. Their audits complete; do not redo.