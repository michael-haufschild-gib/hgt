# CHMD compactly supported operator cores — 2026-10-16

RH goal remains ACTIVE and unbounded. This turn made verified structural progress: spatial cutoff multiplication preserves the actual maximal operator domains, converges in operator graph norm, and the compactly supported part of each actual generator graph has closure equal to the full graph. Smooth compact operator-core density and RH remain open. Do not mark goal complete.

Read each new turn: /Users/michael/.codex/attachments/2c5020c9-b71c-40b8-ba6c-e8fb1100e229/pasted-text-1.txt
User requires one significant CHMD structural contribution per turn, not estimates, receivers or RH equivalences. No web, novelty search, numerical experiments, or old research Markdown reads. Corpus-first research. No subagents authorised. No full/umbrella builds; one owned build/check at a time; targeted lake --old build; final plain lake env lean on every new leaf; all-declaration axiom audit in /tmp; no heartbeat hacks; cleanup owned scratch. No commits/push.

Formalised card: docs/drafts/pipeline/3-formalized/chmd-compact-support-operator-core-2026-10-16.md
Prior actual generator construction and remaining smooth-core context: `mem:rh/chmd-stationary-ground-generators-2026-10-16`
Prior arithmetic removal: `mem:rh/chmd-prime-operator-domain-2026-10-16`
Prior spectral nullspace/synthesis frontier: `mem:rh/chmd-full-spectral-nullspace-2026-10-16`

## Exact contribution
Namespace RHTower.CHMDDoobGraph; MassSpace from CHMDPolar.
Theta=riemannKernelReal, c=cosh(x/2), mu=massMeasure=Theta*c dx.
Existing arithmeticGenerator L=(resolvent)^(-1)-I and stationaryGenerator G are selfadjoint, closed and nonnegative; DomL=DomG; L=G+K, K=primeGenerator+groundPotentialOperator bounded.

Define archMomentWeight e=e.1*archWeight e and archMomentMeasure=archBase.withDensity(ofReal archMomentWeight). Thus eta(dt dx)=t*kappa(t)*Theta(x)*Theta(x+t) dt dx for t>0. Both endpoint pullbacks of EVERY mass-L2 source belong to L2(eta). Proof uses global theta bound, integral t*kappa<infinity and integrability of Theta*u^2. The right endpoint uses the volume-preserving product shear. No boundedness or smoothness of u is used.

admittedPullbackLM/admittedPullback constructs the literal bounded pullback from automatic MemLp admission plus endpoint nonsingularity, via the closed graph theorem and AE subsequences. Instantiated as archMomentLeft and archMomentRight, with AE representative formulas. Generic machinery is fully instantiated for the actual CHMD measures.

The already-defined smooth spatial cutoffs chi_n satisfy 0<=chi<=1, uniform Lipschitz bound, compact support, chi_n(x)->1. massCutoff n is their bounded multiplier on MassSpace. cutoffSlope n(t,x)=(chi_n(x)-chi_n(x+t))/t is uniformly bounded by cutoffLipschitz (including t=0) and converges pointwise to zero. cutoffSlopeOperator is its bounded multiplier on moment L2. Dominated convergence proves strong convergence to zero; no improved quantitative estimate is the result.

Cutoff form admission holds for arbitrary ArchGraph vectors, removing the previous bounded-source restriction. Exact identity:
 D(chi*u)=chi(left)*Du+(chi(left)-chi(right))*u(right).
The correction is L2(archMeasure) because (Delta chi)^2 <= Lip(chi)*t and the right first-moment endpoint is L2. archCutoff and fullCutoff are actual graph vectors with source massCutoff n u.

Exact bounded archimedean commutator:
 Carch_n = Eleft^* B_n Eright - Eright^* B_n Eleft.
Its pairing equals integral b_n [u(right)v(left)-u(left)v(right)] d eta.
 archCutoff_pairing:
 <archCutoff n p,q>_graph - <p,archCutoff n q>_graph
 = <Carch_n source(p),source(q)>_mass.
 Carch_n u -> 0 strongly for every u.

Full commutator:
 C_n=Carch_n+P M_n-M_n P, P=primeGenerator.
 fullCutoff_pairing is the same exact graph identity with C_n.
 C_n u ->0 strongly, using bounded P and strong multiplier convergence.

Maximal-domain admission is PROVED by Riesz uniqueness, not assumed:
 rieszLift(M_n w+C_n Rw)=fullCutoff n(rieszLift w)
 resolvent_cutoff: R(M_n w+C_n Rw)=M_n Rw.
Therefore M_n preserves range(R)=Dom(L), and
 arithmeticGeneratorCutoff_apply:
 L(M_n u)=M_n(Lu)+C_n u.
Both M_n u->u and L(M_n u)->Lu. The representative chi_n(x)*u(x) is compactly supported with no boundedness/smoothness premise. Exact graph closure is formalised.

G's domain equals L's and differs by bounded K, so the same actual cutoffs converge with G's output and have the same compact-support graph closure. Do NOT claim that these approximants are smooth: only chi_n is smooth; u need not be.

## New leaves and main theorems
All under formal/GaloisForLFunctions/RHTower:
1. CHMDArchMomentPullback.lean: 177 lines, 18 declarations.
2. CHMDOperatorCutoffForm.lean: 178 lines, 21 declarations.
3. CHMDOperatorCutoffCommutator.lean: 132 lines, 14 declarations.
4. CHMDCompactSupportOperatorCore.lean: 165 lines, 16 declarations.
Total 652 lines, 69 declarations.

Capstone lines:
18 rieszLift_cutoff
32 resolvent_cutoff
43 massCutoff_mem_arithmeticGenerator_domain
53 arithmeticGeneratorCutoff_apply
65 arithmeticGeneratorCutoff_tendsto
81 arithmeticGenerator_compact_support_core
125 stationaryGenerator_compact_support_core
136 arithmeticGenerator_compact_graph_closure
151 stationaryGenerator_compact_graph_closure.

The graph-closure statements say closure of {(u,Lu) in graphL : u has compactly supported AE representative}=graphL, and similarly G. They are unconditional actual-source theorems.

## Verification and cleanup
All four targeted builds passed. Final plain lake env lean <file> passed on all FOUR with empty output. /tmp axiom audit printed ALL69 declarations; only propext, Classical.choice, Quot.sound. API probes also passed; no errors/warnings/sorryAx in final audit. An initial scratch-only API probe needed explicit universe levels in have := @Name.{0,...}; corrected and verified. No leaf source was changed after successful final plain checks.
All69 declaration names checked unique in CHMDDoobGraph source files. All4 umbrella imports occur exactly once. No full/umbrella build or commit/push. Concurrent workspace activity committed some new files while working; we issued no commit.
All owned processes terminal and 14 exact owned scratch files removed. No owned live process/scratch remains.
Global scripts/formal_tools.py lint EXIT1 with exactly4 unrelated UNWIRED modules:
RHTower.CHMDFarFieldEnergy
RHTower.CHMDPrimeWindowTail
RHTower.XiGaussianHeatRegularTransfer
HTGeometry.MomentNormalBlockRecurrence.
No proof-debt lint error. Do not wire unrelated unfinished work or claim global lint clean.

Hashes revalidated after final audits and during cleanup:
CHMDArchMomentPullback a469573c78519d5c3b6d0cdc9f3b68fd34112c88544eb6322fcce60d40087d94
CHMDOperatorCutoffForm 2171e6b87f6d804ff10c95e1072c5cf51b240bb5d6d0ed0aab0887934be804f0
CHMDOperatorCutoffCommutator 7501c35a4b042a1d9d5cb0a04dae622312a993f31a9bf42cafcdaf4745679a25
CHMDCompactSupportOperatorCore 53212585e2a27e329a3eed6d034f935ee538c4d15f3a120b5d195b27b412571c
Prior CHMDStationaryGenerators and CHMDStationaryKernelRigidity hashes still matched their prior audited memory.

## Current frontier: local smoothing, not global localization
Compactly supported OPERATOR-core approximation is now proved. Compact SMOOTH operator-core density remains open; do not confuse the two. Full compact FORM core was already proved earlier. Weak compact-smooth-test domain admission and primal cardinal synthesis remain unresolved; no RH critical sign inequality has been proved.

New possible continuation, avoiding the previous global Glaeser/half-density essential-SA proposal:
1. Construct the correct ordinary-volume stationary generator A with kernel kappa(t), not kappa(t)/t. The Gamma clock corpus has the latter wrong kernel and cannot be identified with this A.
2. For compactly supported u in Dom(G), f=Theta*u is compactly supported and in the stationary form domain. Show f in Dom(A) by splitting arbitrary stationary form tests q with a smooth chi=1 near supp(f). The localized test chi*q/Theta is admissible in the actual ground graph using strict theta positivity on a compact and the form cutoff admission. G's exact form identity handles the local pairing. The complementary separated-support pairing is a bounded ordinary-L2 tail functional. This should give actual ordinary operator-domain admission for compact f, without assuming a smooth operator core.
3. Compact convolution mollifiers should commute with actual A and converge in its graph norm; prove this using translation invariance of the closed form/resolvent or a correct Fourier model. Then f_epsilon compact smooth, f_epsilon->f and A f_epsilon->Af in ordinary L2.
4. Divide by Theta on the common compact support: u_epsilon=f_epsilon/Theta is smooth compact. Source convergence follows from local positive lower theta bound. Output convergence for G follows from G u_epsilon=(A f_epsilon)/cosh and global bounded Theta/cosh. Diagonalize after the proved spatial cutoffs to close smooth operator core.
These remain candidate obligations, not formalised results. Do NOT assert global Dom(G)={u:Theta*u in Dom(A)}: weighted output can admit more. Ordinary-domain admission above is proposed only AFTER compact localization.

## Useful Lean lessons
Integrable.mul_prod, not prod_mul. For the shear use MeasurePreserving.integrable_comp_of_integrable and change the target measure to explicit (restricted volume).prod volume before simpa.
Lp.stronglyMeasurable v must be explicit for the MassSpace abbreviation; v.stronglyMeasurable failed namespace inference.
Absolute continuity transfers arbitrary AE assertions via .ae_le, not .ae.
A graph membership p.property may need an explicitly typed AE equality before applying .mono.
For real norms, give a separately typed nonnegativity proof for archMomentWeight e before rw Real.norm_of_nonneg; loose implicit expressions failed rewriting.
Tendsto of a defined CLM family may not match by simpa alone; change the target to its explicit pointwise algebra and use Function.comp_def.
For a multiplier identity he: multiplier1 u=u, use rw [he] at h rather than he ▸ h, which rewrites other occurrences of u in the target.
No heartbeat settings were changed. Build logs contain extensive replayed unrelated warnings; redirect and inspect only target output/errors.
