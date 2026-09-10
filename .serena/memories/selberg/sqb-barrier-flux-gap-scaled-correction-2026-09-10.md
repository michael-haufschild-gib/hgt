SQB74 current state: progress, RH OPEN. Rank-seven integral/global correction compatibility and all-rank propagation OPEN. Frontier map read-only and not edited; universal ledger untouched. No computations, Git, launch.sh, or subagents. One foreground Lean/Lake at a time.

Two new installed/wired/audited modules in formal/GaloisForLFunctions/RHTower, namespace RHTower.ThetaCuspModularRatio:
1. ThetaCuspModularBarrierFlux.lean.
B=barrierDefect=u/3-J>=0; amp=sourceAmplitude=H*t/12; Psi=barrierMass=amp²*B; Q_a=barrierFlux a=x*sinh(2ax)*Psi.
dBarrierMass: Psi'=amp²[t(k+1/3)(4/3-k)+u(5/3-2k)B].
center bound gives k>=4x/3+2/3 and u(2k-5/3)>=8x-1.
barrierMass_pos: Psi>0 for x>=2/3, by excluding B=0 local minimum with negative derivative.
barrierMass_deriv_upper: Psi'<=-(8x-1)Psi there.
barrierFlux_deriv_upper: Q'_a<=-(2/9)sinh(2ax)Psi for 0<=a<=1/2,x>=2/3.
barrierFlux_deriv_neg line157: strict if a>0.
barrierMass_le_source_sq: 0<=Psi<=Phi² on x>=0.
barrierFlux_tendsto_zero: squeezed by polynomial times squared tilted Schwartz source.
integrableOn_barrierFlux_deriv: compact continuity + nonpositive tail derivative + limit.
integral_barrierFlux_deriv line260: integral_0^infty Q'_a=0 for 0<=a<1/2.
barrierReserve=Psi/(18x); positive on x>=2/3.
barrierReserve_weighted_lower line274: 4x sinh(2ax)*reserve<=-Q'_a on that ray.
barrierRepairedMatrix K x: literal native even Hankel4, last entry plus L*G+K*reserve, L=10^12.
barrierRepairedMatrix_det: det=D_L+K*reserve*det(nativeEvenHead).
exists_barrierRepairedMatrix_posDef_on_upper_ray line323: EXISTS ONE K>0 such that matrix PD for ALL x>=2/3. Proof compact max of -D_L/(reserve*headDet) on [2/3,6/5], plus existing strict native compensated tail beyond6/5.
CRITICAL SCOPE: reserve lower comparison to actual -Q' only on x>=2/3. Do NOT identify this lower source matrix with zero-flux correction globally. Exact inner correction cost integral_0^(2/3)(-KQ')=-KQ(2/3); outer gain same. Compactness-selected K gives NO bound on inner cost. Global rank7 sign still OPEN.
Scratch /tmp/sqb74_barrier_flux.lean passed; capstones flux strict/zero integral/upper-ray matrix use only propext,Classical.choice,Quot.sound. Final lake build GaloisForLFunctions.RHTower.ThetaCuspModularBarrierFlux passed 56s/2jobs in /tmp/sqb74-barrier-flux-leaf-audit (actual source/cached deps).

2. ThetaCuspModularGapScaledBarrier.lean.
T=t*(k+1/3), V=gapScaledDefect=B-T/12.
Exact V'=2u(k+2/3)V+(T/6)[8-2(3-u)k+2u/3-J].
kineticGap_lt gives (3-u)k<19/5; J<=u/3 makes bracket STRICTLY POSITIVE everywhere.
V>0 would persist by derivative fencing and grow at fixed positive rate on complete ray, contradict V<=B<=1. Hence V<=0; local max excludes equality at x>0, V0<0.
barrierDefect_lt_gap line128: B<T/12.
normalized_barrierDefect_bounds line151: 0<=B/T<1/12 for all x>=0.
Scratch /tmp/sqb74_gap_scaled_barrier.lean passed, both capstone axiom audits standard only.
Final lake build GaloisForLFunctions.RHTower.ThetaCuspModularGapScaledBarrier passed16s/2jobs in /tmp/sqb74-gap-scaled-barrier-leaf-audit.
Both imports exactly once RHTower.lean lines16261-16262 at check. Global formal lint PASSED /tmp/sqb74_formal_lint.txt after both installed. All owned Lean/Lake/search/lint handles terminal/collected.

Current card docs/drafts/pipeline/1-in-progress/sqb-native-spectral-source-comparison.md updated exact positive construction, audits, remaining inner budget. Existing SQB73 determinant+reserve comparison and integrated Schur variance alternative still open.

Next attack: control inner correction cost, possibly normalize profile to REMOVE unnecessary small t factor:
U=B/T in [0,1/12); analytical (NOT Lean yet):
U'=4/3-k+[4u(k+1/3)-2J]U.
N=amp² U, N'=amp²[4/3-k+(5u/3-2J)U].
N<=amp²/12; unlike Psi=amp²B, N doesn't include extra small gap factor in reserve. Need actual flux sign and compatible GLOBAL coefficient; do not merely prove another arbitrary compact repair or generic receiver. Previous original finite compact gap-coefficient queue remains stopped; don't redo huge Horner tables.

Searches inspected all main sections + obligations, all retrieval views incl method:
 /tmp/sqb74_dissipation_search.json (factorization dissipation OR), multiplier_search (mechanism total derivative), schwartz_search (Schwartz polynomial OR), virial_search (single word). Partial/stale source/compiler; first malformed judging/interrupted retrieval/local rerankdeadline, second deadline, Schwartz interrupted; virial noerrors. No absence conclusions. Most virial/Stein/PSD receivers retain energy/moment/positivity premises. Actual flux admission instead used mathlib integrableOn_Ioi_deriv_of_nonpos' and theta tilted Schwartz domination. Relevant source theorem names verified via scratch.
Own arxiv term metastability, direct recent-sorted search. Read https://arxiv.org/html/2607.20882v1 (Eyring–Kramers third-order Langevin), intro and sections3.1/flatness mechanism: unstable dual coordinate via unique positive cubic root, exact weak current until controlled localization. No theta join/no stochastic/small-noise/gaussian premise imported. Card citation ~80words. Original requested2607.08139 read earlier.