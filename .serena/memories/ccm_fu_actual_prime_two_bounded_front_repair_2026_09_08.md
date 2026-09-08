# Actual prime-two repair with bounded remaining front — progress; RH goal ACTIVE

This goal turn made progress: two new declarations kernel-closed and an actual batch containing small prime2 is now produced. RH NOT proved/falsified; do not mark goal complete/blocked for difficulty. Full chain: actual divisor source → renewable signed reserve → exhaustive prime selection → uniform signed Abel bound → RH. Next hard target is preparing/propagating a front with several unresolved small primes or growing quotient bound, not re-proving finite source geometry.

## Current authoritative files
- docs/drafts/pipeline/3-formalized/ccm-fu-two-bounded-front-repair.md: complete paper proof and exact statement with arbitrary fixed J.
- docs/drafts/pipeline/1-in-progress/ccm-fu-inherited-debt-source-cycles.md: updated current bridge state.
- docs/drafts/pipeline/3-formalized/ccm-fu-prescribed-window-repair.md: previous macroscopic producer, now links prime2 closure case.
- FRONTIER MAP READ ONLY, despite original goal replay. No edits by us. STATUS unchanged; no new route-independent entry warranted. Shared worktree changes/commits happened externally, including commits of our files; no commits/pushes/subagents by us. Preserve external changes.

## Diagnostic, not a Lean premise
Read docs/meta/scientific-method.md and froze one BRIDGE diagnostic at computations/ccm-fu-prepared-two-envelope-2026-09-08/README.md. Enumerated EVERY cutoff16..96 and EVERY P containing{3,5,7,11,13} excluding2: 3,185,446 states. Full exact-in-structure subset energies computed via sparse XOR autocorrelation followed by subset zeta transform, no random sampling. Only RunPod root@157.157.221.29 port27094 key~/.ssh/id_ed25519. Eight NumPy workers, one numerical-library thread each, 50s internal/60s external limits. Finished0.377s. 526 numerical failures of Ψ(P+2)≤Ψ(P); no scanned originally-admitted state violated ORIGINAL DIAGONAL budget after2.
First failure M84,P=P0: currentenergy3.1722471458280252812→3.0649666689233850869 decreases; fullenvelope3.9578210987596731863→4.0195065227018060691 increases through successor17. 80decimal independent reconstruction confirms excess0.06168542394213288, with both entire successor lists, all signedfibres and all immediate repair choices saved. Selecting offending17 worsens envelope;23 and several larger primes restore parent envelope. Numerical witness is NOT formally proved and must not become proof premise. Script/output downloaded+documented; scriptSHA1e86bbf78bbd71583706afcd31f99d54b47951f446cfc6fee05c87a42b189ec4, summarySHAe92f3d2f95fe82f8c6fa029756adea504ef5812a6779d2fcee731013bdb3da3c. Remote/tmp/ccm-prepared-two-UvoLxo removed, all handles terminal. No expanded/repeated scan.

## New general transport theorem
formal/GaloisForLFunctions/RHTower/MobiusDivisorRemainingFrontTransport.lean (~31lines):
`mobiusDivisorSuccessorEnvelope_insert_le_remaining_quotient (M K) P hp hpM hpP hfront`
where hfront: ∀q∈selectionPrimesM\insertpP, M/q≤K.
Conclusion Ψ(M,insertpP)≤Ψ(M,P)+(6/5)*(K:ℝ)*sqrt(M*Ψ(M,P)).
This handles ANY prescribedprimep; its own quotient is unrestricted. Proof uses currentQ(P+p)≤oldΨ by definition, then charges each newqsuccessor to q's quotient via existing abs_mobiusDivisorSelectionEnergy_insert_le_quotient. No core, sign, overlap, or RH premise in this general local law beyond stated availability/front bounds. This complements existing transport charged to p's own quotient; no need re-prove a min-of-two wrapper.

## Actual prime2 producer
Appended to EXISTING formal/GaloisForLFunctions/RHTower/MobiusDivisorPrescribedWindowRepair.lean (aroundline334; file ~470lines). Uses its private source_window_geometry, packet and repair_error_budget; new importRemainingFrontTransport. Serena find_symbol refused ignored Lean path, so used read-verified scratch/appending.
`exists_mobiusDivisor_two_bounded_front_repair`:
∃fixedb≥15,∀J:ℕ,∀C>0,∃A>0,eventuallyN, M=14(b+1)N:
∀P⊇P0,2∉P, all sourcewindowsW (quotients2,7,14) fresh, Ψ(M,P)≤CM²,
(∀q∈selectionPrimesM\insert2P, M/q≤J) →
∃L,2∈L,L⊆insert2W,|L|=ceil(A√M)+1, Ψ(M,P∪L)+M≤Ψ(M,P).
A and threshold depend J,C, independentP; P may grow withN. M/2 unbounded. J fixed BEFORE N; choosing J=M cannot be justified uniformly. J<14 is vacuous with nonempty fresh14window, but statement valid; meaningful cases J≥14.

Mechanism: E=ΨP,E'=Ψ(P+2). General transport gives E'≤E+(6/5)J√M√E≤E+F√C M√M, F=2(J+1). Thus E'≤C'M² for C'=C+F√C. Existing two-coordinate sourcegeometry at PRE-insertionP supplies bounds9, marginc>0, bothsquarefloord>0. Select n distinct sourceprimes with zero initial displacement and normalized absolute coordinate sum≤H=2(81/c+9). At P'=insert2P exactchildfoldI0'=I0+I2,I2'=0, so physical Z=√M(x+y), |Z|≤H√M and both reserves collapse toT=∑p(I0+I2)²≥dnM. All selectedp≥15, child≤15, hence mutuallyinactive. Apply full approximate envelope law atP'. Set B=(2√C'H+H²+1)/(d/2),D=4(J+1)√C/d,A=B+D,n=ceil(A√M). Half dnM pays receivingerror+M via oldprivate repair_error_budget; otherhalf pays E'−E. Capacityκ−1≥A√M eventually supplies n. L=insert2S cardinaln+1. This is actual prime-batch production, not exact real circuit weights.

## What remains
This closes prime2 as sole exceptional small prime once all OTHER remaining quotients have a fixed bound. Does not prepare that front while preserving a uniform energy budget, handle several unresolved smallprimes/overlappingchildren, replenish used windows, or provide exhaustive order/globalAbelestimate. Previous macroscopic producer still valid; untouched-window premise prevents naive iteration. No pointwise monotonicity claim for inserting2 alone survives diagnostic. Source2,7,14 negativecovariance still allows merged-square reserve; positive2,11,15 debtcircuit available separately.

## Verification / discipline
Both newpublicdeclarations audited ONCE, each only propext,Classical.choice,Quot.sound. No old6/18 axioms re-audited. Bothfinalexactleafemissions passed WITHOUTwarnings, including arbitraryfixedJ generalization. NewleafwiredexplicitlyRHTower; neverbuiltumbrella. Indexrefreshed. Global lint --check-generated: six unrelated unwired Coppo modules (FockRotation,JosephsonPotential,KerrPhaseGeometry,NonlocalNoise,PartnerEigenspaces,SSH) and3staleindexes from concurrent work; no proofdebt/RHTowererrors. Do not fix others' unfinished modules. Known lake build packaging audit expands broad stale prerequisites; do NOT retry its preflight/full/umbrella builds, reportpending. Allownedlocal/remotehandles terminal and scratchfilescleaned afteraudit. Keepneededoleans. One ownedforegroundLeanprocess atatime; checkterminalexit BEFORE nextLean. OnlyfutureNEWaxioms audits. No mandatorynewcomputation; ifneeded onlyRunPod, frozen surprisingdecision, multicore,timebounds,download/cleanup.

## Lean notes
Use spacesafter≤/< toavoidMatroidtoken. Cast floorquotient as((M/p:ℕ):ℝ). `add_le_add_left` is shadowed in this imported namespace; use explicitcalc/linarith toavoidorientation surprises. `norm_num only[Nat.cast_ofNat]` may reduce(6/5)*14 to84/5, so changegoalmustmatch. `simp only[zero_pow]` doesnotresolve0² here; use `zero_pow (by norm_num : (2:ℕ)≠0)`. field_simp for front-payment identity leaves4=2²; norm_num closes. Existing inherited sourcegeometry private in samefile, avoidduplicating it. See mem:ccm_fu_actual_prescribed_window_repair_2026_09_08 and mem:ccm_fu_inherited_two_cost_positive_source_cycle_2026_09_08 for priorclosedpieces.