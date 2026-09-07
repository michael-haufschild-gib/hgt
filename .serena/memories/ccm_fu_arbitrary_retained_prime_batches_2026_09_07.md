# CCM-FU arbitrary finite retained-field actual batches — CLOSED; exhaustive uniform coverage/RH OPEN

## Goal, classification and discipline
Active UNBUDGETED goal remains unconditional kernel-checked proof/falsification of RH via CCM-FU. Full chain: Guinand–Weil source → marked rectangular current → affine Suzuki checkpoints → signed curvature → prime–polar–Gamma/unit-Riesz boundary → Xi-screw Green → RH. This turn is PROGRESS: 17 new public declarations in four modules close arbitrary finite-field actual-state transport, complete energy pairing, safe prime choices, finite pool orders, simultaneous common-parent windows and unconditional growing batches including the full finite preparation budget. Do NOT mark complete/blocked. Exhaustive compatible cofinal coverage, uniform-in-field costs, PE4/PE4G/PE4C, SD1 and RH remain OPEN.

Previous closed inputs: `mem:ccm_fu_finite_retained_landau_control_2026_09_07` (37 declarations, Landau and finite clipping margins), `mem:ccm_fu_retained_source_mellin_transport_2026_09_07` (43, exact Mellin), `mem:ccm_fu_finite_retained_spectral_separation_2026_09_07` (28, surviving poles). Do NOT re-prove or re-audit those, or the 17 declarations below.

All four modules passed scratch and exact-file lake env lean checks; only four needed oleans emitted. Four unique RHTower imports wired, NO umbrella/full/dependency builds. All17 new public declarations axiom-audited ONCE: only propext/Classical.choice/Quot.sound. Global formal lint PASS (existing large-file warnings). Formal index regenerated ONCE,14changed0removed including other tasks' concurrent work. Source whitespace/paper links checked. All owned processes terminal and eight /tmp scratch/log paths removed. No numerical experiment, computed proof premise, RunPod work, subagent, commit or push. Preserve other tasks' shared edits/commits. No source edits after audit.

User: one owned foreground Lean process at a time, exact-file checks, audit only new names, no full/umbrella builds. Numerical experiments only bounded multicore RunPod ssh root@157.157.221.29 -p27094 -i~/.ssh/id_ed25519, genuinely unpredictable scientific design, download/doc/clean. No computation needed for the algebra below. scientific-method.md read again this turn; derived work remains [BRIDGE], not a replacement for RH. update_plan unavailable, Serena manual already read, task memory read and list_memories refreshed (topic filter returned{}); architecture/testing absent.

## Current authoritative docs
NEW complete certificate: docs/drafts/pipeline/3-formalized/ccm-fu-arbitrary-retained-prime-batches.md.
Updated current card: docs/drafts/pipeline/1-in-progress/ccm-fu-finite-source-cone-exhaustion.md.
Updated adaptive-prime-ceiling final arbitrary-field section; rh-current-frontier-map executive/table/detailed/open-core paragraphs; universal-law-field/STATUS.md MUST-PAY-GROWING-WITNESS-COSTS now explicitly distinguishes arbitrarily long actual bounded batches from compatible exhaustion; old finite-retained-directional-control certificate remaining gate updated. No history/diary in frontier. Paper has final validation and cleanup/index results.

## New Lean modules — all namespace RHTower
Directory formal/GaloisForLFunctions/RHTower/. Q:Finset Nat.Primes, S=Q.image(fun q:Nat.Primes=>(q:Nat)). U(M)=mobiusDivisorSelectionPrimes M={primes<M}. F(M,P,R)=mobiusDivisorSelectionFibre M P R. E(M,P)=mobiusDivisorSelectionEnergy M P. V_Q(M)=retainedPrimeFieldProfile Q M on subtype S.powerset. Norm on coordinates is SUP NORM.

### RetainedPrimeStateTransport —7 public
Imports RetainedPrimeFiniteSourceMargin and MobiusDivisorPrimeFibreInterpolation.
1 `mobiusDivisorSelectionFibre_eq_retainedProfile Q M P hcore hdis R`:
 hcore:U(M)\S⊆P, hdis:Disjoint P S, R:retainedPrimeFieldIndex Q ⇒ F(M,P,R.val)=V_Q(M)(R).
 Proof uses source sum_Icc; for d<M, pf(d)⊆U(M), so pf(d)\P=pf(d)∩S. Terminal d=M has zero channel. All coefficients kept.
2 `mobiusDivisorSelectionFibre_eq_zero_of_not_subset_retained M P S R hcore hR`:
 hcore:U(M)\S⊆P, hR:¬R⊆S ⇒F(M,P,R)=0. No hdis needed. S arbitrary FinsetNat, not only primes.
3 `retainedPrimeParentField Q M P : retainedPrimeFieldCoordinates Q` := R↦F(M,P,R.val).
4 `retainedPrimeClippedProfile Q K w` := (1-w)•V_Q(K)+w•V_Q(K+1).
5 `mobiusDivisorInterpolatedFibre_eq_retainedProfile Q M p P hcore hdis R`:
 hcore:U(M/p+1)\S⊆P ⇒ literal interpolatedFibre M p P R.val = clippedProfile Q (M/p) (divisorPrimeClipWeight M p) R.
6 `retainedPrimeClippedProfile_pairing Q z K w`: sum_R zR*clippedProfileR=(1-w)*fieldPairing Q z K+w*fieldPairing Q z(K+1).
7 `mobiusDivisorSelectionEnergy_insert_retainedProfile Q M P hp hpM hpP hpQ hQM hcore hdis`:
 pprime,p<M,p∉P,p∉S,S⊆U(M),hcore:U(M/p+1)\S⊆P,hdis:DisjointPS ⇒
 E(M,insert p P)-E(M,P)=(-2sqrtp)*ΣR:fieldIndexQ parentFieldQMP(R)*clippedProfileQ(M/p)(clipMp)(R).
 FULL energy difference. Sum over U(M).erasep powerset reduced to S.powerset because all outside child fibres zero; removed prime-packet squares cancel algebraically. No dimension energy norm conversion or discarded outside energy.

### RetainedPrimeDescentOrders —5 public
Imports new StateTransport, PartialSubsetEnergyOrder and MobiusDivisorSignedPrimeBatches.
1 `retainedPrimeFieldPairing_eq_zero_of_le_one Q z hM`: M≤1 ⇒literal pairing0.
2 `exists_retainedPrimeField_nontrivial_clip_margin Q`:
 ∃Knonempty,(∀k∈K,2≤k),∃cδ,0<c,0<δ,δ≤1,∀clip satisfying [0,δ] onK,∀z,∃k∈K,c*normz≤(1-clipk)pairingQzk+clipk pairingQz(k+1).
 Filters oldK to k≥2. Extend clipping by zero on0/1; positive norm forces nontrivial witness. Nonemptiness uses constant1 field. Handles z0 separately.
3 `exists_retainedPrimeField_prime_descent Q`:
 ∃Knonempty allk≥2,cδ positiveδ≤1,∀M P prime:Nat→Nat, S⊆U(M),DisjointPS,
 (∀k∈K,U(k+1)\S⊆P),
 (∀k∈K,(primek).Prime ∧primek<M ∧primek∉P ∧primek∉S ∧M/primek=k ∧clip(M,primek)≤δ) ⇒
 ∃k∈K,E(M,insert(primek)P)-E(M,P)≤-2sqrt(primek)*(c*norm(parentField Q M P)).
 Quantified actual descent, strict if receiving field nonzero.
4 `exists_retainedPrimeField_pool_orders Q`:
 ∃Knonempty allk≥2,δ>0δ≤1,∀M P pool:Nat→FinsetNat n,
 S⊆U(M),DisjointPS,(∀k∈K,U(k+1)\S⊆P),
 (∀k∈K,n≤(poolk).card),
 (∀k∈K∀p∈poolk,pprime∧p<M∧p∉P∧p∉S∧M/p=k∧clipMp≤δ) ⇒
 ∃l:ListNat,Nodup,length=n,toFinset⊆K.biUnion pool,∀j,E(M,P∪(l.takej).toFinset)≤E(M,P).
 Reuses exists_partialSubsetEnergyOrder. Any chosen L withcard<n leaves unusedp in every pool; choose family then actual descent in stateP∪L. Complementary-core inclusion persists, Disjoint(P∪L)S follows allpoolprimes outsideS. No separate inactive-prime hypothesis is necessary: coverage/disjointness already preserves the exact child fields.
5 `mobiusDivisorSelectionEnergy_subcore_le M P T hP hT`:
 hP:∀p∈P,pprime∧p<M;hT:T⊆P ⇒ E(M,T)≤(2:Real)^P.card*722*(M:Real)^2.
 Existing doubling bound2^T.card + complete diagonal722M² +cardmonotonicity. Covers ALL core-preparation subsets and hence every preporder.

### RetainedPrimeWindowSupply —4 public
Imports newDescentOrders and oldMobiusDivisorCoupledTwoPrimeBatches (alreadybuilt/audited).
1 `divisorPrimeClipWeight_general_quotient_window hK hb hlo hhi`:
 K,b,N,pNat,1≤K,K≤b,bN<p,p≤(b+1)N ⇒
 (b:Real)*divisorPrimeClipWeight(K*(b+1)*N)p≤2*(K:Real)*(K+1).
 Generalizes oldrestrictedK≤14 clipping estimate. Analytic gap1≤2(K+1)(sqrt(K+1)-sqrtK); exact clipping step and endpoint rationalization; no numerical values.
2 `retainedPrimeWitnessWindow A b N k` := HTGeometry.primesInIoc (b*((A/k)*N)) ((b+1)*((A/k)*N)).
3 `retainedPrimeWitnessWindow_data hk hkb hA hkA hN hp`:
 2≤k,k≤b,0<A,k∣A,1≤N,p∈window ⇒pprime∧p<A*(b+1)*N∧b<p∧(A*(b+1)*N)/p=k∧b*clip≤2k(k+1).
 Commonparentidentity usesk*(A/k)=A; all primes aboveb avoidfixedcore.
4 `eventually_retainedPrimeWitnessWindow_card_ge hA hkA hb n`:
 0<A,k∣A,1≤b ⇒eventuallyN n≤windowcard. kpositive inferredfromdivisibilityA>0.
 Uses OLD eventually_fixed_prime_window_card_ge via Nat multiplication atTop. No new PNT bound or computation.

### RetainedPrimeBoundedBatches —1 public capstone
Imports newWindowSupply.
`exists_retainedPrimeField_bounded_batches Q`:
∃B:Nat,∃P:FinsetNat,
 P=U(B)\S ∧DisjointPS ∧
 ∀n T:Nat,∃M:Nat,T≤M ∧S⊆U(M) ∧
 (∀D⊆P,E(M,D)≤2^P.card*722*M²) ∧
 ∃l:ListNat,Nodup∧length=n∧Disjoint l.toFinset(P∪S)∧
 (∀p∈l,pprime∧p<M)∧∀j,E(M,P∪(l.takej).toFinset)≤E(M,P).
 This is unconditional, no unproved existence/energy/sign/source hypothesis.
Proof chooses Kδ frompoolorders; B=K.sup id+S.sup id+2, P=U(B)\S. Chooseb≥B withbδ≥2B(B+1). A=prodK k>0. EverykdividesA. Simultaneousfinitewindowcapacity via Filter.eventually_all_finset; chooseN≥T+1, M=A(b+1)N. Window_data givesallpoolproperties, clippingbound≤δ. CorehPactive; subcorebound andpoolorders conclude. The retained S and other active primes remain unprocessed. P/budgetdependonQ, notn,T,M.

## Exact remaining frontier and next productive work
Do NOT target actual finite-state identification, prime-window supply, finitepoolorders, or fixed-fieldpreparation bounds again; all CLOSED. Only cofinal compatibility/exhaustion and uniform costs asQchanges are missing from this producer. The new result is stronger than earlier two-coordinatebatches, but not SD1. AllfiniteSexistence does not permit core-first processing throughgrowingS: old middle-singleton obstruction atparent64N² afterprocessingbelow4N stillforces energy/M²→infinity, unaffectedbyscalarreserves.

Openquantities: witnessmaxK, inversec/inverseδ, commonmultipleA, poolcapacity/preparationresources asQchanges; budget2^|P| nowexplicit. Need a genuineinterleaving strategy covering everyactiveprime before inherited nonisolatedenergy grows. Batchlength→infinity is not exhaustion; arbitrarylatecutoffsare not compatiblehistories. Supnormmargins are not Euclideanenergybounds withoutdimensioncost.

A concrete next derived cost target suggested directly by the current profile formula, NOT yetformalized: the full retained-label coordinate R=S is zero for M≤product(S), since contributingd mustcontainallprimefactorsS and terminalC_M(M)=0. Hence any finite witnessfamily detecting both signs of everycoordinate must reach beyondproduct(S); forprimeprefixS that is a primorialcost. Search corpus before proving this or the sharper maskedhomothety of the full-labelcoordinate. This is a possible intrinsic witness/preparation-cost diagnostic, not a proved no-go or a substitute for uniformcofinalconstruction. Its algebraic result is predictable by reasoning, so no RunPodexperimentforit. Ifcomputinglater, freezeagenuinelyunresolvedquantitative strategytradeoff per scientificmethod; no morequalitativefinitefieldscreening.

## Lean efficiency/API pitfalls
- Finset.sum_coe_sort S.powerset reindexesΣR∈S.powerset asfinite subtype sum.
- For profile-if subtype equality, simp[Subtype.mk.injEq] failed withNat.Primes reducibility warning. Use congr1; applypropext; constructors usingSubtype.ext he andcongrArg Subtype.val he.
- Finset.sdiff_subset_sdiff_left has an explicit Finsetargument; manualmem_sdiff proof was clearer.
- Nat atTop multiplication requires Filter.Tendsto.const_mul_atTop' hdiv tendsto_id. Trying tendsto_id.const_mul_atTop hdiv led to deterministic200000-heartbeattimeout due wrong API/inference; fixedwithoutraisingheartbeats.
- Give le_sup (f:=id) hk an explicit expected type `k≤K.sup id`; otherwiseomega treatsidkandkseparately.
- In real2^cardmonotonicity, gcongr solvescardgoalfromsubsetand leaves1≤2; norm_num closesit.
- Rename nlinarith-only variable hN to_hN toavoid unused-variablewarning.
- Allscratch/lognameswereprefix /tmp/ccm_fu_retained_... andall8removed. No liveownedLean/lakeprocesses. Audit,lint,indexsessionsallterminal.
