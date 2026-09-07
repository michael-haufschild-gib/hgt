# CCM-FU: complete actual quotient subpool orders after arbitrary retained states

Goal ACTIVE, unbudgeted. RH/SD1, all-cutoff two-prime ceiling, middle quotient profiles and globally bounded growing schedule remain OPEN. This turn is PROGRESS: 11 new verified theorems and 5 source definitions (16 public declarations), 2 new leaves. Do not mark goal complete or blocked for the remaining mathematical difficulty.

## Rules and current process state
One foreground Lean/lake process per agent; lake env lean only, no full/umbrella/dependency rebuilds. Only needed new oleans. Audit ONLY new declarations ONCE. Preserve extensive unrelated shared-tree work. No subagents/commit/push authorized.
All own work is stopped and checked. Owned scratch files removed:
- /tmp/ccm_fu_window_order_tools.lean
- /tmp/ccm_fu_window_packets.lean
- /tmp/ccm_fu_window_axioms.lean
Final strict ps executable snapshot: ZERO lean/lake. No live owned handles.

## Full proof chain / current bottleneck
Guinand–Weil source -> marked rectangular current -> affine Suzuki checkpoints -> signed curvature -> prime–polar–Gamma/unit-Riesz boundary -> Xi-screw Green -> RH.
The new result reduces every selected same-quotient prime subpool after arbitrary P to THREE PREDETERMINED source endpoint energies. It does not bound those values by E_empty. Global subpool choices and endpoint estimates remain the arithmetic bottleneck.

## New leaf 1 (147 lines)
formal/GaloisForLFunctions/RHTower/AffineFieldSubsetOrder.lean
Imports SignedScalarMergeOrder. Three public theorems:
1. exists_increasingMarginalSubsetOrder:
   For F on subsets U, if insertion marginals increase with processed subset,
   exists distinct complete list of U with every prefix F <=max(F_empty,F_U).
   Strong induction: contracting first move if available; otherwise positive initial marginals plus monotonicity make all subsequent moves increasing and final bounds every subset.
2. affineField_inner_nonneg_of_transverse_product:
   Finite fields A,D; if <A+tD,D>*<A+uD,D>>=0 then <A+tD,A+uD>>=0.
   H=sumA²,C=sumAD,Q=sumD², C²<=HQ. Q*Gram-projprod=HQ-C².
   Q0 handled by C0 from Cauchy. No dimension/sign premise.
3. exists_twoBlockSubsetOrder:
   Fixed disjoint A,B with endpoint-bounded complete orders (second starts at A) concatenate under max(F_empty,F_A,F_AunionB).
   A is fixed input; no existentially chosen peak.

## New leaf 2 (295 lines)
formal/GaloisForLFunctions/RHTower/MobiusDivisorQuotientWindowOrder.lean
Imports MobiusDivisorNonemptyEnergy and new AffineFieldSubsetOrder.
Five public definitions:
- mobiusDivisorPrimePacket M P p R = -sqrt(p)*mobiusDivisorInterpolatedFibre M p P R.
- mobiusDivisorPrimePacketOverlap M P p q = sum over (selectionPrimes M).powerset of packet_p(R)*packet_q(R).
- mobiusDivisorQuotientWindowPrimes M N P = (selectionPrimes M minus P).filter(p => M/p=N and N+1<=p).
- mobiusDivisorQuotientTransverse M N P p = sum_R (F_N(P,R)+w_p*(F_(N+1)-F_N)(P,R))*(F_(N+1)-F_N)(P,R).
- mobiusDivisorQuotientPositivePart M N P U = U.filter(p => transverse>=0).
  CRITICAL: this explicitly fixes separator from source BEFORE ordering. Never weaken final statement to exists unspecified separator: that would merely allow choosing the path maximum, a tautology.

Eight public theorems:
1. mobiusDivisorSelectionFibre_union_inactive:
   If all p in L >=N, F_N(P unionL,R)=F_N(P,R). Direct source-support proof, all labels.
2. mobiusDivisorPrimePacket_union_inactive:
   Fixed quotient M/q=N and all p in L >=N+1 make packet_q unchanged under P unionL.
3. mobiusDivisorSelectionEnergy_window_marginal:
   For q available, qPrime,q<M,qNotP,qNotL,M/q=N,q>=N+1;
   all p in L prime,freefromP,M/p=N,p>=N+1,
   E(P union insertqL)-E(P unionL)
   =2 sum_R F_M(P,R)*packet_q(R)+2 sum_pInL PacketOverlap(P,p,q).
   Exact full signed source. Extends erase-q label sum using packet support;
   source at disjoint labels is F_P+sum packets, other-label product vanishes.
4. mobiusDivisorPrimePacketOverlap_union_inactive: both fixed-quotient packet overlaps unchanged throughout window processing.
5. mobiusDivisorPrimePacketOverlap_nonneg_of_transverse_product:
   If p,q share quotientN and their actual transverse product>=0, complete signed overlap>=0.
   Exact packet=-sqrtp*(A+w_pD), so reflected factors multiply nonnegatively.
6. exists_mobiusDivisorAcuteQuotientWindowOrder:
   For any finite U satisfying window constraints and pairwise overlap>=0,
   complete distinct prime order after arbitrary P stays below max(E_P,E_PunionU).
   Exact marginal + sum monotonicity feed generic increasing-marginal theorem.
7. exists_mobiusDivisorQuotientSubwindowOrder:
   For ANY U subset canonical WindowPrimes(M,N,P), exists complete distinct list U
   with EVERY prefix <=max(E_P,max(E_(P union PositivePart(M,N,P,U)),E_(P unionU))).
   NO sign assumption. PositivePart fixed by source. Split U by transverse>=0 vs<0;
   both internal Gram kernels nonnegative. Second kernel unchanged after firstpart;
   apply two complete endpoint orders and concatenate.
8. exists_mobiusDivisorQuotientWindowOrder:
   Same fixed-separator result for ENTIRE canonical WindowPrimes, inputs only M,N,P,
   no unproved arithmetic premise.

Support interpretation: p>=N+1 and M/p=N -> M<p(N+1)<=pq, so no active coefficient contains two pool primes. Small fields at N,N+1 stay fixed. P is arbitrary, including retained sign changes. Arbitrary SUBPOOLS are essential: existing late-mass capacity still forbids exhausting required late mass in a fixed number of uniformly bounded blocks.

## Verification COMPLETE for new work — do not repeat old audits
Both full scratch proofs and exact leaves passed lake env lean.
Only TWO required new oleans emitted via -o (base for source, source for new axiom scratch).
Both imports wired once in RHTower umbrella; NO umbrella/full/dependency builds.
All 16 new public declarations audited ONCE: only propext,Classical.choice,Quot.sound.
No sorryAx, Lean.ofReduceBool, added axioms or numerical certificates. No diagnostic/experiment run.
Index refreshed once (reported13changed0removed due shared work).
New-file whitespace, new card links, added references, both imports, scoped git diff --check PASS.
A blank trailing line at STATUS EOF was trimmed for scoped whitespace check.

GLOBAL LINT IS NOT GREEN:
scripts/formal_tools.py lint reports 11 unwired modules elsewhere:
RHTower.ThetaCuspEvenCompactCorrection, ThetaCuspEvenCompactState;
HTGeometry.PolynomialODEEvenCompactMomentOne, MomentTwo, MomentZero, Quartic,
ReflectedTwelve, SourceEleven, SourceScalars, SourceTwelve, UnitCoordinates.
Also132existinglargefilewarnings. Neither own newleaf amongerrors.
Those files are other shared-tree work and were NOT modified. Final read-only rg found no matching direct umbrella imports yet. Do not claim global lint passed; do not wire/audit unrelated incomplete work.

## Docs
Promoted own stage1 card to:
docs/drafts/pipeline/3-formalized/ccm-fu-quotient-window-orders.md
Complete source-preserving paper proof, explicit separator, verification, global lint limitation.
Updated current CCM-FU row+detailedparagraph in rh-current-frontier-map.md;
ccm-fu-adaptive-prime-ceiling.md; mobius-divisor-source-diagonal-dominance.md.
Added route-independent MUST-SOURCE-FIXED-SEPARATORS in universal-law-field/STATUS.md:
source-defined separator required, unspecified path maximum supplies no control;
fixed-endpoint ordering is distinct from bounding those endpoint values.

## Next direction (not yet proved; research before code)
Need arithmetic bounds for the predetermined separator/final states and globally compatible subpool choices.
The exact marginal/packet formulas expose a possible further compression: within fixed quotient,
sqrt(p)*w_p=(sqrt(M)-sqrt(p)*sqrt(N))/(sqrt(N+1)-sqrt(N)).
Thus copied packet vectors are affine in sqrt(p), with fixed source fields; a block energy should
compress to card(U), sum sqrt(p), sum p and source Gram/mixed coefficients, retaining removed packet squares.
The source transverse coordinate is affine in w_p; w_p decreases with p within the quotient window,
so the fixed separator may be a contiguous prime subinterval. These refinements are NOT formalized or audited.
Any such next work must help bound actual endpoint energies, not merely rename the unresolved SD1 condition.

Previous memory: mem:ccm_fu_two_channel_initial_blocks_and_source_supply_2026_09_07.
