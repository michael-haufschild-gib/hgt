# EDQ Möbius current escape — verified

Goal ACTIVE: unconditional Lean RH proof/falsification through Euler deletion → exact complex zero balance → signed arithmetic separation → off-line exclusion → RH. RH NOT proved/falsified. Previous mixed-current turn classified progress, revalidated from current source/frontier/STATUS. This turn constructs the actual growing Möbius family and proves unit endpoint defect plus cofinal current escape. No external blocker, no route retired.

## Verified new leaf
formal/GaloisForLFunctions/RHTower/EulerDeletionMobiusCurrentEscape.lean (250 lines).
Namespace RHTower.DeletionMobiusCurrent.
Imports EulerDeletionMixedCurrentGram and DeningerMobiusHarmonicZero.
14 public theorems, 5 definitions, 5 private helpers.

coefficient p=(mu(p+1):Complex)/(p+1).
sourcePath N s=mixedPath(range N) coefficient s.
sourcePrefix N s K=ordinary endpoint of sourcePath at K.
sourceCurrent N s=full quadraticCurrent(range N) coefficient s.
energyHead N s K=sum n<K mixedEnergy(range N) coefficient s n.
Index0 (modulus1) is harmless zero path; all full mixed results allow it for bounds.

Public:
- source_coefficient_initial line71: n+1≤N ⇒ sum p<N c_p*a_p(n)=cast H_N - (if n=0 then1else0).
- sourcePath_initial line85: same coefficient times literal kernel.
- sourcePrefix_initial line96: 0<K≤N ⇒ P_N(s,K)=H_N * sum n<K kernel s n -1.
- sourcePrefix_tendsto line116: every complex s and fixed K>0, P_N(s,K)→-1 as N→∞.
- sourcePrefix_zero_endpoint line125: every actual zero rho and fixed N, P_N(rho,K)→0 as K→∞; uses old explicit combined tail bound.
- endpoint_limit_defect line134: both previous limits retained, with their different nonzero unit boundary. No limit exchange.
- energyHead_tendsto line148: any s, fixedK, head_N→weight s K-1=(K+1)^(2Re(s)-1)-1.
- sourceCurrent_partner line157: full complex current at 1-star s is minus current at s, same coefficients.
- sourceCurrent_tendsto_atTop line167: at actual right-half zero, real current tends+∞.
- abs_sourceCurrent_tendsto_atTop line184: at any actual off-line zero, absolute real current tends+∞, using exact reflection for left side.
- sourceCurrent_bounded_iff line199: at actual zero existsB forallN absReQ_N≤B iff critical location.
- sourceCurrent_cofinally_bounded_iff line212: weaker existsB forallK existsN≥K absReQ_N≤B iff critical location.
- riemannHypothesis_iff_mobius_current_bounded line228.
- riemannHypothesis_iff_mobius_current_cofinally_bounded line239, exact Mathlib RH. Bound and cofinal subsequence may depend on rho; no uniform bound across zeros required.

At actual zeros Q is real by old mixed-current Gram theorem. New theorem statements explicitly bound abs of its real part.
No off-line zero is asserted to exist. The bounded-return producer is still OPEN; the equivalences are not RH proofs.

## Proof
Finite divisor inversion gives H_N-delta_unit; do not rearrange conditional infinite mu/n series.
Corpus proves ordinary H_N→0 through Mertens saving plus Abel convergence and reciprocal-zeta pole normalization (PNT alone doesn't identify sum value).
For each positive fixedK, prefix exact formula →-1. Each fixed finiteN at actualzero endpoint→0. Thus different iterated limits.
Norm of each fixed prefix→1, so finite Gram heads telescope to weightK-1.
At a right-half zero fullQ_N≥every finite positivehead. ChooseK with weightK-1>B, then letNgrow. This proves actual current→∞. Reflection handlesleft.
Critical source current identically0 at every N even without zero premise.
Escape precludes even cofinal bounded returns, yields exact RH receivers.

## Audits COMPLETE — no reruns needed
Final API scratch /tmp/edq_mobius_api.lean session72651 exit0.
Final proof scratch /tmp/edq_mobius.lean session66016 exit0 EMPTYdiagnostics.
Copied exact scratch and one umbrella import after EulerDeletionMixedCurrentGram.
Foreground final LEAN_NUM_THREADS=1 lake build --old GaloisForLFunctions.RHTower.EulerDeletionMobiusCurrentEscape session49973 exit0. ONLY new leaf Built7.2s, graph13057cached/replayed.
New-only axiom audit /tmp/edq_mobius_axioms.lean session7971 exit0, all19public declarations only propext/Classical.choice/Quot.sound; dependencyclosure covers5private.
Repository lint ONCE session71624 exit0, formal lint passed (existing file-size warnings). Prior unrelated unwired modules were gone; this turn did not edit them.
Search-index ONCE exit0:4changed0removed,32956files402004declarations3945gaps. Exact no-refresh cofinal receiver lookup returnsline239.
Scoped whitespace/local links, exact singleumbrellaimport, equalitytocheckedscratch, forbiddendeclaration scan passed.
All3 owned scratch .lean files removed, no owned Lean/Lake process.
Logs retained /tmp/edq_mobius.{api,check,build,axioms,lint,index}.log.
No full/umbrella build, no commits/push, no subagents, no oldaxiomrechecks.

## Documentation
Positive card docs/drafts/pipeline/3-formalized/edq-mobius-current-escape.md, movedfrom1-in-progress, paper+formalcertificate+precisecompletedchecks.
Frontier CURRENT paragraph afterMixedCurrent and EDQrow established/remaining updated. Concrete remaining target is cofinal bounded return of this literal Möbiuscurrent or other independent source law.
STATUS added route-independent MUST-KEEP-THE-ENDPOINT-DEFECT; restored blank after own precedingmultiplicityentry.
No failed-route card because no route retired. Unit-defect law is positive exact classification.

## Corpus consulted
EulerDeletionMixedCurrentGram292–407 (previousverified), EulerDeletionMeanInterferenceDescent1–220 (different coefficient-mean quotient, no substitution).
DeningerMobiusHarmonic full; DeningerMobiusHarmonicZero full; DeningerHarmonicPartial definitions andtendsto.
BaezDuarteMobiusPrefixApproximation1–185 plusdeclarationsearch: raw modular approximant -sum mu(m)*(n modm)/m, exact prefix 1-A_N(n)=nH_N. Its global fullerror→0 is OPEN and actually its criticalrawerror knownfails; don'tsubstitute for ourcurrent.
Sieve.MoebiusHarmonicLogRate1–95: unconditional |M(N)|≤B N exp(-(logN)^(1/3)/108), H_N=O(log^-3); tendsto_log_mul_deningerHarmonicPartial_zero line230.
Indexed Sieve.MoebiusHarmonicArbitraryLogRate.tendsto_log_pow_mul_deningerHarmonicPartial_zero line257 (NOT readstatement yet): every fixed logarithmic power timesH_N→0.
EulerDeletionRemainderMobiusInversion22–63: private finite divisor-inversion pattern using coe_moebius_mul_coe_zeta; old absolutelyadmitted remainder inversion has nonzero boundary, differentobject.
Sieve.MertensThird1–190 read when consideringprimorials; notused. OrdinaryMöbius cutoff simpler andexact.
Broad indexed searches deletioninfinitechannels, Möbiusrecovery, chronologicalHilbert; unrelatedHilbertquotientnotused.

## Lean lessons
- tendsto_rpow_atTop is ROOT, not Real.tendsto_rpow_atTop.
- Filter.Tendsto.atTop_add_const_right/atTop_sub_const don'texist. Avoided: compose rpowatTop with natCast and Filter.tendsto_add_atTop_nat1; chooseK from eventual_gt_atTop(B+1), then linarith weightK-1>B.
- Function.comp_def must be in simp when converting composed cast/power tendsto to explicit lambdas; definitionalcongruence alone didn'telaborate.
- Nat.zero_dvd_iff doesn'texist; simp at h handleszero divisor/zero Möbius term.
- Finset.sum_range_succ' f N: sum k< N+1 f k = sum k<N f(k+1)+f0.
- range(N+1).filter(d dividesn+1)=(n+1).divisors forN≥n+1; Nat.mem_divisors givesdvdandnonzero; Nat.le_of_dvd boundsd.
- sourcePrefix must unfold sourcePrefix endpoint before applying Finset.sum_congr.
- Filter.eventually_atTop givesexistsK forallN≥K; usedforcofinalboundedcontradiction.
- APIproofs useexample:=@Name andsignaturesin/tmp, no treeaxiomprints.

## Potential next advance — NOT yet proved
Quantify escape using corpus's arbitrarylogdecay ofH_N and the already verified exact expanding-window prefixformula. ForRe rho>0, normkernel≤1, so ordinaryprefixnorm≤K; chooseK=floor((logN)^L), useH_N(logN)^L→0 to keep allprefixes1..K near-1. Then Q_N≥constant*((K+1)^(2Re rho-1)-1). By choosingL large, likely obtain divergence faster than any fixed logarithmic power atoff-linezeros and weaken remainingproducer tocofinalpolylogceiling. This is a paper/Lean task, notanestablishedclaim. Read exact arbitrarylogtheorem andsearchwholecorpus beforeusing.
The genuine missing source bound is not supplied by another rephrasing. Seek actual cumulative Möbius tail/mixed arithmetic control, keeping endpointdefect; BaezDuarte/CCM-FU completedsource comparisons may provideusefulcorpuslinks but their remainingtailbounds mustnotbeassumed.