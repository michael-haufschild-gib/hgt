# Exact Weil pole entry handoff and discrete odd tail

GOAL ACTIVE: RH not proved/disproved. This goal turn is PROGRESS: 14 public theorems plus one definition, 3 finished leaves, exact actual boundary handoff and discrete tail criterion. No numerics, subagents, commits, full/umbrella builds. No owned live process. Previous chain: `mem:rh/pole-prime-chamber-differential-and-positivity-2026-09-06`, `mem:rh/fixed-exponential-pole-rh-criterion-2026-09-06`.

## Current proof chain
All-aperture actual pole sign |C|≤A → square-root P(T)=∫0..T(exp t−ψ(exp t)) → bounded actual unit-Riesz resolvent → mathlib RH; converse formal. Prior odd chamber comparison E''−E<0 above2 only samefloor. NOW exact cancellation includes the next integer-entry boundary and reduces every odd inequality on tail a≥2 to Qodd(a) and Qodd(log n/2) at all later integer entries. NEW exact RH equivalence retains ALL even signs, odd range0<a≤2, odd integer-entry signs above2. No endpoint sign proved. All integer entries, not only prime powers.

## Finished files (namespace RHTower)
All under formal/GaloisForLFunctions/RHTower and wired sequentially after OddPrimeChamberComparison before ThetaTiltLogDensity in RHTower.lean.
1 CCMRestrictedWeilPolePrimeEntry.lean (111 lines;5pubtheorems;no defs).
ccmWeilPoleChamberDiagonal_eq_explicit exposes original private bulk coefficients using definitional change+ring. Frozen A =2κsinh s+(−1−2M(exp2a))exp s+(2s+1+2ψ(exp2a))exp(−s)+8s sinh s+B1primitive(s).
ccmWeilPoleChamberCross_eq_explicit: Cch=κ2s+2s²+(2sinh s)²+B0primitive(s)−[T(a)+2(s−a)W(a)].
Let N=floor exp2a, n=N+1, exp2b=n. Private exact Mjump=Λn/n and ψjump=Λn, using Finset.sum_Icc_succ_top. M lowerindex2; ψ_eq_sum_Icc lowerindex0 (important!). T(b)=T(a)+2(b−a)W(a), since entering tent zero by log n=2b. expb/n=exp(−b), so diagonal entering atom alsozero.
Public ccmWeilPoleDiagonal_eq_chamber_at_next_entry and ccmWeilPoleCross_eq_chamber_at_next_entry identify ACTUAL entries atb with incoming frozenmodela despitefloorjump.
ccmWeilOddPole_eq_chamber_at_next_entry actualQodd(b)=Ech_a(b).

2 CCMRestrictedWeilOddPrimeEntryComparison.lean (147 lines;3pubtheorems).
ccmWeilOddPole_eq_chamber_until_next_entry: a≤b, exp2b≤floor exp2a+1 ⇒actualQodd(b)=Ech_a(b); split strictcutoff/equalityboundary.
ccmWeilOddPole_pos_before_next_entry: 2≤a, exp2b≤floor exp2a+1, a<c<b, actualQodd(a),Qodd(b)≥0 ⇒actualQodd(c)>0.
ccmWeilOddPole_nonneg_until_next_entry_iff_endpoints: 2≤a≤b and sameupperbound ⇒Qodd≥0wholeIcc iffendpointpair≥0.
Proof: original compactminimum and localderivative argument, derivative negativityonlyinterior (samefloor via Nat.floor_eq_iff); positive-radius frozenmodel continuous onclosedinterval; newactualhandoffatrightendpoint. Private helper proofs follow prior module, not generic fixedstate theorem.

3 CCMRestrictedWeilOddIntegerEntryCriterion.lean (136 lines;6pubtheorems+1def).
ccmWeilIntegerEntry (n:ℕ)(hn:2≤n): SuzukiPositiveAperture :=⟨log n/2,positive⟩.
exp_two_mul_ccmWeilIntegerEntry and floor_exp_two_mul_ccmWeilIntegerEntry exact n.
ccmWeilOddPole_nonneg_tail_iff_integer_entries (a)(ha:2≤a): [∀c≥a,Qodd(c)≥0] iff [Qodd(a)≥0 ∧∀n hn,a≤entryn→Qodd(entryn)≥0].
Proof given c: N=floor exp2c≥2 from exp tangent, l=entryN≤c<r=entry(N+1). Ifa≤l apply[l,r]; else a liesinsamecutoffN andapply[a,r]. Boundary equalityliteral, no limiting gap.
ccmWeilOddPole_nonneg_iff_small_and_integer_entries: allodd iffodd0<a≤2 andinteger-entryoddabove2.
riemannHypothesis_iff_even_and_odd_integer_entries: RH iffalleven ∧smallodd ∧entryoddabove2. Uses actual existing riemannHypothesis_iff_parityPole_nonneg.
ccmWeilOddPole_negative_tail_iff_integer_entry: ∃negativeactualtailwitness iffnegativestart ORnegativeinteger-entry. Negationofexacttailcriterion, not genericfirstfailureassumption.

## Verification DONE
Scratch /tmp/hgt-pole-entry.5i0d6Q/{API,API2,Entry,Comparison,Endpoints,Witness,Axioms}.lean. Proof scratches allPASSforeground lake env lean. API probes had expected failed unknown names; corrected APIs all in passing proofs. 3 final named leaf builds PASS (~8.7/12/10s), criterion final rebuildincludesWitness. All15public axiomaudits EXACT[propext,Classical.choice,Quot.sound]. Formal lintPASS existinglargefilewarnings,gitdiff--checkPASS. Researchindexrefreshed queryinteger entry findsnewdeclarations. NoLean/Lakeprocess atfinalinspection. No numerical experiments/Runpod/backgroundbuild/agent/commit. Sharedtreehas unrelatededits;preserve.

## Docs DONE
New formalcard docs/drafts/pipeline/3-formalized/weil-pole-prime-entry-comparison.md: fullpaperproof,conjecture/proofloop,scope,allverificationfinished.
Transient1-in-progress/weil-pole-prime-entry-comparison.md deleted (ourscreatedthisturn).
Mainactive1-in-progress/weil-two-pole-compression-prime-error.md nowstateshandoffclosed,tailintegercriterion,andactualentriesopen.
FrontierRouteO paragraphFull odd-source propagation... updatedCURRENTstateonly. UniversalSTATUS Cannotpropagatepositivityfromnewprimeterms entry strengthenedwithexacttaildiscretization+negativewitnesslocalization. Failedpermanententrysigncardpositive survivor strengthened. Prior3-formalizedchambercardCurrentfrontierlinksupdatescopewithoutchangingoldtheorem.

## Candidate next mathematics (NOT proved)
1 Actual endpoint signs now central. Could derive exact frozen-model transition for consecutivecutoffs n=N+1 atb=.5log n. From actual formulas, expected ΔA(s)=2Λn(exp(−s)−exp(s)/n); ΔC(s)=−2Λn(1+1/n)(s−b). Thus ΔEodd(s)=4Λn[exp(−s)−exp(s)/n+(1+1/n)(s−b)], zeroatb and slopejump4Λn(1−exp(−b))²>0 iff genuineprimepower. Even slopejump expected−4Λn(1+exp(−b))². These are algebraic conjectures derived FROM THE CORPUS formulas, not yet Lean/paper-audited. Positive odd slopejumps explain why a global smooth-minimumargument acrossallcutoffs isnotautomatic; nonprimeentrieshavezerojump. A reductionfromallintegerentries toprimepowerentries needsnewproof,notclaimed.
2 Read exact statements CCMSharpPrimeWindowPrimeReduction.riemannHypothesis_of_eventually_dyadicCriticalThetaMellinErrorIncrement_upper and CCMSharpPrimeWindowSquareSampling.riemannHypothesis_of_eventually_squareThetaErrorIncrement_upper. They assume allε one-sided dyadicthetaerrorincrement≤C n^ε (latteronlysquare samples), not our logarithmicprimitive/polevalue. No connectorproved. Priorcandidate oddnonneg→one-sidedPbound→RH wouldneed actual Landau/oscillation bridge; do not assumetheseincrementtheorems apply.
3 Evenall andsmallodd remainopen. NoRHclaim,no route retirement.

## Lean pitfalls
M cutoffsumIcc2; Chebyshev.psi_eq_sum_Icc isIcc0. Finset.sum_Icc_succ_top (hab:a≤b+1)(f) exact finitejump. Nat.floor_eq_iff needs expnonneg; Nat.lt_floor_add_one givesexp<N+1. `change` expands private chamber defs without inaccessibleprivate names, thenring handlesassociation. Normalize div_eq_mul_inv atgoalAND cancellationhypothesis before nlinarith. `le_of_not_ge` alreadyreturns≤; adding.leinvalid. Subtype equality endpoints: `subst c;exact hQa` works where simpa only[hca] usinghQa failed with dependent source type. `push_neg` deprecated; `push Not at h` turnsnotandintop→notq, then `simpa only[imp_iff_not_or,not_le] using h` obtainsnegativewitnessdisjunction. All buildcommands cwdformal (onefailedrootcwdbuildproducednoconfig,rerunproperly).