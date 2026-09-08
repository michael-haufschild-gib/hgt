# CCM-FU: every-order coarea obstruction and exact correction

RH goal ACTIVE, unachieved. Frontier map READ ONLY. No computations run: obstruction is derived exactly from corpus source laws. Do not return to optimizing the uncorrected maximum-cell coarea envelope; it is now formally impossible for EVERY complete one-index order, not merely greedy or bounded-block orders.

## Main result
Let F_R be actual signed fibre mass, A_R original absolute fibre mass; f=F_empty, a=A_empty, K=sum_nonempty F²/A, H=f²+aK. L=mobiusDivisorActiveLatePrimes M, b_p=|C_p|, T=sum_L b_p=mobiusDivisorLatePrimeMass M. Define t(P)=sum_(L∩P)b_p and r(P)=sum_(L\P)b_p. New unconditional source proofs: t+r=T, a≥t, K≥r, H≥t*r. Consumed source absolute mass cannot cancel; remaining late singleton coarea equals b_p exactly.

For any P:Nat→Finset Nat, q:Nat→Nat, k, with P0 disjoint L, L⊆Pk, and P(n+1)=insert(q n)(Pn) for n<k, t crosses from0 toT with increments≤D=(3/5)sqrt M. A sharp generic prefix lemma gives some n≤k with t_n(T−t_n)≥(T²−D²)/4. Hence H(Pn)≥(T²−(9/25)M)/4. Existing T(4N)/(4N)→∞ gives: for every fixed C, eventually every such complete order has H>C(4N)² at some prefix. Permits arbitrary small/middle interleaving, arbitrarily many late blocks, repeated/nonprime indices. Starting empty is included. Does NOT rule out treating a giant simultaneous batch while omitting all internal prefixes, and does NOT refute raw Q/RH.

B(P)=max_R A_R * sum_all F²/A is now defined as mobiusDivisorCoareaMassEnvelope via Finset.sup'. Proved H≤B and eventual every-order B>C M². Definitive exclusion of uniform quadratic uncorrected coarea envelope.

## Positive survivor
Define mixed labels=all nonempty labels minus singleton labels of L\P. Kmixed=K−r equals exactly sum_mixed F²/A and is nonnegative. Elate=sum_(L\P) C_p². Hcorr=f²+a*Kmixed+Elate=H−a*r+Elate. Exact Q=f²+Elate+sum_mixed F². Under dominance A_R≤a for every MIXED label only, Q≤Hcorr. No need head domination over isolated late singletons. Elate≤722 M² unconditionally. The restored diagonal preserves actual squared source size and removes artificial t*r comparison loss.

Fresh active late prime p of mass b preserves Kmixed; Hcorr'−Hcorr=b*(Kmixed−2f). Entire fresh active late block L of total mass u and square reserve R=sum C_p² satisfies Kmixed unchanged and Hcorr(P∪L)−Hcorr(P)=u*(Kmixed(P)−2f(P))+u²−R. Receiving-head square and removed diagonal remain explicit. Uniform control of Hcorr or Q still unproved. Next hard target: quantitative mixed-cell/head control; do not merely optimize uncorrected g (prior monotone slope cannot rescue impossible B).

## Files and theorem API
Card docs/drafts/pipeline/5-failed/ccm-fu-coarea-all-orders-mass-split.md: full dependency-closed paper proof, formal links, no-go closure, validation. Old ccm-fu-coarea-mass-envelope.md updated to point to every-order obstruction. STATUS has one route-independent entry about consumed/remaining comparison costs. Frontier map never edited here.

Three new wired leaves (namespace RHTower):
1 MobiusDivisorCoareaMassSplit.lean (8 public theorems,2defs):
abs_mobiusDivisorDilationChannel_activeLate; mobiusDivisorConsumed_add_remainingLateMass; mobiusDivisorConsumedLateMass_le_headMass; mobiusDivisorCoarea_activeLate_singleton; mobiusDivisorRemainingLateMass_le_nonemptyCoarea; mobiusDivisorCoareaHeadAction_ge_late_mass_split; mobiusDivisorConsumedLateMass_insert; mobiusDivisorConsumedLateMass_insert_step_le. Defs consumed/remaining late mass as above.
2 MobiusDivisorCoareaOrderBarrier.lean (5 public,1def): exists_prefix_mass_product_ge; exists_mobiusDivisorCoareaHeadAction_prefix_ge; eventually_every_mobiusDivisorCoarea_order_exceeds_quadratic; mobiusDivisorCoareaHeadAction_le_massEnvelope; eventually_every_mobiusDivisorCoarea_massEnvelope_exceeds_quadratic. Generic lemma takes x,T,D,k, nonneg T,D,x0=0,xk=T,upper jump bound. No monotonicity assumption needed.
3 MobiusDivisorCorrectedCoareaAction.lean (9 public,4defs): mobiusDivisorMixedCoarea_eq_sum; mobiusDivisorMixedCoarea_nonneg; mobiusDivisorCorrectedCoareaAction_eq_correction; mobiusDivisorSelectionEnergy_eq_late_mixed; mobiusDivisorSelectionEnergy_le_correctedCoareaAction; mobiusDivisorRemainingLateEnergy_le_quadratic; mobiusDivisorMixedCoarea_insert_activeLate; mobiusDivisorCorrectedCoareaAction_insert_activeLate; mobiusDivisorCorrectedCoareaAction_late_block.

## Verification / cleanup
All scratch/installed leaves lake env lean passed; only own3oleans emitted. All22newpublictheorems audited once externally: propext, Classical.choice, Quot.sound only. Do NOT repeat these or old audits. Final exactmodule lakebuilds passed one foregroundprocess at a time in byte-identical isolated temporary package exposing preexisting cache oleans via empty-glob stub packages. Only new3leaves compiled:8.5s,8.2s,6.4s. No full/umbrella/dependency source rebuild. Missing stub manifest warnings packaging only; no Lean warnings. All3imports wired, index regenerated once.
Global lint --check-generated currently failed solely for2foreignunwiredmodules SelbergOneSidedCurvatureDecay, SelbergScalarHorizontalAverage. Previous3foreignmissingimports from prior turn now resolved. Do not edit another agent's ongoing leaves. Own sourcecopies/links/imports/whitespace/debtscan passed.
Removed /tmp/ccm_mass_split_names.lean,ccm_mass_split.lean,ccm_prefix_barrier.lean,ccm_corrected_coarea.lean,ccm_coarea_split_axioms.lean,ccm_coarea_split_audit_path and isolated /var/folders/h4/zrd73pg91clb__kg1kzrlcph0000gn/T/ccm-coarea-split-audit-ny2c4wm1. All owned process sessions finished. No RunPod work needed. No commits. Shared worktree has many unrelated ongoing modifications; preserve them.

## Lean tactics worth retaining
Finset.sum_erase_add needs (s:=...) explicit in remaining_sum_insert helper; f alone leaves a finset positional parameter. rw [if_true] doesn't rewrite if p=p; use if_pos rfl or simp. For t+r=T inside a product, nlinarith alone won't multiply equality: rw [←hsum,add_sub_cancel_left] at hb then simpa only[hsum] using hb.trans hsplit. Finset.le_sup' (f:=f) (by simp) verifies head≤max.
