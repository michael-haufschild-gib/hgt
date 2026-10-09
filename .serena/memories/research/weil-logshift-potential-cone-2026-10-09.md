# Uniform asymptotic log-shift cone equals a signed-potential cone

User restriction: Lean corpus ONLY. No web, external papers, numerical experiments, heartbeat increases, full/umbrella builds, commits or pushes. Active endless corpus goal remains ACTIVE. Read objective attachment before each new goal turn. Current increment is verified progress, not overall completion.

New source: formal/GaloisForLFunctions/RHTower/WeilLogShiftPotentialCone.lean. Imports WeilLogShiftDiagonalMoment. Namespace RHTower, opens WeilExcess. Six public declarations, all leaf/kernel/axiom verified:

1. exists_uniform_truncatedDeviationPotential_error (hs : Summable fun n => |weilDeviation lam n|): exists C>=0, for ALL real L,y, |truncatedDeviationPotential lam L y - deviationPotential lam y| <= C exp(-2(L-1)). Uniform in every real shift, no positivity assumption.

2. exists_uniform_logShift_potential_error hs (epsilon>0): exists cutoff, ALL k>=cutoff, ALL m in finite panel Icc2 floor(exp2k), |Re P_k(lam,m)-2(psi(logm)-psi0)|<epsilon. psi=existing WeilExcess.deviationPotential. One cutoff for entire expanding panel, including moving m.

3. WeilLogShiftAsymptoticPositive lam := forall epsilon>0, exists cutoff, forall k>=cutoff, forall panel m, -epsilon<=Re P_k(lam,m). Uniform negative-tolerance predicate; not exact positivity.

4. weilLogShiftAsymptoticPositive_iff hs: this predicate iff forall integers m>=2, psi0<=psi(logm). Exact static signed-potential cone classification in absolute-summable-deviation domain.

5. exists_uniform_logShift_positive_of_potential_gap hs delta>0 (forall m>=2, delta<=psi(logm)-psi0): one cutoff after which every panel value is STRICTLY greater than delta.

6. exists_persistent_logShift_negative_of_potential_gap hs (m>=2) (psi(logm)<psi0): exists cutoff, all k>=cutoff contain that SAME m in panel, and its full-functional real value is STRICTLY less than psi(logm)-psi0 (a negative constant).

Proof dependencies: exists_riemannKernelAutocorr_decay gives uniform |K_L-K|<=D exp(-2(L-1)) after exp(-2|y|)<=1. Summable abs deviation yields potential defect <=2D*(tsum abs deviation)*exp(-2(L-1)), all shifts. Exact panel identity is zero-side real value +2*(truncatedPotential(logm)-truncatedPotential0). Norm zero side <=4exp(2k)*nearRadicalEnergy(k), uniformly for m<=exp2k; existing energy decay sends this to zero. Combined error goes to zero uniformly, then epsilon arguments prove cone iff and margins. All private helpers are in this leaf, no existing leaf modified.

Important scope: ABSOLUTE summability is required. Summable excess alone DOES NOT imply summable deficits for mixed signs. General mixed-sign summable-excess replacement remains OPEN. This is a verified reframe, not a claim that original all-window positivity or RH is solved. Even a strict potential gap gives eventual positivity; finitely many initial windows remain separate. External novelty unassessed under user source restriction.

Card: docs/drafts/pipeline/3-formalized/weil-logshift-asymptotic-potential-cone.md. Paper proof closed before Lean; full exact API and significance/next-attack audit recorded. Exact logShift-potential lexical query returned zero declarations, targeted exhaustive source search found no existing panel/potential law. Broad kernel/shape search found no monotonicity theorem supporting speculative two-atom construction; do not assume monotonicity/logconcavity from training data.

Audits2026-10-09: final leaf64970exit0, no diagnostics, olean emitted at default heartbeat. Separate public signature/axiom audit86987exit0, all SIX declarations exactly [propext, Classical.choice, Quot.sound]. Umbrella import exactlyonce observedline6928. Index16433exit0,sixAPIrows. Scoped whitespace no diagnostics. Authoritative lint7689exit1 only nine unrelated unreachable modules: RHTower.{PaperCirclePhaseCancellation,SincSeparatorMellin,StretchedBoseDefect}; HTGeometry.{ApertureConeCalculus,ApertureConeWinding,ApertureLogTranslation,ApertureOpenHistoryIdeal,BoundaryCoronaCStarAlgebra,ComplexRateGammaIntegral}. No own leaf errors. All own jobs terminal. All10 inventoried /tmp/hgt-weil-mixed* files removed and absence verified.

Lean gotchas: positivity tactic does not solve negative-expression<=0 here; use linarith only [abs_nonneg y]. For m : Finset.Icc..., m.2 is membership NOT a pair: use (Finset.mem_Icc.mp m.2).1/.2. Rewriting exp(2k) in a goal containing dependent m can fail motive typechecking; use nlinarith only [hsq,heq] instead of rw [heq]. Unfold local scalar abbreviations before linarith and include epsilon positivity when comparing 3epsilon/4<epsilon. Norm_tsum_le_tsum_norm requires summable norms; real Summable.norm available. Explicit guarded weilDeviation form change needed before Complex.re_tsum.

Next mathematical attack: competing conjectures remain rigidity vs a finite-support counterfamily. Potential criterion makes a two-atom construction precise: deficit at2, positive excess at largeN. Need rigorously separate K(logN) from finite collection K(log(N/m)) for m>=2; existing coarse exponential decay and positivity alone do NOT supply this. A finite set of m could be repaired with a positive spike if the ratio is sufficiently large, while large m are protected by a negative central moment and decay. Required ratio theorem OPEN, no numerical evidence or proof. Even success gives only eventual tests; original initial windows still need compatible control. Alternatively find stronger rigidity mechanism for mixed signs or extend potential criterion from absolute summability to one-sided excess with proven deficit control. Do not silently replace general question by solved majorant/absolute-summability sector.

Predecessor: `mem:research/weil-logshift-diagonal-moment-2026-10-09`; earlier finite-deficit counterfamily: `mem:research/weil-logshift-finite-deficit-separation-2026-10-09`.
