# Distinct actual prime interference, 2026-09-06

RH goal ACTIVE and unbudgeted; not proved/disproved, never marked complete/blocked. This turn is verified progress. No subagents, numerical experiments, commits or pushes. All owned Lean/build sessions terminal. Exact named builds and all 17 public axiom audits PASS, axioms exactly [propext, Classical.choice, Quot.sound]. Formal lint PASS (large-file warnings only), git diff --check PASS. Concurrent unrelated Bellman/ChronologicalTensor work persists; preserve it.

New wired leaves:
1. formal/GaloisForLFunctions/HTGeometry/NilpotentContractionInterference.lean (149 lines, 5 public theorems); HTGeometry umbrella.
2. formal/GaloisForLFunctions/RHTower/CCMRestrictedWeilPrimeInterference.lean (~449 lines, 12 public theorems); RHTower umbrella.
Card: docs/drafts/pipeline/3-formalized/weil-distinct-prime-interference-gap.md.
Route O current-state paragraph and route-independent compatibility constraint updated. Existing single-atom work in mem:rh/weil-prime-outer-shell-2026-09-06 remains valid.

Full proof chain pursued: literal prime-Gamma source -> joint estimate on constrained ground -> exclude H_a f=c(p_++p_-) or c(p_+-p_-) zero-ground equations -> all-aperture positive constrained floor -> weighted pole exclusion -> RH. The joint PRIME estimate is now stronger; no adequate comparison with Gamma energy is proved.

Conjecture loop:
- Initial idea that distinct outer shifts cannot simultaneously preserve one constrained vector's norm is FALSE.
- Positive survivor: outputs cannot align at the separate maxima. Their product has exact support drift and is nilpotent with an explicit exponent.
- Support reasoning improved the initial full-diameter exponent to overlap width.
- Literal weighted pair gain extends to strict full-source separate-atom budget for every a>=log 5 via Bertrand.
- The false initial conjecture now has a formal common-norm-preserving constrained vector, so the distinction is fully audited.

Notation: S_h=P_a(T_h+T_-h)P_a, T_h f(x)=f(x+h), actual aperture [-a,a]. For a<h<k, d=k-h>0:
C=S_h S_k acts as f(x-d) on [-a,a-h], f(x+d) on [-a+h,a], zero elsewhere. Every power C^N f has support radius <=a-Nd; every positive power is also supported where |x|>=h-a. Thus C^N=0 whenever N>0 and Nd>2a-h. No k<2a hypothesis is required for these identities; larger lags already vanish.

Generic HTGeometry theorems:
- contraction_norm_sub_pow_apply_le: contraction C gives ||x-C^n x||<=n||x-Cx||.
- nilpotent_contraction_real_inner_gap: C^N=0 yields 2N² Re<x,Cx><=(2N²-1)||x||².
- selfAdjoint_pair_sq_bound_of_nilpotent_product: A symmetric, A/B contractions, (AB)^N=0, u,v>=0 gives N²||(u:complex)Ax+(v:complex)Bx||²<=[N²(u+v)²-uv]||x||².
- selfAdjoint_pair_opNorm_sq_bound_of_nilpotent_product: same operator-norm inequality for N>0.
- selfAdjoint_pair_norm_lt_sum_of_nilpotent_product: u,v>0 gives strict norm <u+v. Only A symmetry is needed in these generic statements; actual A,B are both self-adjoint.

Actual RHTower theorems:
- ccmOuterShiftProduct_coeFn: exact piecewise source product.
- ccmOuterShiftProduct_pow_shrinking_support.
- ccmOuterShiftProduct_pow_eq_zero: exact nilpotence at overlap width.
- ccmOuterShiftPair_opNorm_sq_bound: source supplies nilpotence; explicit N²||uS_h+vS_k||²<=N²(u+v)²-uv.
- ccmOuterShiftPair_norm_lt_sum: choose a positive N above width/d; no nilpotence assumption remains.
- ccmWeightedPrimeTransport_eq: (w:complex)T(n)=(w/sqrt n:complex)S_log n.
- ccmPrimeSourcePair_opNorm_sq_bound: literal weights u=Λ(n)/sqrt n, v=Λ(m)/sqrt m; nonnegativity discharged.
- ccmPrimeSourcePair_norm_lt_separate: positive distinct outer prime-power atoms have strict norm subadditivity.
- norm_ccmFinitePrimeOperator_lt_outerShellBudget_of_pair: for two such atoms in literal finite Icc window, extract pair, bound remaining atoms as before, obtain strict full operator bound.
- exists_two_outer_primes_of_log_five_le: every a>=log5 has two actual distinct primes in window and above exp a.
- norm_ccmFinitePrimeOperator_lt_outerShellBudget_of_log_five_le: unconditional eventual strict improvement over the previous separate-atom budget.
- exists_polarConstrained_common_outerShift_norm: for a<h<k<2a, a nonzero constrained form vector preserves both norms; choose S_k +1 eigenvector from previous leaf, use nested endpoint projections and symmetry.

Bertrand proof: X=exp a>=5, b=ceil X; choose primes b<p<=2b and p<q<=2p. Then X<p<q<=4b<4X+4<=X². Both belong to finite source window, Λ positive. No PNT or computation needed.

Verification:
- Scratch /tmp/hgt-prime-interference.ysms8iuq/Production.lean is exact final actual production copy.
- ContractionFinal.lean is exact generic production copy.
- Audit.lean imports actual leaf, prints all 17 public axioms and actual mathlib RiemannHypothesis.
- Lint.txt says formal lint passed; LintWarnings.txt captures large-file warnings.
- Named generic build completed (12s, 3079 cached/target jobs); actual leaf build completed (32s, 11310 cached/target jobs). No umbrella/full builds.
- Intermediate Contraction.lean/Product.lean/Pair.lean/Final.lean/FinalWithCommon.lean/Body files are assembly stages. Combined.lean is STALE with an old type inference error in final finite-sum norm step. Do not reuse it as final source. FinalWithCommon has one redundant change tactic removed in Production.

Lean lessons:
- RCLike.re vs Complex.re needs explicit change or exact arguments. Last norm_sq_eq_re_inner reversal required explicit f, not underscore.
- Generic norm_add_le / norm_smul on CLMs can leave stuck norm instances: supply explicit A n+A m and explicit remaining sum; use local htri then linarith.
- scalar normalizations of actual CLMs are robust via ContinuousLinearMap.ext, vector smul_smul, and a scalar field identity.
- For eventually predicates use tendsto_ae.eventually; for ae function equality use comp_tendsto.
- Source nilpotence is easiest via support radius shrink and outer-shell support, not a full explicit formula for every iterate.
- Mathematical nlinarith real lower bound X²>4X+4 at X>=5 used sq_nonneg(X-5), not numerical evaluation.

Possible next corpus-first work: exploit multiple pair deficits collectively, or use their support/alignment mechanism in the exact signed prime-polar/Gamma comparison. Mere strictness below a large separate-atom norm budget cannot prove constrained ground positivity. Avoid repeating single-atom sharpness, common norm-preservation exclusion, or another RH-equivalent receiver. Full-source all-aperture sign remains the target, and broader RH routes/candidates remain in scope.
