# Finite Weil quadratic fast replication — 2026-10-12

User constraint: mathematical research uses only local Lean corpus. No web, external papers, numerical experiments, or literature novelty claims. See `mem:workflow/research-corpus-only-2026-10-12`.

Formalized card: docs/drafts/pipeline/3-formalized/finite-weil-quadratic-fast-replication.md. Predecessor: `mem:research/finite-weil-quadratic-adaptive-replication-2026-10-12`.

Four leaves, nine theorems, all native builds passed with empty logs; umbrellas wired without building.

HTGeometry/ProbabilityAffinityRigidity.lean: integrable_sqrt_rnDeriv_sub_one_sq (finite measures); bhattacharyya_defect_decomposition for arbitrary probability P,Q gives 2*(1-affinity.toReal) = integral (sqrt((Q.rnDeriv P).toReal)-1)^2 dP + (Q.singularPart P).real univ. No absolute continuity premise. bhattacharyya_le_one, bhattacharyya_eq_one_iff, bhattacharyya_lt_one_iff give exact equality/strictness iff P=Q/P≠Q.

HTGeometry/FastDiagonalSelection.lean: exists_monotone_fast_diagonal_tendsto. Eventually convergent rows F(r,n) into a countably generated filter admit monotone m(r)>=r, m→infinity and F(r,m(r))→target. Uses m(r)=max r (partialSups N r).

HTGeometry/FastAffinityReplication.lean: exists_monotone_ennreal_fast_powers_zero_iff for arbitrary f:N→ENNReal. Monotone m>=id escaping with f(r)^m(r)→0 exists iff eventually f(r)<1. No f<=1 assumption.

RHTower/WeilLogShiftQuadraticFastReplication.lean: finiteWeilCanonicalJointQuadraticTilt_bhattacharyya_eq_one_iff at arbitrary finite r,k and all real coefficient pairs. exists_finiteWeilCanonicalJointQuadraticTilt_fast_replication_iff applies actual Measure.pi Fin(m r) tilted laws for arbitrary k:N→N and arbitrary a,b,d,A,B,D. Fast product affinity→0 exists iff actual finite laws are eventually unequal. No subcriticality, canonical depth, or depth-growth assumption. This is a measure-level criterion, not a classification by coefficients.

Verification: final scratch /tmp/hgt-weil-fast-replication-final-audit.lean; 9 axiom reports use only propext/Classical.choice/Quot.sound; 14 API checks; metadata 8 direct edges,7 incoming imports,4 fresh objects, direct dependency freshness; scoped index9/9 no partial/stale markers or stderr; source/umbrella whitespace clean. Prefix /tmp/hgt-weil-fast-replication- contains audit scripts/results. Single lint run:11 unrelated errors,367 warnings (10 unreachable modules plus existing CCMPolarOddPrimeJumps.lean:104 sorry); no owned error. Do not present whole corpus as clean.

Proof lessons: withDensity_congr_ae and withDensity_one are under MeasureTheory, not Measure. Measure.eq_of_le_of_isProbabilityMeasure is exact name. Explicitly type integral_nonneg result and Integrable subtraction to avoid function-valued inference. HasBasis.tendsto_right_iff has three universe arguments. Actual root follows generic power criterion via simpa only [bhattacharyya_pi,bhattacharyya_lt_one_iff].

Remaining: classify equality of actual finite laws by coefficients; prescribed same-diagonal schedules. Possible future conjecture (unproved): same-diagonal subcritical, eventually distinct laws admit every target affinity q∈[0,1] via escaping schedules (interior may require nonmonotone schedules). No claim this is formalized. Entire corpus goal remains active.