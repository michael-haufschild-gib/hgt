# Square-root cost improvement for quadratic cluster starts

Status: formalized; native leaf builds and complete axiom/API audit passed.
Date: 2026-10-10. Local Lean corpus and installed Lean dependencies only.

Prior work: exact arithmetic mass G_r=2^(r+1)/choose(r+1,(r+1)/2); log-grid comparison A^n G_r <= U^n S and A^n S <= U^n G_r, where n=r+1, A=k+2, U=A+n. Existing fixed-constant Gram-test receivers prove gap*S*A²2^r <= l1distance*B*cost and every actual coordinate reader satisfies S*A²2^r <= 2B*cost under 4Ln<=A. All analytic premises already discharged.

Local prior search `sqrt mass quadratic`, module WeilLogShift, has no hits. Earlier `centralBinom sqrt` search exposed the corpus's exact Wallis identity and Wallis lower bound. This is a bridge between those proved results, not an external asymptotic claim.

Paper proof:
1. Put m=floor(r/2)+1 and c_m=centralBinom(m)/4^m. For r=2j+1 the exact mass formula directly gives G_r=1/c_(j+1). For r=2j, Pascal's identity and choose symmetry give centralBinom(j+1)=2*choose(2j+1,j), giving the same identity. Thus G_r*c_m=1 for every r. This also exposes the exact adjacent-order plateau G_(2j)=G_(2j+1).
2. Existing `wallis_mul_normalizedCentralBinom_sq` gives W_m*c_m²=1/(2m+1), and `one_le_Wallis_W` gives W_m>=1. Therefore (2m+1)c_m²<=1. Multiply by G_r² and use G_r*c_m=1 to obtain G_r²>=2m+1>=r+2. G_r>=2 gives G_r>=sqrt(r+2).
3. Suppose A>=2n², n>=1. Put U=A+n. Bernoulli at a=-n/U gives (A/U)^n>=(1-n²/U)>=1/2. All denominators are positive. Thus U^n<=2A^n. Combined with the two existing mass comparisons, this gives G_r<=2S and S<=2G_r; hence sqrt(r+2)<=2S.
4. Choose fixed K=4L+2. Because n>=1, K*n²<=A implies both 4Ln<=A and 2n²<=A. The old mass-weighted whole-fiber receiver then gives gap*sqrt(r+2)*A²2^r <= l1distance*(2B)*cost. The old coordinate-reader receiver gives sqrt(r+2)*A²2^r <= (4B)*cost. Reader existence remains supplied by the same proved finite Weil coefficient surjectivity.

New target: unconditional existence of fixed constants for both receivers under a quantified quadratic cluster-width condition, with an explicit unbounded square-root factor in order. No unknown analytic estimates are accepted as premises. No claim about uniform distortion under only linear starts.

Completed leaves:
- `WeilLogShiftArithmeticSqrt.lean`: six theorems; exact reciprocal central-binomial identity, adjacent-order plateau, stronger parity-sensitive squared bound 2*floor(r/2)+3<=G_r², and sqrt(r+2)<=G_r.
- `WeilLogShiftQuadraticMass.lean`: four theorems; Bernoulli power distortion, two-sided factor-two mass comparison, sqrt(r+2)<=2S, and the fixed quadratic-width bridge.
- `WeilLogShiftSqrtCost.lean`: both unconditional fixed-constant receivers. Whole-fiber sensitivity at line10 and actual coordinate-reader cost at line45. Both include actual-reader existence; no new analytic premise.

Verification: all three `lake --old env lean <leaf> -o <olean>` builds exited0 with empty logs. `/tmp/hgt-sqrt-final-audit.lean` exited0: all 12 declarations use only `propext`, `Classical.choice`, `Quot.sound`; all 20 explicit API terms elaborate. `/tmp/hgt-sqrt-metadata.py` found no source/direct-dependency freshness, axiom-coverage, or umbrella-count issues. Exhaustive incoming imports are the umbrella plus the new internal chain. Local index refresh exited0. One owned Lean process at a time, no full/umbrella build, no numerical experiment, no heartbeat change.

Formal lint `/tmp/hgt-sqrt-lint.log` exited1 on one unrelated missing umbrella import: `HTGeometry.QKrawtchoukCompanionTriangular`. No errors in these leaves; foreign work left untouched.

Implementation lesson: the first native pass found one redundant `omega` after `congr 1`; removing that tactic produced the clean final build. No mathematical weakening was needed.

Positive refinement completed: `finite-weil-relative-mass-error.md` retains Bernoulli's error term and proves A*abs(S-G)<=2(r+1)²G. The companion `finite-weil-cubic-mass-limit.md` also connects the existing Wallis limit to the explicit cubic sequence k_r=2(r+1)³. All 10 declarations passed native builds and complete axiom audit. Standard normalization by sqrt(r+1) remains the next refinement.

Exact post-index lookup passed: `exists_finiteWeilGram_sqrt_coordinate_cost`, module `WeilLogShiftSqrtCost`, source line45. All owned build, audit, lint, index, and search sessions are terminal.
