# CCM-FU exact smooth mean and bounded quotient obstruction — verified 2026-09-07

## Goal and frontier
RH goal remains ACTIVE and OPEN. This turn is PROGRESS: new actual source mean and a uniform large-quotient factor-two comparison are closed in Lean. Full chain remains Guinand–Weil source → marked rectangular current → affine Suzuki checkpoints → signed curvature → prime–polar–Gamma/unit-Riesz boundary → Xi-screw Green → RH. SD1, all-cutoff unit factor-two comparison, all-cutoff original two-prime ceiling and complete growing adaptive schedule remain open. Do not claim bounded quotient means bounded cutoff or finitely many numerical cases.

## New leaves
1. `formal/GaloisForLFunctions/RHTower/HarmonicStirlingExactBounds.lean` — 136 lines, two public theorems, imports existing HarmonicSecondErrorBounds.
- `harmonic_mascheroni_ge_half_sub_twelfth`: for n>=1, 1/(2n)-1/(12n²) <= H_n-log(n)-gamma. Proved by cubic rational logarithm lower bound log x>=2t+2t³/3, t=(x-1)/(x+1), monotone corrected harmonic sequence and actual limit. Existing complementary upper is 1/(2n)-1/(12(n+1)²).
- `sum_log_Icc_exact_stirling_bounds`: with c=log(2*pi)/2, for N>=1, 0<=log(N!)-NlogN+N-logN/2-c<=1/(12N). Actual Stirling sequence, its reciprocal difference bound and its sqrt(pi) limit; no numerical inputs.

2. `formal/GaloisForLFunctions/RHTower/DivisorSmoothSquareBlockMean.lean` — 494 lines, one definition and ten public theorems. Imports new foundation, existing DivisorSecondCenteredHyperbola and MobiusDivisorTwoPrimeLocalCriterion.
- `divisorHyperbolaSmoothRemainder_exact_quadratic_bounds`: s=Nat.sqrt N, q=c-gamma-1/3+(N-s²-s)²/(2s²), q-5/s <= smooth(N) <= q+2/s for N>=1.
- `divisorHyperbolaSmoothMean` definition a=c-gamma-1/6.
- `sum_divisorHyperbolaSmooth_square_block_mean_error`: each complete Ico(s²,(s+1)²) block, s>=1, sum(smooth-a) has abs<=15. Exact quadratic sum s(s+1)(2s+1)/3.
- `sum_divisorHyperbolaSmooth_mean_error`: ALL N, abs(sum k=1..N smooth(k)-a*N)<=33sqrt(N), last partial block retained.
- `divisorHyperbolaSmoothAbel_mean_error`: ALL M, abs(smoothAbel(M)-a*sqrt(M))<=9log(M+1)+25+abs(a).
- `divisorHyperbolaSmoothMean_gt_one_sixth`: a>1/6 analytically. Stirling global lower bound and limit give c>=11/12; existing analytic gamma bound gives gamma<7/12. No decimal approximation needed.
- `divisorUnsignedDilationChannel_one_exact_mean_bounds`: ALL M, (a-5/48)sqrt(M)-10log(M+1)-26-abs(a) <= K1(M) <= (a-1/24)sqrt(M)+10log(M+1)+26+abs(a). Uses actual K1=smoothAbel+2C and previous centered band.
- `eventually_divisorUnsignedDilationChannel_one_exact_mean_bounds`: for every epsilon>0 eventually coefficient band [a-5/48-epsilon, a-1/24+epsilon].
- `exists_divisorUnsignedDilationChannel_large_quotient_factor_two`: exists T>=1, ALL M,p>0, T<=M/p -> K_p(M)<=2K1(M). Choose epsilon=(a-1/6)/4, so U<2L. Common unit tail at quotient N, N+1 and parent M; exact clipped interpolation preserves U*sqrt(M). Uniform in p, not merely each fixed p separately.
- `exists_divisorUnsignedDilationChannel_factor_two_failure_quotient_bound`: exists T>=1, any actual failure 2K1(M)<Kp(M), p>0, has M/p<T.
- `exists_mobiusDivisorSelectionEnergy_two_prime_bounded_quotient_obstruction`: exists universal T>=1, for any M and distinct primes p,q<M, either E_{p,q}(M)<=E_empty(M), or exists witness r<N<=M, r=p or q, N/r<T and 2K1(N)<Kr(N). Closed actual-source alternative, does NOT eliminate remaining failure.

## Remaining mathematical work
Bounded quotient profiles with unbounded dilation and variable clipped phase remain. The universal threshold is existential, not explicit or computed. No finite-case computational proof is supplied or authorized as a Lean premise. Need a sharper global normalized unit-channel envelope or direct comparison of these bounded quotient profiles to the large parent, then handle any true small parent regime. Exact source upper/lower coefficient gap is now closed; do not redo it. Possible next direction: derive a sufficiently small global upper K1(M)/sqrt(M), retaining exact smooth/centered signs rather than +large log errors. Existing 7sqrt(M) upper is too loose. A global 1/8 upper, IF proved, would combine with the strict eventual lower coefficient >1/16, but it is NOT yet proved or asserted true.

## Verification / efficiency — do not repeat
Complete scratch checked, then both reduced-import exact leaves checked with lake env lean and only required new leaf oleans generated. All 13 NEW public declarations axiom-audited ONCE: only propext, Classical.choice, Quot.sound. No sorryAx, Lean.ofReduceBool, added axioms or numerical certificates. Both leaves wired once in RHTower umbrella, NO umbrella/full/dependency builds. Formal lint PASSED, 132 existing large-file warnings only. Index refreshed (13 changed, 0 removed; other concurrent work exists). Scoped diff whitespace and card links passed. All FIVE exact owned scratch/log files removed; strict final ps snapshot showed ZERO live lean/lake processes. No saved channel computation repeated.

## Docs
Formal card `docs/drafts/pipeline/3-formalized/ccm-fu-smooth-square-block-mean.md` contains paper proof and verification. Stage1 duplicate removed. Updated current frontier detailed paragraph+CCM-FU row, two-prime-local-blocks, adaptive-prime-ceiling, source diagonal dominance. Added route-independent MUST-UNIFORM-DILATION-TAILS in universal STATUS: tail in quotient does not eliminate bounded quotient profiles at unbounded cutoff; retain clipped phases and separate comparison.

## Lean details
`sum_Ico_consecutive` needs f supplied by name when giving order hypotheses first, e.g. sum_Ico_consecutive h1 h2 (f := f); Finset version has explicit function first. `Finset.sum_range_succ` avoids root-name ambiguity. `abs_sub a b` is two-term triangle; `abs_sub_le a b c` is three-point triangle. `ge_of_tendsto` passes a common LOWER bound to limit, `le_of_tendsto` common upper. Simplify div_eq_mul_inv before nlinarith when comparing constant multiples across variable denominators. `inv_natCast` was not available; norm_num handles rational constant inversion.

See prior memories `mem:ccm_fu_second_centered_hyperbola_and_unit_floor_2026_09_07` and `mem:ccm_fu_two_prime_local_factor_and_unit_obstruction_2026_09_07` for already checked source bounds and exact local comparison.