# Digital energy and the exact prime-tower payment domain

- **ID:** biarithmetic-digital-energy-and-prime-tower-payment
- **Stage:** 1-in-progress
- **Type:** CANDIDATE (Lean formalization incomplete)
- **Proof status:** Only statements with completed Lean checks and axiom audits are proved. Paper arguments below are proof plans; every significant claim remains a formalization obligation.
- **Parent:** [Golden digital module](../1-in-progress/biarithmetic-golden-digital-module.md)
- **Statement:** A weighted base-five digit row has finite pronic energy exactly when its digit coefficients divided by `5^(l/2)` lie in `ell2`. For the critical geometric source, a prime-five-supported Wiener kernel repairs exactly when its normalized coefficient partial sums lie in `ell2`.

## Exact finite digit moment

Let `x_l` be arbitrary real numbers and write `W_x(n)=sum_l digit_l(n)x_l`. On the block
`5^M<=n<5^(M+1)`, the leading digit is uniform on `{1,2,3,4}`, the lower `M` digits are
independent uniform elements of `{0,1,2,3,4}`, and these choices enumerate the block exactly.
The leading mean and variance are `5/2` and `5/4`; the lower-digit mean and variance are
`2` and `2`. Expanding the finite square therefore gives exactly

`sum_block W_x(n)^2 = 4*5^M * [(5/4)x_M^2 + 2 sum_(l<M)x_l^2 + ((5/2)x_M+2 sum_(l<M)x_l)^2]`.

No independence of the arithmetic source is asserted: this is the complete combinatorial
parameterization of all integers in one base-five block, with arbitrary fixed signed coefficients.

## Pronic norm equivalence

Put `u_l=5^(-l/2)x_l` and `lambda=1/sqrt(5)`. Since every block denominator `n(n+1)` is at
most `5^(2M+2)`, the exact moment gives

`sum_block W_x(n)^2/[n(n+1)] >= (1/5) u_M^2`.

For the upper bound, `|W_x(n)|<=4 sum_(l<=M)|x_l|`, and telescoping the pronic weights gives
`sum_block 1/[n(n+1)]=4/(5*5^M)`. Hence block energy is at most

`(64/5) [sum_(l<=M) lambda^(M-l)|u_l|]^2`.

Weighted Cauchy–Schwarz bounds the square by
`(1-lambda)^-1 sum_(l<=M) lambda^(M-l)u_l^2`. Summing `M=0,...,R`, interchanging finite sums,
and bounding the remaining geometric sum gives the exact finite estimate

`(1/5) sum_(l<=R)u_l^2 <= E_(5^(R+1)-1)(W_x)
 <= [(64/5)/(1-1/sqrt(5))^2] sum_(l<=R)u_l^2`.

Every horizon is between complete blocks. Positivity therefore proves finite total pronic
energy iff `sum_l u_l^2<infinity`.
For complex coefficients, apply the same bounds separately to the real and imaginary
parts and add them, using `|z|^2=(Re z)^2+(Im z)^2`. Thus the identical two-sided constants
and payment criterion hold over the complex Wiener algebra.

## Exact payment criterion on a geometric tower

Let `I_a(5^r)=a^r` and zero off powers of five, with `0<a<5`. Its mean is summable, and its
centered ordinary-floor receiver is `-a/(5-a) D_a(n)`. Let a critical Wiener kernel be supported
on powers of five, with values `f_r=f(5^r)`, so `sum_r |f_r|5^(-r/2)<infinity`.
Put `S_l=sum_(r<=l)f_r a^-r`. The exact finite digit-splitting law gives

`sum_(r<=floor(log_5 n)) f_r D_a(floor(n/5^r))
 = sum_l digit_l(n) a^l S_l`.

The convolution/mean-correction identity differs from this action by a paid critical-Wiener
prefix. The preceding norm equivalence therefore proves

`f repairs I_a iff sum_l (a^2/5)^l |S_l|^2 < infinity`.

The exact criterion in fact holds for every real `a` with `a!=0` and `|a|<5`.
The source-to-digit identity already holds on this absolute-convergence domain;
the digit norm theorem permits arbitrary signed coefficients; and the scalar
`-a/(5-a)` is nonzero. No positivity of `a` occurs in those three steps.
Only the subsequent positive-tower phase and profile analysis use `a>0`.
This signed extension is formalized in `PrimeFivePaymentCriterion.lean`,
including normalized critical partial sums; its direct source check and all
five transitive axiom audits passed.

At `a=sqrt(5)`, set `g_r=f_r 5^(-r/2)`. The exact condition is that the partial sums of the
`ell1` sequence `g` belong to `ell2`. This is strictly stronger than `sum_r g_r=0`. For example,
`g_0=-1`, `g_r=1/sqrt(r)-1/sqrt(r+1)` for positive `r` gives partial sums
`-1/sqrt(l+1)`, whose squares have divergent harmonic sum. Corrected finite truncations have
finite-support partial sums, so are paid and converge to this unpaid kernel in Wiener norm.
This classifies the whole prime-five-supported boundary payment domain, not just one obstruction.

If `a<sqrt(5)`, the normalized digit coefficients are convolution of the `ell1` normalized
kernel coefficients with a decaying geometric sequence, hence are in `ell2`; every kernel pays.
If `a>sqrt(5)`, write `lambda=sqrt(5)/a<1`. Finiteness forces
`sum_r f_r a^-r=0`. Conversely that equality gives the normalized output coefficients as
`-sum_(r>l) g_r lambda^(r-l)`, an `ell1` sequence by geometric summation, hence an `ell2`
sequence. Thus the strict regime recovers exactly the one-prime evaluation ideal.

The golden source differs from a nonzero multiple of `I_a` by a critical Wiener source.
Its paid ideal is identical, so this criterion transfers to its prime-five-supported kernels.
The full ordinary-integer kernel class and all cofactor tangents still need the separate
profile and jump arguments on the parent card.

## Scope and verification

The digit second-moment identity belongs to classical weighted sum-of-digits theory, including
Larcher and Pillichshammer's [Moments of the Weighted Sum-of-Digits Function](https://doi.org/10.2989/16073600509486132).
The intended contribution is the exact pronic norm equivalence and source-defined payment
domain, particularly its critical nonclosed boundary. No general novelty claim is made.

- [x] Dependency-closed proof plan of finite moment and norm equivalence.
- [x] Paper source comparison and all three tower regimes.
- [x] Lean complete-word and leading-digit moments: `WeightedDigitMoments.lean`, direct check and five clean transitive audits.
- [x] Lean natural-index enumeration: direct source check and six clean transitive audits.
- [x] Lean real pronic norm equivalence: direct source check and three clean transitive audits.
- [x] Lean real actual-source comparison and full signed prime-five criterion.
- [x] Lean complex norm formulation and golden-source transfer: direct check and five clean audits.
- [ ] Lean explicit nonclosedness and full phase classification.
- [ ] Direct checks, axiom audits, and umbrella wiring.

The natural-index bridge is formalized in
`BiarithmeticGeometry/WeightedDigitEnumeration.lean`. The standard equivalence
`finFunctionFinEquiv : (Fin M -> Fin 5) ≃ Fin (5^M)` reads inverse digits as
`floor(n/5^i) mod5`. Thus it transports the checked word moments to complete initial
integer intervals. Subtracting the moments below `5^M` from those below `5^(M+1)`
gives the displayed annular identity without introducing another digit bijection.
This bridge and `FiniteGeometricConvolution.lean` passed direct repository checks
and all main-declaration axiom audits; separate stage-3 cards record their scope.
`BiarithmeticGeometry/DigitPronicBlocks.lean` now supplies the exact pronic block
mass and both block estimates, with a direct source check and three clean audits.
`BiarithmeticGeometry/WeightedDigitPronicEnergy.lean` combines them into complete-prefix
two-sided bounds and the full bounded-energy iff weighted-square-summability theorem
for real digit coefficients. Its direct source check and three audits passed; its
stage-3 card records the exact scope. `GoldenPrimePayment.lean` now supplies
the complex payment formulation and actual golden transfer, with its own
stage-3 card, direct source check, and five standard-axiom audits.
The exact finite cofactor-to-digit identity is formalized separately in
`BiarithmeticGeometry/DigitCofactorConvolution.lean`. Mathlib's generated additive
`Finset.sum_range_diag_flip` directly reindexes the causal triangle, and
`Nat.div_div_eq_div_mul` identifies the shifted digits. This removes the need
to import the much larger finite-jet module surfaced by the corpus search.
The leaf also factors the resulting geometric coefficients into partial pole sums.
Its direct check and three audits passed. The actual infinite-kernel payment bridge
is a separate statement.
That general mean-correction bridge is formalized in
`BiarithmeticGeometry/CofactorPaymentCriterion.lean`: critical Wiener convolution is
paid exactly when its full cofactor action has bounded pronic norm. The direct leaf
check and both transitive audits passed; a separate stage-3 card records the scope.
Together with the exact kernel lift, these interfaces now prove
`receiverBounded_fiveTowerKernelLift_iff` and
`receiverBounded_critical_fiveTower_iff_partialSums` in
`BiarithmeticGeometry/PrimeFivePaymentCriterion.lean`. The real actual-source
criterion passed direct checking and five clean audits. The complex golden
transfer and nonclosedness are separate pending checks.

Source-checked APIs for this bridge: `Nat.log_eq_iff` and
`Nat.lt_pow_succ_log_self` in Mathlib `Data/Nat/Log.lean`; generated additive
`Fin.sum_univ_eq_sum_range` from `Fin.prod_univ_eq_prod_range` in
`Data/Fintype/BigOperators.lean`; and `Finset.sum_range_add_sum_Ico` from
`prod_range_mul_prod_Ico` in `Algebra/BigOperators/Intervals.lean`.
The corpus search also found the exact pronic mass theorem
`BezoutValuationIncidence.sum_range_pronic_inv` and the direct interval telescope
`RHTower.sum_reciprocal_telescope` in `RHTower/PsiRemainderHarmonicSum.lean`.
Both statements and proofs were inspected. The reciprocal telescope is the smaller
direct interval interface; the pronic mass theorem imports a larger cofactor stack.
