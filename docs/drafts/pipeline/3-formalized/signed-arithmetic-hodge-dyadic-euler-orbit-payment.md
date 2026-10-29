# One Gamma reserve for the dyadic Euler factor across all levels

## Theorem

The actual generator cutoff P_A retains the root and every label a<A at all
dyadic levels. It reduces the weighted cell clock W_2. The entire physical
prime-two correlation series has head error at most

(2 log(2)/(sqrt(2)-1)) * 32 Gamma(f)/(1+log A)

for every finite original cell source f, uniformly in its horizon and coarse
coefficients. The actual physical translations and critical Euler weights
are retained. This concerns the full prime-two correlation contribution, not the
separate one-level coarse/detail mixed source.

## Proof mechanism

1. P_A is an orthogonal projection through the proved coordinate isometry.
   It commutes with W_2 on every orbit basis vector, hence on the completion.
2. Both head and tail are invariant under every forward dyadic power.
   Orthogonality removes their cross terms exactly:
   inner(W_2^k x,x)-inner(W_2^k P_A x,P_A x)
   =inner(W_2^k (x-P_A x),x-P_A x).
3. The clock is an isometry, so the absolute real error is bounded by the
   squared tail norm. The verified original-source estimate pays this by
   32 Gamma(f)/(1+log A), with no cutoff on levels.
4. Existing primeTwoPowerWeight has exact sum2 log(2)/(sqrt(2)-1).
   Absolute summability is proved before subtracting the two Euler series.
5. Powers of the clock are identified with literal physical translations at
   log(2^k). The original whole-cell integral series is absolutely convergent
   and equals the cell-coordinate series term by term.
6. For any delta>0, choose A>exp(32*primeTwoEulerWeightTotal/delta).
   The head error is then at most delta*Gamma(f), uniformly over every finite
   original cell profile and horizon.

## Formalization and boundary

Lean: `SignedArithmeticHodgeTheory/GeneratorOrbitCutoffsReduceTheDyadicClock.lean`
and `SignedArithmeticHodgeTheory/OneGammaReserveControlsTheDyadicEulerTail.lean`.
Capstones: `dyadicEulerCorrelation_sub_head`,
`summable_norm_physicalDyadicEuler_on_cells`,
`physicalDyadicEulerCorrelation_wholeCell`,
`summable_norm_wholeCell_dyadicEuler_integrals`,
`abs_physicalDyadicEuler_wholeCell_head_error_le`,
`exists_physicalDyadicEuler_finite_generator_approximation`.
Individual no-olean audits pass. Printed capstone dependencies contain only
`propext`, `Classical.choice`, `Quot.sound`.

Every fixed finite Euler family also has all-level generator approximation;
its proof uses orthogonal tail localization and Gamma translation invariance,
with constant96 before the coefficient sum. See
[all-lag Euler payment](signed-arithmetic-hodge-all-lag-euler-payment.md).
Growing prime families, continuous Gamma interactions, retained-orbit signs
and both poles remain separate full-Weil obligations.
