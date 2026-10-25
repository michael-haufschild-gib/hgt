# The endpoint Vaughan limit has rank two

- **ID:** the-endpoint-vaughan-limit-has-rank-two
- **Stage:** 2-fully-proven
- **Type:** CLAIM (Lean verification pending)
- **Verification:** All twelve finite Euler, cell, determinant, independence, and row-span targets are Lean-verified. The actual infinite Gram and endpoint rank consequences remain pending.
- **Source:** uniform-half-damping-vaughan-harmonic-gram.md
- **Statement:** At every positive damping, the first two cells of the actual centered Möbius row and centered pole row have determinant at least `2^(-2ε)/36`. Consequently the endpoint limiting Gram has rank exactly two.
- **Novelty status:** Corpus search found general prefix observability and Gram laws, but no matching two-row independence theorem. The arithmetic determinant specialization is new within this audit; no external novelty claim.

## The two source cells

Let `A(n)` be the actual centered divisor prefix, `P(n)=-Δa_ε(n)`,
`ρ=Re(1/ζ(1+ε))`, `a=2^(-ε)`, and `b=3^(-ε)`. The finite source formulas give

`A(1)=1-ρ`, `A(2)=2-a-2ρ`, `P(1)=-a/4`, `P(2)=a/4-b/3`.

Their two-cell determinant is

`D=(1-ρ)(3a/4-b/3)-a²/4`.

The finite Euler bound `ρ≤(1-a/2)(1-b/3)` gives

`D≥a²/8+ab/12-b²/9-a²b/8+ab²/18`.

For `0<b≤a≤1`, multiplying this lower bound minus `a²/36` by `72` gives

`5a²(1-a)+(a-b)((8-4a)b+2a+5a²)≥0`.

Thus the quantitative determinant bound is `D≥a²/36>0`
for every `ε>0`. At half damping, both rows have finite pronic energy, so their
Gram is positive definite and the five-row limiting Gram has rank two.

The multiplier `3a/4-b/3` is positive: it is at least `5a/12`, since `b≤a`.
This justifies the direction of the substitution using the Euler bound. All polynomial
terms in the displayed decomposition are nonnegative because `0<b≤a≤1`.

## Closing the Euler and initial-value dependencies

The read theorem `hasProd_one_sub_primeCpow_neg` identifies the reciprocal Euler product
with `1/ζ(1+ε)` for `ε>0`. Each factor is real and lies in `(0,1)`. Every finite product
containing primes `2` and `3` is therefore at most their two-factor product. Passing
to the convergent product gives `ρ≤(1-2^(-1-ε))(1-3^(-1-ε))`, the stated bound.
No zero-free information outside the absolutely convergent half-plane is used.

The read definition `pmPowerDampedCenteredDivisorPrefix_eq` expresses `A(n)` as the
sum of the divisor coefficients up to `n`, minus `ρn`. The coefficient at one is one;
the read prime formula gives `c_ε(2)=1-a`. This proves both displayed values of `A`.
The active formula gives `a_ε(1)=0`, `a_ε(2)=a/4`, and `a_ε(3)=b/3`. Forward
differences prove both displayed values of `P`. Expanding their determinant gives `D`.

## Finite and infinite Gram consequences

For every `T≥2`, form the two-by-two pronic Gram of `A` and `P`. Its determinant is

`Σ_(1≤m<n≤T) (A(m)P(n)-A(n)P(m))²/[m(m+1)n(n+1)]`.

This finite identity follows by expanding the two products of sums and pairing
the terms `(m,n)` and `(n,m)`; diagonal terms cancel. Every term is nonnegative.
The pair `(1,2)` therefore proves the quantitative lower bound

`det Gram_T(A,P)≥D²/12≥2^(-4ε)/15552>0`.

In particular the two sequences are linearly independent, at every positive damping,
already on their first two positive cells. This assertion needs no finite total-energy
assumption.

At half damping the existing receiver theorem and active-energy bound pay both total
energies. Cauchy–Schwarz pays their mixed pairing. The finite Gram converges entrywise,
so its determinant retains the lower bound `1/62208`. It is positive definite.
The five limiting rows `(A,A,-A,0,P)` span exactly these two independent rows.
Their limiting Gram therefore has rank exactly two. This strengthens the endpoint
paper law without supplying any below-half receiver estimate.

## Audit and Lean status

Source statements have been read in `PMPowerDampedMobiusDiscreteEnergy`,
`PredictableMartingaleDecompositionAndCovarianceCancellationBridge`,
`HorizonFreeActiveDeletedEnergyAndShiftedCovariance`,
`RadicalInvariancePrimePowerAbsorptionAndSubHorizonFermiEvaluation`, and
`PrimeWinningFaceAugmentation`. The real finite-product identity was also checked in
`PMPowerDampedMobiusPrimeThreshold`. The proof above is dependency-closed on paper.
No numerical experiment was used. All twelve finite targets in
`BezoutValuationIncidence/TheVaughanLimitRowsAreIndependentInTwoCells.lean`
passed corrected producing and final direct checks, with only `propext`,
`Classical.choice`, and `Quot.sound` as transitive axioms. The module is wired
and its scratch removed:

- `pmPowerDampedDivisorDensity_re_le_prime_product`
- `pmPowerDampedDivisorDensity_re_le_two_three`
- `pmActiveSawtoothComponent_prime`
- `pmPowerDampedCenteredDivisorPrefix_two`
- `addDiff_pmActiveSawtoothComponent_two`
- `pmPowerDampedPrefix_pole_two_cell_determinant_lower`
- `pmPowerDampedPrefix_pole_independent_two_cells`
- `pronic_gram_determinant_lower_two_cells`
- `pmPowerDampedPrefix_pole_pronic_gram_determinant_lower`
- `pmPowerDampedPrefix_pole_linearIndependent`
- `span_pmPronicVaughanLimitFrame`
- `finrank_span_pmPronicVaughanLimitFrame`

The actual infinite endpoint Gram rank still needs a verified Lean proof.

`TheActualEndpointVaughanGramHasRankTwo.lean` drafts ten infinite-limit
consequences, including absolute-series pair limits, symmetry, positivity of
every quadratic form, the exact two-outer-product representation, and rank at
most two. Passing the finite arithmetic minor bound to the limit gives
`1/62208`; its nonsingular two-by-two submatrix gives rank exactly two. The
pole entry retains its lower bound `1/64`. These ten targets now specialize
the shared eleven-target draft `TheActualVaughanLimitGramHasRankTwo.lean`.
That draft derives summability
from the actual endpoint and upper-half limits, and proves the same exact
rank and quantitative minor for every `ε≥1/2`. No analytic summability
premise is left to assume. All these drafts remain UNPROVED until their
dependency checks and axiom audits pass.

The explicit positive-definiteness claim above has named drafts
`pmPronicVaughanLimitGram_prefix_pole_posDef` and
`pmPronicVaughanHalfLimitGram_prefix_pole_posDef`. Their matrix APIs passed a
minimal scratch check. These corollaries remain pending until the actual
Gram leaves and their transitive dependencies pass direct Lean verification.
