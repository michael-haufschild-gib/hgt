# Quantitative finite-rank critical collar

- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Wall:** Σ6
- **Target:** There exist constants `A≥1`, `c>0`, independent of rank, such that the actual signed theta Hankel section of size `N` is positive definite whenever `|a−1/2| < c/[A^(N+1)·((2N+1)!)^(N+2)]`.

A fixed compact frequency interval carries a positive lower bound for the
boundary current. Rescaling reduces its polynomial square integral to the
uniform moment matrix `Hᵢⱼ=1/(i+j+1)` on `[0,1]`.
For `N≥1`, `D=(2N)!` makes `DH` integral. Strict positivity then gives
`det H≥D^(−N)` without an explicit determinant formula. Cofactors bounded
by `(N−1)!` and Cauchy–Schwarz in the `H` inner product would give
`vᵀHv≥‖v‖²/[N!D^N]`.

A uniform exponential bound for the aperture derivative of the actual
current would bound the moment perturbation by factorial growth. Comparing
that bound with the displayed coercivity should give the proposed radius.

**Unproved:** the quantitative moment coercivity, the derivative majorant,
and their actual-source assembly. The [qualitative finite-rank collar](../3-formalized/theta-cusp-finite-rank-critical-collar.md)
is formalized; no quantitative radius is certified here.
