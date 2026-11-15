# Arithmetic coefficients separate the prime-two deformation

- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper); Lean audit pending
- **Obstacle:** O11, review 1511 §2.2.
- **Connection:** the passive prime-two scattering deformation and uniqueness of absolutely convergent Dirichlet series.

## Statement

For every `1/2 < α < 1`, put `t = 2^α + 2^(1−α)` and remove the conductor factor from the existing deformation:

`Dα(s) = 2^(1/2−s) primeTwoFactor(α,s) ζ(s)`.

Its Dirichlet coefficients at positive integers are exactly

`aα(n) = 1 − t [2 ∣ n] + 2 [4 ∣ n]`.

They are bounded, positive at odd integers and multiples of four, and negative exactly when `2 ∣ n` but `4 ∤ n`. No absolutely convergent Dirichlet series with nonnegative coefficients represents `Dα` on a real right ray. This separates the named O11 family from ζ using arithmetic coefficients, independently of zero locations and ringdown estimates.

## Proof [PROVED HERE]

Expand the two factors in `primeTwoFactor`: their product is `1 − t 2^(−s) + 2 4^(−s)`. The conductor factors cancel. For `Re s > 1`, absolute convergence permits reindexing ζ along `n ↦ 2n` and `n ↦ 4n`, giving the displayed coefficients. The three possible values are `1`, `1−t`, and `3−t`. The established estimate `0 < t < 3`, together with `2^α > 1`, gives `1 < t < 3`. Thus the stated sign classification holds. Boundedness gives absolute convergence on `Re s > 1`. Uniqueness of convergent Dirichlet series forces any competing coefficient at two to equal `1−t < 0`, contradicting nonnegativity.

## Scope

This excludes the specific positive-trace deformation in O11. It does not assert RH, positivity of Weil's form, or exclusion of every possible Euler deformation. Sign-reversed trace gates require a separate audit; ordinary coefficient positivity may survive them.

## Verification

- Lean module: `BlackHoleRingdown/ThePrimeTwoDeformationHasSignedArithmeticCoefficients.lean` (in preparation).
- Final compile and umbrella integration pending. Axiom checks skipped at user request.
- Not counted toward 250 before these gates and significance review pass.
