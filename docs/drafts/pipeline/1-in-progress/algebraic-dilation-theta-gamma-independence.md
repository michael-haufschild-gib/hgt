# Algebraic-dilation independence over theta–Gamma coefficients

- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Parent:** [rational-dilation independence](../3-formalized/rational-dilation-theta-gamma-independence.md).

## Target

All actual functions `ζ(rs)`, indexed by positive real algebraic `r`, are
jointly differentially algebraically independent over
`ℂ(s)⟨Γ,θ₂,θ₃,θ₄,E₂⟩` in the common upper-end meromorphic field.
This would extend the exact differential–Mahler obstruction from rational
to algebraic multipliers, with `q=1` the repeated-coordinate exception.

## Source and missing proof

The rational theorem clears a finite packet's denominators and transports
integer-dilation jets to a physical line. That mechanism does not cover
irrational algebraic dilations.

The corpus contains unconditional algebraic-coefficient independence of
prime logarithms (`BakerIteration.primeLog_algIndep`) and the physical-line
Gamma separation theorem. A finite algebraic dilation packet has a finite
rational span. Baker independence can separate prime frequencies in each
basis direction; rational dependencies among the dilations remain explicit.

The unresolved step is joint algebraic independence of the actual physical
jets on a line of absolute convergence. It must handle those rational
dependencies, rather than assuming all scaled prime frequencies independent.
After that, existing physical Gamma separation and theta differential-algebraic
base change would apply. Their analytic representatives and chain factors
must remain in the physical variable.

## Candidate prime-frequency argument

For a finite dilation packet, use the actual logarithmic derivatives
`F_r(s)=−(ζ(rs))′/ζ(rs)=r Σ_p Σ_{m≥1} log(p) p^(−mrs)` on a common
right half-plane. A constant polynomial relation of degree `d` can be tested
at a frequency supported on `d` distinct primes. Baker separation forbids
outside primes; positivity of the dilations forces exactly one factor per
prime, isolating the top homogeneous part.

At prime frequency `α log p`, the `(r,k)` jet coefficient, after removing
common nonzero factors, is `r (−α)^k (log p)^k` when `α/r` is a positive
integer, and zero otherwise. Order the distinct dilation values `α`.
The incidence matrix is triangular with nonzero diagonal; polynomial
uniqueness at infinitely many prime logarithms should make these jet rows
span every finite packet even after deleting finitely many primes.
Polarization would then kill the top homogeneous relation.

The corpus already proves absolutely convergent product expansion
(`ExponentialSeriesAlgebra.prod_expSeriesCarrier`) and coefficient extraction
with frequency collisions (`ExponentialSeriesFiberwise.fiberAmplitude_eq_zero_of_expSeriesCarrier_eq_zero`).
The missing bridge is the actual log-derivative jet expansion, its summability,
and the Baker-separated prime-fiber and top-degree polarization argument. Logarithmic derivatives are
meromorphic in the upper half-plane, so they cannot be inserted as analytic
representatives into the physical Gamma receiver. Transfer their differential
independence to the actual zeta dilates in rotated right-half-plane germs,
then recover physical zeta-jet independence before Gamma separation.

No theorem or stronger Mahler exclusion is claimed yet. Special-value
relations and other nonlinear realizations remain outside this conjecture.
