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

The exact frequency statement needed is sharper than global independence of
all scaled prime logs: if `D` target terms use distinct primes and positive
algebraic weights, every representation by at most `D` positive algebraic
prime terms has exactly `D` terms and permutes the same prime–weight pairs.
Baker gives equality of total weight at each prime. Positivity gives equal
prime supports; cardinality forces one term per target prime, and weight
balance identifies each exponent. The cofinite prime-jet law then extends to
all multilinear forms by currying one slot and excluding its prime from the
remaining slots. These two exact lemmas are being formalized; the full
independence theorem remains open.

The corpus already proves absolutely convergent product expansion
(`ExponentialSeriesAlgebra.prod_expSeriesCarrier`) and coefficient extraction
with frequency collisions (`ExponentialSeriesFiberwise.fiberAmplitude_eq_zero_of_expSeriesCarrier_eq_zero`).
The actual undilated jet identity is already proved in
`XiCollapseDirichletLeg.iteratedDeriv_zetaLogDeriv_eq_LSeries`; argument
scaling has an unconditional chain rule. The missing bridge transports these
jets to common positive-algebraic prime atoms with absolute summability, then
uses the Baker-separated prime fibers and top-degree polarization. Logarithmic derivatives are
meromorphic in the upper half-plane, so they cannot be inserted as analytic
representatives into the physical Gamma receiver. Transfer their differential
independence to the actual zeta dilates in rotated right-half-plane germs,
then recover physical zeta-jet independence before Gamma separation.
`CoordinatewiseDifferentialFamilyMatroid.differentialIndependent_deriv_div_self_iff`
already supplies the abstract family transfer.

No theorem or stronger Mahler exclusion is claimed yet. Special-value
relations and other nonlinear realizations remain outside this conjecture.
