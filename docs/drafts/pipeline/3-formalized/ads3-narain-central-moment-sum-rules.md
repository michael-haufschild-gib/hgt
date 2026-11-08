# Narain Mellin boundary jets as physical logarithmic moments

- **ID:** W11-NJM
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Source:** [Central orders](ads3-narain-central-order-classification.md) · [Schwartz boundary](ads3-narain-boundary-schwartz.md)

## Theorem

For fixed positive target heights, put `R(y)=yA_YZ(y)+(3/π)log y−B_YZ`
and `M(u)=narainMellinMean Y Z u`. For every real `t` and natural `n`,

`∫₀∞ y^(−3/2+it)(log y)^n R(y)dy=M^(n)(it)`.

Every displayed integral converges absolutely. In particular, the central
moments `μ_n=M^(n)(0)` have first nonzero index
`1+2·1_{Y=Y*}+2·1_{Z=Y*}`, where `Y*=exp(c)` and `c=2−4 Re ξ′(1)`.
The zeroth moment vanishes at every target pair. With the real constant
`κ=(logDeriv ξ)″(1)<0`,

- `μ₁(Y,Z)=4√(YZ)(c−log Y)(c−log Z)`.
- `μ₃(Y*,Z)=32√(Y*Z)(2−κ)(c−log Z)`.
- `μ₅(Y*,Y*)=(2560/3)Y*(2−κ)²>0`.

Writing `P=YZ` and `v=(log Y−log Z)/2` gives the exact identity
`μ₁=4√P[(c−(log P)/2)²−v²]`.

## Proof

The actual clock `H(L)=exp(L/2)R(exp(−L))` is Schwartz, and its
Fourier transform is `G(t)=M(2πit)`. All polynomial clock moments
are therefore absolutely integrable. Differentiating the Fourier
identity and transporting real tangential derivatives to complex jets
gives

`M^(n)(it)=∫ℝ exp(−itL)(−L)^n H(L)dL`.

The chain factor `(2πi)^n` cancels the Fourier differentiation factor.
The logarithmic substitution `y=exp(−L)` gives the physical formula,
including its power, Jacobian and reflection sign. The oscillatory
factor has norm one, so the same Schwartz domination proves absolute
convergence at every frequency.

The central order classification gives the first nonzero index. The
factorization `M(u)=u D_Y(u)D_Z(u)U(u)`, with `U(0)=4`, gives the
leading coefficients. At `Y*`, the divided factor has zero zeroth and
first jets and second jet `(8/3)√Y*(2−κ)`. Leibniz allocations
`(1,2,0,0)` and `(1,2,2,0)` have coefficients `3` and `30`, respectively.
Reality and strict negativity of `κ` give strict positivity of `μ₅`.
The fixed-product formula follows by expanding the two logarithmic defects.

## Lean

Modules under `ArithmeticScatteringHolography/ModularBootstrap`:
`NarainMeanCentralMoments`, `NarainMeanMomentJets`,
`NarainMeanBoundaryMomentJets`, `NarainMeanExceptionalJets`,
`NarainMeanExceptionalMoments`.

Endpoints: `integrableOn_narainScalarHeatAverage_boundary_moment`,
`integral_narainScalarHeatAverage_boundary_moment`,
`narainMeanMoment_first_nonzero`,
`integral_narainMeanMomentDensity_one_product_imbalance`,
`integral_narainMeanMomentDensity_one_exceptional_three`,
`integral_narainMeanMomentDensity_two_exceptional_five_pos`.

Five direct module checks and 25 endpoint axiom audits passed; dependencies
use only `propext`, `Classical.choice`, `Quot.sound`. Umbrella imports wired.

## Unproved refinements

The full-axis moment identity on `0<Re u<1/2` still requires its
Mellin-regularization argument. Boundary moments alone do not establish
holomorphy across the boundary. Finite sign-change bounds from moment
cancellation still require a precise oscillation definition and polynomial
separation theorem. The stronger [arithmetic oscillation conjecture](../0-backlog/ads3-narain-two-sided-oscillation.md)
remains open. None of these moment identities gives an RH-strength rate
or cancels an arithmetic pole.

## Gates

- [x] 0 → 1: clock tails, Fourier differentiation and jet transport audited.
- [x] 1 → 2: actual-source moments and exact leading coefficients proved.
- [x] 2 → 3: direct Lean checks, axiom audits and umbrella imports.
