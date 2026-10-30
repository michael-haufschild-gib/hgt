# A volume-one additive domain for the elliptic adeles

- **ID:** elliptic-adeles-have-a-volume-one-additive-domain
- **Stage:** 1-in-progress
- **Target:** For `K=F₃(x,y)`, `y²=x³−x`, construct an additive fundamental
  domain of `A_K/K` with normalized Haar volume one and its quotient measure.

## Candidate domain

Write `t=x/y`, `O∞` for the completed infinity integers and `m∞=tO∞`.
The proposed domain is `D=(∏finite O_v)×(F₃ t⁻¹+m∞)`.

Finite strong approximation first clears all finite poles. At infinity,
successive leading-coefficient subtraction uses affine monomials of every
pole order at least two; these orders are already realized in Lean.
The only remaining negative Laurent coefficient is the simple-pole gap.
Subtracting a constant removes the constant coefficient, leaving `D`.

For uniqueness, a diagonal element in `D` is affine because every finite
valuation is at most one. Its infinity pole order is at most one, so the
proved pole-semigroup gap makes it constant. A nonzero constant has value
one, whereas a nonzero element of `F₃t⁻¹+m∞` has value `exp(1)` or less
than one. The intersection is therefore zero.

Both `D` and the integral adelic product contain
`B=(∏finite O_v)×m∞` with additive index three. Translation invariance
therefore gives equal Haar volumes; the integral product has volume one.

## Exact formal obligations

Completed infinity pole reduction; compact/open subgroup structure of `D`;
global decomposition and uniqueness; equal-index Haar comparison; quotient
additive homeomorphism and normalized quotient measure.

## Inputs

`finiteAdele_exists_integral_difference`, `completedInfinity_sub_constant`,
`exists_affine_infinity_valuation`, `poleDegree_le_one_iff`,
`coordinateRingEquivRingOfIntegers`, `adeleHaar_integralAdeles`.
Mathlib `HeightOneSpectrum.mem_integers_of_valuation_le_one` supplies the
finite-place integrality criterion. No global quotient normalization is assumed.
