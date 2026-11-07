# Möbius becomes a cubic Gauss coefficient

- **ID:** mobius-cubic-gauss-conversion
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** A Möbius-weighted conjugate sextic Gauss sum equals a cubic Gauss sum times an explicit factor of unit modulus.

## Exact statement

Let `P_i` be distinct Eisenstein primes away from two and three, with canonical
primary generators `p_i`. Put `I=∏P_i`, `p=∏p_i`. The actual sextic residue
character `χ_i` has square equal to the cubic residue character and cube equal
to the quadratic residue character.

For any primitive additive character `ψ` on `O/I`, let `ψ_i` be its CRT
coordinate restrictions and let `G_j` be the actual residue sum on `O/I`
with multiplicative character `∏χ_i^j`. Then

`(∏χ_i(4)) G₁G₂ = μ_K(I) p G₃`,

`μ_K(I) conjugate(G₁) = c(I,ψ) G₂`, where

`c(I,ψ) = ∏_i [χ_i(4) #O/P_i / (p_i G(χ_i³,ψ_i))]`,

and `|c(I,ψ)|=1`. A fixed complex embedding is understood. A definite primitive
composite character also gives a canonical instance of these identities.

## Proof

The square map has `1+χ₂(y)` preimages at `y`. Counting its fibres and changing
variables by `t=2x−1` gives `J(χ,χ₂)=χ(4)J(χ,χ)`. The Gauss–Jacobi product
identities and nonvanishing of primitive Gauss sums give
`χ(4)G₁q=G₃G₂²`. Combining this with `G₂³=−pq` gives
`χ(4)G₁G₂=−pG₃`. Multiply by `conjugate(G₁)` and use `|G₁|²=q` to obtain the
explicit local conversion. Its factor has norm one since `|p|=|G₃|=√q` and
`|χ(4)|=1`.

CRT factors the composite sums and preserves local primitivity. Multiplication
assembles the local minus signs into the ideal Möbius function and preserves
the unit norm of the explicit factor.

## Lean and scope

Module: `GaloisForLFunctions/MetaplecticMobiusDescent/MobiusBecomesACubicGaussCoefficient.lean`.

- `JacobiQuadratic.jacobi_quadratic`, `JacobiQuadratic.gauss_sextic_relation`
- `Eisenstein.sextic_cubic_gauss_product`, `Eisenstein.sexticResidueGauss_product`
- `Eisenstein.neg_star_sexticGauss_eq_cubic`
- `Eisenstein.norm_compositeConversionFactor`
- `Eisenstein.moebius_star_sexticGauss_eq_cubic`
- `Eisenstein.canonical_moebius_conversion`

Direct `lake --old env lean` audit passed. Eight endpoint axiom audits use only
`propext`, `Classical.choice`, `Quot.sound`. Umbrella import wired. The quadratic
Jacobi and Hasse–Davenport proofs are adapted from the external OpenAI sources;
source attribution and license accompany the module.

## Analytic normalization and fixed ray phase

For the actual character `ψ_p(x)=exp(2πi Tr(x/[p(1+2ω)]))`, set
`A(p)=G_quadratic(p)/‖p‖` and `R(p)=(p/(2))₃/A(p)`. Then

`μ_K(I) conjugate(G₁)=R(p)(‖p‖/p)G₂`.

The factor `R` depends only on `p mod 4`, has norm one on squarefree primary
products away from six, and equals one when `p≡1 mod 4`.

Square-root counting over each odd residue field identifies its quadratic
Gauss sum with `Σ_x ψ(x²)`: the extra constant term vanishes by primitivity.
CRT therefore identifies `G₃` with the actual quadratic trace sum modulo `p`.
The evaluated quadratic phase gives `G₃=‖p‖A(p)`, while the residue orders
multiply to `‖p‖²`. Substitution in the conversion factor proves the formula.
Cubic reciprocity against the inert prime two fixes the numerator modulo two;
the quadratic evaluation fixes the denominator modulo four. Unit norm follows
from the previously proved norm of the conversion factor and `|‖p‖/p|=1`.

Module: `MetaplecticMobiusDescent/TheAnalyticConversionHasAFixedRayPhase.lean`.
Endpoints: `analytic_sextic_third_eq_quadratic`,
`rayConversionPhase_eq_of_mod_four`, `analyticConversionFactor_eq_rayPhase`,
`rayConversionPhase_norm_primaryProduct`,
`analytic_moebius_conversion_fixed_ray`,
`analytic_moebius_conversion_principal_ray`.
Direct Lean audit passed; all six axiom audits contain only `propext`,
`Classical.choice`, `Quot.sound`.

Theta identification and mean-square descent remain on
[metaplectic-mobius-descent](../1-in-progress/metaplectic-mobius-descent.md).
