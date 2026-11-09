# Finite Weyl conjugation retains the global degree configuration

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Obstacle:** B133, global carrier geometry.
- **Statement:** A discrete finite Weyl conjugate of the rational adelic group
  separates every original square-degree point.

## Exact construction and theorem

Let `K_p=SL₂(ℤ_p)`, `g_q=diag(q,q⁻¹)`, and let `V` be the finite-support
restricted product of the actual coset spaces `SL₂(ℚ_p)/K_p`. The rational
diagonal embedding into `SL₂(ℂ)×Π'_p SL₂(ℚ_p)` is faithful and discrete.
In its quotient of `ℍ³×V`, for positive integers `a,b`,

`[(z_{(ab)²}, (g_{a/b}K_p)_p)] = [(z_{b⁴}, (K_p)_p)]`.

Two such classes agree exactly when their factors `b` agree. Principal
orientation collapses all square degrees; opposite finite orientation separates
them. Set `J=(1,(w)_p)`, where `w=[[0,-1],[1,0]]`. The group
`J⁻¹SL₂(ℚ)J` is discrete, and the original points
`x_{n²}=(z_{n²},(g_nK_p)_p)` have pairwise distinct classes in its quotient.
Thus changing the arithmetic gluing retains the original configuration.

## Proof mechanism

Denominators give finite support of every rational matrix. Integrality at every
finite place forces rational entries to be integers; an archimedean unit
neighbourhood then isolates the identity. Normalize the finite component by
`g_{a/b}⁻¹` to obtain height `b⁴`. The remaining finite stabilizer is integral.
For its bottom row `(c,d)` and height `t≥1`, the hyperbolic denominator
`c²t²+d²≥1`; applying this inequality to a matrix and its inverse proves height
rigidity. The finite Weyl element reverses the diagonal and fixes every base
vertex, transferring this separation to the original points.

## Formalization and scope

[TheOppositeAdelicDegreeConfiguration.lean](../../../../formal/GaloisForLFunctions/HyperbolicArakelovTheory/TheOppositeAdelicDegreeConfiguration.lean)
proves `arithmeticGroup_discrete`, `splitDegree_eq_iff`,
`conjugateArithmeticGroup_discrete`, and
`original_degree_injective_on_conjugate_carrier` in namespace
`GaloisForLFunctions.HyperbolicArakelovTheory.OppositeAdelic`.
Direct source audit passed; all eleven capstone axiom audits contain only
`propext`, `Classical.choice`, and `Quot.sound`. Umbrella import added.

This constructs the determinant-one local vertex spaces and handles square
degrees. Full `PGL₂` tree geometry, all degrees, the global Green operator,
the off-diagonal Frobenius identity, and Weil's Robin diagonal remain open.
One contribution: the carrier construction and its exact orbit classification.
