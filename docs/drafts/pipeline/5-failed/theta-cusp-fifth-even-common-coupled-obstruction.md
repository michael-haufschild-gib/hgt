# Equal coupled theta loads fail globally

- **Stage:** 5-failed; native and weighted obstructions formalized.
- **Wall:** Σ6; integrated rank-nine positivity remains open.
- **Claim:** No real common coefficient of `u₁u₁ᵀ+u₂u₂ᵀ` makes the fifth even source globally positive semidefinite, including its literal weighted flux representative at any `0<a<1/2`.
- **Positive survivor:** The independent pair `(C,D)=(10⁸,10¹²)` is positive definite at the origin. Its origin-neighborhood, Gaussian-tail and integral-preservation extension has a complete paper proof and Lean formalization.

Put `u₁=(0,0,1,420,0)`, `u₂=(0,0,0,1,1568)`,
`N=u₁u₁ᵀ+u₂u₂ᵀ`, and `G=3Φ²+2xΦΦ′`.
The normalized origin Schur matrix after the first two coordinates has
negative second leading minor at `C=D=10⁹`. This is an exact polynomial
inequality on the actual modular interval `19.1≤X≤19.2`. Since `G(0)>0`
and `N≽0`, positivity of `H(0)+C G(0)N` therefore forces `C>10⁹`.

At `x₇=½log(7/π)`, the complete eighth reflection derivative satisfies
`H₂₂(x₇)<3·10⁹ f₁(x₇)²`, while `G(x₇)≤−(229/55)f₁(x₇)²`.
The first bound retains both theta atoms and pays the exact Cauchy tail.
Thus the coordinate `e₂` is negative for every `C≥10⁹`, contradicting
the origin requirement.

For `w_a(r)=r sinh(ar)`, the weighted source is `w_a H(r/2)+C K_a′N`.
The established slack bound
`0≤K_a′−w_aG(r/2)≤w_a a r Φ(r/2)²` transfers global weighted
positivity to native origin positivity by continuity. At `r=2x₇`,
`K_a′≤−3w_a f₁²`; the same coordinate is strictly negative for every
`C≥10⁹`. This excludes every real common coefficient at each critical aperture.

Independent coefficients escape this origin restriction. For
`(C,D)=(10⁸,10¹²)`, all three denominator-cleared origin Schur leading
minors are strictly positive on the actual modular interval. The resulting
[unequal repair](../3-formalized/theta-cusp-fifth-even-unequal-origin-repair.md)
preserves the common positive kernel and the scale-seven eighth-degree
witness. The [sixth-degree obstruction](theta-cusp-fifth-even-large-coupled-load-obstruction.md)
also excludes this fixed unequal pair globally. Its exact positive capacity
region retains the smaller pair `(10⁷,10¹²)` in that direction. This smaller
pair also has a [formalized origin-and-tail repair](../3-formalized/theta-cusp-fifth-even-reduced-coupled-repair.md),
but its [full Schur direction fails](../5-failed/theta-cusp-fifth-even-reduced-coupled-schur-obstruction.md).

Lean: `EvenFiveOrigin.coupled_common_origin_load_needed`,
`coupled_common_source_fails`, `coupled_common_weighted_fails`, and
`coupledRepair_unequal_zero_posDef` in
`ThetaCuspSections/FifthEvenOriginObstruction.lean`. All pass standard-axiom
audits and the canonical module check. The owner umbrella imports the module.
