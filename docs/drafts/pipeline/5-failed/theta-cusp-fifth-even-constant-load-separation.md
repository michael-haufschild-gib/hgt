# Fifth even theta source: constant load separation

- **Stage:** 5-failed; constant correction with nonnegative fifth load refuted in Lean.
- **Wall:** Σ6; the integrated rank-nine sign remains open.
- **Claim:** No real fourth load and nonnegative fifth load make the corrected source globally positive semidefinite; the actual weighted representative also fails at every critical aperture.
- **Positive survivor:** Exact signed load region preserving the positive origin head and the positive scale-seven direction at every critical aperture; paper proof and Lean formalization complete.

Let `C₀=−S₄(0)/(3Φ(0)²)`. The complete modular coefficient band gives
`333·10⁹<C₀<10¹²`. The corrected fourth head at zero is positive definite
exactly when `C>C₀`; positive semidefiniteness requires `C≥C₀`.

At `x=½log(7/π)`, use `v=(-658560,47040,-420,1,-1/1568)`, native energy
`E=vᵀH₅v`, and `G=3Φ²+2xΦΦ′`. The exact radial polynomial bound sharpens
the retained energy to `E₂<10¹²Φ₁²`. With the proved Cauchy error
`|E−E₂|≤350·10⁹Φ₁²`, this gives `E<1.35·10¹²Φ₁²`. Since
`G≤−(229/55)Φ₁²`, the positive native capacity `B=E/(-G)` satisfies
`B<330·10⁹<C₀`.

A globally positive semidefinite corrected fifth block would therefore
require both `C≥C₀` and `C+D/1568²≤B`. These are incompatible with `D≥0`.
This excludes every real `C`, not merely the previously fixed `10¹²`.

The exact surviving region for a strict origin head and a positive witness
direction at every critical aperture is

`C>C₀` and `D≤1568²(B−C)`.

It is nonempty and forces `D<0`. For example, take `C=C₀+1` and
`D=1568²(B−C−1)`; this also leaves the native witness direction positive.
The statement concerns the origin fourth head and the specified direction;
it does not assert positivity of the complete fifth block or its integral.

The stronger modular reserve `−P₄−2·10¹²P₃P₀>0` follows by shifting
`X=(191+z)/10`, `z≥0`: every coefficient of the difference is positive.
Hence `C₀>660·10⁹`. The existing weighted bound `K_a′≤−3wΦ₁²` and the
sharper energy give `B_a<450·10⁹`, uniformly for `0<a<1/2`.

To recover the origin condition from weighted positivity on positive radii,
write `δ_a=K_a′−wG`. The exact flux identity and
`0<t cosh(t)−sinh(t)<t sinh(t)` give `0≤δ_a≤w a r Φ(r/2)²`.
For every real `C`, the weighted fourth-head quadratic form is therefore
at most `w` times the native corrected fourth-head form plus
`|C| a r Φ(r/2)²v₃²`. This upper form is continuous at zero and equals
the corrected origin head there. Global weighted positivity thus forces
`C≥C₀`; at scale seven it forces `C+D/1568²≤B_a<C₀`, contradicting `D≥0`.
The strict uniform gap is `B_a+210·10⁹<C₀`.

Lean: `ThetaCuspSections/FifthEvenInheritedLoadBoundary.lean`, namespace
`GaloisForLFunctions.ThetaCuspSections.EvenFiveBoundary`.
`constant_source_repair_fails` excludes simultaneous source positivity at
the two explicit centers; `constant_weighted_repair_fails` excludes global
weighted positivity at each critical aperture. The positive survivor is
`signed_boundary_region_iff` and `exists_signed_boundary_repair`.
Canonical Lean check passes. All 23 public theorem axiom audits contain only
`propext`, `Classical.choice`, and `Quot.sound`; the owner umbrella imports
the module.
