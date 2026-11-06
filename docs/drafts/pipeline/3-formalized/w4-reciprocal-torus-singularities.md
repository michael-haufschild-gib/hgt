# W4 — the singularities of the reciprocal torus locus

- **Stage:** 3-formalized
- **Type:** THEOREM
- **Statement:** On `Σx_i=Σx_i⁻¹=0` with nonzero coordinates, dependence of the two differentials is equivalent to equality of all `x_i²`. After normalizing one coordinate to one, every critical coordinate is `±1`.

## Quadratic structure

At a normalized critical point, the reciprocal equation along a sum-zero tangent vector `v` has quadratic term `Σx_i v_i²`. The associated diagonal pairing has radical exactly the scaling line on `Σv_i=0`. Fixing the leading coordinate removes this radical. In characteristic different from two, the transverse Hessian is therefore nondegenerate.

## Proof mechanism

The annihilator of the sum-zero hyperplane consists of constant covectors, tested on differences of coordinate vectors. Apply this to the reciprocal differential with coefficients `−x_i⁻²`. Euler's identity `d(Σx_i⁻¹)_x(x)=−Σx_i⁻¹=0` shows that fixing the leading coordinate preserves criticality on the double-zero locus.

For the quadratic pairing, apply the same annihilator theorem to coefficients `x_i v_i` and use `x_i²=1`. The exact formal inverse is `Σ_n x_i⁻¹(−v_i x_i⁻¹)^n t^n`. Its first three coefficients are `x_i⁻¹`, `−x_i⁻²v_i`, and `x_i⁻³v_i²`. At a normalized critical point these give zero constant and linear terms and quadratic term `Σx_i v_i²`. Polarization gives twice the diagonal pairing. For `v` with zero coordinate sum and zero leading coordinate, testing against `w−w_0x` extends vanishing from the normalized tangent space to the full sum-zero hyperplane; the scaling coefficient then vanishes.

## Scope

The result is the exact differential and transverse quadratic-form classification, including its application to the tuples in the moment identity. No scheme smoothness or cohomological weight theorem is asserted. Boundary analysis and an arithmetic family containing ζ remain separate obligations.

## Lean

[`ReciprocalTorusSingularities.lean`](../../../../formal/GaloisForLFunctions/ArithmeticKunnethTheory/WeightFamilies/ReciprocalTorusSingularities.lean), namespace `ArithmeticKunnethTheory.WeightFamilies`:

- `sum_zero_annihilator_iff`, `reciprocal_critical_iff`: constant covectors and equality of squared coordinates.
- `reciprocal_projective_critical_iff`, `normalizedDoubleZeroTorus_critical_iff`: exact sign classification in the projective chart and the actual moment locus.
- `reciprocalLineInverse_mul`, `reciprocalSeries_linear`, `reciprocalSeries_quadratic`: formal inverse and its first coefficients.
- `reciprocalPairing_radical_iff`: radical equals the scaling line.
- `reciprocalHessian_transverse_nondegenerate`: nondegenerate transverse Hessian when `2≠0`.

Direct Lean check passed.
