# Joint gauge germs force complex normal summability

- **ID:** B130-complex-normal-gauge-classification
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** Common isozeric half-planes and bounded holomorphic prime phases.

## Target

Let `u_p(z)` be holomorphic on one parameter disk, uniformly bounded
there, with `u_p(0)=1` and actual unit prime phases for real parameters.
Suppose the actual gauge regularization is jointly holomorphic at `(0,1)`.
Then there exist a smaller radius `r>0` and `1/2<σ<1` such that

`Σ_p p^(-σ) sup_{|z|≤r}|u_p(z)-1| < ∞`.

This would give a normally convergent joint Euler logarithm difference
on a product of a complex parameter disk and a half-plane left of one.
The original regularization would have a joint normal form `Z(s)exp(H(z,s))`.

## Paper proof

Unit prime coordinates at zero identify the central Euler product with ζ;
continuity of the regularization fixes `U(0,1)=1`.
Write `f_p=u_p-1`; these functions have a common complex bound `M>0`.
The common-pole theorem gives `σ₀∈(1/2,1)` and a real interval about zero
on which `Σ_p p^(-σ₀)|f_p(t)|` converges at every point.

1. The closed sets on which every finite partial sum is at most `n`
   cover this interval. Baire gives a closed subinterval `J=[c-r,c+r]`
   with a common finite-sum bound `C`. Choose the initial interval inside
   a sufficiently small part of the holomorphy disk.
2. Put `A_p=∫_J |f_p(t)|dt+p^(-2)>0`. Integrating the finite-sum bounds
   proves `Σ_p p^(-σ₀) A_p<∞`. Cauchy's derivative estimate supplies a
   common Lipschitz constant `L` on `J`. At an inner point with height
   `m=|f_p(t)|`, the interval of length `m/(2(L+M/r))` to its right lies
   in `J` and has height at least `m/2`. Thus, on the middle half of `J`,
   `|f_p(t)|²≤4(L+M/r) A_p`.
3. For a bounded holomorphic `f` on the unit disk, assume `|f|≤m` on
   its real diameter and `0<m≤M`. On the upper half-disk use
   `q(z)=-2iz+z²` and `g=f exp(-log(M/m)q)`.
   On the diameter `Re q≥0`; on the upper semicircle `Re q≥1`.
   The maximum principle gives `|g|≤m`. For `|z|≤1/8`, `Re q≤1/2`,
   hence `|f(z)|²≤Mm`. Apply the same argument to `f(-z)` below the
   diameter. The case `m≥M` follows from the global bound.
   Scaling and step 2 give `sup_{|z-c|≤r/16}|f_p(z)|≤C₁ A_p^(1/4)`.
4. Connect `c` to zero by a finite chain of disks lying strictly inside
   the original disk. Each three-circle step replaces a relative bound
   `a` by `a^(1/2)`. After `N` steps, for some `ρ>0` and common `C₂`,
   `sup_{|z|≤ρ}|f_p(z)|≤C₂ A_p^α`, where `α=2^(-N)/4∈(0,1)`.
   If an initial bound exceeds `M`, the same inequality follows from
   `|f_p|≤M`; thus every prime is covered.
5. Weighted Cauchy–Schwarz turns summability of `a_p² p^(-(1-δ))`
   into summability of `|a_p| p^(-(1-δ/4))`. Apply it `N+2` times to
   `A_p`, obtaining summability of `A_p^α` at
   `σ=1-(1-σ₀)/4^(N+2)∈(1/2,1)`. Step 4 then bounds the exact closed-disk
   suprema by a constant multiple of this summable family.

## Lean theorem

[`ComplexNormalSummability.lean`](../../../../formal/GaloisForLFunctions/ArithmeticWeightTheory/GaugeDeformations/ComplexNormalSummability.lean):
`joint_gauge_complex_normal_summability` proves the exact closed-disk
supremum statement. `exists_complex_normal_majorant` gives the underlying
majorant theorem for any bounded holomorphic prime family with pointwise
real summability below one. `regularized_prime_normalized_residue` derives
the central residue from `u_p(0)=1`; no condition on unused gauge
coordinates is imposed.

[`RealNormalControl.lean`](../../../../formal/GaloisForLFunctions/ArithmeticWeightTheory/GaugeDeformations/RealNormalControl.lean)
proves the Baire, integration, and Lipschitz peak estimates.
[`NormalPropagation.lean`](../../../../formal/GaloisForLFunctions/ArithmeticWeightTheory/GaugeDeformations/NormalPropagation.lean)
proves the half-disk barrier and finite three-circle propagation.

Final direct checks of all three modules passed without warnings.
Transitive axiom audits contain only `propext`, `Classical.choice`, and
`Quot.sound`.

## Corpus boundary

`joint_pole_common_isozeric_halfPlane` gives a shared exponent for real
fibres. `exists_linearEulerChange_normal_bound` proves a joint normal
bound for linear phase flows; `phaseEulerLog_tsum_regular` works where
the undisturbed damping is summable. Searches found these predecessors,
not complex normal summability below one for arbitrary nonlinear phases.
No external novelty claim; B130's arithmetic Stepanov estimate remains open.

[Joint Euler factorization](joint-gauge-germs-have-a-normal-euler-factorization.md).
