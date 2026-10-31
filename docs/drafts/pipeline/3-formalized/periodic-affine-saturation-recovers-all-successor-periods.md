# Periodic affine saturation recovers all successor periods

- **ID:** AFFINE-PERIODIC-SATURATION
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Parent:** [Subgroup-indicator successors](continuous-affine-dilations-classify-subgroup-indicator-successors.md)
- **Statement:** Let `k` be a Hermitian finite-index kernel on `Aff(ℚ)` invariant under right integer translations. If `k(T_b)=k(1)`, then `k(gT_b)=k(T_bg)=k(g)` for every affine `g`.

## Proof

For the column action of `T_b`, local periodicity splits the column space as the orthogonal sum of its fixed space and `M=range(T_b−1)`. Finite negative index and affine dilation covariance make `M` nonnegative. If `x∈M` has zero squared norm, Cauchy–Schwarz makes it orthogonal to `M`; it is also orthogonal to the fixed space. Nondegeneracy of the full column form forces `x=0`. Thus the moving space is positive definite.

Take `x=v_(T_b)−v_1`. Hermitian symmetry and `k(T_b)=k(1)` give `B(x,x)=0`, so `v_(T_b)=v_1`. Evaluating these column functions at `g⁻¹` gives right invariance. Applying right invariance at `gT_b⁻¹` gives invariance under the inverse; Hermitian symmetry then gives left invariance.

For a subgroup-indicator successor `1_H` with `1∈H`, every `b∈H` has the identity value. After the zero-axis polynomial correction supplies integer invariance, the entire subgroup `H` therefore acts trivially on the identity column. A translation orbit of a dilation column can then be averaged over its exact order in `ℚ/H`, giving projection norm equal to the reciprocal quotient order. This strengthens the full-denominator counting argument without assuming `H`-invariance.

## Lean verification

- `HeckeKreinToeplitz/Index/PeriodicSaturation.lean`: `kernelColumnPairing_moving_re_pos` makes the moving space positive definite; `periodic_saturation_right_invariant` and `isHermKernel_left_invariant_of_right` prove the general saturation law.
- `AdelicKreinGeometry/Haar/TranslationSaturation.lean`: `translation_saturation_right_invariant` and `translation_saturation_left_invariant` specialize the law to rational affine kernels of finite index.
- `BiarithmeticGeometry/Affine/SubgroupOrders.lean`: quotient orders are positive and divide reduced denominators when `1∈H`.
- `AdelicKreinGeometry/Haar/SubgroupOrbits.lean`: `subgroup_successor_right_invariant`, `subgroup_successor_affine_orbit_orthonormal`, and `subgroup_successor_projection_pairing` recover all subgroup periods and the reciprocal-order projection norm.

All modules passed direct `lake --old env lean` audits. Printed transitive axiom closures contain only `propext`, `Classical.choice`, and `Quot.sound`.
