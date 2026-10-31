# Periodic affine saturation recovers all successor periods

- **ID:** AFFINE-PERIODIC-SATURATION
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Parent:** [Subgroup-indicator successors](continuous-affine-dilations-classify-subgroup-indicator-successors.md)
- **Statement:** Let `k` be a Hermitian finite-index kernel on `Aff(ℚ)` invariant under right integer translations. If `k(T_b)=k(1)`, then `k(gT_b)=k(T_bg)=k(g)` for every affine `g`.

## Paper argument

For the column action of `T_b`, local periodicity splits the column space as the orthogonal sum of its fixed space and `M=range(T_b−1)`. Finite negative index and affine dilation covariance make `M` nonnegative. If `x∈M` has zero squared norm, Cauchy–Schwarz makes it orthogonal to `M`; it is also orthogonal to the fixed space. Nondegeneracy of the full column form forces `x=0`. Thus the moving space is positive definite.

Take `x=v_(T_b)−v_1`. Hermitian symmetry and `k(T_b)=k(1)` give `B(x,x)=0`, so `v_(T_b)=v_1`. Evaluating these column functions at `g⁻¹` gives right invariance. Applying right invariance at `gT_b⁻¹` gives invariance under the inverse; Hermitian symmetry then gives left invariance.

For a subgroup-indicator successor `1_H`, every `b∈H` has the identity value. After the existing zero-axis polynomial correction supplies integer invariance, the entire subgroup `H` therefore acts trivially on the identity column. A translation orbit of a dilation column can then be averaged over its exact order in `ℚ/H`, giving projection norm equal to the reciprocal quotient order. This strengthens the full-denominator counting argument without assuming `H`-invariance.

## Novelty and verification boundary

The corpus supplies `kernelColumnPairing_normSq_le_on_subspace`, nondegeneracy of the column form, orthogonal cyclic projections, and `translation_moving_subspace_nonnegative`. Searches did not find the stated finite-index saturation law. It generalizes the positive-kernel identity-value argument to these periodic indefinite carriers.

- [x] Dependency-closed paper proof of the saturation statement.
- [ ] Formalize positive definiteness of the periodic moving space and the affine saturation law.
- [ ] Direct `lake --old env lean` audit and standard transitive axiom closure.

No Lean theorem is claimed yet. The broader subgroup-indicator classification remains open.
