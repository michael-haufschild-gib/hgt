# The critical adelic Green inverse is unbounded

- **ID:** the-critical-adelic-green-inverse-is-unbounded
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Obstacle:** B133: distinguish pointwise critical Green finiteness from a bounded global inverse.

## Result

For the actual weighted adjacency `A=Σ_p p⁻²A_p` on counting `ℓ²(V)`,
`λ=Σ_p 2p⁻²√p` is its sharp upper spectral edge, approached by
finite nonnegative charges. The critical precision `λI−A` has no bounded
right inverse, no bounded operator has the critical Green matrix, and the
critical spherical operator integral is not
Bochner integrable, although every matrix entry is integrable and equals
the established minimal Green kernel.

The positive statement is the exact subcritical resolvent norm
`‖sphericalGreenTransform ν‖=(1/4−ν²)⁻¹` for `0<ν<1/2`, together with
finite-charge witnesses approaching the edge. These statements hold on
the actual all-prime carrier.

## Proof mechanism

1. The exact local return sum is `G_s(x,x)=1/(p^s−p^(−s))` at
   `λ_s=p^s+p^(1−s)`. At `s=1/2`, `λ′_s=0` but `G′_s(x,x)<0`.
   A finite first moment of critical return occupation would make the
   diagonal Lipschitz in `λ`, contradicting these derivatives.
2. Convergence at any `0<ell<2√p` would imply a finite critical first
   moment by exponential comparison. Thus return occupation converges
   exactly for `ell≥2√p`.
3. Suppose every finite nonnegative charge has Rayleigh quotient at most
   `c<2√p`. Choose `max(c,0)<ell<2√p` and let `v_N` be the truncated
   occupation column. Its nonnegative remainder gives
   `(ell−c)Σv_N²≤v_N(x)`; since `v_N(x)²≤Σv_N²`, its diagonal is bounded
   by `(ell−c)⁻¹`. This contradicts step 2 and yields finite charges
   approaching the local edge.
4. Tensor finite charges at a finite set of primes. Squared norms multiply;
   each local quadratic form multiplies by the other squared norms.
   Contributions from remaining primes are nonnegative. Exhausting the
   summable edge weights yields the actual all-prime edge `λ`.
5. For unit charges approaching this edge,
   `‖(λI−A)f‖²≤2λ⟨(λI−A)f,f⟩→0`. Hence no bounded inverse exists.
   The existing subcritical inverse identity then gives exact norm
   `(1/4−ν²)⁻¹`. A Bochner-integrable critical spherical average would
   produce a bounded right inverse through its already proved matrix
   entries, a contradiction.

## Formalization

All five steps are formalized:

- [ThePrimeWalkHasTheSharpTemperedSpectralEdge.lean](../../../../formal/GaloisForLFunctions/HyperbolicArakelovTheory/ThePrimeWalkHasTheSharpTemperedSpectralEdge.lean):
  `PrimeSpectralEdge.not_summable_critical_return_moment`,
  `summable_return_iff`, `supersolutions_empty_below_edge`,
  `exists_finite_charge_above`.
- [TheWeightedAdelicAdjacencyHasSharpSpectralEdge.lean](../../../../formal/GaloisForLFunctions/HyperbolicArakelovTheory/TheWeightedAdelicAdjacencyHasSharpSpectralEdge.lean):
  `WeightedAdelicGreen.exists_finite_charge_above`,
  `adjacencyOperator_norm_eq_edge`.
- [TheCriticalAdelicGreenInverseIsUnbounded.lean](../../../../formal/GaloisForLFunctions/HyperbolicArakelovTheory/TheCriticalAdelicGreenInverseIsUnbounded.lean):
  `WeightedAdelicGreen.exists_unit_critical_residual_lt`,
  `criticalPrecision_no_bounded_right_inverse`,
  `sphericalGreenTransform_norm_eq`, `no_bounded_critical_green_matrix`,
  `not_integrable_critical_spherical_operator`.

Each module passes its direct Lean check. All eleven theorem dependency
audits contain only `propext`, `Classical.choice`, and `Quot.sound`.

## Boundary

This concerns the already constructed weighted Green kernel. The
accepted obstruction to one invariant glued realization of Weil's
diagonal remains in force. Identifying Weil's diagonal remains open.
