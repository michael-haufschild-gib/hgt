# Orbifold tail family — the `RatFunc` order calculus and what is left

Cards: `rational-coarse-graining-orbifold-tail-classification`, `floquet-orbifold-tail-emergence`,
`orbifold-tail-holographic-reconstruction` (all still stage 2).

## New unconditional, axiom-clean, umbrella-wired modules

| module | contents |
|---|---|
| `HTGeometry/RationalOrder.lean` | `ratOrder Q c = mult_c(num Q) − mult_c(denom Q)`; `ratOrder_mul`, `ratOrder_algebraMap`, `ratOrder_C`, `ratOrder_inv`, `ratOrder_pow`, `ratOrder_zpow`, `ratOrder_eq_zero_iff`, `finite_support_ratOrder` |
| `HTGeometry/RationalOrderComposition.lean` | `rootMultiplicity_pow`, `rootMultiplicity_comp`, `ratFuncSubstitution_algebraMap`, `ratOrder_ratFuncSubstitution` |
| `HTGeometry/RationalInvariantOrbit.lean` | `rootMultiplicity_eq_one`, `ratOrder_relation_transport`, `ratOrder_eval_eq_of_deriv_ne_zero`, `ratOrder_eq_zero_of_orbit` |
| `HTGeometry/RationalBackwardOrbit.lean` | `exists_eval_eq`, `backwardOrbit`, `exists_backward_orbit`, `ratOrder_eq_zero_of_backward_orbit`, `ratOrder_eq_zero_of_aperiodic`, `adjoin_C_mul`, `ratFuncDegree_C_mul`, `not_isConst_algebraMap`, `eq_C_of_weight_zero_relation` |
| `HTGeometry/QuadraticNoInvariantDifferential.lean` | `quadOne = X²+1`, `quadTwo = (X−1)²`, orbit/aperiodicity lemmas, `quadOne_no_invariant_differential`, `quadTwo_no_invariant_differential` |
| `HTGeometry/QuadraticOrbifoldTail.lean` | `substitutionDeriv_algebraMap_ne_zero`, `quadOne/quadTwo_no_order_one_eigen`, `quadOne/quadTwo_eigen_eq_one` |
| `HTGeometry/FloquetOrbifoldPeriodMaps.lean` | `quadTwo_comp_quadOne = quadPow (z⁴)`, `quadOne_comp_quadTwo = quadPowShift`, `quadOne/quadTwo_pullback_current`, `quadPow/quadPowShift_invariant_relation`, `..._isInvariantDifferential`, `differentialAdjoin_le_orbifoldTail_quadPow(Shift)` |

`RationalInvariantDifferential.lean` gained `ratFuncDeriv_algebraMap` (the derivation on `RatFunc`
restricts to `Polynomial.derivative`).

## The mechanism

`ord_{R(a)}(Q)·e_a + k·m_a = ord_a(Q)` with `e_a = mult_a(R − R(a))`, `m_a = mult_a(R')`.  Away
from critical points `e=1, m=0`, so the order is constant along the map.  An injective
critical-free orbit (forward or backward) therefore forces the order to vanish, since
`finite_support_ratOrder`.  Backward orbits exist over an algebraically closed field from any point
that is neither periodic nor postcritical.  For `z²+1` the critical orbit `0,1,2,5,26,…` is real
and nonnegative, so `i` and `−1` qualify; for `(z−1)²` the critical orbit is the 2-cycle `1,0`, so
`2` qualifies.  One ramified transport (`e = 2`, `m = 1`) then gives `k = 0`, and a weight-zero
relation forces `Q` constant by degree multiplicativity.

## The one remaining obstruction

Only the **fixed** branch `Φ_R(u) = u`, `u` nonconstant of finite order, is open.
`exists_nonzero_isInvariantDifferential_or_eq_one` + the two non-existence theorems already force
`lam = 1` for every finite-order eigenvector of these maps.

Why the existing descent does not finish it: `substitutionEigen_normalized_trichotomy` returns
either an order drop, or a *coefficient ratio* satisfying a nonzero-weight eigen-relation one order
lower — the link to `u` is lost.  And the resulting configuration is realizable, so it cannot be
contradicted: at jet order one `substitutionShift_one` makes the substitution an exact scaling, so
`w = e·y₁^(−κ)` with `e ∈ C^*` satisfies `Φ_R(w)·(R')^κ = w` for every `κ`.  Note `Φ_R(w) = ρ^(−κ)·w`
is *not* a constant multiple of `w`, so these do not violate the scaling statement.

Next attack: a descent that keeps `u` (not a coefficient ratio), or exploit that `Φ_R(u) = u` makes
the whole differential field `C⟨u⟩` pointwise fixed.
