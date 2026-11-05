# Positive Tate dimensions form a closed initial interval

- **ID:** tate-positivity-is-downward-closed-in-dimension
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** review-0411 §2.1, A6.
- **Lean:** `WindowTowerOfSpecZ/PositivePrimeMultipliersLowerTateDimension.lean`;
  `WindowTowerOfSpecZ/PositiveTateDimensionsFormAClosedInitialInterval.lean`.

## Exact statement

At `A≤log 2`, every nonnegative Tate dimension is positive. At `A>log 2`,
the positive dimensions are exactly `[0,κ(A)]`, where
`0<κ(A)≤log₂(1+2√2)`. These sets decrease with aperture and shrink to `{0}`.
Every `0≤k<κ(A)` has a uniform positive quadratic-form floor.

## Proof

For `0≤k≤K`, `K>0`, and each prime `p`, put `t=p^(k−K)` and
`c=(p^k−1)/(p^K−1)`. Then `0≤c≤t≤1`. The sequence
`r(0)=1`, `r(m)=c t^(|m|−1)` is the convex combination
`(c/t)t^|m|+(1−c/t)[m=0]`, hence positive definite on the integers.
Taking products over prime valuations gives a positive semidefinite kernel
on every finite rational vertex set. Its value on an integer ratio `n` is
`J_k(n)/J_K(n)`. The Schur product with the dimension-`K` Hecke matrix is
the dimension-`k` matrix. The proved graph/window equivalence transfers
this implication to window tests without a finite-component assumption.
The case `K=0` is the diagonal form.

For `0≤k<K`, write
`ρ_p=(1−p^(−k))/(1−p^(−K))` and
`ε=∏_{p≤N}(1−ρ_p)>0`. Each prime kernel is
`ρ_p t_p^|v_p(r)−v_p(s)|+(1−ρ_p)[v_p(r)=v_p(s)]`.
Expanding the product retains a positive term of weight `ε` that pinches
all prime valuations. Every off-diagonal Hecke edge changes one of them,
so this term contributes exactly the diagonal to every Hecke form. Removing it
leaves a positive semidefinite kernel. The graph/window equivalence therefore gives
`τ_H(k)≥ε∫H²` at the same finite level.

Finite dependence on the coefficients then makes the positive dimensions
a closed initial interval with a strictly positive interior. Above the
first prime its endpoint is finite; the two-vertex graph bounds it by
`log₂(1+2√2)`.
At and before `A=log 2`, every nonidentity correlation vanishes and every
nonnegative dimension is positive. Above it, a constant Barta weight at
sufficiently small positive dimension makes the finite endpoint strictly positive.
Nesting in aperture and the existing negative prime-star tests then force the
whole positive interval to shrink to zero along the tower.

## Lean declarations and verification

- `tateFunction_nonneg_of_dimension_le`.
- `tateFunction_ge_dimensionMargin`;
  `exists_tateFunction_uniform_floor_of_dimension_lt`.
- `tatePositiveDimensions_beforeFirstPrime`; `exists_exact_tateHorizon`.
- `tatePositiveDimensions_antitone`; `tatePositiveDimensions_shrink_to_zero`.

Both direct `lake --old env lean` source checks passed. Ten transitive axiom
audits use only `propext`, `Classical.choice`, and `Quot.sound`.
Both modules are imported by the owning umbrella. Explicit later-stage
criteria and the critical Barta-weight question remain outside this theorem.
