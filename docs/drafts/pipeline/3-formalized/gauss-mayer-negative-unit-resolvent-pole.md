# Negative-unit inverse pole behind determinant cancellation

- **Stage:** 3-formalized
- **Type:** Theorem
- **Parent:** [negative-unit real nonvanishing](gauss-mayer-negative-unit-real-nonvanishing.md).
- **Input:** [positive-unit source pole](gauss-mayer-positive-real-pole-coefficient.md).

## Theorem

Let `u_w(z)=1−(1+z)^(-w)`, `F(w)f=f(0)u_w`, and `G(w)=(I+R(w))⁻¹`.
For every real `w>0` and every complex `t`, the actual operator
`I+R(w)+tP` is invertible, with exact inverse

`(I+R(w)+tP)⁻¹=(I−tF(w))G(w)`.

Throughout the complex half-plane `Re w>0`, the factorization
`I+R+tP=(I+R)(I+tF)` proves that scalar-mode perturbation preserves
invertibility. The factor `I+tF` has inverse `I−tF`.

Near `w=1`, both `F` and `G` are holomorphic, and the actual source inverse
has a genuine simple pole with nonzero rank-one residue

`(w−1)(I+L(w))⁻¹ → Q = −F(1)G(1) ≠ 0`.

Its negative-unit determinant is holomorphic and nonzero at the same point.
The signed determinant product `D(w,−1)D(w,1)` has order exactly `−1`.

## Proof

1. The exact response satisfies `(I+R)u=1` and `u(0)=0`. Hence `F²=0`,
   `(I+R)F=P`, and the displayed factorization holds. Multiplication by
   `I−tF` proves the invertibility equivalence.
2. Real-source determinant nonvanishing and the actual Fredholm
   invertibility equivalence make `I+L` a unit. Since `L=R+ζP`, the
   factorization makes `I+R` a unit. Its inverse gives the exact formula
   for every complex `t`.
3. The response equals the negative of the first entire branch remainder
   applied to `1`. Thus `u` and `F` are entire. Operator-norm holomorphy
   of `R`, openness of the unit group, and analytic inversion give
   holomorphy of `G` near one.
4. Substituting `t=ζ(w)` gives `(I+L)⁻¹=G−ζFG` near one. With the
   analytic scalar numerator `Z(w)=(w−1)ζ(w)`, filled by `Z(1)=1`,
   the function `H(w)=(w−1)G(w)−Z(w)F(w)G(w)` is holomorphic near one.
   On the punctured neighborhood it equals `(w−1)(I+L(w))⁻¹`, and
   `H(1)=Q`.
5. The residue is exactly `−u_1 ⊗ (e₀∘G(1))`. On the concrete input
   `(I+R(1))1`, it returns `−u_1≠0`; nonvanishing of `u_1` follows
   from its response equation. Consequently the source inverse has no
   continuous extension through one.
6. The negative-unit determinant is an analytic unit at one. Multiplying
   the certified positive-unit simple pole by this unit preserves order.

## Lean certificate

`RenormalizedIntersectionTheory/GaussMayerNegativeUnitResolventPole.lean`,
namespace `MayerResolvent`:

- `responseShear_twice`, `perturbed_factorization`, `source_factorization`,
  `perturbed_isUnit_iff`, `remainder_isUnit_real`, `perturbed_inverse_real`;
- `response_eq_entireRemainder`, `differentiable_responseShear`,
  `analyticAt_remainderInverse_one`, `sourceInverse_eventually_eq`;
- `inversePoleResidue_rank_one`, `inversePoleResidue_ne_zero`,
  `analyticAt_clearedSourceInverse_one`, `sourceInverse_residue`,
  `not_continuousAt_sourceInverse_one`, `signed_source_product_simple_pole`.

The direct production check passes without diagnostics. All 16 transitive
axiom audits contain only `propext`, `Classical.choice`, and `Quot.sound`.
Umbrella import wired.

## Scope

The source operator is meromorphic: determinant cancellation leaves its
inverse's source pole intact. Invertibility is proved on the positive real
axis and a complex neighborhood of one. General complex-source resonance
exclusion, primitive modular coding, and Selberg/scattering comparison remain
open. No RH conclusion or literature-priority claim follows.
