# Discriminant covers and polynomial Möbius signs

- **ID:** RIAC-discriminant-cover
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean); classical finite-field calibration
- **Source:** [RIAC](../1-in-progress/renormalized-intersection-arithmetic-counts.md)
- **Statement:** Explicit cross-resultants identify the actual polynomial-discriminant and residue-field orientation covers. Their signed local weights equal polynomial Möbius signs, and independent arithmetic counts prove degree cancellation.

## Actual arithmetic comparison

For a monic polynomial `f` over a finite field, let `P₁,…,P_r` be its
normalized irreducible factors with multiplicities. Set

`R(f)=∏_i Res(P_i,∏_(j>i) P_j)`.

Let `D(f)` be the product of the residue-field power-basis discriminants
when `f` is squarefree, and zero otherwise. The formalized identity is

`disc(f)=D(f) R(f)²`.

On the squarefree locus `R(f)≠0`. Put `u(f)=R(f)` there and `u(f)=1`
elsewhere. Then `u(f)≠0` everywhere and `disc(f)=D(f)u(f)²`. The maps

`(f,y) ↦ (f,u(f)y)`,  `(f,z) ↦ (f,z/u(f))`

are inverse bijections between the two actual finite covers in every degree.
They retain the coefficient polynomial. Repeated-root fibres are included:
both discriminants vanish and the map fixes their sole point zero.

## Proof

For monic polynomials, the resultant is independent of padding its second
formal degree. Adding a multiple of its first argument preserves it.
Applying these identities to `(fg)′=f′g+fg′`, then using resultant
multiplicativity and its interchange sign, proves

`disc(fg)=disc(f)disc(g)Res(f,g)²`

over every commutative ring. Induction gives the finite-factor version.
No separability assumption is imposed on this product formula.

For a separable simple field extension, embeddings give all distinct roots
of a power-basis generator's minimal polynomial. The trace determinant and
the Sylvester discriminant are the same Vandermonde square. Thus each monic
irreducible residue-field discriminant equals `disc(P_i)` over finite fields.
The derivative resultant identifies the zero-discriminant locus with the
nonsquarefree locus. Together these facts prove the displayed square identity
and the explicit fibre bijection.

## Independent signed cancellation

Over an odd field, quadratic characters ignore the proved nonzero square.
The residue-field orientation character therefore gives Pellet's identity

`χ(disc(f))=(-1)^deg(f) μ(f)`.

The [integral cover comparison](riac-integral-discriminant-cover.md) identifies
this same character with the actual root-orbit transporter weight. Hence
`w(f)=(-1)^n μ(f)` on monic degree-`n` polynomials, point by point.
Independent normal-basis counts cancel these weights for `n≥2`; consequently

`#factorOrientationCover_n=q^n`,  `Σ_(f monic, deg f=n) μ(f)=0`.

No polynomial Möbius degree-sum theorem is used as input. The cover bijection
also applies in degrees zero and one, where the integral cover has `2` and
`2q` points over odd fields.

## Formalization

[MonicDiscriminantProducts.lean](../../../../formal/GaloisForLFunctions/HTGeometry/MonicDiscriminantProducts.lean):
`discr_mul_of_monic`, `discr_list_prod_of_monic`,
`monic_discr_eq_zero_iff_not_separable`, and monic resultant identities.

[PowerBasisPolynomialDiscriminant.lean](../../../../formal/GaloisForLFunctions/HTGeometry/PowerBasisPolynomialDiscriminant.lean):
`powerBasis_discr_eq_minpoly_discr`, `adjoinRoot_powerBasis_discr_eq`.

[FiniteFieldDiscriminantComparison.lean](../../../../formal/GaloisForLFunctions/RenormalizedIntersectionArithmeticCounts/FiniteFieldDiscriminantComparison.lean):
`discr_eq_factorTrace_mul_cross_square`, `factorCrossResultant_ne_zero`,
`discriminantFibreEquiv`, `factorOrientationCoverEquiv`,
`factorOrientationCover_card_independent`, `discriminant_character_eq_moebius`,
`frobeniusOrientationWeight_eq_moebius`,
`moebiusDegreeSum_eq_zero_of_orientation_count`.

Direct leaf checks and 23 transitive axiom audits use only `propext`,
`Classical.choice`, `Quot.sound`.

## Integer scope and classical context

This closes the finite-field discriminant-cover comparison. It supplies no
map to the integer conductor cutoff and no estimate for
`Σ_p index_p(N)=1−M(N)`. The governing target remains signed cancellation
at the square-root scale; `Oε(N^(1/2+ε))` is the RH scale and a literal
`O(√N)` bound is stronger.

Pellet's identity is classical: [Afshar, §§1–2](https://arxiv.org/html/2001.05641v1).
The ramified Frobenius-cover framework is treated by
[Gadish, Definition 1.1 and Corollary 1.4](https://arxiv.org/html/1703.01710v2).
No new classical point-count theorem is claimed.
