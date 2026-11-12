# Source equations of the complete signed-width divisor

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Questions:** Source-field equations; the full real-width action.

Let `K` be the complete-fibre source field, write `w_q=t_q+iδ_q`, and
let `F=K(all δ_q)`. All fibres include analytic multiplicity.

## Theorem

For every nonempty ordinate fibre of mass `n`, there is a monic polynomial
`R_t∈K[X]` whose complex root multiset is exactly its signed-width divisor.
It has degree `n`, and every complex root is real. The whole field `F` is
the compositum of these splitting fields, hence is normal over `K`.

Every source-field automorphism of a field containing a width sends it to
a width in the same complete ordinate fibre. Consequently any simultaneous
width reversal is central in `Gal(F/K)`.

These results cover all fibres and the entire infinite width field. Realness
of the widths gives no reason for them to vanish.

## Proof

Let `P_t∈K[X]` be the previously formalized complete-fibre source equation,
and put `Q(X)=P_t(X+t)`. Since `t∈K`, translation stays over `K`. The exact
product identity is

```
Q(iX) = i^n ∏_q (X−δ_q).
```

The product on the right after removing `i^n` has real coefficients. Its
coefficient of degree `j` is `i^(j−n) Q_j`. Gaussian phases are `±1` or
`±i`; a purely imaginary phase times a real coefficient can be real only
when that coefficient vanishes. Thus every coefficient belongs to `K`.
The product proves monicity, degree, and the full root multiset directly.

The root sets exhaust all widths. Adjoining their union gives `F`, proving
the splitting-field compositum and normality. Automorphisms preserve each
source equation, so they preserve its width support. Global width reversal
commutes with these permutations; widths generate `F`, proving centrality.

## Lean

`formal/GaloisForLFunctions/GaloisTheoryOfZeros/TheSourceEquationsOfTheZeroWidths.lean`

- `translatedSourceFibrePolynomial_rotation`
- `realWidthFibrePolynomial_coeff_mem_sourceField`
- `sourceWidthFibrePolynomial_monic`, `sourceWidthFibrePolynomial_natDegree`
- `sourceWidthFibrePolynomial_roots`, `sourceWidthFibrePolynomial_rootSet`
- `sourceWidthFibrePolynomial_hyperbolic`
- `realWidthField_eq_iSup_sourceWidthFields`, `realWidthField_normal_from_source`
- `sourceWidthFibrePolynomial_aut_image`, `realWidth_reversal_central`

Final source audit passed. All seven audited dependency closures contain
only `propext`, `Classical.choice`, and `Quot.sound`.
