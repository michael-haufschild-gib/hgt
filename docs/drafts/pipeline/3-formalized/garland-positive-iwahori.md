# Positive Iwahori and completed unipotent coordinates

- **Stage:** 3-formalized
- **Type:** BRIDGE / known mathematics
- **Parent:** [Garland loop Eisenstein series](../1-in-progress/garland-loop-eisenstein-over-q.md)
- **Target:** Construct the positive Iwahori and its unipotent radical inside
  the actual central loop group, with unique Gauss coordinates.

## Dependency audit

The positive-loop splitting supplies an injective homomorphism from the full
power-series matrix group. Reduction by constant coefficient is an actual
homomorphism to `SL₂(F)`. The corpus already constructs the upper-triangular
subgroup `BorelWeil.borel` and the upper-unipotent homomorphism
`FiniteRingSl2.upperHom`; their statements have been inspected. The rank-two
inverse formula is also used in `RealUpperBorelPrincipalSeries`.
These are finite algebraic inputs, not a loop Iwasawa theorem.

## Dependency-closed paper proof

Let `I` be the inverse image of the upper triangular subgroup under reduction
`SL₂(F[[X]])→SL₂(F)`, and let `U` be the inverse image of the upper unipotent
subgroup. Both are actual subgroups. In entries,

`g∈I ⇔ c(0)=0`,

`g∈U ⇔ c(0)=0, a(0)=d(0)=1`.

For `g=[[a,b],[c,d]]∈I`, the determinant relation at degree zero gives
`a(0)d(0)=1`, so `a` is a power-series unit. Direct multiplication gives the
unique Gauss decomposition

`g=L(c/a) D(a) U(b/a)`.

The lower parameter has zero constant coefficient; the diagonal parameter is
a power-series unit; the upper parameter is arbitrary. Conversely every such
triple gives an element of `I`. Recovering `a`, then `c/a` and `b/a`, from the
matrix entries proves uniqueness. The condition `g∈U` is exactly `a(0)=1`.
Thus this is an actual completed positive-unipotent group with power-series
coordinates, not a finite truncation.

For `g∈U`, the right diagonal entry `d` is a principal unit. Hence its tame
pairing with every Laurent unit is one. The positive-loop correction is
therefore one on all of `U`, including `c=0`. In the concrete Kubota coordinate
model, the canonical lift of `U` has central coordinate one and its restricted
tame cocycle is trivial. This is a consequence of the same residue formula,
not an additional splitting assumption.

The split power-series torus has trivial tame defect. Writing its diagonal
parameter as the product of its nonzero constant coefficient and a principal
unit therefore separates the finite Cartan factor from `U`. The central
extension restricted to positive loops is split, with faithful projection, so
its central factor is independent and unique. This yields the expected
central/finite/unipotent decomposition of the completed positive Borel.

## Status and limits

All four modules passed final direct `lake --old env lean` source checks at
ordinary limits, without warnings. The transitive audit reports only
`propext`, `Classical.choice`, and `Quot.sound`; the concrete rational and
real positive-Borel factorizations also typecheck. Saved audit:
[garland-positive-iwahori-axioms.txt](garland-positive-iwahori-axioms.txt).

| Exact mathematical result | Lean declaration |
| --- | --- |
| Actual Iwahori and unipotent membership | `mem_iwahoriMatrices`, `mem_positiveUnipotentMatrices` |
| Trivial tame cocycle on full positive unipotent group | `LoopSL2.positiveUnipotent_tameFactor` |
| Unique full power-series Gauss coordinates | `iwahoriGaussEquiv` |
| Unipotent condition is principal diagonal | `IwahoriCoordinates.unipotent_iff` |
| Exact finite-coordinate kernel | `iwahoriFiniteCoordinate_eq_one_iff` |
| Unique finite-torus/unipotent factors | `iwahoriTorusUnipotentEquiv` |
| Finite factor agrees with actual root-word coroot | `LoopSL2.positiveEmbedding_iwahoriFiniteCoroot` |
| Independent central and Iwahori factors | `LoopSL2.positiveBorelEmbedding_injective` |
| Unique central/finite/unipotent coordinates | `LoopSL2.positiveBorel_unique_coordinates` |

Sources: `PositiveIwahori`, `IwahoriGaussCoordinates`,
`IwahoriTorusFactorization`, and `PositiveBorelCoordinates`, all under
`GaloisForLFunctions.HTGeometry.LoopEisenstein` and wired into its umbrella.
This does not prove global Iwasawa decomposition, construct a compact
subgroup or arithmetic lattice, or supply the unipotent quotient measure.

The natural topology of the central extension must be built from split
positive-loop and Bruhat charts. No product topology on the set-theoretic
Kubota coordinates has been asserted.
