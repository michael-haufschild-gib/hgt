# Exactness of covariant ind-extension

## Status

Formalized in Lean 4. No conjectural hypothesis introduced.

## Classification

Not new scientific knowledge. Missing formal categorical infrastructure.

## Target

For small abelian categories `C,D` and an exact functor `F : C → D`, prove that the covariant
ind-extension `Ind.map F : Ind C → Ind D` preserves finite limits and finite colimits, hence
homology and quasi-isomorphisms of degreewise-mapped complexes.

## Proven dependencies

- `StokesIndFunctorExtension`: covariant presheaf-left-Kan ind-extension and Yoneda comparison.
- `StokesProperPullbackExact`: enhanced-projection pullback on small compact-support models is exact.
- `StokesEnhancedIndProjectionPullback`: concrete ind-extension and comparison on representables.

## Dependency-closed paper proof

Let `A = colimᵢ y(Cᵢ)` be a filtered presentation of an ind-object. Presheaf left Kan extension is
a left adjoint, hence

`Lan(Fᵒᵖ)(A) ≅ colimᵢ Lan(Fᵒᵖ)(y(Cᵢ)) ≅ colimᵢ y(F(Cᵢ))`.

Thus `Lan(Fᵒᵖ)` restricts to `Ind.map F : Ind(C) → Ind(D)` and agrees with `F` on representables.
If `F` preserves finite limits, mathlib's presheaf theorem says `Lan(Fᵒᵖ)` preserves finite limits;
the ind inclusions create and reflect finite limits, so `Ind.map F` preserves them.

If `F` preserves finite colimits, `Fᵒᵖ` preserves finite limits. Precomposition along `Fᵒᵖ`
therefore carries left-exact presheaves to left-exact presheaves, equivalently ind-objects. Restrict
the presheaf adjunction

`Lan(Fᵒᵖ) ⊣ (- ∘ Fᵒᵖ)`

along the fully faithful ind inclusions. Hence `Ind.map F` is a left adjoint and preserves all
existing colimits, in particular finite colimits. An exact `F` therefore induces an exact
`Ind.map F`.

If `F` is also fully faithful, the unit of the presheaf Kan adjunction is an isomorphism. The unit
of its restriction to ind-objects maps under the fully faithful ind inclusion to a composite of
that unit with comparison isomorphisms. It is therefore an isomorphism, so the restricted left
adjoint `Ind.map F` is fully faithful.

## Lean status

- `StokesIndFunctorExtension`: presentation transport, restriction to ind-objects, underlying-Lan
  comparison, representable comparison.
- `StokesIndFunctorExact`: finite-limit preservation, restricted right adjoint, adjunction, and
  finite-colimit preservation; full faithfulness when the original functor is fully faithful.
- `StokesEnhancedIndProjectionPullbackExact`: exactness and homology preservation for enhanced
  ind-pullback.
- `StokesDerivedEnhancedIndPullback`: canonical unbounded derived-category lift, degreewise
  factorization, shift compatibility, and triangulatedness.
- Direct Lean checks and targeted module builds passed. All new and changed declarations use only
  `propext`, `Classical.choice`, and `Quot.sound`.

## Ruled-out shortcuts

- Inferring exactness from agreement on representables: invalid without filtered-colimit
  preservation and an exactness argument.
- Using presheaf restriction along `Fᵒᵖ` as covariant extension: wrong variance.
- Descending degreewise `Ind.map F` before proving homology preservation: would assume the result.

## Downstream opened by this theorem

- Concrete negligible subcategory `π⁻¹D(IndSheaf X)`.
- Instantiation of the abstract enhanced Verdier quotient.

## Positive survivor already formalized

`StokesDerivedSmallEnhancedPullback` remains the universe-small model. The stronger
`StokesDerivedEnhancedIndPullback` now supplies the corresponding derived functor on ind-sheaves.
