# Generated enhanced Verdier quotient

## Status

Formalized in Lean 4. Standard-identification gap remains separately recorded.

## Classification

Not new scientific knowledge. Concrete categorical infrastructure for enhanced ind-sheaves.

## Target

Construct a concrete unbounded Verdier quotient on `X × EReal` which kills the derived essential
image of enhanced-projection pullback, without assuming unproved fullness.

## Dependency-closed paper proof

Let `D_X` be the unbounded derived category of compactly generated ind-sheaves on `X`, and let
`Lπ⁻¹ : D_X → D_{X×EReal}` be the triangulated functor induced by exact enhanced-projection
pullback. Its essential image is nonempty because it contains `Lπ⁻¹(0)`.

Take the triangulated envelope of that essential image: the smallest subcategory closed under
integer shifts, extensions, finite biproducts, isomorphisms, and retracts. This envelope is a thick
triangulated object property. Localizing at morphisms whose cones lie in it gives a triangulated
Verdier quotient. Every object in the original essential image becomes zero because the essential
image is contained in its envelope. Standard localization universal properties give descent and
factorization for every functor inverting this cone class.

## Exact standard-identification gap

The literature writes the negligible category directly as `π⁻¹D_X`. Identifying that essential
image itself with the generated envelope requires fullness of derived projection pullback. This is
expected from cohomological contractibility of `EReal`, but no such sheaf-cohomology theorem is yet
formalized here. Do not claim equality before proving fullness.

## Positive survivor

The generated quotient is unconditional, kills every base-pulled object, is triangulated, and has
the exact Verdier descent property. It is the canonical safe replacement until fullness is closed.

## Lean status

`StokesGeneratedEnhancedVerdier` formalizes derived projection image, its thick triangulated
envelope, Verdier localization, triangulatedness, annihilation of base-pulled objects, descent, and
factorization. Direct Lean check and targeted module build passed. All declarations use only
`propext`, `Classical.choice`, and `Quot.sound`.
