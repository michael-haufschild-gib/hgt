# Open extension by zero for ordinary additive sheaves

## Stage

2 — fully proven on paper

## Claim

For a universe-0 open embedding `j : U ↪ X`, construct the ordinary additive-sheaf functor `j_!`
as sheafification of presheaf left Kan extension along the image-of-open functor.  Prove `j_!` is
left adjoint to open restriction `j^*`.  Use it with closed direct image to define an ordinary sheaf
on a locally closed support.

This is underived ordinary sheaf theory.  It is not proper-support direct image, enhanced
convolution, or an enhanced ind-sheaf.

## Dependency audit

- Corpus search found ordinary direct and inverse image, but no open `j_!` implementation.
- Mathlib provides sheafification, presheaf left Kan extension, open-embedding naive pullback, and
  full faithfulness of the sheaf forgetful functor.
- `StokesClosedSupportSheaf.lean` supplies closed direct image and epigraph specialization.

## Paper proof plan

Let `L : Opens(U) → Opens(X)` send an open subset to its open image.  Open restriction on
underlying presheaves is precomposition by `Lᵒᵖ`.  For a sheaf `F` on `U`, define

`j_! F := a_X (Lan_{Lᵒᵖ}(forget F))`,

where `a_X` is sheafification.  For every sheaf `G` on `X`, sheafification adjunction, Kan-extension
adjunction, and full faithfulness of sheaf inclusion give

`Hom(j_! F,G) ≃ Hom(F,j^*G)`.

Naturality of this composite equivalence supplies the adjunction.  For a locally closed
`S = U ∩ C`, first use `j_!` inside `C` for the open inclusion `S ↪ C`, then direct image along the
closed inclusion `C ↪ X`.

## Lean status

- [x] exact functor/API scratch check
- [x] `j_!` construction in `StokesOpenExtensionByZero.lean`
- [x] adjunction to naive restriction and standard sheaf pullback
- [x] locally closed factorization and exponential-epigraph specialization
- [x] direct file check
- [x] targeted module build
- [x] axiom audit of new declarations only: `propext`, `Classical.choice`, `Quot.sound`

Repository-wide Stage 3 promotion remains blocked by unrelated pre-existing formal-lint reachability
failures recorded in the irregular-RH foundations report.  New module is wired through
`GaloisForLFunctions.HTGeometry`.

## RH status

No implication for RH.  This closes one ordinary-sheaf prerequisite only.
