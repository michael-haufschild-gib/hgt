# Monoidal tensor on chain complexes of module presheaves

## Classification

- Stage: 3 — formalized
- Status: `[LEAN-PROVED]`; exact theorem surface verified
- Scientific status: `[BRIDGE]` / standard homological-algebra infrastructure
- Route: irregular microlocal Riemann--Hilbert foundations
- Novelty claim: none

## Exact claim

Let `C` be a small category and `A : Cᵒᵖ ⥤ CommRingCat` a presheaf of
commutative rings. The category of nonnegative chain complexes of module
presheaves over `A` has the standard monoidal structure whose degree-`n` object is
the finite coproduct of `Kᵢ ⊗ Lⱼ` over `i + j = n`, with signed total
differential. Its tensor functor, unit, associator, and unitors can therefore be
exposed in Lean.

This claim does **not** say tensor preserves quasi-isomorphisms. It constructs
neither K-flat replacements nor a tensor on the derived category.

## Dependency and duplication audit

- `scripts/formal_tools.py research "homological complex monoidal sheaf tensor chain complex"`:
  no corpus declaration supplies this tensor for module presheaf complexes.
- `StokesPresheafDerivedTensor.lean` proves additivity of tensoring on either side
  and enough projectives for module presheaves.
- Mathlib's `Algebra.Homology.Monoidal` constructs the monoidal category of chain
  complexes once tensor is additive, relevant coproducts exist, and tensor
  preserves them.
- Module-presheaf tensor preserves colimits on both sides. The only missing
  instance for this specialization is additivity of the curried tensor functor
  in its first variable as a functor into the functor category.
- Mathlib contains no K-flat predicate or general theorem that this tensor
  preserves quasi-isomorphisms.

## Paper proof

Module presheaves over `A` form an abelian symmetric monoidal category. Tensoring
with any fixed object on either side preserves colimits and is additive. To prove
the curried tensor functor additive, evaluate its map on a morphism sum at an
arbitrary second tensor factor. The component is `(f + g) ▷ Z`, which equals
`f ▷ Z + g ▷ Z` by additivity of right tensoring. Extensionality in `Z` proves
additivity in the functor category.

For nonnegative chain complexes, every degree of the total tensor uses only the
finite set of pairs `(i,j)` satisfying `i + j = n`. Finite coproducts exist, and
left and right tensor preserve them. Mathlib's homological-complex monoidal
construction therefore supplies total tensor, signed differential, tensor unit,
associator, and unitors with their coherence laws.

## Hostile review

- Degreewise projectivity or flatness is not asserted for arbitrary complexes.
- No quasi-isomorphism preservation theorem is available from monoidal coherence
  alone.
- The resulting tensor lives on chain complexes, not the derived category.
- Nonnegative chain complexes are sufficient for projective resolutions used by
  the existing degreewise left-derived API, but not for an unbounded enhanced
  category.
- This is not sheaf tensor: it remains in module presheaves.

## Lean certificate plan

1. Prove additivity of the curried module-presheaf tensor by natural-transformation
   extensionality and existing right-tensor additivity.
2. Instantiate mathlib's monoidal construction for nonnegative chain complexes.
3. Expose chain tensor, unit, associator, and unitors.
4. Check only axioms of declarations created here; run direct file check and one
   targeted module build.

## RH relevance and boundary

This supplies the coherent chain-level tensor needed before a K-flat or
projective-resolution comparison can descend tensor to a sheaf/enhanced derived
category. Quasi-isomorphism invariance, sheafification compatibility at chain
tensor level, and the zero-independent arithmetic source remain open.

## Lean certificate

- Module: `GaloisForLFunctions.HTGeometry.StokesPresheafComplexTensor`
- Direct check: `lake env lean GaloisForLFunctions/HTGeometry/StokesPresheafComplexTensor.lean`
- Targeted build: `lake build GaloisForLFunctions.HTGeometry.StokesPresheafComplexTensor`
- Result: both passed on 2026-08-24; targeted build completed 8662 jobs in 4.3 seconds.
- Created declarations: module-presheaf and chain-complex abbreviations, curried-tensor
  additivity, monoidal chain-complex structure, tensor bifunctor, tensor unit,
  associator, and left/right unitors.
- Batched axiom audit of all nine created declarations:
  `[propext, Classical.choice, Quot.sound]`.
- No `sorry`, `admit`, new `axiom`, `opaque`, or `unsafe` declaration introduced.
- Authoritative repository lint passed on 2026-08-27.
