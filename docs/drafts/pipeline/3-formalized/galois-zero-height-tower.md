# The complete height tower of the zero field

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** Complete height stages recover the whole zero field and its Krull-topological Galois group.

Let `K` be the complete-fibre source field, `L=ℚ(all w)`, and `P_t`
the complete source polynomial at ordinate `t`. Let `S_n` contain every
occupied ordinate with `|t|≤n`, and let `H_n` be the splitting field inside
`L` of `∏_(t∈S_n)P_t`.

## Theorem

Each `S_n` is finite and contains whole fibres. The fields `H_n/K` are
finite Galois and increase with `n`. They are cofinal among the finite
complete-fibre composita, and `sup_n H_n=L`.

Restriction gives a group isomorphism and homeomorphism

```
Gal(L/K) ≅ lim_n Gal(H_n/K),
```

where compatibility uses the actual inclusions `H_n→H_m` for `n≤m`.
Every compatible family extends uniquely to `L`; the inverse-limit
coordinates recover the full Krull topology.

## Proof

The finite zero-copy set in `[-n,n]×[-1/2,1/2]` has ordinate image `S_n`.
Every centered zero lies in the open half-width strip, so this selects
exactly the occupied fibres with `|t|≤n`. Every finite collection of
occupied ordinates has a natural height bound. Empty fibres generate `K`.
Thus every finite source compositum lies in some `H_n`, and their known
exhaustion of `L` gives height exhaustion.

Restriction respects inclusions. Equality of all restrictions implies
equality on every zero generator, hence on `L`. For a compatible family,
the global automorphisms realizing one stage form a closed subset of
`Gal(L/K)`. Any finite collection of these conditions is realized by
extending the action at its largest height, using normality. Compactness
gives a simultaneous extension. Each restriction is continuous; a continuous
bijection from the compact Galois group to the Hausdorff inverse limit is
a homeomorphism.

## Formalization

`GaloisTheoryOfZeros/TheHeightTowerOfTheZeroField.lean`:
`finiteFibreField_le_height`, `iSup_heightFibreField`,
`heightSourceRestriction_injective`, `heightSourceRestriction_surjective`,
`heightSourceGaloisEquiv`, and `heightSourceGaloisHomeomorph`.

Direct source audit passed with `lake --old env lean`. These dependency
closures contain only `propext`, `Classical.choice`, and `Quot.sound`.
