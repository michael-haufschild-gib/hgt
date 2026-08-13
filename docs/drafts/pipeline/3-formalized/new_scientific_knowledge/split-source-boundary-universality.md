# Split source-boundary universality — formalization certificate

- **ID:** `split-source-boundary-universality`
- **Stage:** 3-formalized
- **Paper proof:**
  `other/split-source-boundary-universality.md`
- **Umbrella:** `formal/GaloisForLFunctions/HTGeometry.lean`
- **Status:** `[UNCONDITIONAL LEAN] [NOT RH]`

## Formalized theorem

Lean proves the arbitrary-family additive and mixed Ostrowski dependence/coboundary equivalences,
the raw/logarithmic finite-family replacement theorem, the localized simultaneous-coboundary
quotient representation, and the equality of the complete raw mixed differential-family matroid
with the source-boundary quotient matroid.  Its finite-packet rank is exactly the fraction-field
dimension of the localized quotient-class span.

## Source modules and capstones

```text
formal/GaloisForLFunctions/HTGeometry/SourceLogarithmicBoundary.lean
formal/GaloisForLFunctions/HTGeometry/LocalizedQuotientMatroid.lean
formal/GaloisForLFunctions/HTGeometry/SourceBoundaryQuotientMatroid.lean
formal/GaloisForLFunctions/HTGeometry/SplitSourceBoundaryMatroid.lean

automorphismFamily_mixedRaw_differentialIndependent_iff
sourceBoundaryQuotientMatroid_indep_iff
sourceBoundaryQuotientMatroid_eRk_finset
automorphismFamily_mixedRaw_differentialFamilyMatroid_eq_sourceBoundaryQuotientMatroid
automorphismFamily_mixedRaw_differentialFamilyMatroid_eRk_finset
```

## Verification and boundary

Serialized direct checks and the `HTGeometry` umbrella build pass.  Combined scratch
`#print axioms` audits use only `propext`, `Classical.choice`, and `Quot.sound`.  The split
additive/multiplicative boundary and its linearized matroid are complete.  Noncommutative adjoint
twisting and pro-algebraic source envelopes remain separate conjectural successors.
