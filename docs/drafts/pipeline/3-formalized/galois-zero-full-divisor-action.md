# The full arithmetic action on the zero divisor

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Question:** Which simultaneous complete-fibre permutations are arithmetic?

Let `K` be the complete-fibre source field and `L=ℚ(all w)`.
For each ordinate `t`, let `Z_t` be its finite distinct-root support,
`m_t` analytic multiplicity, and `c_t` conjugation. Define

```
C_t = {π∈Sym(Z_t) : πc_t=c_tπ and m_t∘π=m_t}.
```

## Theorem

The entire source Galois group acts faithfully and continuously through
`∏_t C_t`, with closed image. Every finite-coordinate permutation has an
open kernel in the Krull topology.

A family `π∈∏_t C_t` extends uniquely to an automorphism of `L/K` exactly
when, for every finite set `S` of ordinates, some source automorphism has
coordinates `π_t` for all `t∈S`.

For a finite set `S` of ordinates, let `L_S` be the splitting field inside
`L` of the actual source product `∏_(t∈S)P_t`. Each `L_S/K` is finite
Galois, and the supremum of these fields is `L`. The extension criterion
is equivalently intrinsic: for every finite `S`, an automorphism of `L_S/K`
realizes the selected permutations of all its fibre roots.

## Proof

Automorphisms fix the complete source polynomial and therefore preserve
its root multiplicities. Its finite support is preserved, and the established
identity `conj(w)=2t−w`, with `t∈K`, gives commutation with conjugation.
The full set of roots generates `L`, proving faithfulness.

A coordinate kernel is the finite intersection of stabilizers of its roots.
These stabilizers are open because the roots are algebraic over `K`.
Hence each coordinate, and the whole product action, is continuous.
The Galois group is compact and the product is Hausdorff, giving closed image.
For prescribed coordinates, the corresponding closed subsets of the Galois
group have the finite intersection property precisely under the displayed
condition. Compactness gives a simultaneous extension; faithfulness gives
uniqueness.

The complete source products split in `L`. Their root-generated finite
composita are their actual splitting fields and hence finite Galois.
Every centered zero belongs to its one-fibre stage; the whole source field
is therefore exhausted. Restriction of a global automorphism gives each
intrinsic finite action. Conversely normality extends each finite-stage
automorphism to `L`, reducing intrinsic compatibility to the compactness
criterion above.

## Formalization

`GaloisTheoryOfZeros/ThePermutationActionOnAllZeroFibres.lean`:
`fibrePermutation_preserves_multiplicity`, `fibrePermutation_kernel_isOpen`,
`allFibreDivisorAction_injective`, `allFibreDivisorAction_continuous`,
`allFibreDivisorAction_range_isClosed`, and
`allFibreDivisorAction_unique_extension`.

`GaloisTheoryOfZeros/TheFiniteSourceCompositaOfTheZeros.lean`:
`finiteFibreField_isSplittingField`, `finiteFibreField_isGalois`,
`iSup_finiteFibreField`, `allFibreDivisorAction_source_compatibility`, and
`source_compatible_unique_extension`.

Both direct source audits passed with `lake --old env lean`. Main dependency
closures contain only `propext`, `Classical.choice`, and `Quot.sound`.
Umbrella imports wired. The [countable height tower](galois-zero-height-tower.md)
also recovers the group and its Krull topology. The
[weighted signed-permutation classification](galois-zero-fibre-centralizers.md)
identifies the exact ambient factors and transports the arithmetic criterion.
