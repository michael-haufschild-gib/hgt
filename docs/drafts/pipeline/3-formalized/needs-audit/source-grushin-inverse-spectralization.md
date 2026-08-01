# Source Grushin inverse spectralization

- **ID:** `source-grushin-inverse-spectralization`
- **Stage:** 3-formalized / needs audit
- **Type:** THEOREM / OPERATOR INFRASTRUCTURE
- **Scientific status:** `[LEAN-PROVED] [UNCONDITIONAL] [CLASSICAL CORE] [NOT RH]`
- **Lean:** `GaloisForLFunctions.HTGeometry.SourceGrushinInverse`
- **Child application:**
  `../../2-fully-proven/needs-audit/hedenmalm-theta-source-compressed-inverse-determinant.md`.

## Exact theorem

Let `G0 : E ≃L[ℂ] H` be an invertible source-augmented map and let
`J : E →L[ℂ] H` be its spectral injection. Define

```text
B   = J ∘ G0⁻¹,
G_z = G0 + z J.
```

Then

```text
(I + z B) ∘ G0 = G_z.                                    (1)
```

Consequently, for `z ≠ 0`,

```text
G_z has a nonzero kernel
  ↔ I + z B has a nonzero kernel
  ↔ B has a nonzero eigenvector with eigenvalue -z⁻¹.     (2)
```

If `J` is compact, `B` is compact.

The construction is source-first: `B` is defined from `G0` and `J`, not from the set of spectral
parameters at which `G_z` fails to be injective.

## Formal declarations

- `sourceGrushinRelativeOperator`
- `sourceGrushinPencil`
- `sourceGrushinPencil_factor`
- `exists_sourceGrushinPencil_kernel_iff`
- `sourceGrushin_shift_kernel_iff_eigen`
- `exists_sourceGrushinPencil_kernel_iff_eigen`
- `sourceGrushinRelativeOperator_isCompact`

## Verification

- `lake env lean GaloisForLFunctions/HTGeometry/SourceGrushinInverse.lean` passes.
- Final targeted audit
  `lake build GaloisForLFunctions.HTGeometry.SourceGrushinInverse` passes.
- Formal lint passes.
- Headline declarations use only `propext`, `Classical.choice`, and `Quot.sound`.
- No `sorry`, `admit`, custom `axiom`, `opaque`, or `unsafe` declaration.

## Significance boundary

This is the exact bounded algebraic core of the new Hedenmalm construction, but it is classical
Grushin/Fredholm technology. It does not prove that Hedenmalm's concrete graph map is an equivalence,
that its injection is Hilbert--Schmidt, that its determinant is `XiC`, or that its spectrum is real.
Those are separate analytic and arithmetic obligations. No novelty is claimed for `(1)`--`(2)`.

## Gates

- [x] relative operator defined before spectral set
- [x] exact affine factorization
- [x] nonzero kernel transported both ways
- [x] reciprocal eigenvalue law
- [x] compactness transfer
- [x] focused Lean check
- [x] final module build
- [x] axiom audit
- [x] formal lint
