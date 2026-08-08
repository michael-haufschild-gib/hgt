# Double-sine defect coset differential matroid — formalization certificate

- **ID:** `double-sine-defect-coset-differential-matroid`
- **Stage:** 3-formalized
- **Paper proof:**
  `../../../2-fully-proven/new_scientific_knowledge/other/double-sine-defect-coset-differential-matroid.md`
- **Lean modules:**
  - `formal/GaloisForLFunctions/HTGeometry/DoubleSineDefectCosetMatroid.lean`
  - `formal/GaloisForLFunctions/HTGeometry/MeromorphicRationalBaseOperatorMatroid.lean`
- **Umbrella:** `formal/GaloisForLFunctions/HTGeometry.lean`
- **Status:** `[PAPER-PROVED] [LEAN-PROVED] [NOVELTY UNVERIFIED] [NOT RH]`

## Formalized theorem

For every positive imaginary-ray period frame `i a, i b` with irrational ratio, Lean constructs a
genuine meromorphic double-sine source.  For arbitrary shifts, its additive translation defects
represent over `ℂ(z)` exactly the pointed collision matroid of period-lattice classes: the zero
class is a loop, equal nonzero classes are parallel, and distinct nonzero classes are jointly
differentially algebraically independent.  The rank of every indexed subpacket is exactly the
number of distinct nonzero classes it meets.

For every finite separated support and every finite family of constant-coefficient differential-
operator rows, Lean also proves that differential rank of the resulting translation
superpositions is exactly dimension of the localized row span over `ℂ(δ)`.  Choosing support
representatives for finite elements of `ℂ[δ][ℂ/H]` gives the paper's complete group-algebra rank
law.

Capstones:

```text
GaloisForLFunctions.HTGeometry.doubleSineDefect_rationalBase_matroid_imaginaryRay
GaloisForLFunctions.HTGeometry.doubleSineSeparatedOrbit_operatorRows_eRk_imaginaryRay
GaloisForLFunctions.HTGeometry.differentialOperatorRows_eRk_rationalBase_eq_finrank_span
```

The source, cotangent increments, dense-period fixed-field input, and irrational cylinder orbit
are constructed or discharged inside the imaginary-ray theorems.  No hypertranscendence,
telescoping, Picard--Vessiot, or matroid-classification premise is added.

## Verification

- Direct `lake env lean` checks pass for both owning modules.
- Targeted builds pass:
  - `lake build GaloisForLFunctions.HTGeometry.MeromorphicRationalBaseOperatorMatroid`
  - `lake build GaloisForLFunctions.HTGeometry.DoubleSineDefectCosetMatroid`
- Scratch `#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound` for all three
  capstones.
- Both modules are imported by the `HTGeometry` umbrella.
- Targeted audit finds no `sorry`, `admit`, `axiom`, `opaque`, or `unsafe` declaration in either
  owning module.
- Repository-wide formal lint currently exits on unrelated concurrently added modules missing
  umbrella reachability; it reports no forbidden construct or ownership failure for these modules.
