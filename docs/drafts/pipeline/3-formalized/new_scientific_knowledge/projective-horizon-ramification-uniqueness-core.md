# Projective-horizon ramification uniqueness core

- **ID:** `projective-horizon-ramification-uniqueness-core`
- **Stage:** 3-formalized
- **Type:** THEOREM (LEAN)
- **Scientific status:** `[FORMALIZED CORE] [NOVELTY PROVISIONAL] [SIGNIFICANCE CANDIDATE]`
- **Paper parent:** `projective-horizon-full-symmetric-monodromy`
- **Lean module:** `GaloisForLFunctions.HTGeometry.ProjectiveHorizonRamificationUniqueness`

## Formalized declaration

- `criticalHorizon_sharedConormal_displacement_eq_zero`
- `criticalHorizonConormalPairing`
- `criticalHorizonConormalPairing_eq_symplecticPairing`
- `criticalHorizonConormalPairing_reciprocalBasis`
- `criticalHorizonConormalPairing_rawBasis`
- `criticalHorizonMultiplicity_ge_six`

## Certified content

Lean first proves that the conormal pairing is literally the ambient coefficient-residue symplectic
pairing.  It then proves that this pairing reads every coefficient of the low tangent pair exactly
from the complementary reversed tail-monomial bases.  This certifies the perfect-pairing assertion
by which the branch conormal remembers `(U,V)`.

Let `(X,Y)` be inverse modulo `t^(m+n)`, let `(U,V)` be a low tangent pair, and suppose the shifted
pair `(X+C U,Y-C V)` is also inverse and has the same marked nonzero coefficient `y_n`.  If
`deg(CU)<m`, Lean proves `C=0`.

The proof constructs the exact forbidden divisibility

```text
t^(m+n) divides (C U)(Y+(Y-CV)).
```

The first factor is nonzero of degree below `m`; the second has nonzero `n`th coefficient because
the two states have the same tail and the field has characteristic zero.  The previously formalized
trailing-degree exclusion produces a nonzero product coefficient below `m+n`, a contradiction.

This is the algebraic uniqueness step in the paper proof that a smooth generic branch value has one
ramified preimage.  The surrounding conormal geometry and etale fundamental-group argument remain
paper-level.

The adjacent critical-multiplicity module also certifies that every `m,n>=2` horizon has at least
six states, the exact combinatorial threshold used by the radical-unsolvability corollary once full
symmetric monodromy is supplied by the paper theorem.

## Verification

The module is checked with the targeted leaf command

```text
lake env lean GaloisForLFunctions/HTGeometry/ProjectiveHorizonRamificationUniqueness.lean
```

No full build is run.  Scratch `#print axioms` reports only `propext`, `Classical.choice`, and
`Quot.sound`; there are no project axioms or placeholders.

## RH impact

The uniqueness theorem is universal and target-translation blind.  It has no RH consequence without
an arithmetic reduction of the resulting generic symmetric monodromy.
