# FZZ-P Hermitian reporters outside the reflection cone

- **ID:** FZZ-P-HC3-NG
- **Stage:** 5-failed
- **Type:** SHARP NO-GO WITH POSITIVE SURVIVOR
- **Route:** Use an arbitrary fixed Hermitian quadratic reporter to distinguish every centered FZZ
  Mellin carrier from its critical-line reflection.
- **Lean:** `GaloisForLFunctions.RHTower.FZZCigarParityHermitianReflectionDetectorCone`

## Failed premise

Hermiticity or a nonzero off-diagonal coefficient might suffice for a fixed reporter to detect
reciprocal-radius reflection uniformly over unknown Mellin phase.

## Exact killing theorem

The classification

`UniversalRadialReflectionSeparating(a,b,c,d)`

`<-> d != 0 and b^2+c^2 <= d^2`

shows this premise is false.  Every reporter with `d=0`, or with `d^2<b^2+c^2`, admits an explicit
positive nonunit radius and unit phase at which its value equals the value at reciprocal radius.
Thus Hermiticity alone, including the source-native chiral reporter from FZZ-P-HC2, cannot provide a
phase-uniform reflection detector.

## Strongest positive survivor

The exact survivor is the punctured closed Lorentz cone.  Every coefficient tuple in this cone,
including its nonzero lightlike boundary, is a phase-robust detector.  On literal centered FZZ
Mellin characters, equality with the reflected reading is equivalent pointwise to
`rho.re=1/2`.  Matching one such reporter on all parity-Mellin divisor modes is equivalent to RH.

Paper proof and unconditional Lean formalization are complete in
`../3-formalized/fzz-p-hermitian-reflection-detector-cone.md`.

## New insight

Source orientation and radial reflection require different coefficient geometry.  Chiral
orientation is controlled by `c`; universal radial separation requires a dominating nonzero
diagonal coefficient `d`.  Future FZZ/GFZZ dynamics must either generate a cone reporter or add a
separate phase constraint.  Searching outside this cone without such extra control is now closed.

## Status

- exact no-go and strongest survivor proved on paper;
- both constructive failure branches formalized in Lean;
- detector endpoint formalized and axiom-audited;
- literature search found no exact collision; independent priority audit remains.

## Log

- 2026-08-28 — Arbitrary-Hermitian route retired after sharp cone classification; positive
  survivor formalized before retirement.
