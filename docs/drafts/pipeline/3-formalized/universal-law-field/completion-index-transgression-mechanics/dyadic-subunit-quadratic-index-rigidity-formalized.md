# Dyadic subunit quadratic-index rigidity — Lean certification

- **ID:** `ULF-DQIR-1`
- **Paper card:**
  `completion-index-transgression-mechanics/dyadic-subunit-quadratic-index-rigidity.md`
- **Lean module:**
  `GaloisForLFunctions.RHTower.DyadicQuadraticGhostIndexRigidity`
- **Universal-law umbrella:**
  `GaloisForLFunctions.HTGeometry.UniversalLawField`

## Certified declarations

- `dyadicOneCopyQuadraticGhost_mem_subunit`: the existing one-copy Laurent Hermitian-square
  evaluation lies in `(-1,0]` for every normalized grade of absolute value below one.
- `dyadicOneCopyQuadraticGhost_integral_iff`: in that open strip, the dyadic value is integral iff
  grade is zero.
- `xiDyadicOneCopyQuadraticGhost_integral_iff_line`: for every actual Xi divisor copy, one-copy
  dyadic ghost integrality is equivalent to critical-line placement.

## Verification

```text
lake env lean /tmp/dyadic_quadratic_scratch.lean
lake env lean GaloisForLFunctions/RHTower/DyadicQuadraticGhostIndexRigidity.lean
lake build GaloisForLFunctions.RHTower.DyadicQuadraticGhostIndexRigidity
lake env lean /tmp/dyadic_quadratic_axioms.lean
```

Scratch check, direct module check, and targeted module build passed. Module is wired into universal-
law umbrella; no umbrella build was run. `#print axioms` reports only `propext`,
`Classical.choice`, and `Quot.sound`.

## Exact field consequence

One ordinary integer index at prime two is enough to force neutral grade. Required new producer is
therefore a character-to-index transgression for the already-existing Laurent quadratic ghost,
resolved on each canonical one-dimensional local-length layer; no positivity or all-scale trace
family is needed.

