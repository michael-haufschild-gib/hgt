# Dyadic relative-reflection integral-frame rigidity — Lean certification

- **ID:** `ULF-DRRIF-1`
- **Paper card:**
  `completion-index-transgression-mechanics/dyadic-relative-reflection-integral-frame-rigidity.md`
- **Lean module:**
  `GaloisForLFunctions.RHTower.DyadicRelativeReflectionIntegralFrameRigidity`
- **Universal-law umbrella:**
  `GaloisForLFunctions.HTGeometry.UniversalLawField`

## Certified declarations

- `DyadicRelativeReflectionIntegralFrame`: one complex frame in which the prime-two curved
  reflection suspension has integer coordinates.
- `DyadicRelativeReflectionIntegralFrame.detDescent`: such a frame makes the exact framed
  determinant integral.
- `eq_zero_of_dyadicRelativeReflectionIntegralFrame`: in the open strip, any such frame forces
  grade zero.
- `dyadicRelativeReflectionIntegralFrame_nonempty_iff`: frame existence is exactly neutrality.
- `xiDyadicRelativeReflectionIntegralFrameAt_iff_line`: pointwise Xi frame existence is exactly
  critical-line placement.
- `everyXiDyadicRelativeReflectionIntegralFrame_iff_riemannHypothesis`: global frame existence is
  exactly RH.

## Verification

```text
lake env lean /tmp/relative_reflection_frame_scratch.lean
lake env lean GaloisForLFunctions/RHTower/DyadicRelativeReflectionIntegralFrameRigidity.lean
lake build GaloisForLFunctions.RHTower.DyadicRelativeReflectionIntegralFrameRigidity
lake env lean /tmp/dyadic_relative_reflection_axioms.lean
```

Scratch, direct module check, targeted module build, and axiom audit passed. Every certified
declaration depends only on `propext`, `Classical.choice`, and `Quot.sound`. Module is wired into
universal-law umbrella; no umbrella build was run.

## Exact field consequence

One finite integral mapping-torus lattice for the difference between bare and Gamma-transported
functional-equation reflections is enough to force critical-line placement. The remaining higher
law is now a precise global formation/properness construction, not a scalar selection premise.
