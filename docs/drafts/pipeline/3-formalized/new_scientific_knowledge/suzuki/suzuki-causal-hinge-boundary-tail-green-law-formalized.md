# Suzuki causal hinge boundary--tail Green law — formalization certificate

- **Stage:** 3-formalized
- **Paper proof:**
  `./suzuki-causal-hinge-boundary-tail-green-law.md`
- **Lean module:**
  `formal/GaloisForLFunctions/RHTower/SuzukiCausalHingeBoundaryTailGreenLaw.lean`
- **Scientific status:** `[PAPER-PROVED] [LEAN-PROVED] [SOURCE-SPECIFIC]`
  `[CANDIDATE NEW SCIENTIFIC KNOWLEDGE] [NOT RH]`

## Formalized core

Lean proves exact closed-form cancellation of low delayed-hinge mass before aperture limit, exact
entry-wall specialization, Xi-real quarter-turn, diagonal Pick formula, positive vertical and
negative phase-aligned Pick diagonals of actual far-prime atom, and preservation of negative sign
under every nonzero compound denominator.

Key declarations:

```text
suzukiDelayedHingeExteriorFromCut_eq_boundaryTail
suzukiDelayedHingeExteriorFromCut_entryWall
I_mul_suzukiDelayedHingeMultiplier
suzukiScalarPickKernel_self_eq_im_div
suzukiCriticalDelayedHingeJumpAtom_im_pos_vertical
suzukiCriticalDelayedHingeJumpAtom_im_neg_phaseAligned
suzukiCriticalDelayedHingeJumpAtom_pickDiagonal_pos_vertical
suzukiCriticalDelayedHingeJumpAtom_pickDiagonal_neg_phaseAligned
suzukiCompoundDenominatorScaledPick_self_eq
suzukiCompoundDenominatorScaledPick_delayedHinge_neg_phaseAligned
```

Physical integral evaluation and completed polar--Gamma source expansion are dependency-closed
paper theorems.  Lean formalizes exact algebra consumed by compound-Bezoutian frontier; it does not
replace missing collective source positivity with a hypothesis.

## Integration

- imported by `GaloisForLFunctions.RHTower` umbrella;
- imported and summarized in `RiemannHypothesisSOTA2026`;
- active rooted-midpoint card records atomwise producer as falsified and replaces it by
  `SUZUKI-CAUSAL-APERTURE-ENTRY-COMPOUND-WELD`.

## Verification

- direct source check:
  `lake env lean GaloisForLFunctions/RHTower/SuzukiCausalHingeBoundaryTailGreenLaw.lean`;
- exact module build: `9015/9015` jobs;
- axiom audit: `propext`, `Classical.choice`, `Quot.sound` only;
- forbidden declaration scan: no `sorry`, `admit`, `axiom`, `opaque`, or `unsafe`.

