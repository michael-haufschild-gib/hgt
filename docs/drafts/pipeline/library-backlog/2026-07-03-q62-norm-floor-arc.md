# Ticket: door index/status — q62 norm-floor arc (2026-07-03)

Informal ticket for the library agent; source of record is
`docs/drafts/pipeline/3-formalized/not-new/norm-bounded-tower-mixed-pair-far.md` (with its two
addenda) and `docs/open-problems/16-integer-harmonic-mass-level.md`.

New formalized surface (all axiom-clean, umbrella `GaloisForLFunctions.Bottcher`, lint green):

- Mixed q62 closed unconditionally for disconnected `‖c₁‖ ≥ 1000` × connected
  `c₂ ∈ M ∖ {0,−2}`, both orientations (`q62_phiMero_mixed_far`, `_swapped`).
- Both-disconnected q62 closed on the quadratic-gap region
  `‖c_big‖ ≥ 1000 ∧ 300·(max 2 ‖c_small‖)² ≤ ‖c_big‖`, both orientations
  (`q62_phiMero_pair_far_general`, `_swapped`; special cases `_smallSecond`, `_smallFirst`).
- Placement-free master: `q62_phiMero_norm_gap` (no Mandelbrot hypothesis on the second
  parameter).
- Mechanism: `s`-norm-floored radical tower (parametric Green pinch + wedge-slit at the
  critical-value ball + raised section); modules `MixedTowerExt`, `MixedTowerData`, parametric
  additions in `GreenBallPinch`, `PatchSquareLocalize`; piece-selection `MoatPiece`.

Status changes for the door map:

- The disconnected-pair frontier (W4) residual is now EXACTLY the comparable-norm region, and
  it is REDUCED to open problem 16 (integer harmonic mass on a Green level curve) — no
  assembly/calibration route remains (two recorded no-gos: reach-threshold/band-avoidance;
  hlevel and univalence-shell for comparable norms).
- OP16 Question B (isolated piece with a moat) is banked in Lean (`MoatPiece.lean`).
- Mixed residual: `‖c₁‖ < 1000` (small disconnected parameter) — needs `K₂`-steering or
  recalibrated constants.
- Both-connected: unchanged (conditional on OneSidedDense × ExposedOneSided ×
  SmoothPieceRigidity).
