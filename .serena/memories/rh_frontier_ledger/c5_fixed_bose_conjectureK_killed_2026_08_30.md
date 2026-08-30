# C5 fixed Bose Conjecture K killed (2026-08-30)

Unconditional Lean theorem `RHTower.thetaCuspC5LikelihoodHomotopy_conjectureK_false` disproves universal fixed lowest-mode Bose shifted cone.

Mechanism: at `l=0`, literal first face has jets 0 through 6 equal to zero and seventh derivative
`3360 * thetaCuspC5FirstFaceSeamObstruction u > 0` at every positive scale-six seam. Taylor--Lagrange gives local positive first face, contradicting cone requirement `faceOne <= 0`. Continuity preserves `scale(u-t)>=6`.

Positive survivor: exact seventh-order seam classification and theorem
`eventually_thetaCuspC5LikelihoodHomotopy_boseShiftedTransportOne_zero_pos`.
Consequence: no proof requiring four individually nonpositive fixed Bose faces can close M''' positivity. Surviving C5 route must prove full weighted three-term balance using cancellation or a different sign architecture; M''(0)>=0 remains.

Files:
- formal/GaloisForLFunctions/HTGeometry/LikelihoodHomotopyFirstFaceSeam.lean
- formal/GaloisForLFunctions/RHTower/ThetaCuspLikelihoodHomotopyFirstFaceObstruction.lean
- formal/GaloisForLFunctions/RHTower/ThetaCuspLikelihoodHomotopyBoseFirstFaceSeamNoGo.lean
- docs/drafts/pipeline/5-failed/theta-c5-fixed-bose-shifted-cone.md

Targeted build passed. Axioms: propext, Classical.choice, Quot.sound only. Global lint locally clean for these modules; global command remains red on unrelated concurrent umbrella reachability failures.