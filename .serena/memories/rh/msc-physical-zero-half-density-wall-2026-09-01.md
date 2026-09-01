# MSC physical-zero half-density wall

Formal route kill: `formal/GaloisForLFunctions/RHTower/HedenmalmGammaSewnSquarefreeFisherPhysicalHilbertWall.lean`.

Facts:
- `Summable (squarefreeMobiusMass a) ↔ 1 < a`.
- For `sigma > 1`, real damped Möbius source norm-squares are summable iff `u > -1/2`; complex phase version iff `Re u > -1/2`.
- For `mscPhysicalZeroCoordinate rho sigma = (rho-sigma)/(sigma-1)`, if `Re rho < 1` and `sigma > 1`, then `Re u < -1/2`.
- Therefore physical source coefficients have nonsummable squared norm and no `lp (fun _ : ℕ => ℂ) 2` representative at any finite `sigma > 1`.

Consequence: ordinary-Hilbert singular-graph MSC landing at a fixed strict-right Xi divisor is impossible. Graph normalization repairs gain, not domain loss. Survivor: algebraic regular germ remains, but continuation must use rigged/distributional source completion.

Verification: source check and targeted `lake build GaloisForLFunctions.RHTower.HedenmalmGammaSewnSquarefreeFisherPhysicalHilbertWall` pass; axioms only `propext`, `Classical.choice`, `Quot.sound`; umbrella wired. Global lint fails only pre-existing unreachable modules.

Status: `docs/drafts/pipeline/1-in-progress/rh-research-status.md`; card: `docs/drafts/pipeline/3-formalized/msc-physical-zero-half-density-wall.md`.