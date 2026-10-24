# Universal positive-shell cancellation

- **ID:** universal-positive-shell-cancellation
- **Stage:** 5-failed
- **Type:** NO-GO WITH FORMALIZED POSITIVE SURVIVOR
- **Source:** Arithmetic Local Divisor Geometry
- **Killed mechanism:** Inferring coefficient nonnegativity of a local factor solely from coefficient nonnegativity of its product with a nonmonomial coefficient-positive shell.

## Obstruction and exact survivor

Every nonzero coefficient-positive nonmonomial `Q` admits a real polynomial `P` with a negative coefficient, while `PQ` has nonnegative coefficients and `P(y)>0` for every `y≥0`. The witness can have degree at most `2deg Q`. Thus imposing real-axis positivity of the local slice does not validate cancellation.

The positive survivor is a complete classification: multiplication preserves and reflects the coefficient cone for every polynomial exactly for `Q=cX^a`, `c>0`. Central multiplicities and positive normalization scalars are therefore precisely the universally reversible transitions.

The witness degree bound is optimal. For `Q=1+X^D`, cancellation is valid for every `P` of degree below `2D`, while `P=X^(2D)−X^D+1` is strictly positive on the entire real axis and satisfies `PQ=1+X^(3D)`.

## Proof status and scope

Complete paper proof and exact Lean statements: [universal-coefficient-reflectors.md](../3-formalized/universal-coefficient-reflectors.md), `ArithmeticLocalDivisorGeometry/UniversalReflectors.lean`.

The plain foreground module check passed. Classification, constructive witness, and sharpness depend only on `propext`, `Classical.choice`, and `Quot.sound`. No unproved source condition is used.

This retires universal cancellation of a positive shell. It does not retire WD, the coefficient-cone endpoint, or a source-specific signed cancellation theorem. Such a theorem would need additional information about the actual factor and shell.
