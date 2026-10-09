# BAG actual moving-line physical Mellin pairing

- **Stage:** 3-formalized

The complete positive rational cone with both original numerator cofactors
and both physical label exclusions pairs with every three-coordinate
Schwartz Fourier test on every pair of Mellin lines with real parts>1.
The paired profile is the full positive-line Mellin transform of the actual
cone restriction; no product or stationary approximation is substituted.

Proof: factor each rational character into the fixed signed mass and the
full two-variable Mellin kernel. Its norm on a vertical line equals its norm
at the real line point. The existing rational-cone HasSum is absolutely
convergent there. Multiply this summable majorant by the integrable Schwartz
Mellin profile, apply dominated sum/integral interchange, then the proved
positive-line Mellin inversion at each positive rational pair.

Choose line real parts1+rho_i/logN, rho_i>0, N>=2. Applying this identity to
the existing actual physical Fourier family retains all its regularity,
integer-lift summability and negligible sharp/smooth cubic comparison.
Both the source cutoff and physical test use the original N. This is an
unconditional actual-family theorem; domains are encoded as subtypes.
Scratch83145 empty PASS. Production and final axiom/index/lint audits pending.

The identity closes the mismatch with the near-pole scale. It does not
interchange the growing-prime limit with the physical integral. Uniform
profile/tail control and coupled signed cancellation in every frequency
sector remain hard open obligations.

Final01ap: production86634 (positive lines) and4433 (actual pairing) empty
PASS. Axiom62726 all17 public declarations standard3 only. Index87535 passed;
API17/17 and both umbrella imports once. Lint67343:27 unrelated unreachable
modules,174warnings; no finding in these leaves, global NOT clean.

## Lean certificate (2026-10-08 promotion audit)

Every claim of this card was re-read against the public statements below; each statement
is unconditional (structural domain subtypes only, no analytic or arithmetic premise).

| Module | Public theorems |
|-|-|
| `GaloisForLFunctions.RHTower.ChiPrimeGaussianCubicMovingMellin` | `criticalRationalCone_physical_line_hasSum`, `exists_bagCubicPhysicalMovingMellinFamily` |

- `lake env lean <module source>`: every module above compiles with no errors (2026-10-08).
- Axiom audit: every declaration of these modules (643 declarations across the 83 BAG modules)
  depends only on `propext`, `Classical.choice`, `Quot.sound`; no `sorryAx`.
- Each module is imported exactly once in its area umbrella (`RHTower.lean` / `HTGeometry.lean`).
- Open targets recorded on this card (route-level obligations, RH) are not claimed.

## Log (promotion)

- 2026-10-08 — promotion audit passed; moved from `2-fully-proven/route BAG` to `3-formalized/route BAG`.
