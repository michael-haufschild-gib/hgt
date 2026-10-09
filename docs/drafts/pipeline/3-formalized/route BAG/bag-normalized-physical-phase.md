# BAG exact normalized physical cone phase

- **Stage:** 3-formalized

01ax, 2026-10-06. Paper and production Lean proof complete.
ChiCubicNormalizedPhysical152lines/API2. Complete scratch74577PASS
(one sequence-focus style warning removed before production);
final production36893emptyPASS. Both axiom prints28398 report standard3
only; the combined scratch exited1 on subsequent polynomial-window budget
elaboration, not this leaf. Index42693PASS/API2; umbrella import once.
Lint74659terminal1: two unrelated unreachable modules
KuznetsovEisensteinGrowth and HTGeometry.ResetPathSingularity,362warnings;
no finding in this leaf. Scoped diffcheckPASS. Global lint is not clean.
No resource-limit increase or full/umbrella build.

For every N>1 and the actual controlled cutoff width0<H<N/2,
 L^3/N * bagCubicConeSchwartz(actualPhysicalSchwartz_N,H)(x,y)
equals
 2*pi*N * integral_R integral_Q integral_P
  F(P)F(Q)conj(F(R))/R * W(PQ/R)
  * exp(2*pi*i*N*(P-Ry)*(Q-Rx)/R),
where L=logN and F=bagCubicNormalizedSlice(H/N,1/L).
Every original Gaussian/logarithmic slice, height window and conjugate is
retained. This is an exact identity, not a stationary replacement.

Proof: the physical amplitude contains1/r. Ordinary three-dimensional
Fourier integration on the cone (x,y,-xy) therefore has phase
 pq/r-p*x-q*y+r*x*y. Coordinate Fubini is justified by integrability of the
actual Schwartz amplitude times a unit-modulus phase. Rescale all three
coordinates byN using positive-dilation integral identities. The N^3
Jacobian, amplitude1/(NR), normalizationL^3/N and three exact identities
L*slice(NP)=F(P) leave prefactorN and reciprocal1/R. The phase factors as
N*(P-Ry)*(Q-Rx)/R. AtR=0 total field division makes both amplitudes zero;
no forbidden cancellation at zero is used.

Source distinction: the original physical amplitude has1/r; its SECOND
Fourier kernel has1/r². Confusing these would introduce a false N factor
in the physical tail argument. The new identity fixes that normalization
against the literal source and exposes both stationary equations.

Next: prove admitted physical jets and their rapid weighted nonstationary
bounds outside a positive box. Logarithmic coordinate transfer, fractional
regularity, Mellin line tails, arithmetic moving-source cancellation and
full original sharp-action/self-return bridges remain open. RH is open.

## Lean certificate (2026-10-08 promotion audit)

Every claim of this card was re-read against the public statements below; each statement
is unconditional (structural domain subtypes only, no analytic or arithmetic premise).

| Module | Public theorems |
|-|-|
| `GaloisForLFunctions.RHTower.ChiCubicNormalizedPhysical` | `bagCubicControlledCone_normalized_physical` |

- `lake env lean <module source>`: every module above compiles with no errors (2026-10-08).
- Axiom audit: every declaration of these modules (643 declarations across the 83 BAG modules)
  depends only on `propext`, `Classical.choice`, `Quot.sound`; no `sorryAx`.
- Each module is imported exactly once in its area umbrella (`RHTower.lean` / `HTGeometry.lean`).
- Open targets recorded on this card (route-level obligations, RH) are not claimed.

## Log (promotion)

- 2026-10-08 — promotion audit passed; moved from `2-fully-proven/route BAG` to `3-formalized/route BAG`.
