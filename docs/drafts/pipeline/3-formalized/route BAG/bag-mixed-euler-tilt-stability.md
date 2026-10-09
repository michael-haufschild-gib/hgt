# BAG off-pole Euler tilt stability

- **Stage:** 3-formalized

For every nonzero real tau and every fixed complex u, the literal ratio
 product_(p<=N) [1-p^(-1-i*tau+u/logN)]/[1-p^(-1-i*tau)]
tends to1. Both products retain the original cutoff. This is an unconditional
relative-stability statement; no Euler-product boundary limit is a premise.

Put q_N(p)=exp((u/logN-1-i*tau)*logp) and q_0(p)=p^(-1-i*tau).
The complete sum of q_N-q_0 tends to0 by the actual oscillatory logarithmic
window theorem, including both real and imaginary components of u.
Once |Reu/(2logN)|<=1/8, both nomes have norm<=3/4 and square norm<=p^(-3/2).
The existing complex logarithm estimate bounds each log(1-q)+q by twice
its square norm. Their difference therefore has summable majorant4p^(-3/2).
For each prime q_N->q_0; the uniform norm bound keeps1-q_0 in the logarithm
slit plane. Dominated convergence of the cutoff sums makes the complete
logarithmic remainder tend to0. The exact finite exponential-of-log-sum
identity, with all nonvanishing factors proved, gives the displayed ratio.

This pays the moving exponent in the mixed BAG Euler source. Identification
of the fixed boundary product with1/zeta(1+i*tau), complete rational-label
responses/collisions and uniform physical remainder/tails remain open.
Scratch13235 and production57574 empty PASS. ChiRamanujanMixedEulerTilt
256lines passed its final `lake --old env lean ... -o ...olean` audit.
Axiom25259 PASS (standard three axioms only); index95668 PASS/API2; wired once.

## Lean certificate (2026-10-08 promotion audit)

Every claim of this card was re-read against the public statements below; each statement
is unconditional (structural domain subtypes only, no analytic or arithmetic premise).

| Module | Public theorems |
|-|-|
| `GaloisForLFunctions.RHTower.ChiRamanujanMixedEulerTilt` | `criticalMixedEulerTiltRatio_tendsto` |

- `lake env lean <module source>`: every module above compiles with no errors (2026-10-08).
- Axiom audit: every declaration of these modules (643 declarations across the 83 BAG modules)
  depends only on `propext`, `Classical.choice`, `Quot.sound`; no `sorryAx`.
- Each module is imported exactly once in its area umbrella (`RHTower.lean` / `HTGeometry.lean`).
- Open targets recorded on this card (route-level obligations, RH) are not claimed.

## Log (promotion)

- 2026-10-08 — promotion audit passed; moved from `2-fully-proven/route BAG` to `3-formalized/route BAG`.
