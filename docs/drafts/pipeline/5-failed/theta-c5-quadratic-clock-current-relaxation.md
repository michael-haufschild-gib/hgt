# Quadratic clock relaxation loses the complete current sign

- **ID:** TH-N38
- **Stage:** 5-failed
- **Type:** FALSIFIED
- **Source:** ../1-in-progress/theta-c5-nonlocal-defect-transport.md
- **Statement:** The quadratic clock relaxation cannot prove positivity even of the complete enriched constant-shape current.

## Goal
Preserve the cancellation needed for the actual TH inner-current sign. This retires only the coarse quadratic clock substitution, not route TH.

## No-go closure
- **Exact killing theorem:** `constantShape_quadraticClock_current_neg`. With alpha=gamma=1, beta=delta=epsilon=0 and Q=Z, substituting C=1+6Z gives exactly `-(5968/75)Z²-(4464/125)Z³-(336/25)Z⁴-(1728/625)Z⁵`, strictly negative for every Z>0. This is an algebraic comparison model, not an actual-source counterexample.
- **Strongest positive survivor:** `constantShape_linearClock_current_pos`. For every z>0, the complete enriched constant-shape current is strictly positive at Z=z²/18 and the rational clock envelope `(15+3z+6z²+z³)/(15+3z+z²)`.
- **New insight:** That envelope equals `1+z²/3-z⁴/[3(15+3z+z²)]`. Keeping its quartic correction reverses the sign of the entire comparison current; retaining only the quadratic clock term destroys the needed cancellation.
- **Paper proof:** Negative side is the displayed polynomial identity. On the positive side, the unenhanced current equals its positive reserve times `constantInverseClockGrowth-linearClockEnvelope`, positive by the existing exact rational certificate. Writing R16,R36 for the two reserves and F16,F36 for their flows, `4R36R16+F36R16-F16R36` is a polynomial with strictly positive coefficients on Z>0. It forces positivity of the second action-power current too. Their positive weighted sum is the claimed survivor. No open paper dependency remains.
- **Lean status:** Both signs and the quartic identity pass scratch3183 and saved final74609 (exit0, empty logs). Saved in `ThetaCuspC5ClockQuarticCancellation`, wired once. Imported axiom20364 exits0; all three endpoints use only propext, Classical.choice, Quot.sound. Lint18373 reports twelve unrelated unreachable modules, no error in this module.

## Remaining hard problem
The actual theta source has nonzero, correlated shape derivatives. Its complete inner-current sign remains open. The next attack must retain this clock correction together with the positive correlated-source slack and common primitive-clock constraints; ordering curvature alone does not order this nonlinear current.

## Log
- 2026-10-04 — Full coarse relaxation falsified; full rational comparison survivor proved on paper and in Lean scratch. No numerical experiment used.
