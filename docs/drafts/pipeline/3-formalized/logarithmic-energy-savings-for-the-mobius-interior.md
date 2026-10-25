# Logarithmic energy savings for the Möbius interior

- **ID:** logarithmic-energy-savings-for-the-mobius-interior
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** ../2-fully-proven/uniform-second-scale-vaughan-gram-at-all-cutoffs.md
- **Statement:** The actual centered Möbius divisor prefix and its Bézout interior have every logarithmic pronic norm saving below half damping.

## Exact results

The centered damped Möbius pattern equals the actual divisor prefix: its
reciprocal series is exactly `Re(1/ζ(1+ε))`. For `0<ε≤1/2` and each
integer `q≥0`, that prefix satisfies

`|A_ε(n)|≤C_q n^(1-ε)/(log n)^q`

at a common eventual threshold. For `0<ε<1/2`, the prefix and the actual
interior `I_ε` also satisfy

`‖A_ε‖_T, ‖I_ε‖_T ≤ B_q sqrt(T^(1-2ε))/(log T)^q`.

The checked arbitrary logarithmic Möbius bounds discharge the generic
floor-transform inputs. A global smooth-power bound controls the finite
head before the prefix-to-energy transfer. The identity
`I_ε=A_ε-Δ(active_ε)` and the uniform bound `|Δ(active_ε)|≤1/2`
then give the interior estimate. No new analytic assumption is introduced.

## Lean audit

Module: [LogarithmicEnergySavingsForTheMobiusInterior.lean](../../../../formal/GaloisForLFunctions/BezoutValuationIncidence/LogarithmicEnergySavingsForTheMobiusInterior.lean).

Four public theorems:

- `patternPrefix_moebius_eq_centeredDivisorPrefix`
- `exists_pmPowerDampedCenteredDivisorPrefix_log_rate`
- `exists_pmPowerDampedCenteredDivisorPrefix_pronicNorm_log_rate`
- `exists_pmBezoutInteriorPrefix_pronicNorm_log_rate`

Corrected scratch checks and all four transitive axiom audits passed with
only `propext`, `Classical.choice`, and `Quot.sound`. Producing and final
direct `lake --old env lean` checks passed. The module is wired into the
BVI umbrella. Its scratch file was removed; no limits were raised.

These logarithmic savings do not give a fixed power saving or receiver
admission below half damping. The complete uniform Gram law remains under
verification; full Q-I remains open.
