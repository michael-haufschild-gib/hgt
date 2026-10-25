# Uniform logarithmic prefix cancellation controls pronic energy

- **ID:** uniform-logarithmic-prefix-to-pronic-energy
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** ../2-fully-proven/uniform-second-scale-vaughan-gram-at-all-cutoffs.md
- **Statement:** Every common logarithmic prefix saving survives in pronic energy and norm below half damping, with the finite head retained.

## Exact result

Let `0<ε<1/2`, `β=1-2ε`, and let a family `f_i(n)` have a common
global bound `|f_i(n)|≤K n^(1-ε)`. If every integer `q≥0` has a common
constant and threshold with `|f_i(n)|≤B_q n^(1-ε)/(log n)^q`, then

`Σ_(1≤n≤T) f_i(n)^2/[n(n+1)] ≤ C_q T^β/(log T)^(2q)`

and

`‖f_i‖_T ≤ sqrt(C_q) sqrt(T^β)/(log T)^q`,

uniformly over the family index. Splitting at `D=floor(sqrt(T))` gives
`C_q=(K²+(4^q B_q)²)(1+1/β)` after enlarging the common threshold.
A common linear bound suffices to absorb the finite head of an eventual
smooth-power bound. Uniformly bounded pronic norm families also satisfy
every logarithmic saving relative to any positive norm power scale.

This is a reusable transfer theorem: its inputs are explicit bounds on a
family. Actual arithmetic applications must discharge those inputs; they
remain under separate verification.

## Lean audit

Module: [UniformLogarithmicEnergyFromPrefixCancellation.lean](../../../../formal/GaloisForLFunctions/BezoutValuationIncidence/UniformLogarithmicEnergyFromPrefixCancellation.lean).

Six public theorems:

- `exists_uniform_rpow_bound_of_eventually`
- `sum_pronicCell_le_of_split_rpow`
- `exists_uniform_pronicEnergy_log_rate_of_prefix_log_rate`
- `exists_uniform_pronicNorm_log_rate_of_prefix_log_rate`
- `eventually_log_pow_le_sqrt_rpow`
- `eventually_pronicNorm_log_rate_of_uniform_bound`

Corrected scratch checks and all six transitive axiom audits passed with
only `propext`, `Classical.choice`, and `Quot.sound`. Producing and final
direct `lake --old env lean` checks passed. The module is wired into the
BVI umbrella; its scratch file was removed. No limits were raised.

The complete uniform Vaughan Gram theorem remains under formalization.
These logarithmic estimates supply no fixed power saving and do not resolve Q-I.
