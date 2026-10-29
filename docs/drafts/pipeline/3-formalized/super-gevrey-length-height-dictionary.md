# The complete Steklov receiver in length and height coordinates

- **ID:** super-gevrey-length-height-dictionary
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** For `β>2`, put `c_N=loglog N (logloglog N)^β` and `T_N=N/c_N`.
  Then `c_N→∞`, `T_N→∞`, `log N/log T_N→1`, and `N~T_N c(T_N)`.
- **Module:** `TransMetzlerWeilPositivity/SuperGevreyLengthHeight.lean`.

## Proof

The existing little-o bound places `c_N` eventually between one and `(log N)²`.
Consequently `log c_N/log N→0`, and the exact identity
`log T_N=log N-log c_N` gives `log T_N~log N`. Taking two further logarithms,
powers, and products yields `c(T_N)~c_N`. Combining this with the exact identity
`N=T_N c_N` proves the height substitution.

For every fixed `α>1`, eventually `N<T_N^α`. Nevertheless this schedule is RH-complete:
eventual nonnegativity of the complete Weil form on the fixed Steklov profile dilated
by `T_N` is exactly RH. No positivity premise is supplied to this equivalence.

The limiting bandwidth one therefore does not distinguish fixed overlap from this
unbounded, RH-complete overlap schedule. The argument of the slow factor can be changed
from length to height asymptotically, not by an exact identity.

## Lean declarations

- `superGevreyRatio_atTop`, `superGevreyHeight_atTop`
- `tendsto_log_superGevreyRatio_div_log`
- `superGevrey_log_height_equivalent`, `tendsto_superGevrey_bandwidth`
- `superGevrey_ratio_at_height_equivalent`
- `superGevrey_length_equivalent_height_mul_ratio`
- `eventually_superGevrey_length_lt_height_rpow`
- `riemannHypothesis_iff_steklovDCProfile_nonneg_at_height`

Direct `lake --old env lean` check and all four transitive axiom audits passed.
Only `propext`, `Classical.choice`, and `Quot.sound` occur. Umbrella import is wired;
the corrected Steklov dependency also passed its direct audit.
