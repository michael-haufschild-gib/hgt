# Uniform logarithmic prefix bounds in all Vaughan rows

- **ID:** uniform-logarithmic-prefix-remainders-in-all-vaughan-rows
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Source:** ../2-fully-proven/uniform-half-damping-vaughan-harmonic-gram.md
- **Verification:** Six targets passed producing and final direct repository checks. Transitive axioms: `propext`, `Classical.choice`, `Quot.sound` only.

For every `0<ε≤1/2` and integer `q≥0`, all five smooth-subtracted Vaughan
rows satisfy

`|r_i(n;U,V)|≤C_(ε,q)n^(1−ε)/(log n)^q`

eventually, with one constant and threshold for every cutoff pair and row.
There is also one linear bound `|r_i(n;U,V)|≤E_ε n` at every positive cell.
Both bounds include zero cutoffs. At half damping, these are the actual
square-root prefix bounds needed by the summable critical-pairing theorem.

The truncated Möbius and convolution estimates control the first three rows.
The unit-pattern remainder has a smaller power, and the active correction is
bounded. The exact five-row sum determines the both-large remainder from
the other four rows and the actual interior. A reciprocal divisor majorant
and unit-bounded pattern estimate control the entire finite head uniformly.

The module
`GaloisForLFunctions/BezoutValuationIncidence/UniformLogarithmicPrefixRemaindersInAllVaughanRows.lean`
proves:

- `eventually_bounded_prefix_log_rate`;
- `eventually_abs_subHalfRemainder_log_rate`;
- `abs_pmPronicVaughanSmoothRemainder_large_le`;
- `exists_uniform_pmPronicVaughanSmoothRemainder_prefix_log_rate`;
- `abs_patternPrefix_le_linear_of_abs_le_one`;
- `exists_uniform_pmPronicVaughanSmoothRemainder_linear_bound`.

The module is imported by the programme umbrella and the endpoint Gram leaf.
Its temporary draft was removed after the final direct check. The endpoint
Gram specialization remains a separate verification obligation. These bounds
do not prove a fixed strip or bounded complete energy below half damping.
