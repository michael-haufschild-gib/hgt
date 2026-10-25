# Power saving from absolute Vaughan atom assembly

- **ID:** absolute-vaughan-atom-assembly-power-saving
- **Stage:** 5-failed
- **Type:** REFUTED ESTIMATE WITH FORMALIZED POSITIVE SURVIVOR
- **Source:** ../1-in-progress/q-i-selective-square-root-band.md
- **Retired claim:** Summing the known individual remainder norms absolutely over the Vaughan rectangle supplies a fixed power saving at the square-root horizon.

For `0<ε<1/2`, the absolute coefficient mass satisfies
`N^(1/2-ε)/4≤W_ε(N)≤(1+1/(1/2-ε))N^(1/2-ε)` for every `N≥1`.
The literal atom constant is positive. Its squared rectangular budget is therefore
bounded above and below by positive multiples of `N^(2-4ε)`, exactly the trivial
exponent `T^(1-2ε)` at `T=N²`. No fixed power gain in this budget is possible.

The first audited positive survivor is the exact signed decomposition into
floor, smooth-power, and dilated remainder terms, together with the finite norm
bound and matching explicit budget powers. Individual unsigned atoms are admitted;
the obstruction lies in their absolute assembly. Retaining the signs is essential
to any improvement over that budget.

The dependency-closed paper proof and fourteen Lean statements are recorded in
`../3-formalized/vaughan-smooth-remainder-and-absolute-budget.md`. All transitive
axiom reports use only standard axioms, the final direct leaf check passed, and
the umbrella import is present.

A stronger positive survivor is now formalized: every actual centered Vaughan
row, after subtracting its explicit common smooth-power term, has every
logarithmic pronic norm saving uniformly in both cutoffs. The convolution row
retains its signed coefficient fluctuation; the exact five-row identity controls
the both-large remainder. The precise theorem is
`exists_uniform_pmPronicVaughanSmoothRemainder_log_rate` in
`UniformLogarithmicRemaindersInAllVaughanRows.lean`. Its six supporting/public
targets passed standard-axiom audits, producing and final direct checks; see
`../3-formalized/uniform-logarithmic-remainders-in-all-vaughan-rows.md`.

The new insight is that the absolute assembly obstruction coexists with every
uniform logarithmic gain for the actual smooth-subtracted rows. It cannot serve
as a lower bound for those rows or the complete receiver. No fixed power gain
has been obtained; full Q-I remains open. Further Gram and classification claims
remain unproved until their own Lean checks pass.
