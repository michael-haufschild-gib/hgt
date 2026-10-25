# Moving truncations preserve dominated limits

- **ID:** moving-truncations-preserve-dominated-limits
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Source:** uniform-half-damping-vaughan-harmonic-gram.md; vaughan-admission-phase-transition-at-half-damping.md
- **Verification:** Producing and final direct repository checks passed. Transitive axioms: `propext`, `Classical.choice`, `Quot.sound` only.

Let `f_t(n)` be real sequences with one nonnegative summable envelope
`|f_t(n)|≤b(n)`. If `f_t(n)→g(n)` for every cell, `g(0)=0`, and the integer
horizon `H(t)→∞`, then

`Σ_(1≤n≤H(t)) f_t(n) → Σ_(n≥0) g(n)`.

Zero-extension outside each finite horizon preserves the common envelope.
Every positive cell is eventually included, so dominated series convergence
proves the result without a relation between the horizon and the cellwise
convergence rates.

The declaration
`GaloisForLFunctions.HTGeometry.tendsto_sum_Icc_at_moving_horizon_of_summable_bound`
is proved in
`GaloisForLFunctions/HTGeometry/MovingTruncationsPreserveDominatedLimits.lean`.
Its summability, domination, and pointwise-limit hypotheses are explicit
transfer inputs. The module is wired into its umbrella; its olean supports
the written endpoint and upper-half Vaughan applications. Its temporary
draft was removed after the final direct check.
