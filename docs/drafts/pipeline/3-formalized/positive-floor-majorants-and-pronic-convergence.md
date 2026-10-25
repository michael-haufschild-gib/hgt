# Positive floor majorants and pronic convergence

- **ID:** positive-floor-majorants-and-pronic-convergence
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Source:** ../2-fully-proven/uniform-half-damping-vaughan-harmonic-gram.md; ../2-fully-proven/vaughan-admission-phase-transition-at-half-damping.md
- **Verification:** Five targets passed corrected producing and final direct repository checks. Transitive axioms: `propext`, `Classical.choice`, `Quot.sound` only.

Write `A_a(n)` for the centered floor prefix with reciprocal mean `Σ a(d)/d`.
If `Σ b(d)/d` converges and `|a(d)|≤b(d)`, then
`|A_a(n)|≤|A_b(n)|` at every positive cell. The nonnegative floor-mean defect
gives this domination after multiplying by `n`.

A uniform finite-horizon pronic norm bound gives summability of the complete
square-cell series. Under a common summable square envelope

`f_t(n)²/[n(n+1)]≤g(n)`,

cellwise convergence `f_t(n)→F(n)` implies

`Σ_(n≥1)(f_t(n)−F(n))²/[n(n+1)]→0`.

The same convergence holds in pronic norm at any moving finite horizon,
including bounded horizons. The proof bounds each difference square by four
times the common envelope, applies dominated convergence, and bounds finite
partial energies by the nonnegative full series. A separate quadratic estimate
bounds every mixed cell by a common square-cell bound.

The module
`GaloisForLFunctions/BezoutValuationIncidence/PositiveFloorMajorantsControlPronicEnergy.lean`
proves:

- `abs_weightCenteredPrefix_le_abs_majorant`;
- `summable_sq_div_pronicSeq_of_pronicNorm_bound`;
- `abs_pair_div_le_common_square_bound`;
- `tendsto_tsum_pronic_square_sub_of_summable_envelope`;
- `tendsto_pronicNorm_sub_at_moving_horizon_of_summable_envelope`.

These are general transfer theorems with their summability, domination, and
pointwise-convergence inputs explicit. The module is wired; its olean supports
the written endpoint and upper-half specializations. Its temporary draft was
removed after the final direct check. The actual moving Vaughan limit claims
remain separate verification obligations.
