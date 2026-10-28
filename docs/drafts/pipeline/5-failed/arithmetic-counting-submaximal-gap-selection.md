# A submaximal prime gap does not select complete Weil positivity

- **ID:** ACP-SUBMAXIMAL-SELECTION
- **Stage:** 5-failed
- **Type:** FALSE IMPLICATION; positive survivor formalized
- **Rejected route:** A fixed positive prime-hyperplane gap, multiplicativity,
  the von Mangoldt absolute majorant and untwisted polar matching suffice for
  complete Weil positivity.
- **Parent:** ../1-in-progress/arithmetic-counting-positivity.md

## Exact obstruction

For every `a<2log 2`, a prime `p` gives the completely multiplicative sign
`omega_p(n)=(-1)^v_p(n)` with hyperplane gap at least `a` and

`|sum_{n<=y}omega_p(n)Lambda(n)/n-log y|
 <=log 4+4+2log p/(p-1)`.

Its actual source `lambda_p(n)=omega_p(n)Lambda(n)` satisfies
`|lambda_p(n)|=Lambda(n)` but fails complete Weil positivity. Indeed full-cone
uniqueness would force `lambda_p(p)=Lambda(p)`, whereas these values are
`-log p` and `log p`. The failure has an actual compactly supported `C^2`
test witness in the literal functional, retaining Gamma, both poles and every
prime-power term.

Lean: `near_maximal_gaps_do_not_force_weil_positivity` and
`primeFlip_exists_negative_complete_test` in
`ArithmeticCountingPositivity/NearMaximalGapsDoNotForceWeilPositivity.lean`.

## Strongest positive survivor

The count retains useful energy rather than merely detecting a failure:

1. Uniformly over all sign gauges and all horizons beyond an
   epsilon-dependent threshold, the retained gap is at least
   `(2log 2)(S_N/H_N)^2`. The geometric projection bound underlying this
   inequality is attained by the projected gauged pole.
2. Negative prime-parity fibres are exactly `p` times positive fibres.
   Their weighted count gives `p(H_N-S_N)=H_floor(N/p)+S_floor(N/p)`.
3. The exact excess over `S_N/H_N=(p-1)/(p+1)` is a positive boundary count
   bounded by `2(1+log p)`. Thus this harmonic ratio has the stated exact
   limit, and the paid gap is `(2log 2)((p-1)/(p+1))^2`.
4. The prime-two flip retains gap `2log 2/9`, although Liouville has no
   positive hyperplane gap. Selectivity against Liouville is therefore
   strictly weaker than selection among multiplicative sources.

Paper proof: `arithmetic-counting-pole-angle.md`. Lean survivors:
`eventually_prime_gap_ge_squared_correlation`,
`gaugeWitness_attains_variance_bound`, `prime_parity_pairing`,
`prime_parity_boundary_identity`, `prime_parity_boundary_bounds`,
`primeFlip_harmonicCorrelation_tendsto`, `primeFlip_hasHyperplaneGap`, and
`two_adic_parity_has_gap_but_liouville_does_not`.

All 28 theorems in the four-module contribution have transitive axiom audits
containing only `propext`, `Classical.choice`, and `Quot.sound`. Canonical
source checks and the durable audit report accompany the formalized paper
card. No unproved analytic estimate is stored in the survivor's hypotheses.

## New insight and remaining boundary

Counting can pay a selective gap without recovering the source information
needed by the complete form. A transfer using only a fixed submaximal gap and
leading polar matching cannot be valid for the whole multiplicative class.
The construction leaves the maximal gap and the full producer mechanisms
open; neither the programme nor the exact endpoint is retired by this card.
The separate maximal-gap card investigates whether arithmetic spectral
coordinates expose a stronger obstruction.
