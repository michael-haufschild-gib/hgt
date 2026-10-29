# Even the maximal prime gap does not select complete Weil positivity

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

The endpoint is now also ruled out: every prime `p>=11` gives a nontrivial
flip with greatest gap exactly `2log 2`, the same polar matching and an
actual negative complete-Weil test. This is
`maximal_gap_does_not_select_the_source` in
`LargePrimeFlipsAttainTheMaximalGap.lean`, with paper
`../3-formalized/arithmetic-counting-maximal-gap-rigidity.md`.

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
5. The exact cutoff is eleven. Every prime-flip gap is at most
   `p log p/(p+3)`, strictly below the maximum for p<11; combined with
   the large-prime theorem, maximal-gap attainment holds iff p>=11.
6. The parity constraint has a complete arithmetic spectral measure:
   squared mass `c_p^2` at the ground and `4c_p^2/phi(p^k)` on each
   positive p-power. Its finite tower approximations have the sharp error
   `4p/((p+1)^2 p^K)` uniformly over every positive integer horizon.

Paper proof: `../3-formalized/arithmetic-counting-pole-angle.md`. Lean survivors:
`eventually_prime_gap_ge_squared_correlation`,
`gaugeWitness_attains_variance_bound`, `prime_parity_pairing`,
`prime_parity_boundary_identity`, `prime_parity_boundary_bounds`,
`primeFlip_harmonicCorrelation_tendsto`, `primeFlip_hasHyperplaneGap`, and
`two_adic_parity_has_gap_but_liouville_does_not`.

All 28 theorems in the four-module contribution have transitive axiom audits
containing only `propext`, `Classical.choice`, and `Quot.sound`. Canonical
source checks and the durable audit report accompany the formalized paper
card. No unproved analytic estimate is stored in the survivor's hypotheses.

Survivors 5 and 6 have dependency-closed proofs and Lean formalizations in
`../3-formalized/arithmetic-counting-small-prime-gap-boundary.md` and
`../3-formalized/arithmetic-counting-parity-spectral-mass.md`. Their three
and eight public endpoints respectively passed canonical source checks
and transitive axiom audits. The combined cutoff equivalence also audits
the imported large-prime endpoint transitively with only standard axioms.

## New insight and remaining boundary

Counting can pay a selective gap without recovering the source information
needed by the complete form. A transfer using only the prime-hyperplane gap,
even its exact maximum, and leading polar matching cannot be valid for the
whole multiplicative class. The sharp cutoff and complete parity spectral
measure identify what survives this obstruction. Exact gap values below
eleven and the full producer mechanisms remain open. The separate secular
gap card develops the former from these counted coordinates.
