# Lower separation of discrete logarithmic half-turns

- **ID:** SPL-discrete-half-turn-separation
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper); Lean verification pending
- **Statement:** With `α=log 3/log 4`, every integer `k≥1` and `ℓ∈ℤ` obey
  `|kα−ℓ−1/2|≥1/((3^k+1)log 4)`.
  Consequently a return of precision `1/Q` requires `Q<(3^k+1)log 4`.

For `ℓ≥0`, write the odd integer `3^k` as `2N+1`. The corpus theorem
`RHTower.Sieve.inv_le_abs_log_div_half_integer` gives
`|log((N+1/2)/4^ℓ)|≥1/(2N+2)=1/(3^k+1)`.
Dividing by `log 4` yields the target. For `ℓ<0`, the phase distance is at
least `1/2`, while the proposed lower bound is at most `1/2`.

Since `3^k+1≤2·3^k`, taking logarithms gives the index exclusion

`k > (log Q−log(2 log 4))/log 3`.

Together with the formalized effective upper bound, every integer `Q≥2`
admits a half-turn return whose index lies above this logarithmic lower
bound and at most `Q4^Q log 4/2`.

This complements the upper return bound with an initial-index exclusion.
It concerns one discrete two-scale rotation; the full many-prime
first-return problem remains separate. Lean specialization and its
transitive axiom audit are pending.
