# Full-theta all-rank center tails

- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Wall:** Σ6
- **Statement:** For every `N : ℕ` and `r≥0`, the matrix
  `∫_(s>r) Re((-i)^(j+k)) ∂ₜ^(j+k)[Φ(s/2+t)Φ(s/2−t)]|ₜ₌₀ ds`
  is positive definite, where `Φ` is the complete theta-cusp source.

The [first-atom theorem](../3-formalized/all-rank-first-atom-center-tails.md)
proves the corresponding assertion for `thetaCuspSourceTerm · 1`.
The complete source requires the signed unequal-pair contribution and the
infinite remainder. Existing fixed-rank remainder estimates do not supply
a bound uniform in rank.

The ordered-pair Fourier normal form retains
`exp(-ib(log n−log m))`; its radial factor alone is positive after center
integration. A full-source proof must control these phases jointly and
justify the infinite sum. No such estimate or all-rank full-source proof
is established here.
