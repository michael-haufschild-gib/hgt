# Certified window floors and Artin index transfer

- **ID:** A162-A140-A141
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** `docs/reports/review-1311/obstacles-summary.md`, A162, A140, A141.

## Exact targets

1. **A162:** floor `1/5000` above the ground state on every window of ratio
   `≤103/50`; the same floor for both conditional energies at the first overlap;
   orthogonal and Green overlap criteria; additive loss below the middle's binding
   energy; a positive uniform lower bound for that energy.
2. **A140:** unconditional Weil certificates at aperture `1881/5000`, above
   `log(3)/2`, above `log(2)`, and through `log(5)/2`, with transfer to all block sizes.
3. **A141:** the `7/8` half-plane for all ray class characters over fields containing
   a primitive cube root of unity; Artin index transfer with signed zero/pole orders
   and local conductor/ramification matching.

## A162 proof mechanism

The certified charge-free floor transfers to the ground-state orthogonal complement
by canceling the charge with the positive ground vector. For a conditional energy,
take the harmonic extension from an end into the middle and cancel its charge by
adding the negative middle ground vector. Their cross term vanishes. The certified
floor on the resulting vector bounds the end mass, while the added middle energy
is nonpositive. This retains the exact floor `1/5000` without inverting a matrix
shifted to a possibly singular spectral endpoint.

## Existing ingredients and outstanding checks

- GCW's first two modules contain the Green criterion, harmonic criterion, additive
  loss law and `one_lt_bindingEnergy`; source and transitive axioms require audit.
- Spectral and conditional-energy floors: proof above, formalization pending.
- Larger-aperture certificates and arithmetic transfer: source audit pending;
  no unproved input may become an assumption of a claimed solution.
