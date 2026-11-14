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

## A141 continuation construction

The existing `exists_virtualConfig_artin` identifies orders of an analytic quotient
but takes that quotient as input. For a Brauer factor `Λ_q` put
`G_q(s)=(s−1)Λ_q(s)`, which extends analytically to `Re s>0`. Write
`n_q=n_q⁺−n_q⁻`. Then

`A(s)=∏ G_q(s)^{n_q⁺}(s−1)^{n_q⁻}`,
`B(s)=∏ G_q(s)^{n_q⁻}(s−1)^{n_q⁺}`

are analytic, `B(2)≠0`, and `A=B·L_Artin` on `Re s>1`. Substitution in the existing
order theorem discharges the continuation input of the virtual index law. It does
not supply the general-field `7/8` estimate or conductor/ramification matching.

## Existing ingredients and outstanding checks

- **A162 closed:** see `../3-formalized/a162-certified-window-floors-and-overlap-calculus.md`.
- GCW's Green criterion, harmonic criterion, additive loss law and
  `one_lt_bindingEnergy` passed transitive audits: only `propext`,
  `Classical.choice`, `Quot.sound`.
- `ChargeCancellationPreservesTheCertifiedFloor.lean` proves the spectral floor,
  including `J < R`, exact charge-cancellation Schur transfer and the local
  harmonic index criterion. Direct Lean check and transitive audits passed;
  see `../3-formalized/charge-cancellation-preserves-the-certified-floor.md`.
- The GCW module
  `TheCertifiedFloorsAreAPrioriBoundsForTheGreenMatrixAndTheConditionalEnergies`
  supplies first-overlap floors. Its source snapshot and transitive audits passed;
  only `propext`, `Classical.choice`, `Quot.sound`. Umbrella import added.
- **A140 odd sector closed at `1881/5000`:**
  `WindowTowerOfSpecZ.weilQuad_ge_odd_at_aperture_1881_over_5000` proves
  `weilQuad F ≥ (1/2000)∫F²`. The polynomial comparison, third regional gap,
  and actual Weil transfer passed direct Lean checks and standard-only axiom
  audits. See `../3-formalized/a140-odd-certificate-at-1881-over-5000.md`.
  **The full first-overlap certificate is closed.** The even sector has floor `1/50000`:
  `weilQuad_ge_even_at_aperture_1881_over_5000` passed its direct check and
  standard-only axiom audit. Parity, complexification, the closed form and
  every block matrix of ratio `≤10609/5000` retain that floor. All transfer
  checks and axiom audits passed; see
  `../3-formalized/a140-first-overlap-certificate-at-1881-over-5000.md`.
  Larger apertures remain open; see
  `a140-certificates-through-the-prime-five-boundary.md`.
- A141: the quotient construction is formalized in
  `EveryArtinEulerProductHasAMeromorphicContinuationAndASignedIndexLaw.lean`:
  `exists_analytic_quotient_artin`, `exists_meromorphicContinuation_artin`,
  `exists_analytic_quotient_and_virtualConfig_artin`, and
  `exists_meromorphicContinuation_and_signedIndex_artin`. The last theorem
  identifies actual meromorphic orders and counts zeros and poles directly.
  Direct Lean check passed;
  transitive axioms are only `propext`, `Classical.choice`, `Quot.sound`.
  The located `7/8` producer uses the Hecke family over `ℚ(ζ₃)`, not arbitrary
  containing fields. The corpus now supplies primitive-character matching at every prime, including
  conductor support: see `../3-formalized/agz-conductor-ramification.md`.
  General-field `7/8` and higher ramification conductor exponents remain open.
- The general-field analytic receiver already exists:
  `FamilyContinuationTheory.heckeHalfPlane_of_family_reciprocal_signal`.
  It uses `heckeZeroFunction`, clearing the pole only for the trivial character.
  The missing input is a family of actual arithmetic signals with both direct
  and comparison exponents below each `β>7/8`, uniformly across ray characters.
  The located cubic reciprocity, sieve, and common-probe producers still use
  the Eisenstein ring; their field generalization is not supplied by this receiver.
