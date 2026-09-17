# SP-E signed-Eulerian research facts

- `suzukiWordCoefficient k ν` is exactly a Volterra grade factor times the commutative product of
  the prime-power weights of `ν i`.  It is independent of every `Bool` orientation label and
  invariant under every `Equiv.Perm (Fin k)` reindexing.
- The associated physical inverse-log profile has the same invariance.  Hence this scalar/profile
  carrier cannot instantiate the SP-E open-core signed type-B word action.
- In particular, the physical coefficients of the two four-label orders `3142` and `3241` are
  equal for arbitrary prime-power labels and arbitrary independent Boolean assignments.  The
  carrier loses the first descent-bottom discriminator before a stable top-fibre specialization.
- Lean proof: `formal/GaloisForLFunctions/RHTower/PrimeGammaPhysicalWordHyperoctahedralBlindness.lean`.
- Positive survivor: P-G186's off-diagonal Cauchy Gram retains pair incidence absent from the
  scalar word coefficient.  Its zero-ordinate base edge is `2/(x+y)^3`; every ordered positive
  four-packet has strictly positive signed-Eulerian curvature, and every positive diagonal source
  transport preserves it exactly.  Thus the P-G186 pair source passes the four-label
  descent-bottom discriminator.
- Lean proof: `formal/GaloisForLFunctions/RHTower/PrimeGammaCauchyCubicSignedEulerianCurvature.lean`.
- No corpus theorem presently maps this pair incidence to completed signed-word columns or a
  type-B insertion action.  That categorical source bridge remains open.
