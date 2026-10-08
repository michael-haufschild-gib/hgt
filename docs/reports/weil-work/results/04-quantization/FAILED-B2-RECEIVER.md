# Unweighted B² resonance receiver

- **ID:** WP04-F23
- **Stage:** 5-failed, subroute card retained in WP04's reserved output directory.
- **Type:** FALSIFIED under the assigned arbitrary-hW input.
- **Source:** SOURCE-MEAN-COMPACTNESS.md; main WP04 card stays in progress.
- **Statement attacked:** For an input hW, one finite constant controls the
  normalized height-one resonance response of every finite exponential
  polynomial by its B² norm.

## No-go closure

- **Exact killing theorem:** `quantization_resonance_unbounded`; stronger
  witness `exists_quantization_resonance_discontinuity`. For every hW there
  are finite polynomials with mean square tending to zero and response one.
  No existence of hW is asserted; WP01's existence problem is separate.
- **Positive survivor:** sharp finite-band stability with attained constant
  E_c(N), and the source-specific decomposition E_0/log N→|β|²+V>0,
  E_β/log N→V≥0. Conjugate row coefficients attain equality. This identifies
  the unavoidable pole cost and the separate residual cost exactly.
- **New internal insight:** the normalized resonance map cannot descend
  continuously through unweighted mean-square approximation. Removing the
  pole does not prove boundedness, even if the leading variance vanished.
  P22 itself survives. No unboundedness claim is made about the full radial
  contour operator without a nonzero universal kernel limit.
- **Novelty audit:** BRIDGE. Source energy/variance and finite Hilbert duality
  were already known. Their exact resonance realization and source witness
  close this proposed receiver; they are not independently novel science.
- **Paper status:** dependency-closed in RESONANCE-NORM.md.
- **Lean status:** proved in WeilWorkQuantizationResonanceEnergy and
  WeilWorkQuantizationResonanceMean; direct leaf audits and all fifteen axiom
  checks passed. Only standard axioms. Both imports wired; no full build.
- **Verification limit:** authoritative lint found nine unrelated unreachable
  leaves, no quantization issue. See resonance-norm-lean-audit.txt.

## Next conjecture

P23 source-frequency regularity survives preliminary attack, but its physical
contour identification, B²-null remainder, and general-spectrum receiver all
remain unpaid. The next direct source diagnostic is the interval-phase
increment D(h) in SOURCE-FREQUENCY-REGULARITY.md. No P23 Lean was written.
