# Census bandwidth retains normalized height

- **ID:** census-length-height-coordinates
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `docs/reports/review-2910/fable2.md`, §1.3; `Zeta23.Params`.
- **Statement:** The actual census cutoff is `(T/(2π))^λ`, so its physical overlap is
  `(T/(2π))^(λ-1)/(2π)` and physical bandwidth is `λ(1-log(2π)/log T)`.

The cutoff definition is `exp(λ log(T/(2π)))`. Rewriting the exponential as a real
power gives the cutoff and overlap identities. Taking logarithms gives the bandwidth
formula and its limit. For `T>2π`, overlap is at most one exactly when
`λ≤log T/log(T/(2π))`. At parameter one, physical overlap is `1/(2π)`; at parameter
`4/3`, it is `(T/(2π))^(1/3)/(2π)`.

Lean: `GaloisForLFunctions/RHTower/CensusLengthHeightCoordinates.lean`, namespace
`GaloisForLFunctions.SpacingScaleHarmonicAnalysis.LengthHeight`.
Main declarations: `census_overlap_eq`, `census_physical_bandwidth`,
`tendsto_census_physical_bandwidth`, `census_overlap_le_one_iff`,
`census_overlap_at_four_thirds`. Direct `lake --old env lean` check passed;
transitive axiom audits contain only `propext`, `Classical.choice`, `Quot.sound`.
Imported by the RHTower umbrella.
