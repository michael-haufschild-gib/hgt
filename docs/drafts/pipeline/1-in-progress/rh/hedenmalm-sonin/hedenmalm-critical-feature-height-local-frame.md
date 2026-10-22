# Hedenmalm critical-feature height-local frame

- **ID:** `P-G148`
- **Stage:** `1-in-progress`
- **Status:** `[PAPER-PROVED] [LEAN-PROVED] [CORPUS-NEW SYNTHESIS] [NOT RH]`
- **Parent:** `rh-current-frontier-map.md`, Route P finite-ceiling wall
- **Module:** `formal/GaloisForLFunctions/RHTower/Hedenmalm/HedenmalmCriticalFeatureHeightLocalFrame.lean`

## Conjecture loop

1. `[FAILED]` Aggregate shellwise incomplete-Gamma Ward--Schwarz cones into a relative Xi-energy
   bound. Each shell remainder obeys a uniform derivative cone, but the completed Hermitian fibre
   contains signed divisor-reflected cross terms. Triangle inequality yields only an
   `O(|Xi|)` current bound; excluding an off-line zero requires `O(|Xi|^2)`. Missing power is
   exactly phase coherence, hence RH-bearing. No shellwise aggregation theorem is claimed.
2. `[PIVOT]` Replace Xi itself by Hedenmalm critical features. Their evaluation never vanishes in
   the open strip, so hypothetical zero copies cannot hide behind Xi phase cancellation.
3. `[PROVED]` Real-centered critical feature has exact energy

   ```text
   |ell_z(k_t)|^2 =
     4 / ((1+(Re z-t)^2-(Im z)^2)^2 + (2(Re z-t)Im z)^2).
   ```

4. `[PROVED]` If `|Re z-t|<=1/2` and `|Im z|<1/2`, denominator is at most `25/16`; therefore

   ```text
   |ell_z(k_t)|^2 >= 64/25.
   ```

   Taking `t=round(Re z)` selects one fixed countable reporter family, uniformly over height.
5. `[PROVED]` Functional-equation pairing makes the five-shift feature energy conjugation-even.
   Multiplying by forced transverse Green factor `(-Im z)^(-2)` gives exact factorization

   ```text
   pairedFeatureCurrent(t,z)
     = fiveShiftPairedRenormalizedFeature(1,-Im z) * |ell_z(k_t)|^2.
   ```

6. `[PROVED]` Existing scalar quantum `fiveShiftPairedRenormalizedFeature>=1/81` combines with
   frame bound to give every strict-right Xi copy

   ```text
   pairedFeatureCurrent(round(Re z),z) >= 64/2025.
   ```

## New knowledge

Height escape and reporter degeneration are not obstructions for singular five-shift landing.
Every off-line Xi multiplicity copy deposits fixed rational charge into one nearest-integer
Hedenmalm feature channel, uniformly in ordinate and transverse displacement. Prime--Gamma source
anatomy of each channel is already exact.

Remaining obstruction is narrower: realize inverse-square transverse Green normalization inside a
height-local Hermitian prime--Gamma trace and prove its arithmetic upper budget. Boundary rigidity
shows no bounded continuous diagonal-vanishing source coefficient can do this; successful producer
must retain unbounded tangent/Green graph or intrinsically discontinuous index channel.

## Gates

- [x] failed shell aggregation audited without RH leakage
- [x] exact critical-feature energy law
- [x] uniform nearest-integer frame bound `64/25`
- [x] exact functional-equation-paired factorization
- [x] universal Xi-copy quantum `64/2025`
- [x] direct Lean check
- [x] exact module build
- [x] axiom audit (`propext`, `Classical.choice`, `Quot.sound` only)
- [ ] umbrella build
- [ ] singular source-trace producer
- [ ] unconditional RH
