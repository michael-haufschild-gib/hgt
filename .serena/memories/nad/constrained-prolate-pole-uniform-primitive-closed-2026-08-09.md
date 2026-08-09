# Constrained-prolate card: the pole-uniform primitive is closed (2026-08-09)

Card: `docs/drafts/pipeline/2-fully-proven/nad/constrained-prolate-continuous-polar-charge-law.md`.
All modules wired into `GaloisForLFunctions/RHTower.lean` (a few into `HTGeometry.lean`).
All declarations axiom-clean (`propext, Classical.choice, Quot.sound`).

## Headline results now proved unconditionally

- **`(47)` for the model**: `RHTower.abs_integral_radialProlateBesselProfile_le` —
  `|∫_1^X radialProlateBesselProfile s c x| ≤ 648*64/c` for `1 < X ≤ 2`, `0 ≤ s ≤ 1/2`, `c > 0`.
- **`(47)` for the EXACT mode**: `RHTower.abs_integral_sqrt_mul_radialProlate_le` —
  `|∫_A^X √c·R x| ≤ (8KC/3 + 2·648·64)/c`, `A = dunsterEndpointCrossing c ≤ X ≤ 2`, `c ≥ 5`.
- **`(50)` exterior branch, hypothesis-free**: `RHTower.norm_integral_exterior_dunster_le` — `≤ 21/c`,
  uniform in the endpoint.

## Module map (mine)

`HTGeometry/`: `DerivSignMonotone`, `SturmWronskian`, `L2PairingLimit`,
`InverseSqrtEndpointIntegral` (weights `(t-1)^{-1/2}`, `(t-1)^{1/2}`, `(t-1)^{-1/4}` + quarter-root
identity), `InteriorIntegrationByParts` (bounded-on-open integrability; IBP with interior
derivatives; degenerate-endpoint product continuity).

`RHTower/`: `ProlateProportionality`, `ProlateModeVariation` (= `(19e)`), `VanDerCorputIBP`,
`BesselJOneRecurrence`, `BesselJOneEnvelope` (= `(44)`), `BesselWeightedPrimitive` (= `(45)`,`(46)`),
`BesselWeightedPrimitiveInterior` (`(45)` for a weight with no value at `r=0`),
`OscillatoryDecayPrimitive`, `ExteriorProfileBounds`, `XiReciprocalSpeed` (= `(49)`),
`ExteriorXiPrimitive`, `XiAmplitudeDecay` (= `(48)` amplitude half), `ExteriorDunsterPrimitive`,
`XiCoordinate` (continuity at the singular endpoint, strict monotonicity, image, **substitution**),
`XiTransportedPrimitive`, `XiInverseCoordinate` (`xiInverse` + inverse function theorem),
`XiBesselWeight` (= `(42)`,`(41)`), `XiBesselWeightBounds` (`C⁰` half of `(43)`),
`XiEndpointExpansion` (= `(40)`), `XiEndpointCancellation` (the divergent-term cancellation),
`XiBesselWeightDeriv` (`C¹` half of `(43)`), `XiCompactPrimitive` (= `(47)` model),
`ProlateProfileTransferIntegral`, `ProlateEnvelopeIntegral` (sharp `O(c^{-3/2})` transfer),
`ProlateExactPrimitive` (= `(47)` exact).

## Corpus facts found by searching (do NOT rebuild)

`(38)`/`(48)` **already existed**: `ProlateDunsterUniformTransfer.abs_radialProlate_sub_regularModel_le`
and `ProlateDunsterDensityTransfer.abs_radialProlate_sub_besselProfile_le` — unconditional uniform
`O(c^{-1})` approximation of the actual mode by the regular Bessel model beyond
`dunsterEndpointCrossing c = 1 + 9/(8c²)` (`≤ 11/10` for `c ≥ 5`).  Also `xiAmplitude`,
`xiAmplitude_le`, `xiAmplitudeDeriv`, `hasDerivAt_xiAmplitude`, `phaseLogDefect`,
`abs_phaseLogDefect_le_far`, `xiEndpointPhase_bounds`, `one_le_xiSpeed`, `xiSpeed_pos`,
`continuousOn_*`, `lgEndpointVolterraReconstruction`, `radialProlateBesselProfile`.

## Two rate/method findings worth keeping

1. **Bounding the Bessel envelope by its supremum loses the half power that separates the error from
   the main term.**  Crude bound → error `O(c^{-1})` → after `√c` normalization `O(c^{-1/2})`, which
   *dominates* `(47)`.  Must integrate the envelope: `ξ_s(x) ≥ √(x−1)` gives envelope
   `≤ c^{-1/2}(x−1)^{-1/4}`, integrable, restoring `O(c^{-3/2})`.
2. **The `C⁰` half of `(43)` needs no expansion; the `C¹` half provably does.**  The bracket pins
   `r^{1/2}` to `(x²−1)^{1/4}` within a bounded factor (enough for `B`), but `B'/B` contains a
   difference of two `C/√u` terms whose cancellation needs the next order — i.e. `(40)`.

## Still open on the card

`(16)` for `k ≥ 2` and the summable majorant → `(11)`; `(51)` via `(10)`; `(18)`,`(32)` promotion;
the `h₀,h₄` occupancy gate; and the three RH-bearing gates (true even ground/gap, locally uniform
determinant convergence, true cofinal Weil floor).

## Operational

- **Never `pkill -f "lean --"`.**  It matches concurrent agents' processes and shell wrappers; it
  cost a 2300 s full rebuild and may have disrupted another agent.  Check `pgrep` and wait.
- Concurrent agents rebuild the same umbrella; `lake build <umbrella>` can fail on a *different*
  missing `.olean` each run.  That is contention, not breakage.  Verify with
  `lake build <my module>` individually.
- Only one `lake build` at a time — concurrent invocations block on the lake lockfile and all stall.
