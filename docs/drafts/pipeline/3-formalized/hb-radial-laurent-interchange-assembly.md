# HB: Laurent extraction through the renormalized radial finite part of the temporal current

- **ID:** HB-RADIAL-LAURENT-INTERCHANGE
- **Stage:** 3-formalized (horizon-mode leg; the normalizable-mode leg is a separate open item)
- **Type:** CANDIDATE
- **Source:** docs/notes.md, ledger step 31; frontier-map HB open core ("interchanging Laurent extraction with full horizon exhaustion")
- **Statement:** For the horizon-mode leg (`outer = false`) of the continued temporal Einstein current, the two-counterterm radial finite part is meromorphic at each fundamental Xi QNM and its order −1 Laurent coefficient is `physicalRadialResidueFinitePart`.

## Goal
Close the radial half of ledger step 31. Chain: literal theta-cusp source → Xi occurrence → retained
spin-two source → physical causal radial/left-QNM action → common Hawking-clock extinction → RH.
This step transfers the already-proved pointwise temporal Laurent coefficient
(`continuedPhysicalTimeAction_laurent`) through the horizon-exhausted radial integral. It proves no
extinction and selects no zero.

## Gates
- [x] 0 → 1  in-progress: well-posed; abstract tools in Lean
- [x] 1 → 2  fully-proven (the Lean development is the proof)
- [x] 2 → 3  formalized: `continuedPhysicalTimeAction_horizon_radial_laurent`

## Approach

Radial density (proved, `continuedPhysicalTimeAction_radial_density`):
`(R²−1)·A(u,t) = (−2u(λ−2)·f(u,t)·g(u,t) − u·g(u,t)·F_h(u,t))·N`, with `f` the continued self
response, `g = tortoiseMode outer u χ t`, `F_h` the horizon-regular source projection. In the horizon
coordinate `z = sech²t`: `R² = 1/(1−z)`, `dt = dz/(2√(1−z)·z)`.

For `outer = false`, `g = z^{u/2}·gauss(u,χ,z)`, every channel of `f` is
`continuedResponse(·) = horizon(u,χ')·(E(u) + S(u)z + O(z²))` uniformly on a frequency ball
(`continuedResponse_horizon_quadratic_expansion`), and the elementary pieces `sourceAmplitude`,
`radialLift`, `reducedHorizonQuotient` are `z^{u/2}` times jointly smooth functions. Hence the
density in `z` is `z^{u−1}·G(u,z)` with `G(u,z) = c₀(u) + c₁(u)z + O(z²)` uniformly; `c₀` has the
simple QNM pole of the self channel, all other coefficients are analytic.

Abstract tools (Lean, unconditional):
- `FirstEndpointMellinLaurentInterchange`: one-counterterm finite part analytic in the frequency;
  residue extraction commutes with it.
- `SecondEndpointMellinLaurentInterchange`: two-counterterm finite part via the divided difference
  `H(u,t) = (F(u,t) − F(u,0))/t`; cutoff limit (`secondEndpointMellin_cutoff_tendsto`), analyticity,
  scalar transport, `laurentCoeff_secondEndpointMellin_div_sub`.

Assembly as built (Lean modules, all unconditional, axioms `propext`, `Classical.choice`,
`Quot.sound` only):
1. `HTGeometry/UniformSecondOrderJet`, `ElementaryHorizonJets`, `AnalyticJetGerm`,
   `JetCoefficientUniqueness`: uniform two-jet algebra, elementary jets, analytic germs, uniqueness.
2. `RHTower/…BMHorizonCoordinateJets`, `…BMSelfChannelHorizonJet`, `…BMPrincipalChannelHorizonJet`,
   `…BMTemporalCurrentHorizonJet`: channel jets and the germ of the cleared density profile.
3. `RHTower/…BMHorizonModeOuterUniformBound`: the continued horizon mode is uniformly bounded up to
   spatial infinity on a frequency ball (homogeneous tortoise ODE + symmetric Grönwall bound).
   This was the one analytic input the corpus lacked: the Gauss series at the boundary of its disc
   is never touched.
4. `RHTower/…BMTemporalCurrentClearedDensity`, `…Bound`: `clearing factor × (R²−1) × current =
   z_t^u · core`, spatial continuity, frequency analyticity through the QNM, uniform outer bound.
5. `RHTower/…BMTemporalCurrentRadialCutoff`, `…Package`, `…Laurent`: patched profile, analytic
   compact part, change of variables, cutoff limit with the profile's own counterterms, clearing
   slope, density at the QNM = slope × residue density, jet coefficients `κF/2`, `−κF/4`, Mellin
   value against the corpus mode square, Laurent coefficient `= physicalRadialResidueFinitePart`.

The `outer = true` leg (normalizable mode) adds a second horizon branch weighted by the connection
coefficient and is not done; it needs a uniform outer bound of the normalizable mode up to spatial
infinity and its horizon jet, then the same assembly.

## Log
- 2026-09-12 — created; abstract Mellin tools compiled (`lake env lean` clean).
- 2026-09-12 — horizon-mode leg closed in Lean (`continuedPhysicalTimeAction_horizon_radial_laurent`);
  ten modules wired into the umbrellas; static lint green; per-module `lake build` audit run on the
  final module (see docs/notes.md §2 for the result).
