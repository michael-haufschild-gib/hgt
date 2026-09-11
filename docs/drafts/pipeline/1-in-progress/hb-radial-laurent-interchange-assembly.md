# HB: Laurent extraction through the renormalized radial finite part of the temporal current

- **ID:** HB-RADIAL-LAURENT-INTERCHANGE
- **Stage:** 1-in-progress
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
- [ ] 1 → 2  fully-proven
- [ ] 2 → 3  formalized

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

Remaining assembly (in order):
1. Uniform two-jet algebra on a parameter ball: sums, products, scalars, elementary examples via
   `taylor_mean_remainder_bound` + compactness of `closedBall × Icc 0 b`.
2. Channel expansions: principal channels on a full ball (connection nonzero at the QNM), self
   channel on the punctured ball; cleared coefficients analytic at the QNM by removable singularity.
3. Density assembly `z^{u−1}·G(u,z)`, change of variables `t → z`, analyticity of the compact
   part `z ∈ [b,1]`.
4. Final theorem: cutoff limit with the density's own counterterms, meromorphy, Laurent coefficient
   `= physicalRadialResidueFinitePart` (uses `physicalTimeResidue_radial_cutoff_tendsto` at the QNM).

The `outer = true` leg (normalizable mode) adds a second horizon branch weighted by the connection
coefficient and is deferred.

## Log
- 2026-09-12 — created; abstract Mellin tools compiled (`lake env lean` clean).
