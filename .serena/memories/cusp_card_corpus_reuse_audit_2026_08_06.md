# cusp-spectrum-radius-law — corpus reuse audit (2026-08-06)

Ran before continuing the card, to avoid duplicating existing Lean work.

## NO DUPLICATION in what I built
Nothing in the corpus does Cauchy–Hadamard (`radius = 1/limsup`), the
shift-lattice expansion, the theta-series convergence layer, or the
"no analytic continuation ⇒ radius ≤ R" mechanism.
Other `FormalMultilinearSeries.radius` users are disjoint in purpose:
- `HTGeometry/GutzmerIdentity.lean` — Gutzmer's identity on `cauchyPowerSeries`.
- `HTGeometry/StretchedExponentialMagnitudeHypertranscendence.lean` and
  `HTGeometry/RoughSubleadingPolynomialMagnitudeHypertranscendence.lean` —
  prove `radius = ⊤` for entire phase series.
`HTGeometry/BarnesSourceRepresentative.lean` is the Barnes G/cone-product
logarithmic derivative, NOT Mellin–Barnes contour integration.

## REUSABLE for the remaining work — read these before building
1. **`Bottcher/NaturalBoundary*.lean` (7 modules)** — the corpus's
   natural-boundary layer: `NaturalBoundary`, `NaturalBoundaryReduction`,
   `NaturalBoundaryContradiction`, `RelativeNaturalBoundary`,
   `RelativeRigidityNaturalBoundary`, `ConnectedNaturalBoundaryMandelbrot`,
   `Q62NaturalBoundaryMinimal`.  `NaturalBoundary.no_unit_min_of_analytic` is a
   "nonvanishing analytic `g` on `ball z₀ r` has no interior modulus minimum"
   engine.  This is the closest existing analogue of the ONE input still needed
   by `le_hadamardLimsup_of_no_analytic_extension`, namely "admits no analytic
   extension past a boundary point".
2. **`RHTower/BVPrimeWindowContinuation.lean`** — a fully worked template for
   "Dirichlet series + meromorphic continuation + residue at a zeta zero":
   `continuedSource`, `meromorphicOn_continuedSource_rightHalf`,
   `analyticAt_continuedSource_of_regularizedZeta_ne_zero`,
   `LSeries_polarCoefficient_eq_continuedSource`.  The same
   `LSeries_… _eq_continuation` pattern recurs in
   `RHTower/CCMRectangularObservablePoleTomography.lean`,
   `RHTower/CCMWeightedXiLandau.lean`,
   `RHTower/CCMSharpPrimeWindowSubpowerGate.lean`,
   `RHTower/CCMShiftedXiLandauContinuation.lean`.
   Use this shape for the standard twist `F_α`, do not invent a new one.
3. **Mellin layer already in play**: mathlib's `mellin` is used by
   `HTGeometry/SmoothWeightPerron.lean` (Perron/contour estimates) and
   `HTGeometry/MellinConjugate.lean` (`conj (mellin F s) = mellin F (conj s)`).
   `RHTower/BVPrimeWindow*` carries its own `CompactBVPrimeWindow.mellinTransform`
   with the exact dilation character.  Step 1's boundary case should build on
   mathlib `mellin` + `SmoothWeightPerron`'s contour technique.
4. **`RHTower/SelfDualDirichletRealZeros.lean`** —
   `structure SelfDualPrimitiveDirichletDatum` is the corpus's idiom for an
   "L-function datum" bundling axioms as structure fields.  Model the Selberg
   class `S^♯` structure on it.

## CONFIRMED ABSENT
No Selberg-class structure, no standard twist, no Kaczorowski–Perelli
continuation. The `RHTower/Selberg*.lean` modules are the Selberg SIEVE.
