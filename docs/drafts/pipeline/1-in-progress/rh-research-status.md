# RH research status

- **CCM-FU/CFI:** weighted-curvature first moment and central unit-Riesz barycenter impossible under RH. `RHTower/CCMFULittlewoodNoGo.lean`.
- **MSC germ:** strict-right zero gives `F/B=2m/(v-uσ)+hσ(v)`, `hσ(uσ)→2`, `|hσ(uσ)|²→4`. `RHTower/HedenmalmGammaSewnSquarefreeFisherRegularGermCofinal.lean`.
- **MSC walls:** physical `ℓ²`, fixed-power, reciprocal diagonal, and all Bessel-Hilbert realizations fail in their strict-right regimes. `...PhysicalHilbertWall`, `...PowerRiggingNoGo`, `...DiagonalRiggingNoGo`, `...BesselHilbertStabilityWall`.
- **MSC qualitative rigidity killed:** exact complete-minimal models exist for `Re ρ>0`; for `Re ρ>1/2`, exact strong Markushevich models have every mixed system complete, unit primal norms, and dual norm² `≤2`; all remain non-Bessel when `Re ρ≤1`. `...CompleteMinimalSingularRealization`, `...UniformStrongMarkushevichSingularRealization`.
- **MSC survivor:** derive Bessel/frame stability from arithmetic source geometry; positivity, minimality, hereditary completeness, and uniform biorthogonal bounds are insufficient.
- **Novelty audit through 2026-08:** no collision found for these exact MSC laws.
- **NDS:** terminal conductor naturality commutes at a Xi fibre iff `Re ρ=1/2`; global naturality is exactly RH, not a consequence of reduced nodal geometry. `RHTower/XiNodalConductorHolonomyNaturalityClassification.lean`.
- **KMSS:** no scalar transposition-invariant coefficient-faithful completion exists; sign compensation is universal and nonselective. The surviving zero-specific order-independent completion is exactly RH. `RHTower/XiKoszulSourceTranspositionClassification.lean`.
- **Shared Gamma Ward:** fixed grade-universal countable positive tensor-degree mixtures fail: reflection forces pure degree `4`; two-prime phase kills it. `RHTower/SourceGammaCountableHalfDensityDegreeMixtureNoGo.lean`.
- **TCD:** all work reduces to `D1>0`; actual orbit lies in `X>191/10+(37/5)z²`, `0<z<3/10`, `(13/32+z²/32)z<v<(33/80+z²/16)z`. Scalar-angle concavity cannot imply the required five-point coalescent PSD. Open: positive actual singular flux, or one nonpositive actual singular flux kills TCD.
- **LI real-shape killed:** packet `7×(1/2)+(3/4±i)` has local Bernstein response and globally strictly completely monotone response quotient on `v≥0`, yet endpoint mode `n=3` is negative. `...LocalBernsteinShapeNoGo`, `...GlobalQuotientCompleteMonotonicityNoGo`.
- **LI survivor:** coefficient orientation requires complex singularity-support control; every real-ray derivative sign still permits off-axis squared nodes.
- **D2 contour shortcut killed:** actual boundary-to-interior lower-bound bridge on admissible rational windows is equivalent to RH. Under false RH, one zero-free compact frontier has a finite defect floor while Gaussian-rational interior values are unbounded below. `...PrimeArchLogHeightDefectBoundaryInteriorNoGo`.
- **D2 survivor:** prove zero/residue exclusion before contour transport; boundary-size estimates alone cannot supply the interior floor.
- **E bounded-density singleton histories killed:** exact cancellation with Gibbs defect `D→0` forces `C/(M-2)→∞`; finitely, `C≥-(M-2)log D/2`. Survivor: superlinear component density or nonvanishing curvature. `...RouteEComponentHistorySparseDensityNoGo`.
