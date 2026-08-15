# CCM (not-new-scientific-knowledge) Stage-2 → Stage-3 formalization ledger

Goal: every card in this folder gets an unconditional Lean 4 theorem (no unproved mathematical
premise, no added axioms; `#print axioms` = `[propext, Classical.choice, Quot.sound]`), a
`-formalized.md` certificate, and a move to
`docs/drafts/pipeline/3-formalized/not_new_scientific_knowledge/ccm/`.

Standard applied: formalize every statement the card **proves itself**. Statements the card *cites*
from the literature (Suzuki's screw representation, Krein–Langer, Yoshida's criterion, Weil's
criterion, Connes–Consani radical membership, …) are parents, not theorems of the card, and are
recorded in the certificate under "deliberately outside the Lean statement".

Verification per card: `lake env lean` on a scratch file importing the modules and `#print axioms`
on every non-private theorem; umbrella wiring checked; declaration names cross-checked against the
tree.

## Promoted (Stage 3)

| card | modules |
|---|---|
| `ccm-aperture-morse-index-conservation-law` | `CCMApertureMorseCharge` |
| `ccm-boundary-strip-weak-compactness-transfer-law` | `CCMBoundaryStripTransfer`, `MobiusFisherContactWardBudget` |
| `ccm-bv-muntz-graph-domain-extension` | `CCMBVMuntzSummation` |
| `ccm-cofinal-prime-sawtooth-incidence-law` | `CCMSawtoothDilationMean`, `CCMSawtoothDilationIncidence`, `CCMSawtoothExteriorTail`, `SawtoothFourierSeries` |
| `ccm-cofinal-weil-spectral-floor-criterion` | `CCMCofinalFloorCriterion`, `CCMNestedFloorNoEvacuation` |
| `ccm-coherent-euler-logarithm-square-exclusion-law` | `CCMCoherentSquareExclusion` |
| `ccm-compressed-prime-shift-arithmetic-complement-law` | `CCMCompressedShiftIndependence` |
| `ccm-endpoint-oscillation-poisson-tail-bound` | `SawtoothFourierSeries`, `PeriodicFourierDecay`, `PoissonSummationPiecewise`, `CCMEndpointFourierJet`, `CCMTwoModeDeficitScale` |
| `ccm-exact-finite-aperture-first-row-vanishing` | `ArcoshComparison`, `IntegralGronwall`, `BesselJZero{Envelope,ODE,Phase,SecondSolution}`, `CCMFirstRow{StationaryPhase,VanDerCorputBlocks,EnvelopeTail,DunsterModel}`, `CCMRadialProlate{Defect,EndpointLayer}` |
| `ccm-exterior-range-observability-law` | `HTGeometry.RangeObservabilityDuality` |
| `ccm-finite-prime-parity-hankel-carrier` | `SuzukiParityHankelDecomposition`, `SuzukiPrimeHankelCarrier` |
| `ccm-galerkin-cofinal-diagonal-transfer` | `CCMGalerkinDiagonalTransfer`, `CCMRayleighExcessAngle` |
| `ccm-higher-subset-covariance-fock-lift` | `CCMSubsetCovarianceFock` |
| `ccm-parity-split-evans-gram-law` | `CCMParityInvolutionGrading` |
| `ccm-quartet-resolvent-bilateral-polarization-law` | `CCMQuartetResolventPolarization`, `CCMQuartetPaleyWiener` |
| `ccm-radial-dilation-divisibility-carrier` | `CCMRadialDivisibilityCarrier` |
| `ccm-rayleigh-excess-determinant-transfer` | `CCMRayleighExcessAngle` |
| `ccm-rayleigh-transfer-collapses-to-spectral-floor` | `CCMCofinalFloorCriterion` |
| `ccm-suzuki-deficiency-line-zero-shift-floor-equivalence` | `CCMDeficiencyLineZeroShift` |
| `ccm-weil-exterior-tail-quotient-gate` | `CCMWeilRadicalTailQuotient` |
| `ccm-evans-gram-requires-determinant-line-lift` | `HTGeometry.ComplexGramPlucker` (new), `CCMEvansDeterminantLine` (new) |
| `ccm-fredholm-schur-resolvent-carrier-law` | `HTGeometry.SchurComplementKernel` (new) |
| `ccm-shift-covariant-pole-divisor-capacity-law` | `CCMShiftCovariantPoleDivisorCapacity` (new) |
| `ccm-prime-free-aperture-characteristic-pair-law` | `CCMPrimeFreeApertureCharacteristicPair` (new) |
| `ccm-transverse-index-trace-slope-coercivity-law` | `CCMTransverseIndexTraceSlopeCoercivity` (new) |
| `ccm-hankel-gap-trace-slope-rh-criterion` | `CCMHankelGapTraceSlope` (new) |
| `ccm-gauss-paired-quantized-differential-incidence-law` | `CCMGaussPairedQuantizedDifferential` (new) |
| `ccm-generic-ground-separating-incidence-law` | `HTGeometry.SeparatingGramLocus` (new), `CCMGenericGroundSeparatingIncidence` (new) |
| `ccm-prime-source-ground-incidence-response` | `CCMPrimeSourceGroundIncidence` (new) |

## Open — Lean to be built

Each entry names the statements the card proves that must be formalized.

| card | what must be built |
|---|---|
| `ccm-aperture-morse-hardymodel-index-exhaustion-law` | `(9)` conjugate-pair polarization; `(11)` continuous-kernel negative-index exhaustion by bounded apertures; `(12)` base-point vanishing of the screw series; `(17)` monotone cofinal supremum of the Hardy denominator dimension |
| `ccm-causal-pick-affine-conjugacy-law` | affine conjugacy normal form of the coupled signed-Möbius causal transform |
| `ccm-characteristic-crossing-interior-mode-reduction-law` | interior-mode reduction under the invertible change of variable |
| `ccm-characteristic-evans-boundary-infinite-rank-law` | infinite rank of the characteristic Evans boundary map |
| `ccm-completed-quotient-weighted-schur-seam-law` | positive weighted-contraction normal form of the completed causal quotient |
| `ccm-constrained-endpoint-euler-response-constant` | Fuchs asymptotic `(9)`, constrained-prolate limit `(12)`, and the two branch inputs consumed by `(4)`–`(5)` |
| `ccm-countable-log-chirp-renormalization-law` | the exact constrained radial sum renormalization |
| `ccm-critical-mellin-defect-abscissa-rh-law` | exponential-type ⇒ abscissa statement |
| `ccm-diagonal-fock-polar-prime-mellin-incidence-law` | diagonal Fock polar–prime Mellin incidence |
| `ccm-euler-gamma-radon-nikodym-frame-law` | the Radon–Nikodym frame identity |
| `ccm-euler-observability-relative-index-allocation-law` | relative index allocation in a source-defined finite realization |
| `ccm-euler-pick-logderivative-transfer-boundary-law` | positivity of the logarithmic-derivative Pick transfer for even real-rooted factors |
| `ccm-exact-high-radial-first-row-bv-bound` | high-radial first-row bounded-variation bound |
| `ccm-exact-radial-nonstationary-sector-bound` | off-diagonal radial Gram nonstationary sector bound |
| `ccm-exterior-inverse-symbol-graph-norm-law` | exterior inverse-symbol graph-norm law |
| `ccm-gamma-damped-cauchy-frame-trace-law` | Gamma-damped Cauchy frame trace law |
| `ccm-growing-aperture-mellin-determinant-transfer` | Mellin-evaluation norm determines the determinant transfer on the growing aperture |
| `ccm-hankel-boundary-relative-trace-four-unit-law` | the relative-trace four-unit law replacing full trace class |
| `ccm-infinitesimal-half-unit-cauchy-seam-law` | infinitesimal half-unit Cauchy seam law |
| `ccm-infinitesimal-real-euler-ray-logderivative-index-law` | infinitesimal real Euler-ray log-derivative index law |
| `ccm-leading-endpoint-archimedean-log-law` | archimedean Weil form of the normalized leading lower-endpoint profile |
| `ccm-limiting-radial-first-row-weber-bound` | first row of the limiting radial Bessel Gram matrix |
| `ccm-log-symbol-dirichlet-exterior-reconstruction-law` | exterior reconstruction from the logarithmic symbol |
| `ccm-logderivative-closed-two-channel-graph-law` | the closed two-channel graph of the completed logarithmic source |
| `ccm-poisson-jensen-outer-defect-rh-law` | Poisson–Jensen outer defect law |
| `ccm-polar-euler-frame-minus-level-law` | `(2)`–`(16)` of the polar Euler frame minus-level law |
| `ccm-prime-log-crowding-separating-margin-law` | prime-log crowding separating margin |
| `ccm-prolate-endpoint-jet-resummation-law` | endpoint jet resummation |
| `ccm-radial-prime-first-row-reduction` | radial prime first-row reduction |
| `ccm-radial-prolate-global-defect-measure` | `(16)`, `(20)` from the imported `(13)` |
| `ccm-radial-prolate-two-scale-boundary-carrier` | two-scale boundary carrier |
| `ccm-rational-residual-finite-evans-matrix-law` | finite Evans matrix law for rational residuals |
| `ccm-real-euler-ray-loewner-index-law` | real Euler-ray Loewner index law |
| `ccm-real-spectral-loggraph-transverse-vanishing-law` | transverse vanishing on the real spectral log-graph |
| `ccm-rectangular-critical-mellin-tent-floor-law` | tent-floor law beyond the already-formalized divisor-side equivalence |
| `ccm-rectangular-subpower-lower-floor-rh-law` | remaining half beyond `CCMRectangularSubpowerLowerGate` |
| `ccm-relative-logderivative-coordinate-negative-index-law` | relative log-derivative coordinate negative-index law |
| `ccm-restricted-weil-square-evans-determinant-law` | restricted Weil square Evans determinant law |
| `ccm-safe-kernel-diagonal-fock-lift-rh-law` | safe-kernel diagonal Fock lift |
| `ccm-screw-null-global-log-regularity-law` | global log regularity of screw null vectors |
| `ccm-sonin-log-position-edge-trace-correction-law` | distributional edge identity `(3)` in a tempered-distribution pairing; Sobolev step completing `(14)` |
| `ccm-sonin-three-grade-relative-carrier-law` | `(11)` and the bundling of the three grades |
| `ccm-source-normalized-nonschatten-birman-schwinger-line-law` | source-normalized non-Schatten Birman–Schwinger line law |
| `ccm-spectral-parameter-evans-completion-carrier-law` | spectral-parameter Evans completion carrier law |
| `ccm-unit-riesz-markov-virial-landau-law` | global convolution, zeta Laplace transform of the Markov density, pole retention, Landau step |
| `ccm-unit-riesz-mobius-wavelet-reduction` | the wavelet reduction beyond the already-formalized cell algebra |
| `ccm-universal-boundary-laplace-frame-saturation-law` | universal boundary Laplace frame saturation |
| `ccm-weierstrass-stabilized-square-evans-line-law` | Weierstrass-stabilized square Evans line law |


## Reusable infrastructure added while closing these cards

- `HTGeometry/RealQuadraticMargin.lean` — uniform margin of a negative definite real quadratic form,
  and stability of negative definiteness under a small entrywise perturbation.
- `HTGeometry/ComplexGramPlucker.lean` — complex Cauchy–Binet: the Hermitian Gram determinant is the
  squared Pluecker norm; kernel detection.
- `HTGeometry/SchurComplementKernel.lean` — Schur-complement kernel isomorphism and its determinant
  form.
- `RHTower/CCMShiftCovariantPoleDivisorCapacity.lean` — divisor/pole profiles, their Laplace
  transforms, and the real-axis limit of the shift-covariant symbol.
- `RHTower/CCMTransverseIndexTraceSlopeCoercivity.lean` — the exact Cauchy energy of a divisor
  packet and the four-unit coercivity.
- `HTGeometry/SeparatingGramLocus.lean` — Gram criterion for separation, openness and density of the
  separating locus, the projection criterion, and preservation under approximation.
- `RHTower/CCMGaussPairedQuantizedDifferential.lean` — crossed-homomorphism law of the logarithmic
  quantized differential and its cyclic-coinvariant descent.
- `RHTower/CCMPrimeSourceGroundIncidence.lean` — concavity and Lipschitz continuity of the
  coefficient-pointed floor, and the eigenvector/readout response.
- `RHTower/CCMHankelGapTraceSlope.lean` — the gap profile, its difference-quotient sandwich, the
  initial-slope identity, and the exact first-moment Laplace integral
  `∫_u^∞ (t−u)e^{-bt} = e^{-bu}/b²`.

## Working note

The corpus is very large.  Before building anything, grep `formal/LEAN_API.md` for the *concept*, not
only for the card's own wording: the vertical digamma coercivity needed by the prime-free aperture
card was already in `RHTower/DigammaVerticalLogGrowth.lean` under a name none of the card's keywords
would surface.

- `ccm-hankel-boundary-relative-trace-four-unit-law` → stage 3.
  Module `RHTower/CCMBoundaryRelativeTrace` (19 theorems). Kernel-level Tonelli proof of the exact
  `min(t,u)` boundary-block kernel `(5a)`–`(6)`, the corner/commutator splitting `(7)`, `(8a)`–`(8d)`,
  the gap-increment identity `(11)`, the exact pole trace `4(1−e^{−u})` `(13)`–`(14)`, and the
  RH-equivalent nonexpansive density criterion `(16)`–`(17)`.
  Also exported `leakDensity_polePacketProfile` from `RHTower/CCMHankelGapTraceSlope`.
  Lesson: a card that says "no Lean file is added" because the *operator* layer is missing is often
  still fully formalizable at the *kernel* layer, which is where its proof actually runs.

- `ccm-constrained-endpoint-euler-response-constant` → stage 3.
  Promotion audit only: 39 pre-existing modules, 305 theorems, all axiom-clean and umbrella-wired;
  26/28 Lean gates ticked, the 2 open ones being the card's own declared classical imports (Fuchs's
  lower leakage rate, Slepian's prolate-to-Hermite limits).
  Lesson: several stage-2 cards already carry huge Lean-status sections. Audit before building.

- `ccm-exact-radial-nonstationary-sector-bound` → stage 3.
  New module `RHTower/RadialSymbolTwoBranchInstance` (15 theorems) closes the card's last Lean gate:
  the dilated Liouville amplitude's half-power symbol bounds, a composition lemma whose amplitude
  bound is needed only along the phase, and the instantiated entry estimate
  `abs_integral_radial_entry_le` for genuine solutions of the exterior normal form.
