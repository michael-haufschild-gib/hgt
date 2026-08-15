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

- `ccm-radial-prolate-global-defect-measure` → stage 3.
  New module `RHTower/CCMRadialGlobalDefectMass` (9 theorems): equations (15), (16), (18), (20) —
  the exact `y = λx` change of variables in the leakage norm, the universal masses `1/2` and
  `1/(4π)`, and the escape from the outer coordinate via the corpus's Scheffé `L¹` transfer plus the
  exact arcsine band mass.

- `ccm-radial-prolate-two-scale-boundary-carrier` → stage 3.
  New module `RHTower/CCMRadialTwoScaleCarrier` (11 theorems): the exact two-mode exterior leakage
  (3), the scale-uniform exterior mass `α δ/(2|q(λ)|²)` covering (9) and (16), the outer/inner mass
  limits (10)/(16), and the endpoint-slope identities (11)–(15) — the scale separation is algebra.

- `ccm-unit-riesz-markov-virial-landau-law` — IN PROGRESS (still stage 2).
  New module `RHTower/CCMUnitRieszMarkovTransform` (26 theorems, axiom-clean): equations (6), (7),
  (14), (15)-(16), (17).  The atom-series form of the profile, the term-by-term Laplace transform,
  the exact zeta closed form, `D(0)=1`, the derivative of the causal transform, the complete
  algebraic simplification, and the residue at an off-critical zero.
  Remaining: (5) `w -> 1`, (11) the causal-convolution factorization, (18)-(22) the Landau
  connector (the corpus already owns `RHTower.landau_complexMGF_integrable_transfer`).

### Work plan for the two unit-Riesz cards (as of 2026-08-15)

`ccm-unit-riesz-markov-virial-landau-law` (stage 2):
- DONE: `RHTower/CCMUnitRieszMarkovTransform` — (6), (7), (14), (15)-(16), (17).
- DONE: `RHTower/CCMUnitRieszProfileLimit` — (5): `3 A_m <= 2(m+1)sqrt(m+1)`, `w <= 1`,
  `1 - 9 e^{-v/2} <= w`, `w -> 1`.
- TODO (11): causal convolution factorization.  Plan: extend causal functions by zero and reuse
  mathlib's `MeasureTheory.convolution` + `convolution_assoc`; then
  `I(T) = conv h w T - conv (id*h) d T = conv d V_h T`.
- TODO (18)-(22): the Landau connector.  The corpus already owns
  `RHTower.landau_complexMGF_integrable_transfer` (continuous Landau transfer) and the
  `CCMFirstClockLandau*` family showing how to set it up.

`ccm-unit-riesz-mobius-wavelet-reduction` (stage 2):
- Already formal: (1), (2), (9), (13) in `RHTower/CCMCriticalMellinRieszMobiusRenewal`.
- TODO (4)-(6): the layer-cake representation `g(t) = int_0^1 floor(tv) dv/(2 sqrt v)`,
  `eta(t) = int_0^1 {tv} dv/(2 sqrt v)`, hence `0 <= eta <= min(1, t/3)` and `1 - W(t) <= 3/t`.
  This also sharpens `CCMUnitRieszProfileLimit`'s envelope from `9 e^{-v/2}` to `3 e^{-v}`.
- TODO (7), (10), (11), (15), (18), (20)-(23), (25).

- `ccm-unit-riesz-mobius-wavelet-reduction` — DONE (stage 3, 2026-08-16).  New module
  `RHTower/CCMUnitRieszWaveletFrontier` (8 theorems, axiom-clean) closes (7), (10), (15), (18),
  (20)-(23) and (25).  Earlier note:
  New module `RHTower/CCMUnitRieszQuadratureDefect` (19 theorems, axiom-clean): equations (4), (5),
  (6), and the sharp cutoff bound `1 - W(exp v) <= 3 exp(-v)`.
  Remaining: (7), (10), (15), (18), (20)-(23), (25).

- `ccm-infinitesimal-half-unit-cauchy-seam-law` → stage 3.
  New module `RHTower/CCMHalfUnitCauchySeam` (8 theorems): the termwise proof of (2), the Schur
  factorization (5), the exact two-point minor (6) with its sign, non-positive-semidefiniteness of
  the seam matrix, and the diagonal Fock covariance with its Cauchy Gram factor.
  Reused `RHTower.re_inv_pos_of_re_pos` rather than redefining it.

- `ccm-safe-kernel-diagonal-fock-lift-rh-law` → stage 3.
  New module `RHTower/CCMDiagonalFockLift` (10 theorems): the exponential Gram realization of the
  Cauchy kernel (so the diagonal tensor feature is constructed, not posited), the Schur-product
  factorization D = A o C, J_RH = A - D, the defect-form identity (10)-(12), and contractivity
  <=> RH-form nonnegativity.
  Note: this mathlib's `Matrix.PosSemidef` quantifies over `n ->0 R` (Finsupp), not `n -> R`.

- `ccm-infinitesimal-real-euler-ray-logderivative-index-law` → stage 3.
  New module `RHTower/CCMEulerRayLogDerivativeIndex` (13 theorems): the packet algebra (7)-(8),
  positivity of critical-line packets (9), the exact negative minor of off-line packets (10), the
  quartet polarization, the diagonal identity (17), and the infinitesimal derivation (11)-(13).

- `ccm-real-euler-ray-loewner-index-law` → stage 3.
  New module `RHTower/CCMEulerRayLoewner` (9 theorems): the ray restriction (13) and (9)->(2), the
  two-value determinant obstruction `-(r1-r2)^2` separating scalar from kernel positivity, and
  positivity of every Euler factor of (15)-(16).

- `ccm-causal-pick-affine-conjugacy-law` → stage 3.
  New module `RHTower/CCMCausalPickAffineConjugacy` (9 theorems): the affine embedding (9), the
  quotient identification (11), the Cauchy-denominator collapse (12), the pulled-back Pick kernel
  (13), the explicit completed factorization (7), the scalar conjugacy (5), and the critical
  degeneration (20).  Renamed `shiftedTheta` to `shiftedXiQuotient` to avoid clashing with
  `RHTower.shiftedTheta` in `DeningerWeightOnePolarization`.

- `ccm-euler-pick-logderivative-transfer-boundary-law` → stage 3.
  New module `RHTower/CCMEulerPickTransferBoundary` (9 theorems): the paired-zero kernel identity
  (6), closure of the PSD cone under entrywise limits (the section-2 transfer step), the aperture
  defect (14), the periodic background (14a)-(14c) with its finite-aperture indefiniteness, and the
  relative Herglotz criterion (24).
  Note: `Matrix.PosSemidef` over ℂ needs `open scoped ComplexOrder`.

- `ccm-relative-logderivative-coordinate-negative-index-law` → stage 3.
  New module `RHTower/CCMRelativeLogDerivCoordinateIndex` (6 theorems): the Cauchy-feature Pick
  identity (9), the signed decomposition (10), the residue extraction and the resulting linear
  independence of Cauchy features (section 3), and the active-coordinate floor (23).

- `ccm-completed-quotient-weighted-schur-seam-law` → stage 3.
  New module `RHTower/CCMWeightedSchurSeam` (9 theorems): the strict contraction (2)/(7) via
  `d/dt |X|^2 = 2|X|^2 Re(X'/X)`, the exact factorwise comparison (10d) and its consequence, the
  invariant half-unit (25a), the rotation (12), the Schur substitution (15)-(16), and the Blaschke
  zero (30).  Reused `HTGeometry.hasDerivAt_normSq_comp` instead of redefining it.

- `ccm-logderivative-closed-two-channel-graph-law` → stage 3.
  New module `RHTower/CCMTwoChannelGraph` (5 theorems): abstract paired-graph closedness for
  complementary bounded idempotents, the rank-one residue split (12)-(13), the inverse-horizontal
  energy (20), and the bilateral atom factorization (17a).
| `ccm-aperture-morse-hardymodel-index-exhaustion-law` | `CCMApertureMorseExhaustion` (14 thms) | screw features (7), positive real packet (8), conjugate-pair polarization (9) as kernel and as Gram form, vanishing base row/column (12), perturbation stability of a negative subspace and the Morse-charge lower bound (5)/(11), congruence transport both ways (14)–(16), supremum squeeze (4), unboundedness (10), uniform horizontal shift (17).  Reuses `CCMApertureMorseCharge` and `HTGeometry.neg_of_perturbed_negDef`. | stage 3 |
| `ccm-characteristic-crossing-interior-mode-reduction-law` | `HTGeometry.ExponentialPolynomialModes` (22) + `HTGeometry.CharacteristicModeDimension` (18) + `RHTower.CCMCharacteristicCrossingModes` (9) = 49 thms | New infrastructure: the block calculus `blockOp L μ = L(derivative+μ)`, independence of distinct-frequency blocks, the classical characteristic-mode theorem (frequencies = roots, degree < multiplicity), and `finrank_solutionSpace : finrank (solutionSpace L) = deg L`.  Card layer: finite real zero set from growth (2), damped factor and `(1+D²)^L b = p` (11), zero-free invertible multiplier (5), the reduction to `p(D)v = 0` (8), the `i τ` frequency dictionary with exact multiplicities (9), and the packet dimension `d_a`. | stage 3 |
| `ccm-characteristic-evans-boundary-infinite-rank-law` | `CCMEvansBoundaryInfiniteRank` (10 thms) | Hankel change of variables (5)→(6) and the identification of the columns with translates; Kronecker/Anselone–Korevaar step: finite-dimensional column space ⟹ exponential polynomial ⟹ finitely many frequencies ⟹ entire extension; the infinite-rank theorem as the contrapositive; the exact digamma pole lattice `± i(2n+1/2)` (4), its infiniteness, and non-rationality. | stage 3 |
| `ccm-rational-residual-finite-evans-matrix-law` | `CCMRationalResidualEvansMatrix` (18 thms) | The residual space as the solution space of `(D-1)^L(D+1)^L` with `dim = 2L = d_a` (5); the exact right/left cross-boundary expansions (11), (12) of the Bessel tail into the `2L` modes; the differentiation stability (10); and the full Gram chain `injective ⟺ PosDef ⟺ det > 0` (7), (15). | stage 3 |
| `ccm-screw-null-global-log-regularity-law` | `CCMScrewNullLogRegularity` (9 thms) | (6)→(7) via the local operator; interior smoothness and local square-integrability (4), (8); the exact dimension `d_a` of `F_a`; the empty-characteristic branch (solution space `⊥`); and the kernel transport plus Gram determinant form of (12). | stage 3 |
| `ccm-leading-endpoint-archimedean-log-law` | `CCMEndpointArchimedeanLog` (7 thms) | Sawtooth energy `π²/12` via Basel (11); the uniform logarithmic rescaling `M(Lη)/log L → 1` (9); the exact constant `(16/(11π))(π²/12)·2 = 8π/33` and the limit composition (12)–(15); and the vanishing of the one-order-lower prime response (17). | stage 3 |
| `ccm-poisson-jensen-outer-defect-rh-law` | `CCMPoissonJensenOuterDefect` (10 thms) | The elementary half-plane Blaschke factor and its exact squared modulus (10); the defect identity `-log|b_b(x)| = ½ log(((x+a)²+γ²)/((x-a)²+γ²))` (11); nonnegativity and strict positivity (12); the finite exact-detection equivalence (13); the dephasing identity for exponential mean type (20)–(21); and the limit subtraction (15)–(18). | stage 3 |
| `ccm-euler-gamma-radon-nikodym-frame-law` | `CCMEulerGammaRadonNikodym` (9 thms) | Exact Gamma diagonal `φ(2k log p) = √2 p^k/√(p^{4k}+1)` (4); the exact Radon–Nikodym correction (3), (5) and its two-sided contraction bounds (6); the exact matching identity (7); the prime-power tail bound `∑_{k≥2} 1/(k p^k) ≤ 1/(p(p-1))` (10); and the critical correction with its lower bound (15) and cofinal unboundedness (16). | stage 3 |
| `ccm-gamma-damped-cauchy-frame-trace-law` | `CCMGammaDampedCauchyFrame` (10 thms) | Rank-one compression `P U P = ⟪ξ,Uξ⟫ P` (1); the canonical half-density and its square (2)–(3); the exact channel norm and the diagonal frame energy with no cross terms (4)–(5), (9); the Gram entry retaining the full group overlap (8); and the exact prime diagonal `√2 p/√(p⁴+1)` (10). | stage 3 |
| `ccm-real-spectral-loggraph-transverse-vanishing-law` | `CCMRealSpectralLogGraph` (4 thms) | Nonvanishing of the anti-causal rank-one pole coordinate (7); linear independence of Cauchy kernels with distinct non-real poles tested on ℝ ("distinct pole coordinates cannot cancel"); and the two limit steps turning graph-core convergence from zero finite stages into `D_Ξ = 0` (8)–(9). | stage 3 |
| `ccm-rectangular-subpower-lower-floor-rh-law` | `CCMRectangularSubpowerLowerGate` + `CCMRectangularPowerLowerZeroFree` + `CCMRectangularObservablePowerLowerZeroFree` (18 thms audited) | Already formalized when the card was written; verified: all three modules exist, are umbrella-wired, and every declaration is axiom-clean.  Covers the bounded-remainder absorption, the power-shifted Landau coefficient and its continuation, the translated pole locations, the fixed-exponent zero-free conclusion (3)/(13), and the subpower RH gates (4)–(6). | stage 3 |
| `ccm-countable-log-chirp-renormalization-law` | `CCMCountableLogChirp` (4 thms) | `log t ≤ 2√t`; the countable almost-orthogonality weight `∑ (1+log(1+k))/(1+k)²` summable (8); the scalar-renormalized form (13)–(14) whose consumer is the corpus `RayleighScalarShift`; and the summability of a `C/k²` radial diagonal bound (10)–(11). | stage 3 |
| `ccm-critical-mellin-defect-abscissa-rh-law` | `CCMCriticalMellinAbscissa` (5 thms) | The exact integral `∫_1^X (log t)²/t = (log X)³/3`; the endpoint `O(h²)` and integral `O(h³)` von Koch contributions of (9); polynomial growth ⟹ subexponential (10)→(ii); and subexponential ⟹ vanishing exponential abscissa (ii)→(iii). | stage 3 |
| `ccm-limiting-radial-first-row-weber-bound` | `CCMLimitingRadialWeber` (8 thms) | The bulk difference phase, its derivative, its unique critical point `r = 1/k` and the exact curvature `−(k²−1)/k` (7)–(8); the endpoint phase derivative `k²/(2√…)` and its nonvanishing (10); and the logarithmically weighted first-row bound (4), reusing the corpus `summable_log_div_sq`. | stage 3 |
| `ccm-spectral-parameter-evans-completion-carrier-law` | `CCMSpectralParameterEvans` (7 thms) | The shifted symbol (5) and its null-form equivalence; the reduction of the generalized eigenvalue problem to the shifted multiplier equation (2)→(7); and the conditional finite Morse formula (9)→(10) with the injectivity criterion (11).  The card's missing isomorphism stays an explicit hypothesis; the prime–Gamma wall is the corpus `not_summable_primeLogHerglotzTransportMassOrder_of_pos`. | stage 3 |
| `ccm-exterior-inverse-symbol-graph-norm-law` | `CCMExteriorInverseSymbol` (6 thms) | Fourier-side positivity and injectivity of the inverse-symbol form (6a); the dominated-convergence vanishing of the modulated wave-packet energies (8)–(9); the refutation of every lower bound (6), (10); and the unique-solvability ⟺ range-membership reformulation (12a)–(12b). | stage 3 |
| `ccm-universal-boundary-laplace-frame-saturation-law` | `CCMBoundaryLaplaceSaturation` (5 thms) | The exact two-edge polar expansion and its uniform remainder bound (5); the exponential-character factorization of the autocorrelation and the Fubini identity `∫ e^{-r/2}(f⋆f) = |F_-|²` (9); and the frame-saturation limit (13)–(16). | stage 3 |
| `ccm-weierstrass-stabilized-square-evans-line-law` | `CCMWeierstrassStabilizedEvans` (6 thms) | Conjugate pairing of the stabilized nonreal roots (claim 2 of (2)); positivity of a monic real polynomial with no real root, hence of the stabilized quotient (3); and the empty-zero-divisor restatement (12). | stage 3 |
| `ccm-diagonal-fock-polar-prime-mellin-incidence-law` | `CCMDiagonalFockColligation` (7 thms) | The two ray-Laplace channels (9), (11) via the corpus `integral_exp_ray`; the von Mangoldt feature Gram (10); the incidence rearrangement (6)/(8); the passage of the colligation to finite quadratic forms (18); and the four-channel passivity criterion (19). | stage 3 |
| `ccm-polar-euler-frame-minus-level-law` | `CCMPolarEulerFrameLevel` (9 thms) | Termwise digamma resolvent squares and their nonnegativity (2)–(3); the prime translation-difference square (7) via `|1-e^{iθ}|² = 2-2cos θ`; the even/odd polar splitting (10); the collapse of the exact identity to frame-minus-level on even vectors (15) and to (16) on odd ones; and the lower-frame restatement (17). | stage 3 |
| `ccm-prolate-endpoint-jet-resummation-law` | `CCMProlateEndpointJet` (5 thms) | The degenerate endpoint identity `2ψ'(1) = (κ−c²)ψ(1)` (2); the scaled endpoint derivative and logarithmic derivative (4); the exact critical scale `−2π²λ³ + κ/(2λ)` (6); and the polynomial lower bound `πλ² − O(1)` for the jet ratio (11)–(12). | stage 3 |
| `ccm-log-symbol-dirichlet-exterior-reconstruction-law` | `CCMLogSymbolDirichlet` (4 thms) | The positive infimum of a growing positive symbol (2); Carleman domination of the logarithmic cross kernel (14)–(15); the coercive inverse bound `‖u_f‖ ≤ γ⁻¹‖f‖` (17)–(18); and the observability estimate giving `F_a^adm = F_a` (8)–(9). | stage 3 |
| `ccm-source-normalized-nonschatten-birman-schwinger-line-law` | `CCMNonSchattenBirmanSchwinger` (5 thms) | The Birman–Schwinger factorization (4) and its identity normalization (5); the sufficient direction of the sharp norm criterion (11); the telescoping `1/√n ≤ 2(√n−√(n−1))` behind the explicit chamber (16)–(17); and the `1/n`-domination comparison turning the singular-value law (15) into the non-Schatten conclusion (8). | stage 3 |
| `ccm-rectangular-critical-mellin-tent-floor-law` | `CCMRectangularTentFloor` (10 thms) | The moving tent with its support, endpoints and peak (2); the exact interval-overlap length and the two-edge autocorrelation split (9); the adjacent equal-block form of the readout (6)–(7); the Haar-shell orthogonality (18); and the four-fold quadratic bound giving the uniform Gamma estimate (12), (14). | stage 3 |
| `ccm-restricted-weil-square-evans-determinant-law` | `CCMRestrictedWeilSquareEvans` (4 thms) | Equal dimension of source and target, hence squareness of the Evans map (3)–(4), combining `finrank_solutionSpace` and `finrank_residualSpace`; the determinant/kernel criterion and its transfer through the kernel isomorphism (8)–(9); and the parity grading (22). | stage 3 |
| `ccm-unit-riesz-markov-virial-landau-law` | `CCMUnitRieszVirialConnector` (7 thms) + the four earlier unit-Riesz modules | Closes the card: the wavelet kernel as a derivative (9), the convolution split of (11), the exact polar part of the virial (13), and the Landau bookkeeping (18)–(21).  With `CCMUnitRieszProfileLimit` (4)–(5) and `CCMUnitRieszMarkovTransform` (6), (7), (14)–(17), every non-parent equation is certified. | stage 3 |
| `ccm-sonin-three-grade-relative-carrier-law` | existing Sonin modules + new `CCMSoninCompressedCommutator` (6 thms) | All cited endpoints verified present; the one algebraic gate without a Lean carrier — the projection-compressed degree-one commutator identity `Q[X,Z]Q = [QXQ,QZQ] + L_X^*L_Z + L_Z^*L_X` (9b)–(9d) — is now proved in an arbitrary `*`-ring. | stage 3 |
| `ccm-sonin-log-position-edge-trace-correction-law` | `CCMSoninEdgeCommutatorAlgebra` (4 thms) | The full resolvent-dressing chain: formal-complement commutator (10), alternating-block Leibniz (6e), inverse-commutator identity (6d), and the exact projection commutator (6c) showing every term factors through the single edge commutator `[X,B]`.  All in an arbitrary ring, axioms `[propext]` only. | stage 3 |
| `ccm-euler-observability-relative-index-allocation-law` | `CCMEulerObservabilityAllocation` (5 thms) | Section 3 in full: injectivity of the relative differential on the invisible directions (8), the deficit bound (9), the rank–nullity allocation (10)/(15d), the cofinal index growth (17), and the jet rank bound (4). | stage 3 |
| `ccm-radial-prime-first-row-reduction` | `CCMRadialPrimeFirstRow` (20 thms) + reused `RadialGramOffDiagonalDecay`, `ConstrainedProlateExteriorWeil`, `CCMLimitingRadialWeber` | The exact three-way split of the raw prime charge (10)–(11); the finite-aperture weight `a_λ(k)` with `0 ≤ a_λ(k) ≤ log k`, the domination behind the (12)–(13) transfer; the limiting phase derivative (6); and the full coalescing-scale geometry — existence **and uniqueness** of the stationary point `x_k = √(1+1/k²)` (15), the endpoint values `ρ(x_k)=1/k`, `ρ(kx_k)=k` and curvature `−(k³−1/k)` (20), and the rate `k²(x_k−1) → 1/2` (16).  The divisor identity (3) and the weighted sector convergence (8)–(9) were already in the tree and are reused, not rebuilt. | stage 3 |
