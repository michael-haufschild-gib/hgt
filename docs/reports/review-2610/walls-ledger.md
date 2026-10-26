# Walls ledger

Status: 2026-10-26, corpus `19b8caad1` with the working tree of that day. Every obstacle in the corpus belongs to one of three core families:

- **Wall 1 — critical arithmetic sign.** Estimates, signs and oscillatory payment at the critical endpoint, at the gauge point `0`.
- **Wall 3 — transfer.** Readings, norms, completions, limits, shared budgets, localization and selection.
- **Wall 14 — realization and forcing.** Faithful arithmetic objects, correspondences and their local types, invariants, counts, polarization, and the forcing of the actual source into its blind carrier.

**Organizing principle.** At an off-line reflection pair `{ρ, 1 − ρ̄}` the local form has signature `(1, 1)`; every multiplicative correspondence acts on it by a boost, the successor unipotently, the functional equation and its conjugates `σ_γ` by the reflection swap. The test space of `ζ` carries two forms: Weil's form `W`, Hecke equivariant, whose positivity is RH; and the collided form `D = Σ m_ρ|f̂(ρ)|²`, positive, whose Hecke equivariance is RH [S]; `Re W = D − Δ`. Wall 1 measures the hyperbolic part as a rate or a sign; Wall 3 governs how positivity transfers between readings, localizations, limits and budgets; Wall 14 asks what computed structure makes one form both positive and equivariant. Ten exhaustion laws bound every mechanism tested:

- **Gauge.** Multiplicative data determine a source up to its gauge orbit; finite multiplicative lattice forms are unitarily equivalent at the Euler and Liouville vacua [S]; the actual source is one point (1.18, 3.1).
- **Hyperbolicity.** Positivity invariant under a correspondence that is a boost at an off-line pair forces isotropy there (14.10, 14.17).
- **Resonance.** Inside correspondence-closed carriers a symmetric dilation is elliptic at an off-line point only at scales `a` with `γ log a ∈ πℤ`; the only reflection-compatible affine localizer is `σ_γ`, whose even sector cannot force (3.18, 14.17).
- **Conductor horizon.** Positivity of `ζ`'s form on twisted (elliptic-sector) tests is a theorem only for apertures `e^a ≲ log γ/4`, and there it holds for every prime weight of the same size (3.19).
- **Localization.** Positivity constrains a fibre only where the carrier localizes; non-localizing positivity holds for every prime weight (3.18).
- **Dominated twins.** On nonnegative tests the Weil form is antitone in the source (1.4, 1.18).
- **Linear loss.** Moments, family averages, products and relative powers lose at least linearly; twists are rate neutral (1.15, 1.17).
- **Pole order and one variable.** Pole order pays inserted zeros; a complex quartet contracts only against a real anchor (`κ ≥ 3` if planted); couplings anchor and never count; the global conjugate collision has no analytic carrier (1.16, 14.13, 14.19, 14.20).
- **Collision.** Kernel counts, coupled counts, escape Cauchy forms and `D` pair `ρ` with `ρ̄`; their positivity is automatic and sees no sign (3.1, 3.15, 14.21).
- **Counting.** A section count with RR and Bézout, an effectivity function, a naive height, a one-sided count, a fixed tensor loss and horizon torsion are each RH (1.1, 1.17, 14.4, 14.18).

Over `𝔽_q` one structure escapes all ten: a polarization of `C × C`, from Riemann–Roch and an ample class, makes the Rosati trace (the transpose of correspondences) positive and Frobenius-equivariant at once; `Λ²H¹` collides conjugate eigenvalues at no cost. Over `ℤ` identities, the theorem of the square and the budget are free, the receiver side is complete, a positive form exists, and nothing computes a form that is both positive and equivariant (14.18, 14.21).

Companions: [complete report](hard-obstacles.md), [summary](hard-obstacles-summary.md), [route unification](route-unification-ledger.md). Evidence: corpus search and Lean statement reading, logged in `logs/review-2610/working-log-v3.md`. No compilation. A countermodel excludes the mechanism it was built against, not every route that touches its wall.

**Markers.** `[S]`: working source not recorded as integrated. `[R]`: assessment or model calculation of the review, not a theorem. Q1–Q3 are the summary's next questions: Q1 the elliptic forcing gap (B3.32), Q2 the collided form (B3.33), Q3 the non-archimedean gauge charge (B3.26).

**Status column.**

- *Open*: no answer; the boundary listed is the present one.
- *Sharpened*: open, with an exact boundary or survivor that fixes what must be proved.
- *Resolved*: the face's question is answered; the answer is recorded and the face carries no open task.
- *New*: a face isolated in this version.

## 0. Faces that changed in this version

| Face | Change | Content |
|---|---|---|
| 1.1 | Sharpened | One-sided count `ψ(x) − x ≤ C√x log²x` ⇔ RH; horizon torsion `ψ(N) = N + O(√N log²N)` ⇔ RH; Nair's integrality floor. |
| 1.3 | Sharpened | The Weil sign is the positivity of the equivariant form; `W = D` ⇔ RH. |
| 1.16 | Sharpened | `ζ`'s own zeros are paid by the depth-uniform capacity `Δ`: `Re W = D − Δ`. |
| 1.17 | Sharpened | Twists are rate neutral; fixed tensor loss is one of five equivalent currencies [S]. |
| 1.18 | Sharpened | Finite lattice blindness and successor holonomy [S]; first gauge charge a height twist; edge reduction; second charge not archimedean; Catalan repulsion [S]. |
| 3.1 | Sharpened | Collided readings pair conjugates. |
| 3.4 | Sharpened | The AIP diagonal reserve cancels on the polar-neutral hyperplane [S]; log-cell remainder bound [S]. |
| 3.15 | Sharpened | Escape alternative; dominant-split criterion; escape forms are collided Cauchy forms; Abel escape states read the boundary poles of the symbol [S]. |
| 3.18 | Sharpened | Elliptic localization inside correspondence-closed carriers is resonance. |
| 3.19 | New | The elliptic forcing gap. |
| 14.4 | Resolved | A section count with RR and Bézout is the Hodge index; the effectivity calculus. |
| 14.6 | Sharpened | Selectivity of counts: lattice counts collapse; theta polarization is fibre-independent. |
| 14.7 | Resolved | The base theta `h⁰` does not extend through the degree. |
| 14.17 | Resolved | Local types classified: resonance law, `σ_γ` unique, dihedral dilemma. |
| 14.18 | Sharpened | Polarization law; five currencies; the missing layer is a computed positive equivariant form. |
| 14.19 | Resolved further | Minimum anchored cost `κ ≥ 3`; planting `Δκ ≥ 2`; Fejér coupling cost. |
| 14.20 | Resolved | Fejér barrier, even real orders, non-analytic global collision proved; coupled rigidity refuted [S]. |
| 14.21 | New | The collided polarization. |
| 14.22 | New | The central vanishing ceiling of the coupled class. |

## 1. Wall 1 — critical arithmetic sign

With `Δ = sup_ρ |Re ρ − 1/2|`, a receiver bounded at a fixed rate `σ < 1/2` gives `Δ ≤ σ` (quasi-RH); RH is `Δ = 0`.

| Face | Status | Present obstacle | Established boundary / survivor | Missing input |
|---|---|---|---|---|
| **1.0 Quasi-RH first rung** | Sharpened | Graded receivers, multiplicative forcing and admission at fixed damping have no target between Vinogradov–Korobov and a fixed strip. | Fixed-strip equivalences (balanced statistic, centred-prime band, short windows, JAS level one, PBM abscissa, WL rate, RW/ACS floors, Vaughan power improvements, one-sided Lefschetz bounds at one prime, power growth of the damped energy). Escape at `ε` ⇔ zeros right of `1/2 + ε`, up to countably many `ε`. Collars of width `≍ 1/(d log T)`. Unconditional: dlVP, Littlewood, VK. | A fixed strip (B2.1), or an output that is not graded (Q1's non-isolation law). |
| **1.1 Critical signed cancellation** | Sharpened | Lag, Abel, history, series and bilinear bounds must reach rate zero with every counterterm paid. | Endpoint laws; high-zero tail `O(1)`; `Q^{−δ/32}`; `M(x) = Ω±(√x)`. One-sided count: RH ⇔ `ψ(x) − x ≤ C√x log²x` eventually. Horizon torsion: RH ⇔ `ψ(N) = N + O(√N log²N)`. Integrality gives `ψ(2m+1) ≥ m log 4`; univariate integer polynomials stop below PNT [R]. Gauge forms: RH is typicality of the point `0`. | Source cancellation at every positive slack (B1.1). |
| **1.2 Axis orientation** | Open | A nonnegative defect, winding count or faithful spectrum does not force line support. | Ward cap and trace; cubic trace = winding; subharmonic Newton margin. | Vanishing or a forcing all-height sign (B1.6). |
| **1.3 Complete Weil positivity** | Sharpened | Low and mixed sectors unsigned at large aperture; the negative part at a height is `≥ −4(A+1)²e^A N²Φ(γ)`. | Local–global split at one prime; one shift decides RH; windows `3/10`, `181/500`; averaged positivity on `Γ^{99/100}` windows; positivity at almost every zero ordinate for nonnegative tests. `W` is equivariant for every configuration; RH ⇔ `W = D`. | The Lefschetz part (B1.3), or a computed positive equivariant form (14.21). |
| **1.4 Arithmetic cone membership** | Sharpened | Identifying the source is not proving its positivity. | Full-cone source selection; positive-measure rigidity; worst twin on nonnegative tests. | `Λ` in the full Weil cone, i.e. RH. |
| **1.5 Contrast equality** | Open | Jensen, BSY and Li accounting leaves a residual. | BSY off-line sum nonnegative, zero on critical zeros; the defect `Δ` is a capacity of the same kind; Li depth `≤ 1/431`. | An arithmetic upper bound forcing the residual to zero (B1.7). |
| **1.6 Required uniformity** | Open | Fixed rank, order, history or height does not reach the receiver's quantifier. | Orthant signs; fixed-order thresholds; fixed-rank coercivity. | All-rank or order-uniform estimates (B1.5, B3.12). |
| **1.7 Amplification of a receiver** | Resolved | Raising a receiver to a power multiplies its rate. | Exact exponent bookkeeping. | — |
| **1.8 Critical pronic energy** | Sharpened | Horizon-uniform signed energy at cofinally small damping. | Half-damping admission, rank-two Gram; RH ⇔ admission at every damping ⇔ positive gauge mass of every escape state; the centered divisor prefix = sawtooth + long-modulus quadrature. | Signed control of the long-modulus quadrature (B1.2). |
| **1.9 Signed continuation** | Open | Integrated signed loss bounded uniformly in the horizon. | Canonical corrector; integer local exponents below half. | Flux control at closing damping (B1.2). |
| **1.10 Absolute compensation** | Open | A vanishing relative error coexists with unbounded raw energy. | Power-plus-bounded forcing; record-minimum limits. | Absolute energy bound (B1.2). |
| **1.11 Rates and clusters** | Open | Physical ground rate versus zero width. | `groundRate = polarRate`; form-norm rates `= Δ`. | `polarRate = Δ` (B3.1). |
| **1.12 Interior anti-alignment** | Open | The gap `θ(ε,t) < 1` between the proved collars. | High-height and small-damping collars. | Interior decorrelation (B1.1, B2.6). |
| **1.13 Aperture shell flux** | Open | A strictly decreasing ground energy can cross zero. | RH ⇔ cumulative frozen relaxation `≤ μ(3/10)`. | Signed collar estimate on the moving ladder (B3.6). |
| **1.14 Actual divisor heat sign** | Open | Local repair costs do not sign actual Ξ heads. | Large-height head repair; Hermite barrier; `Λ < 1/8`. | Zero-heat sign on the residual region (B1.5, B3.9). |
| **1.15 Depth homogeneity** | Sharpened | Every amplification over `ℤ` tested gains on depth as fast as it pays. | Gauge moments, products, finite family averages: linear loss; equality iff flatness; harmonic twists rate neutral (`twisted_growth_iff`). | `k`-level forms and Følner coupling (W9); a term that does not scale (1.17). |
| **1.16 Payment of ζ's own zeros** | Sharpened | Pole order pays inserted zeros only; budgets pay a hyperbolic pair only on a finite segment. | `Re W = D − Δ`; `Δ` charges every off-line pair `m\|f̂(ρ) − f̂(ρ*)\|²`, uniformly in the depth; escape rank counts dominant zeros. | `Δ ≤ D` from structure; equivalently the equivariance of `D` (B1.11, 14.21). |
| **1.17 Loss law** | Sharpened | A rate needs `b_k = o(k)`. | Fixed tensor loss ⇔ RH; linear loss ⇔ strip; golden loss `k log φ`; fixed tensor loss is one of five equivalent currencies [S]. | A structure whose cost does not scale (B1.9). |
| **1.18 Gauge selection** | Sharpened | The actual source is one point of a gauge orbit; positivity on prime-free windows and nonnegative tests is gauge blind. | Möbius a.e. law, comeager-null exceptions; prime source atypical only by its pole. Finite multiplicative lattice forms blind at real sign gauges [S]; the successor connection reconstructs `ω(2), ω(3)` on `2 → 3 → 4` [S]. First gauge charge = `ζ` at height `π/log 2` plus Γ/pole corrections; twin positive on tests with edge mass `≤ 1/1961`; no height flips `2` and `3`; Catalan repulsion `e^{−\|γ\|}/50` [S]; Ramanujan torsion contrasts kill the pole mode [S]. | The edge problem (W8, W13); a non-archimedean gauge-charged positivity (B3.26, Q3); a charged estimate at `0` (B3.24). |

Key sources: [one-sided count](../../../formal/GaloisForLFunctions/ArithmeticCorrespondencePositivity/TheStepanovCountIsTheSign.lean), [Stepanov over ℤ](../../../formal/GaloisForLFunctions/ArithmeticEffectivityTheory/TheStepanovMethodOverZ.lean), [horizon torsion](../../../formal/GaloisForLFunctions/ArithmeticEffectivityTheory/TheHorizonTorsion.lean), [capacity](../../../formal/GaloisForLFunctions/ArithmeticPolarization/TheOscillatoryCapacity.lean), [Hecke invariance](../../../formal/GaloisForLFunctions/ArithmeticPolarization/HeckeInvarianceOfTheCollidedPolarizationIsRH.lean), [rate neutrality](../../../formal/GaloisForLFunctions/ArithmeticPolarization/TwistsAreRateNeutral.lean), [first charge](../../../formal/GaloisForLFunctions/ArithmeticPolarization/TheFirstGaugeChargeIsATwist.lean), [edge](../../../formal/GaloisForLFunctions/ArithmeticCorrespondencePositivity/TheFirstGaugeChargedWindowOffTheEdge.lean), [gauge torus](../../../formal/GaloisForLFunctions/BiarithmeticGaugeGeometry/PrimeGaugeTorusAndVacuumIntertwiners.lean), [Catalan repulsion](../../../formal/GaloisForLFunctions/BiarithmeticGaugeGeometry/QuantitativeCatalanDiophantineRepulsion.lean), [Ramanujan torsion](../../../formal/GaloisForLFunctions/BiarithmeticGaugeGeometry/RamanujanTorsionStabilizersAndMonomialCollapse.lean), [escape alternative](../../../formal/GaloisForLFunctions/ArithmeticCorrespondencePositivity/TheEscapeAlternative.lean), [endpoint](../../../formal/GaloisForLFunctions/BiScaleUncertainty/WeilLagCriticalDeficitEndpointAndLimitLaw.lean), [balanced statistic](../../../formal/GaloisForLFunctions/BezoutValuationIncidence/TheBalancedStatisticIsTheQuasiRiemannHypothesis.lean), [Vaughan power bounds](../../../formal/GaloisForLFunctions/BezoutValuationIncidence/UniformVaughanPowerBoundsAreFixedStrips.lean), [energy translation](../../../formal/GaloisForLFunctions/ArithmeticCorrelationGeometry/SubpowerReceiverEnergyTranslatesZeros.lean), [long moduli](../../../formal/GaloisForLFunctions/ArithmeticContinuationAndCriticalEnergy/LongModulusExactDecomposition.lean), [short cycles](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/TheStripLivesOnShortCycles.lean), [one prime](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/OneSidedLefschetzBoundsAtOnePrimeAreTheStrip.lean), [one shift](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/OnePrimeSeesTheDefectOfEveryConfiguration.lean), [short-window averages](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/ShortWindowAveragedWeilPositivity.lean), [zero ordinates](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/AlmostEveryZeroOrdinateIsWeilPositive.lean), [worst twin](../../../formal/GaloisForLFunctions/ArithmeticCorrespondencePositivity/OnNonnegativeTestsZetaIsTheWorstTwin.lean), [first prime window](../../../formal/GaloisForLFunctions/SquareRootThreshold/WindowCertificatesAndThePrimeWeight.lean), [family loss](../../../formal/GaloisForLFunctions/ArithmeticCorrespondencePositivity/MomentAmplificationOfAnyFamilyLosesLinearly.lean), [tensor loss](../../../formal/GaloisForLFunctions/ArithmeticCorrespondencePositivity/TheBaseIsAFixedLoss.lean), [finite segment](../../../formal/GaloisForLFunctions/ArithmeticCorrespondencePositivity/ABudgetPaysAHyperbolicPairOnlyOnAFiniteSegment.lean), [gauge trichotomy](../../../formal/GaloisForLFunctions/ArithmeticCorrelationGeometry/AlmostEveryGaugePointCancelsToTheSquareRoot.lean), [prime pole](../../../formal/GaloisForLFunctions/ArithmeticCorrelationGeometry/ThePrimeSourceIsTypicalExceptForItsPole.lean), [index–pole conservation](../../../formal/GaloisForLFunctions/RHTower/WeilIndexConservation.lean).

**Aperture ceiling.** `μ(A) ≤ K exp(11A/2 − πe^{2(A−2)})`. No positive exponential floor exists.

## 2. Wall 3 — transfer: readings, norms, limits, budgets, localization, selection

Closing a face here enables a route but supplies no Wall 1 sign. Three faces reduce to other walls: closedness of the blind ideal is zero-location data (3.3); selection below the zero spacing is RH-strength (3.14); escape exclusion is positive gauge mass (3.15).

| Face | Status | Present limitation | Established boundary / survivor | Missing transfer |
|---|---|---|---|---|
| **3.1 Readings** | Sharpened | Magnitudes, orientation-blind samples, moments, multiplicative statistics and kernel counts erase the signed data. | Recovery classifications; multiplicative observation is the gauge projection. Determinants, coupled counts, escape forms and `D` pair conjugates (collided readings); Rosati traces pair reflections; symmetric-square spectra and exterior counts over `𝔽_q` see quartets. | Orientation-retaining, gauge-charged, reflection-pairing source readings. |
| **3.2 Aperture/height escape** | Open | Finite windows admit mimics. | Cofinal criteria; quantitative visibility. | Containment along the full exhaustion. |
| **3.3 Norms and completions** | Resolved | One norm does not replace another without a theorem. | Origin-`L²` no faithful reading; golden payment domain nonclosed; blind ideal closed naturally, synthesized by jets plus boundary. | — |
| **3.4 Shared signed resources** | Sharpened | Local payments can spend one surplus twice. | Frustration and holonomy law; descent excess `kB`; the Rosati trace form is one budget. The full archimedean–polar crossing form is a rank-one polar square minus a Lévy form; on the polar-neutral hyperplane the linear diagonal reserve cancels, leaving `−Σ n³q_n²/(n⁴−1)` [S]; log-cell shift correlations = divisibility spine + Euclidean remainder, bounded uniformly in the multiplier [S]. | One continuum budget (B1.3, B3.8). |
| **3.5 Endpoint logarithms** | Open | Pole cancellation alone does not pay the endpoint. | Partial-pole-sum law; Dini thresholds. | The logarithmic remainder for a new source. |
| **3.6 Moving horizons and origins** | Open | Generic below-half interchange fails. | Priced shifts; reset-origin limits. | Source-specific moving-tail bounds. |
| **3.7 Damping topology** | Open | Hilbert–Schmidt and inverse estimates fail before boundedness. | Chain bounded at half damping; integer local exponents below half. | Signed sub-half estimates (B3.11). |
| **3.8 Multiplicity and index** | Open | Packet `m²`, Weil `m`, distinct index and reciprocal depth differ. | Meyer: numerical = principal ⇔ simple. | Keep trace data separate from operator data. |
| **3.9 Observation cost** | Sharpened | Recovery at arbitrary phase has no universal horizon. | Closed-cycle recovery on controlled sources. | A source-specific horizon bound. |
| **3.10 Filters and hulls** | Open | Invertible critical-Wiener filters preserve admission classes. | Unit-orbit dictionaries. | Non-unit repair preserving the source. |
| **3.11 Coupled quantifiers** | Open | Weil margin → heat-Hankel couples degree and time. | Exact bridges. | Decoupling (B3.12). |
| **3.12 Residual reconstruction** | Open | Algebraic injectivity gives no bounded inverse. | Kernel `ℝ q_ε`. | Quantitative inverse (B3.3). |
| **3.13 Joint orientation of families** | Open | Individually positive orbits can choose incompatible endpoints. | Spline-orbit index ≤ 1 ⇔ RH. | A compatible family (B3.10). |
| **3.14 Average to selected heights** | Sharpened | Averages control windows, not every zero. | Averaged positivity on `Γ^{99/100}` windows; zero-ordinate positivity for nonnegative tests; witness persistence on length `2(1 − r/Z)/A`; resolution is length. | Selection to every height and signed test (B1.4). Windows `Γ^{1/2+ε}` are W6. |
| **3.15 Escape states of actual limits** | Sharpened | Escape is classified for model configurations, not for `ζ`. | RH ⇔ admission at every damping; escape fills `(0, Θ − 1/2)` up to a countable set; phase kernels for finite, power-row and summable configurations; the dominant-split criterion and zero gauge spectrum of its limits; escape forms are collided Cauchy (Pick) forms, positive automatically; Abel escape states: finite-height part from the poles of the symbol on the abscissa line, rest at infinite height [S]; RH ⇔ positive gauge mass. | Residue summability and infinite-height mass (B3.2); exclusion is B1.2. |
| **3.16 Prime-to-spectral positivity** | Sharpened | Positivity is known on the prime side only. | Kronecker split; the successor sees continuous spectra, never atoms; Weil's extensions are a box over critical zeros; the successor defect is `O((\|s\|+1)^{1−σ+η})` in the strip and sharp on the real axis. | A self-dual identity with its gap on the spectral side. |
| **3.17 Archimedean-line threshold** | Open | The archimedean line computes gauge moments only below `2rX^k ≤ 1`. | Windowed moment = gauge moment + near-incidence. | A gauge-charged estimate beyond the threshold at `0` (B3.24). |
| **3.18 Localization** | Sharpened | Global positivity does not constrain a fibre unless the carrier isolates it. | Lagrange localization (cyclic positivity ⇔ half-blindness); bounded-aperture carriers positive for every prime weight; separating isometries are boosts. Resonance law: within correspondence-closed carriers, elliptic local type only at scales in `exp((π/γ)ℤ)` (≤ one prime); archimedean-closed carriers blind; Hecke + `σ_γ` stability is blindness. | A non-multiplicative localizer; its forcing is 3.19. |
| **3.19 Elliptic localization beyond the conductor horizon** | New | Positivity on twisted tests is a theorem only for `e^a ≲ log γ/4`, and there it is source-blind; no eventual positivity holds for all tests beyond it (Kronecker peaks). | `σ_γ` sectors are twists; the odd sector carries the forcing half: one sign on the twisted detector at `γ₀`, a local count bound and depth dominance force an off-line companion within `R`. Forcing threshold `e^a ≳ (log γ₀)^{1/(2δ)}`, disjoint from the horizon for every `δ < 1/2` [R]. | The odd-sector sign at zero ordinates beyond the horizon, possibly outside a sparse exceptional set (B3.32, Q1). |

Sources: [resonance](../../../formal/GaloisForLFunctions/ArithmeticCorrespondencePositivity/EllipticLocalizationIsResonance.lean), [elliptic localizers](../../../formal/GaloisForLFunctions/ArithmeticPolarization/TheEllipticLocalizers.lean), [twisted sectors](../../../formal/GaloisForLFunctions/ArithmeticPolarization/TwistedSectorsCollideQuartets.lean), [price and horizon](../../../formal/GaloisForLFunctions/ArithmeticPolarization/ThePriceOfEllipticLocalization.lean), [forcing half](../../../formal/GaloisForLFunctions/ArithmeticPolarization/TheForcingHalfOfEllipticLocalization.lean), [single-height laws](../../../formal/GaloisForLFunctions/arithmetic-positivity-theory/SingleHeightPhaseSelectiveApertureAndPowerSaving.lean), [escape criterion](../../../formal/GaloisForLFunctions/ArithmeticCorrespondencePositivity/TheEscapeCompletenessCriterion.lean), [Abel escape](../../../formal/GaloisForLFunctions/ArithmeticCorrespondencePositivity/TheAbelEscapeStateIsTheBoundaryMeasureOfTheSymbol.lean), [summable configurations](../../../formal/GaloisForLFunctions/ArithmeticCorrespondencePositivity/InfiniteDominantConfigurationsAreComplete.lean), [collided escape forms](../../../formal/GaloisForLFunctions/ArithmeticPolarization/EscapeKernelsAreCollidedForms.lean), [successor defect](../../../formal/GaloisForLFunctions/ArithmeticCorrespondencePositivity/TheSuccessorDefectInTheStrip.lean), [polar-neutral collapse](../../../formal/GaloisForLFunctions/BiarithmeticGaugeGeometry/EuclideanCellRemainderAndPolarNeutralCollapse.lean), [isotropy](../../../formal/GaloisForLFunctions/ArithmeticPositiveDuality/CoupledPositivityIsIsotropy.lean), [local geometry](../../../formal/GaloisForLFunctions/ArithmeticCorrespondencePositivity/TheLocalGeometryOfAReflectionPair.lean), [isometries](../../../formal/GaloisForLFunctions/ArithmeticCorrespondencePositivity/TheIsometriesOfAReflectionPair.lean), [non-localizing carrier](../../../formal/GaloisForLFunctions/ArithmeticCorrespondencePositivity/PositivityBeyondIsotropyDoesNotLocalize.lean), [resolution](../../../formal/GaloisForLFunctions/ArithmeticCorrespondencePositivity/TheResolutionOfACorrespondenceIsItsLength.lean), [kernel counts](../../../formal/GaloisForLFunctions/ArithmeticCorrespondencePositivity/KernelCountsAreBlindToComplexQuartets.lean), [translation Gram](../../../formal/GaloisForLFunctions/ArithmeticCorrespondencePositivity/TheCofactorGramIsATranslationGram.lean), [Laplace form](../../../formal/GaloisForLFunctions/ArithmeticCorrespondencePositivity/TheLaplaceFormOfTheCofactorProfile.lean), [escape rank](../../../formal/GaloisForLFunctions/ArithmeticCorrespondencePositivity/TheEscapeRankCountsTheDominantZeros.lean), [gauge-mass criterion](../../../formal/GaloisForLFunctions/ArithmeticCorrelationGeometry/RHIsTheVisibilityOfEveryEscapeState.lean), [Weil extensions](../../../formal/GaloisForLFunctions/ArithmeticPositiveDuality/TheExtensionsOfWeilsCorrelationAreIndexedByTheZeros.lean), [Kronecker split](../../../formal/GaloisForLFunctions/ArithmeticPositiveDuality/TheKroneckerDecompositionOfPositiveDefiniteFunctionsOnQ.lean), [archimedean line](../../../formal/GaloisForLFunctions/ArithmeticCorrelationGeometry/TheThresholdIsThePriceOfTheArchimedeanLine.lean), [controlled cycles](../../../formal/GaloisForLFunctions/BiScaleUncertainty/ControlledClosedCycleRecovery.lean).

## 3. Wall 14 — realization, correspondences, counts, polarization and forcing

| Face | Status | Obstructed shortcut | Established boundary / survivor | Missing construction |
|---|---|---|---|---|
| **14.1 Capacity and limits** | Open | Fixed finite carriers; trace-class transport; fixed gaps. | Growing carriers; `det₂` renewal. | A source-preserving limit with orientation. |
| **14.2 Algebra without orientation** | Sharpened | Identities, integrality, the theorem of the square, the budget, the involution as forcing. | Layers L1–L3 free over `ℤ`; the Frobenius is always a similitude; similitude + anisotropic eigenvector ⇒ unit modulus; Rosati form `≥ 0` iff unitary; all hold on the golden datum. | Positivity of a computed trace (14.18, 14.21). |
| **14.3 Detector without producer** | Open | A zero-indexed object proves its own input. | Exact depth diagnostics. | Construction first, sign second (B1.6). |
| **14.4 Effectivity** | Resolved | Section counts, effectivity functions or majorants offered as weaker inputs than the sign. | `h⁰ ≡ 1` has RR, `h⁰ ≡ 0` has Bézout; together ⇔ Hodge index ⇔ RH. Riemann inequality + subquadratic growth ⇔ Hodge; off-line zero = abundant class; least growth rate `max(0, ½x²)`; `ℙ¹ × ℙ¹` calibration. | — The construction of an arithmetic count is 14.6 and 14.18. |
| **14.5 Pre-divisor weld** | Open | Assuming reservoir data satisfy the identity. | Prime and Gamma reservoir. | Stabilization at every spectral point. |
| **14.6 Section selectivity** | Sharpened | Rank or count readings; Boolean `h⁰ ≤ 1`; rank-one and Künneth lattice counts; fibre-independent counting polarizations. | Lattice counts on the square give `ζ(s₁ + s₂)` (boundary) or `\|ξ\|²` (determinant) on the reflection plane; the theta surface has RR with characteristic and a counting polarization `πJ²/t` that is the same on every fibre. | A selective count of rank growing with the class (B3.35). |
| **14.7 Base-to-surface theta coupling** | Resolved | Base `h⁰` supplying the surface. | The Riemann inequality forces Hilbert–Samuel growth; the theta `h⁰` of the degree has linear RR on every surface and the quadratic Riemann inequality on none, whether or not RH holds. | — Surface counts are 14.6. |
| **14.8 Blind-carrier exhaustion** | Sharpened | Positivity on a carrier blind by construction. | Maximal blind ideal `= ⊤ ⇔ RH`; left-blind ideal; non-localizing positivity source-blind. | A forcing law with input outside the exhausted classes (B1.6). |
| **14.9 Positivity–faithfulness dilemma** | Open | Operator-norm faithful positivity used for RH alone. | Faithful degree ⇔ RH + simple. | RH through trace-bounded data. |
| **14.10 Carrier positivity** | Sharpened | Forcing inside invariant quadratic positivity. | Blind, half-blind, isotropic; positivity beyond isotropy only without localization. | A localizing carrier with positivity not induced by invariance (3.18, 3.19). |
| **14.11 Multiplicative forcing** | Resolved | Imported regions; finite certificates beating growth. | Boundary forcing law; capacity `⌊k/2⌋`; Fejér barrier; quantum budget. | — |
| **14.12 Completeness of invariants** | Resolved | Assuming a full-invariant countermodel. | Degree-one rigidity; relaxation models. | — |
| **14.13 Zero–pole budget** | Resolved | Pole order as payment for `ζ`'s own zeros. | Conservation; pole order one rigid; `5d < 9κ`. | — Payment is 1.16. |
| **14.14 Base for coefficient systems** | Sharpened | Amplifying `ζ`; grading by pole order; multiplicative base axioms. | Fixed tensor loss ⇔ RH; `CompletedPositiveSystem 1 d = ℝ^× · ζ`; twists rate neutral; the golden datum satisfies the multiplicative base axioms and has no effectivity [S]. | A structure whose tensor cost is independent of the power (B1.9). |
| **14.15 Successor coupling** | Resolved | Prescribing the successor to constrain Weil's correlation. | Affine positivity induced; Weil's extensions a box over critical zeros; the successor unipotent on polar fibres; the successor connection is the gauge-charged datum, flat iff Euler vacuum [S]. | — Its gauge use is 1.18. |
| **14.16 Correspondence ring with a theorem of the square** | Resolved | Hecke graphs as Weil's correspondences. | Normalized graphs obey the theorem of the square; Tate's limit makes bounded-error square laws exact. | — |
| **14.17 Local type at a reflection pair** | Resolved | Treating isotropy as a defect of particular carriers; seeking elliptic localizers among multiplicative correspondences. | Boost law; resonance law; affine reflection-compatible stabilizer `{id, σ_γ}`, `σ_γ` = FE conjugated by the flow; sectors `±2\|G\|²`; dihedral dilemma; twisted symmetric symbols scalar at pairs of ordinate `γ`. | — Forcing through `σ_γ` is 3.19. |
| **14.18 Polarization: the sign layer** | Sharpened | Expecting identities, the square theorem, a budget, an involution or a count to carry Weil's sign. | Rosati positivity ⇔ RH; five currencies (effectivity, nonabundance, naive heights, tensor base, horizon torsion) are one statement [S]; the polarization law isolates positivity as the whole content. | A structure computing a form that is both positive and equivariant (14.21, B3.33, B3.35). |
| **14.19 Cost of zero contraction** | Resolved | Removing off-line zeros by positive multipliers in one system. | Real pairs at `Δκ = 0`; real-anchor law; anchored quartet ⇒ `κ ≥ 3`; planting a weight-two anchor costs `Δκ ≥ 2`, minimal; direct pole-paid cost `1` (`a ≤ 1/4`) or `2` (`a < 1/2`). | — Last calibrations are W11. |
| **14.20 Collision and conductor** | Resolved | Colliding conjugate zeros in one-variable positive objects. | Height coupling contracts one ordinate's quartets at zero marginal pole cost with the classical budget; boundary-twist absorption at `κ₀ + 2κ_γ`; Fejér coupling at central coefficient `9(K+1)/(2K)`; no harmonic lift empties the deepest line; coupled completions have even real orders; the global collision has no analytic carrier; the coupled class is not rigid [S]. | — The two-variable remainder is 14.21; the class ceiling is 14.22. |
| **14.21 Collided polarization** | New | Reading collided positivity as Rosati positivity; expecting the explicit formula to compute `D`. | `D ≥ 0`; `Re W = D − Δ`; RH ⇔ `W = D`; `D(T_L f) = Σ m e^{2δL}\|f̂(ρ)\|²` and its second difference counts off-line charge; RH ⇔ `D` Hecke invariant [S]; kernel, coupled and escape positivity are collided. | A computation of `D` or its Hecke defect from arithmetic data (B3.33, Q2); equivariance of `D` (B1.11). |
| **14.22 Central vanishing ceiling** | New | Two-sided rigidity of `HeightCoupledSystem 2 1 1 γ`. | Rigidity fails at every critical-zero ordinate via `W_β` [S]; inward collapse not positive [S]; the ceiling `ord_{1/2}Λ ≤ ord_{1/2}Λ_γ` implies RH [S]; splitting and quartet contraction leave the Dirichlet-lattice decay class [S]; at zero-free ordinates the ceiling is central nonvanishing [R]. | The ceiling (B1.12), or central nonvanishing / a constrained subclass with a contraction (B3.34). |

Sources: [section counts](../../../formal/GaloisForLFunctions/ArithmeticCorrespondencePositivity/ASectionCountIsTheSign.lean), [effectivity calculus](../../../formal/GaloisForLFunctions/ArithmeticEffectivityTheory/TheEffectivityCalculus.lean), [base does not extend](../../../formal/GaloisForLFunctions/ArithmeticEffectivityTheory/TheBaseDoesNotExtend.lean), [Tate](../../../formal/GaloisForLFunctions/ArithmeticEffectivityTheory/TatesLimitLaw.lean), [theta surface](../../../formal/GaloisForLFunctions/ArithmeticEffectivityTheory/TheThetaSurface.lean), [ℙ¹ × ℙ¹](../../../formal/GaloisForLFunctions/ArithmeticEffectivityTheory/TheProjectiveSquareCalibration.lean), [five currencies](../../../formal/GaloisForLFunctions/ArithmeticEffectivityTheory/TheBaseAxioms.lean), [diagonal collapse](../../../formal/GaloisForLFunctions/ArithmeticPolarization/TheDiagonalCollapse.lean), [polarization law](../../../formal/GaloisForLFunctions/ArithmeticPolarization/ThePolarizationLaw.lean), [Fejér barrier](../../../formal/GaloisForLFunctions/ArithmeticPolarization/TheFejerBarrierForCoupledContraction.lean), [collision law](../../../formal/GaloisForLFunctions/ArithmeticPolarization/TheCollisionLaw.lean), [coupling parity](../../../formal/GaloisForLFunctions/ArithmeticPolarization/CouplingCollidesEvenly.lean), [anchor cost](../../../formal/GaloisForLFunctions/ArithmeticCorrespondencePositivity/IntrinsicExteriorAndMinimumAnchorCost.lean), [coupled class](../../../formal/GaloisForLFunctions/BiarithmeticGaugeGeometry/ChiralDeformationAndNonRigidityOfHeightCoupledSystems.lean), [rigidity implication](../../../formal/GaloisForLFunctions/ArithmeticPolarization/RigidityOfTheCoupledClassExcludesItsZeros.lean), [maximal blind ideal](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/MaximalBlindIdealOfTheMeyerSource.lean), [boundary completeness](../../../formal/GaloisForLFunctions/MultiplicativePositivityGeometry/BoundaryCompleteness.lean), [boundary capacity](../../../formal/GaloisForLFunctions/MultiplicativePositivityGeometry/BoundaryZeroCapacity.lean), [growth-to-forcing](../../../formal/GaloisForLFunctions/MultiplicativePositivityGeometry/GrowthToForcing.lean), [sharp collar](../../../formal/GaloisForLFunctions/StripBochnerWeilForcing/SharpHalfPoleCollar.lean), [reflection rigidity](../../../formal/GaloisForLFunctions/StripBochnerWeilForcing/StripReflectionRigidity.lean), [κ = 1 class](../../../formal/GaloisForLFunctions/StripBochnerWeilForcing/TheSimplePoleClassIsZeta.lean), [theorem of the square](../../../formal/GaloisForLFunctions/ArithmeticCorrespondencePositivity/TheTheoremOfTheSquareIsFree.lean), [budget](../../../formal/GaloisForLFunctions/ArithmeticCorrespondencePositivity/TheBudgetIsFreeItsSufficiencyIsNot.lean), [symmetric squares](../../../formal/GaloisForLFunctions/ArithmeticCorrespondencePositivity/TheSpectrumOfSymmetricSquaresIsTheSign.lean), [exterior counts](../../../formal/GaloisForLFunctions/ArithmeticCorrespondencePositivity/SymmetricSquareContractionsAndExteriorCounts.lean), [real anchors and height coupling](../../../formal/GaloisForLFunctions/ArithmeticCorrespondencePositivity/ExteriorAndHeightCoupledQuartetContractions.lean), [successor](../../../formal/GaloisForLFunctions/ArithmeticCorrespondencePositivity/TheSuccessorIsInvisibleAtZeros.lean), [theta sections](../../../formal/GaloisForLFunctions/ArithmeticOrientationGeometry/TheThetaH0OfSpecZ.lean).

## 4. Resolved local walls

A resolved local passage is not a research task.

| Local question | Disposition | Remaining wall |
|---|---|---|
| Summation-scope "defects" | Never existed. | — |
| Balanced Möbius, centred-prime band, Vaughan power improvements ⇔ `Θ < 1` | Established. | 1.0 |
| Escape location | Escape at `ε` ⇔ zeros right of `1/2 + ε`, up to countably many `ε`; RH ⇔ admission at every `ε`. | 3.15 |
| Escape of dominant configurations | Phase kernels; dominant-split criterion; collided Cauchy forms. | 3.15 |
| Short-window averaged positivity at `Γ^{99/100}`; zero-ordinate positivity for nonnegative tests | Complete. | 3.14 |
| Positivity beyond isotropy | Only on non-localizing carriers. | 3.18 |
| Elliptic localization in correspondence-closed carriers | Resonance only; `σ_γ` unique affine localizer; dihedral dilemma. | 3.19 |
| Twisted positivity | Theorem below the conductor horizon; source-blind there. | 3.19 |
| Section count with RR and Bézout | ⇔ Hodge index ⇔ RH. | 14.18 |
| Effectivity function; naive heights; one-sided count; horizon torsion | Each ⇔ RH. | 14.18, 1.1 |
| Theta `h⁰` through the degree | Fails the quadratic Riemann inequality on every surface. | 14.6 |
| Lattice counts on the square | Boundary or determinant positivity. | 14.6 |
| Finite multiplicative lattice forms vs the Liouville vacuum | Unitarily equivalent [S]. | 1.18 |
| First gauge charge | A height twist; edge reduction. | 1.18 |
| Theorem of the square; fixed budget over `ℤ` | Free; sufficiency is RH. | 14.18 |
| Kernel and coupled counts as effectivity | Collided; blind to sign. | 14.21 |
| Real off-critical zeros of completed systems | Contract at `Δκ = 0`. | — |
| Complex quartet contraction in one system | Real anchor of twice the weight; anchored ⇒ `κ ≥ 3`; planting `Δκ ≥ 2`. | 14.19 |
| Height coupling, Fejér coupling, absorption of shifted poles | Classical local budget; central costs computed; even real orders. | 14.20 |
| Harmonic coupling emptying the deepest line | Impossible (Fejér barrier). | 14.20 |
| Global conjugate collision | No analytic carrier. | 14.21 |
| Two-sided rigidity of the coupled class | False at critical-zero ordinates [S]. | 14.22 |
| The κ = 1 completed class | `ℝ^× · ζ`. | 14.14 |
| Absolute pole-order budget | False. | 1.16 |
| Successor coupling to Weil's correlation | None; successor defect small in the strip. | 3.16 |
| Depth homogeneity of moments, products, family averages; twists | Linear loss; twists neutral. | 1.15 |
| One-sided Lefschetz bounds | One prime, short cycles, one shift; local part holds. | 1.3 |
| Finite-level weight existence | ⇔ RH. | 1.3 |
| AIP linear diagonal reserve | Cancels on the polar-neutral hyperplane [S]. | 3.4 |

## 5. Scoped obstruction register and positive survivors

These distinctions govern which mechanisms may be proposed. None retires a live route.

| Mechanism excluded or limited | Positive survivor / permitted target |
|---|---|
| Collided positivity (determinants, coupled counts, escape Cauchy forms, `D`) as Rosati positivity | The capacity identity `W = D − Δ`; the Hecke defect of `D` as a target (14.21). |
| Section counts, effectivity functions, naive heights, one-sided counts as weaker inputs | The five currencies as exact receivers; a selective count of growing rank (14.6). |
| The theta surface's counting polarization as selective | Fibre-dependent counts (B3.35). |
| Lattice counts on the square as Rosati positivity | Rank growing with the class. |
| Multiplicative correspondences as elliptic localizers | Resonant scales (≤ one prime); `σ_γ`. |
| `σ_γ`-even sectors as forcing | `σ_γ`-odd sectors and the forcing half (3.19). |
| Twisted positivity below the conductor horizon as selective | The odd-sector sign beyond the horizon (Q1). |
| Two-sided rigidity of the coupled class | The one-sided central ceiling (14.22). |
| Inward collapse of critical pairs | Outward splitting (Bochner positive). |
| Finite multiplicative lattice forms as gauge selectors | The successor connection and its holonomy (1.18). |
| Height twists as gauge charge beyond the first prime | Non-archimedean charge (Q3). |
| AIP diagonal reserve | Complete prime-weighted remainder payment (3.4). |
| Single-channel, coupled point-stable, non-localizing carriers as forcing | Non-multiplicative localizers (3.18). |
| Positivity on nonnegative tests as `ζ`-specific | Sign-changing atoms. |
| Haar-typical cancellation as a bound at `0` | The a.e. law; pole-subtracted typicality. |
| Moments, family averages, tensor products, relative powers, twists as sublinear loss | A structure whose cost does not scale. |
| Pole order as payment for `ζ`'s own zeros | The capacity `Δ`. |
| Escape completeness read as exclusion | Positive gauge mass. |
| Average or almost-every-height positivity as exclusion of an individual zero | Exceptional sets below the zero spacing. |
| Prescribed successors as constraints on Weil's correlation | Source-prescribed mixed data. |
| Univariate integer polynomials on `[0, 1]` as Stepanov auxiliaries | Auxiliaries outside the one-prime Hecke algebra (B3.30). |
| Positive exponential aperture floors | Finite-aperture positivity; doubly exponentially vanishing floors. |
| Imported zero-free regions read as forcing | Classical regions with explicit growth input. |

### Catalogue crosswalk

The 44 mechanism codes of the [killed-routes catalogue](../rh-killed-routes.md) map as follows. This is navigation, not re-certification of legacy entries.

| Codes | Family | Faces |
|---|---|---|
| WIP, INT, DEF | Integrality, finite-rank purity, deformation-stable inequalities | 14.2, 14.12, 14.13, 14.18 |
| ODR, HCT, WHL | Drift, transport, endpoint poles | 3.5–3.7 |
| LGP, ADJ | Local payment; cross-prime majorants | 3.4 |
| PAF | Positive aperture floors | 1.13 |
| AUT, SEL | Automorphic gaps and scattering poles | 14.1–14.3, 14.21 |
| LLM, UCF, HUS | Averages or reflection-even readers | 3.1, 3.14 |
| GEN | Fixed-part localization | 3.8, 3.18 |
| TEQ, CAL, JPR, HFR, CCP | Equilibrium, collisions, degree, parity | 1.2, 1.6 |
| TWN, NEV | Unconstructed roots, termwise signs | 1.5, 14.3 |
| ISG, FPR, TRC, GAP, PTR | Fixed or local carriers | 14.1 |
| SRP, APW, CRT | Pole weight, perturbed sources, finite mimics | 1.4, 1.18, 3.2 |
| BAG, RAW | Finite Euler recurrence; unregularized series | 1.1, 1.2 |
| R1, R2, R3 | Trace, renewal or quantization forcing its own defect | 1.2, 14.3, 14.13 |
| BD, COS, POI | Markov kernels, local inversion, Poisson transport | 3.3, 14.1 |
| DSA, TOR, REF, CPF, TMD, TK | Legacy entries, not re-certified | — |

## 6. What counts as crossing a wall

- **Wall 1.** Insert a newly proved source estimate into an existing receiver with every tail and quantifier intact. Any graded gain beyond Vinogradov–Korobov is a fixed strip; a non-graded output (a non-isolation law, a gauge-charged positivity) is progress of another kind. A new mechanism must contain a term that does not scale with amplification, must be gauge charged beyond the archimedean line, and for `ζ`'s own zeros must bound the capacity `Δ`.
- **Wall 3.** Prove a transfer, sharp boundary or reconstruction on a stated class, norm and limit, and show that the source satisfies its hypothesis. For 3.14, selection below the zero spacing. For 3.15, residue summability and infinite-height mass. For 3.18, a non-multiplicative localizer. For 3.19, the odd-sector sign beyond the conductor horizon at zero ordinates.
- **Wall 14.** Construct the arithmetic object independently and prove fidelity, then a forcing law with input outside every mapped class: invariant carrier positivity; resonance and below-horizon twists; non-localizing positivity; one-variable positive systems; collided positivity; counting reformulations of the sign; gauge-invariant data; identities, square theorem, budget, involution. The law must fail on the relaxation models, the coupled-class deformations, the golden datum and complex fake, and the Liouville twin; it must reproduce the κ = 1 collapse, `κ ≥ 3` for anchored quartets and `W = D − Δ`; and it must supply a computed form that is both positive and equivariant, or a computed equivariance of `D`.
