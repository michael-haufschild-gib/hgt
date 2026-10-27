# Walls ledger

Status: 2026-10-27, corpus `80f251476` with the working tree of that day. Every obstacle in the corpus belongs to one of three core families:

- **Wall 1 — critical arithmetic sign.** Estimates, signs and oscillatory payment at the critical endpoint, at the gauge point `0`.
- **Wall 3 — transfer.** Readings, norms, completions, limits, shared budgets, localization and selection.
- **Wall 14 — realization and forcing.** Faithful arithmetic objects, correspondences and their local types, invariants, counts, deformations, renormalizations, polarization, and the forcing of the actual source into its blind carrier.

**Organizing principle.** At an off-line reflection pair `{ρ, 1 − ρ̄}` the local form has signature `(1, 1)`; multiplicative correspondences act on it by boosts, the successor unipotently, the functional equation and its conjugates `σ_γ` by the swap. The test space of `ζ` carries two computed forms: Weil's form `W` (explicit formula), Hecke equivariant, whose positivity is RH; and the collided form `D = Σ m_ρ|f̂(ρ)|²` (the current `Δ log|ξ|`, finite theta prefixes), positive, faithful and coercive, whose Hecke equivariance is RH; `Re W = D − Δ`. A third family joins the two properties except at one place: torsion energies on the characteristic circle are positive at `r < 1`, Hecke equivariant at `r = 1`, and lose positivity in the diagonal renormalization. Wall 1 measures the hyperbolic part as a rate or a sign; Wall 3 governs how positivity transfers between readings, norms, localizations, limits and budgets; Wall 14 asks what structure makes one form positive and equivariant at once. Thirteen exhaustion laws bound every mechanism tested:

- **Gauge.** Multiplicative data determine a source up to its gauge orbit; finite multiplicative lattice forms are blind; the actual source is one point (1.18, 3.1).
- **Hyperbolicity.** Positivity invariant under a correspondence that is a boost at an off-line pair forces isotropy there (14.10, 14.17).
- **Resonance.** Inside correspondence-closed carriers a symmetric dilation is elliptic at an off-line point only at scales with `γ log a ∈ πℤ`; the only reflection-compatible affine localizer is `σ_γ` (3.18, 14.17).
- **Conductor.** Twisted positivity is a theorem only below `e^a ≲ log γ/4`, where it is source-blind; the companion certificate needs `e^{2δa} > 768A log(|γ| + 3)`; the two never meet; the conductor is the local Weyl law of `D` (3.19).
- **Localization.** Positivity constrains a fibre only where the carrier localizes; non-localizing positivity holds for every prime weight (3.18).
- **Dominated twins.** On nonnegative tests the Weil form is antitone in the source (1.4, 1.18).
- **Linear loss.** Moments, family averages, products and relative powers lose at least linearly; twists are rate neutral (1.15, 1.17).
- **Pole order and one variable.** Pole order pays inserted zeros; a complex quartet contracts only against a real anchor; the positive polar-configuration cone is the cone of nonnegative scale weights; the global conjugate collision has no analytic carrier (1.16, 14.13, 14.19, 14.20, 14.23).
- **Collision.** Kernel counts, coupled counts, escape Cauchy forms and `D` pair `ρ` with `ρ̄`; their positivity is automatic, faithful and computed, and sees no sign (3.1, 3.15, 14.21).
- **Counting.** A section count with RR and Bézout, an effectivity function, a naive or convex height, a one-sided count, a fixed tensor loss, horizon torsion and the Farey potential are each RH; large-sieve majorants inflate (1.1, 1.17, 14.4, 14.6, 14.18).
- **Deformation.** Positive deformations keep the off-line divisor; positive rigidity, chirality and central ceilings at an ordinate are exactly the absence of zeros there; changing the central order of an arithmetic member costs a square-root prime deficit (14.22, 14.25).
- **Renormalization.** Positive torsion energies converge to Weil's prime kernel only after subtracting a divergent diagonal self-energy; positivity is lost exactly there (14.24).
- **Completion.** Counting reaches incomplete sums only through a period; the arithmetic point has none (1.20).

Over `𝔽_q` one structure escapes all thirteen: a polarization of `C × C`, from Riemann–Roch and an ample class, makes the Rosati trace positive and Frobenius-equivariant at once, the self-intersection of the diagonal is the finite number `2 − 2g`, and the corpus proves purity for hyperelliptic curves by counting alone (Stepanov's auxiliary section and `|τ|² = q`). Over `ℤ` identities, the theorem of the square and the budget are free, the receivers are complete, a positive form is computed, and positive equivariant families exist before renormalization; nothing yet joins positivity and equivariance in one form.

Companions: [complete report](route-obstacles.md), [summary](obstacles-summary.md), [route unification](route-unification-ledger.md). Evidence: corpus search and Lean statement reading, logged in `logs/review-2710-research-log.md`. No compilation. A countermodel excludes the mechanism it was built against, not every route that touches its wall.

**Markers.** `[S]`: working source (modified or untracked, or marked so in the frontier map). `[R]`: reading or model calculation of the review, not a theorem. Q1–Q3 are the summary's next questions: Q1 Kronecker alignment at zero ordinates (B3.36), Q2 arithmetic adjunction (B3.37), Q3 gauge persistence (B3.26).

**Status column.**

- *Open*: no answer; the boundary listed is the present one.
- *Sharpened*: open, with an exact boundary or survivor that fixes what must be proved.
- *Resolved*: the face's question is answered; the face carries no open task.
- *New*: a face isolated in this version.

## 0. Faces that changed in this version

| Face | Change | Content |
|---|---|---|
| 1.0 | Sharpened | Energy-rate law at the zero abscissa exact in both directions; escaped Möbius pairings at fixed `θ` and large-sieve section supply are fixed strips [S]. |
| 1.1 | Sharpened | Farey potential: `ψ(N) = Σ log(2 sin(πk/n))`, RH ⇔ `N + O(√N log²N)`; `ν̂_N(1) = M(N)`; q-deformation of the horizon period. |
| 1.3 | Sharpened | Gårding inequality; finitely many negative directions at every aperture; full floor `1/5000` through `181/500` [S]. |
| 1.16 | Sharpened | `D` computed; `E_D = E_Δ` [R]; local Weyl law; the missing piece is an inequality. |
| 1.17 | Sharpened | Six currencies (convex heights added). |
| 1.18 | Sharpened | Twins separated at `181/500` and `23/40` [S]; multi-prime repulsion stretched exponential; archimedean-free successor-square separator [S]. |
| 1.19 | New | Budget currencies: prime-error, Mertens, Abel slope; `𝔽_q` slopes count the spectrum. |
| 1.20 | New | Completion law and the arithmetic point. |
| 3.1 | Sharpened | Collided readings are computed from `ξ` without zero indexing. |
| 3.4 | Sharpened | Joint `2, 3` payment at `23/40`; raw continuum towers negative at order `e^A` [S]. |
| 3.15 | Sharpened | Escape classification complete: Abel atoms, capacity, endpoint, shadow, infinite-height laws. |
| 3.16 | Sharpened | Successor defect in `H²` with exact norm. |
| 3.19 | Sharpened | The forcing gap is a theorem at every height; it reduces to Kronecker alignment at zero ordinates [R]. |
| 3.20 | New, Resolved | Norm transfer for `D`: faithful, coercive, sampling, Gårding, local Weyl law. |
| 3.21 | New | Lattice-to-continuum transfer of prime towers. |
| 14.2 | Sharpened | Over `𝔽_q` counting proves purity (hyperelliptic calibration). |
| 14.6 | Sharpened | Jacobi–Hurwitz dichotomy; large-sieve inflation; Serre-dual box cohomology; node twist destroys RI. |
| 14.18 | Sharpened | Naive heights are traces; kernel counts do not supply them (complex fake). |
| 14.21 | Sharpened | `D` computed, faithful, coercive, a polarization whose similitudes are Hecke iff RH. |
| 14.22 | Sharpened | Rational/positive ceilings and positive chirality ⇔ no off-line zero at the ordinate; positive rigidity ⇔ zero-free ordinate; full class open. |
| 14.23 | New, Resolved | The positive polar-configuration cone. |
| 14.24 | New | Torsion intersection and renormalization. |
| 14.25 | New, Resolved | Deformation principle and the square-root deficit law. |

## 1. Wall 1 — critical arithmetic sign

With `Δ = sup_ρ |Re ρ − 1/2|`, a receiver bounded at a fixed rate `σ < 1/2` gives `Δ ≤ σ` (quasi-RH); RH is `Δ = 0`.

| Face | Status | Present obstacle | Established boundary / survivor | Missing input |
|---|---|---|---|---|
| **1.0 Quasi-RH first rung** | Sharpened | Graded receivers, multiplicative forcing and admission at fixed damping have no target between Vinogradov–Korobov and a fixed strip. | Fixed-strip equivalences (balanced statistic, centred-prime band, short windows, JAS level one, PBM abscissa, WL rate, RW/ACS floors, Vaughan power improvements, one-sided Lefschetz bounds at one prime, power growth of the damped energy, escaped Möbius pairings at fixed `θ` [S], sections beyond the large-sieve diagonal [S]). Energy-rate law `E_ε(T) ≤ C(T + 1)^κ`, `κ > max(0, 2Θ − 2ε − 1)`, with its lower direction. Unconditional: dlVP, Littlewood, VK. | A fixed strip (B2.1), or a non-graded output (Q1's non-isolation law). |
| **1.1 Critical signed cancellation** | Sharpened | Lag, Abel, history, series and bilinear bounds must reach rate zero with every counterterm paid. | Endpoint laws; high-zero tail `O(1)`; `M(x) = Ω±(√x)`. One-sided count ⇔ RH; horizon torsion ⇔ RH; Farey potential `ψ(N) = Σ log(2 sin(πk/n))` ⇔ RH at `√N` precision; `ν̂_N(1) = M(N)`; `log P_N(q) = Σ M(⌊N/d⌋) log[d]_q`. Integrality gives Nair's floor; univariate integer polynomials stop below PNT [R]. | Source cancellation at every positive slack (B1.1). |
| **1.2 Axis orientation** | Open | A nonnegative defect, winding count or faithful spectrum does not force line support. | Ward cap and trace; cubic trace = winding; subharmonic Newton margin. | Vanishing or a forcing all-height sign (B1.6). |
| **1.3 Complete Weil positivity** | Sharpened | Low and mixed sectors unsigned at large aperture; negative part at a height `≥ −4(A+1)²e^A N²Φ(γ)`. | Local–global split at one prime; one shift decides RH; windows `3/10`, `181/500` (odd [L], full [S]); averaged positivity on `Γ^{99/100}`; zero-ordinate positivity for nonnegative tests; Gårding `Re W ≥ 2π‖f‖² − K·lowMass`; finitely many negative directions at every aperture. | The Lefschetz part, i.e. zero negative index at every aperture (B1.3). |
| **1.4 Arithmetic cone membership** | Sharpened | Identifying the source is not proving its positivity. | Full-cone source selection; positive-measure rigidity; worst twin on nonnegative tests. | `Λ` in the full Weil cone, i.e. RH. |
| **1.5 Contrast equality** | Open | Jensen, BSY and Li accounting leaves a residual. | BSY off-line sum nonnegative, zero on critical zeros; `Δ` is a capacity of the same kind; Li depth `≤ 1/431`. | An arithmetic upper bound forcing the residual to zero (B1.7). |
| **1.6 Required uniformity** | Open | Fixed rank, order, history or height does not reach the receiver's quantifier. | Orthant signs; fixed-order thresholds; fixed-rank coercivity. | All-rank or order-uniform estimates (B1.5, B3.12). |
| **1.7 Amplification of a receiver** | Resolved | Raising a receiver to a power multiplies its rate. | Exact exponent bookkeeping. | — |
| **1.8 Critical pronic energy** | Sharpened | Horizon-uniform signed energy at cofinally small damping. | Half-damping admission; RH ⇔ admission at every damping ⇔ positive gauge mass; energy-rate law exact; centred divisor prefix = sawtooth + long-modulus quadrature. | Signed control of the long-modulus quadrature (B1.2). |
| **1.9 Signed continuation** | Open | Integrated signed loss bounded uniformly in the horizon. | Canonical corrector; integer local exponents below half. | Flux control at closing damping (B1.2). |
| **1.10 Absolute compensation** | Open | A vanishing relative error coexists with unbounded raw energy. | Power-plus-bounded forcing; record-minimum limits. | Absolute energy bound (B1.2). |
| **1.11 Rates and clusters** | Open | Physical ground rate versus zero width. | `groundRate = polarRate`; form-norm rates `= Δ`; depth-profile rate `(1/L) log D(T_L f) → 2a_f`. | `polarRate = Δ` (B3.1). |
| **1.12 Interior anti-alignment** | Open | The gap `θ(ε,t) < 1` between the proved collars. | High-height and small-damping collars. | Interior decorrelation (B1.1, B2.6). |
| **1.13 Aperture shell flux** | Open | A strictly decreasing ground energy can cross zero. | RH ⇔ cumulative frozen relaxation `≤ μ(3/10)`. | Signed collar estimate on the moving ladder (B3.6). |
| **1.14 Actual divisor heat sign** | Open | Local repair costs do not sign actual Ξ heads. | Large-height head repair; Hermite barrier; `Λ < 1/8`. | Zero-heat sign on the residual region (B1.5, B3.9). |
| **1.15 Depth homogeneity** | Sharpened | Every amplification over `ℤ` tested gains on depth as fast as it pays. | Gauge moments, products, finite family averages: linear loss; harmonic twists rate neutral. | `k`-level forms and Følner coupling (W9); a term that does not scale (1.17). |
| **1.16 Payment of ζ's own zeros** | Sharpened | Pole order pays inserted zeros only; budgets pay a hyperbolic pair only on a finite segment. | `Re W = D − Δ`; `Δ` charges every off-line pair uniformly in the depth; `D` computed by the `ξ` current and theta prefixes; `D(e^{−iγu}f) ∼ ‖f‖² log\|γ\|`; Hecke defect `E_f(L)` computed; `E_D = E_Δ` [R]. | An inequality bounding `E_f` or `Δ` by structure (B1.11, B3.33, Q2). |
| **1.17 Loss law** | Sharpened | A rate needs `b_k = o(k)`. | Fixed tensor loss ⇔ RH; linear loss ⇔ strip; golden loss `k log φ`; fixed tensor loss is one of six equivalent currencies. | A structure whose cost does not scale (B1.9). |
| **1.18 Gauge selection** | Sharpened | The actual source is one point of a gauge orbit; positivity on prime-free windows and nonnegative tests is gauge blind. | Möbius a.e. law; prime source atypical only by its pole; finite lattice forms blind; successor connection reconstructs `ω(2), ω(3)`. First charge a height twist; the twin fails at `181/500` on a witness where `ζ` is positive [S]; the first non-archimedean twin fails at `23/40` with `W_ζ > ‖F‖²/25`, `W_λ < −(3/10)‖F‖²` [S]; `{2,3}` repulsion `e^{−\|γ\|}/50`, `N`-prime repulsion stretched exponential, beating every stretched exponential with enough primes [L]; successor-square separator `w(2)w(4)` [S]. | A margin law on growing prime windows (B3.26, Q3); a charged estimate at `0` (B3.24). |
| **1.19 Budget currencies** | New | A linear log-energy budget of a signed row is offered as weaker than the sign. | Prime-error budget ⇒ RH, slope `≥ 2 + γ_E − log 4π`; unconditional slope `≥ Σ_{critical} m²/\|ρ\|²` on finite sets; Abel slope at the genus ⇒ RH + simple; Mertens budget ⇒ RH + simple + `Σ\|ρζ′(ρ)\|^{−2} ≤ S`; successor shift preserves the cost. `𝔽_q`: prime-error slope `Σ mult²`, Mertens slope = repulsion energy, genus one strict Hasse. | An actual budget (B1.13); converse directions are W7(xv). |
| **1.20 Completion and the arithmetic point** | New | Finite-level square-root counts transported to the arithmetic point. | `\|τ\|² = q` by counting; Pólya–Vinogradov by completion; Burgess moment, energy and inequality at finite level [S]; the arithmetic point has no period. | A period, or a counting mechanism that needs none (B3.30). |

Key sources: [one-sided count](../../../formal/GaloisForLFunctions/ArithmeticCorrespondencePositivity/TheStepanovCountIsTheSign.lean), [horizon torsion](../../../formal/GaloisForLFunctions/ArithmeticEffectivityTheory/TheHorizonTorsion.lean), [Farey potential](../../../formal/GaloisForLFunctions/ArithmeticEffectivityTheory/TheArchimedeanComputationOfTheLogTorsion.lean), [torsion Fourier](../../../formal/GaloisForLFunctions/ArithmeticEffectivityTheory/TheFourierCoefficientsOfTheTorsionMeasure.lean), [q-deformation](../../../formal/GaloisForLFunctions/ArithmeticEffectivityTheory/TheQDeformationOfTheHorizonPeriod.lean), [capacity](../../../formal/GaloisForLFunctions/ArithmeticPolarization/TheOscillatoryCapacity.lean), [Hecke invariance](../../../formal/GaloisForLFunctions/ArithmeticPolarization/HeckeInvarianceOfTheCollidedPolarizationIsRH.lean), [Gårding](../../../formal/GaloisForLFunctions/ArithmeticPolarization/TheCollidedFormSamplesHighFrequencies.lean), [negative index](../../../formal/GaloisForLFunctions/ArithmeticPolarization/WeilsFormHasFinitelyManyNegativeDirectionsAtEveryAperture.lean), [local Weyl law](../../../formal/GaloisForLFunctions/ArithmeticPolarization/TheLocalWeylLawOfTheCollidedForm.lean), [`ξ` current](../../../formal/GaloisForLFunctions/ConjugateDiagonalGeometry/XiSourceCurrent.lean), [prime-error budget](../../../formal/GaloisForLFunctions/ArithmeticCorrespondencePositivity/ThePrimeErrorBudgetDominatesTheArchimedeanGenus.lean), [Abel slope](../../../formal/GaloisForLFunctions/ArithmeticCorrespondencePositivity/AnAbelSlopeAtTheGenusIsRHWithSimpleZeros.lean), [Mertens budget](../../../formal/GaloisForLFunctions/ArithmeticCorrespondencePositivity/TheMertensBudgetForcesASimpleCriticalSpectrum.lean), [curve budgets](../../../formal/GaloisForLFunctions/ArithmeticCorrespondencePositivity/TheMertensBudgetOfACurveIsTheRepulsionEnergyOfItsSpectrum.lean), [completion](../../../formal/GaloisForLFunctions/ArithmeticEffectivityTheory/TheCompletionLaw.lean), [Burgess](../../../formal/GaloisForLFunctions/ArithmeticEffectivityTheory/TheBurgessBound.lean), [`181/500` twin](../../../formal/GaloisForLFunctions/SelectivePositivityAndThresholdLaws/LiouvilleOddWindowRefutationAndSelectiveFullPositivity.lean), [`23/40` twin](../../../formal/GaloisForLFunctions/SelectivePositivityAndThresholdLaws/TwoPrimeCatalanSeparationAndContinuumTowerObstruction.lean), [multi-prime repulsion](../../../formal/GaloisForLFunctions/BiarithmeticGaugeGeometry/MultiPrimeDiophantineRepulsion.lean), [first charge](../../../formal/GaloisForLFunctions/ArithmeticPolarization/TheFirstGaugeChargeIsATwist.lean), [gauge torus](../../../formal/GaloisForLFunctions/BiarithmeticGaugeGeometry/PrimeGaugeTorusAndVacuumIntertwiners.lean), [energy-rate law](../../../formal/GaloisForLFunctions/ArithmeticCorrespondencePositivity/TheReceiverEnergyGrowthAtTheZeroAbscissa.lean), [escaped pairings](../../../formal/GaloisForLFunctions/SelectivePositivityAndThresholdLaws/MoebiusEscapedPairingBoundaryLaw.lean), [tensor loss](../../../formal/GaloisForLFunctions/ArithmeticCorrespondencePositivity/TheBaseIsAFixedLoss.lean), [six currencies](../../../formal/GaloisForLFunctions/ArithmeticEffectivityTheory/TheBaseAxioms.lean), [convex heights](../../../formal/GaloisForLFunctions/ArithmeticEffectivityTheory/TheConvexityOfCounts.lean), [one prime](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/OneSidedLefschetzBoundsAtOnePrimeAreTheStrip.lean), [short-window averages](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/ShortWindowAveragedWeilPositivity.lean).

**Aperture ceiling.** `μ(A) ≤ K exp(11A/2 − πe^{2(A−2)})`. No positive exponential floor exists.

## 2. Wall 3 — transfer: readings, norms, limits, budgets, localization, selection

Closing a face here enables a route but supplies no Wall 1 sign. Three faces reduce to other walls: closedness of the blind ideal is zero-location data (3.3); selection below the zero spacing is RH-strength (3.14); escape exclusion is positive gauge mass (3.15).

| Face | Status | Present limitation | Established boundary / survivor | Missing transfer |
|---|---|---|---|---|
| **3.1 Readings** | Sharpened | Magnitudes, orientation-blind samples, moments, multiplicative statistics and kernel counts erase the signed data. | Recovery classifications; multiplicative observation is the gauge projection. Collided readings (determinants, coupled counts, escape forms, `D`) pair conjugates and are computed from `ξ` and theta prefixes without zero indexing; Rosati traces pair reflections. | Orientation-retaining, gauge-charged, reflection-pairing source readings. |
| **3.2 Aperture/height escape** | Open | Finite windows admit mimics. | Cofinal criteria; quantitative visibility. | Containment along the full exhaustion. |
| **3.3 Norms and completions** | Resolved | One norm does not replace another without a theorem. | Origin-`L²` no faithful reading; golden payment domain nonclosed; blind ideal closed naturally. | — |
| **3.4 Shared signed resources** | Sharpened | Local payments can spend one surplus twice. | Frustration and holonomy law; descent excess `kB`; polar-neutral collapse; log-cell remainder bound; joint signed `2, 3` payment at `23/40` with `1/62` margin. | One continuum budget with prime-weighted remainder (B1.3, B3.8). |
| **3.5 Endpoint logarithms** | Open | Pole cancellation alone does not pay the endpoint. | Partial-pole-sum law; Dini thresholds. | The logarithmic remainder for a new source. |
| **3.6 Moving horizons and origins** | Open | Generic below-half interchange fails. | Priced shifts; reset-origin limits. | Source-specific moving-tail bounds. |
| **3.7 Damping topology** | Open | Hilbert–Schmidt and inverse estimates fail before boundedness. | Chain bounded at half damping; integer local exponents below half. | Signed sub-half estimates (B3.11). |
| **3.8 Multiplicity and index** | Open | Packet `m²`, Weil `m`, distinct index and reciprocal depth differ. | Meyer: numerical = principal ⇔ simple; budgets see `m²` (Cramér constant) and divergence at multiplicity (Mertens). | Keep trace data separate from operator data. |
| **3.9 Observation cost** | Sharpened | Recovery at arbitrary phase has no universal horizon. | Closed-cycle recovery on controlled sources. | A source-specific horizon bound. |
| **3.10 Filters and hulls** | Open | Invertible critical-Wiener filters preserve admission classes. | Unit-orbit dictionaries. | Non-unit repair preserving the source. |
| **3.11 Coupled quantifiers** | Open | Weil margin → heat-Hankel couples degree and time. | Exact bridges. | Decoupling (B3.12). |
| **3.12 Residual reconstruction** | Open | Algebraic injectivity gives no bounded inverse. | Kernel `ℝ q_ε`. | Quantitative inverse (B3.3). |
| **3.13 Joint orientation of families** | Open | Individually positive orbits can choose incompatible endpoints. | Spline-orbit index `≤ 1` ⇔ RH. | A compatible family (B3.10). |
| **3.14 Average to selected heights** | Sharpened | Averages control windows, not every zero. | Averaged positivity on `Γ^{99/100}` windows; zero-ordinate positivity for nonnegative tests; resolution is length. | Selection to every height and signed test (B1.4); windows `Γ^{1/2+ε}` are W6. |
| **3.15 Escape states of actual limits** | Sharpened | Escape classifies; it does not exclude. | RH ⇔ admission at every damping ⇔ positive gauge mass; phase kernels and collided Cauchy forms for dominant configurations. For `ζ` with Abel weights: atoms are the dominant zeros with residues `ζ(ρ − ε)/(ζ′(ρ)(ρ − ε))`; effective orders are visible translated-zero orders; capacity law; endpoint law `C ≥ Σ‖r_ρ‖²/(2θ)` at the zero abscissa; shadow law; non-summable residues, an unattained abscissa or unbounded orders send the mass to infinite height. | Exclusion of infinite-height escape (B3.2); positive gauge mass (B1.2). |
| **3.16 Prime-to-spectral positivity** | Sharpened | Positivity is known on the prime side only. | Kronecker split; the successor sees continuous spectra, never atoms; Weil's extensions a box over critical zeros; successor defect `O((\|s\| + 1)^{1−σ+η})` in the strip and `D_Λ(s)/s ∈ H²` with norm² `2πΣΛ²/(n(n+1))`; every `L²` wave and every density with a.c. part has a visible affine extension. | A self-dual identity with its gap on the spectral side. |
| **3.17 Archimedean-line threshold** | Open | The archimedean line computes gauge moments only below `2rX^k ≤ 1`. | Windowed moment = gauge moment + near-incidence. | A gauge-charged estimate beyond the threshold at `0` (B3.24). |
| **3.18 Localization** | Sharpened | Global positivity does not constrain a fibre unless the carrier isolates it. | Lagrange localization; bounded-aperture carriers positive for every prime weight; separating isometries are boosts; resonance law; Hecke + `σ_γ` stability is blindness. | A non-multiplicative localizer; its forcing is 3.19. |
| **3.19 Elliptic localization beyond the conductor horizon** | Sharpened | Twisted positivity is a theorem only for `e^a ≲ log γ/4`, and source-blind there. | Forcing half [L]; the certificate needs `768A log(\|γ\| + 3) < e^{2δa}` and is disjoint from the horizon for `0 ≤ δ ≤ 1/2` at every height [L]; the conductor is the local Weyl law of `D`; beyond the horizon the detector's prime side is a polynomial of length `(log γ)^{O(1)}` at the zero's ordinate [R]. | The odd-sector sign at zero ordinates beyond the horizon, possibly outside a sparse set: Kronecker alignment of zero ordinates with small primes (B3.32, B3.36, Q1). |
| **3.20 Norm transfer for the collided form** | Resolved | `D` offered without norm control, or its positivity offered as `W`'s. | `D(f) = 0` ⇒ `f = 0`; `c_A‖f‖² ≤ D(f)` at every aperture (non-effective); Gårding for `W` and `D`; `D ≤ C∫\|f̂\|² log(\|σ\| + 4)` [S]; local Weyl law; `W` has finite negative index. | — The sign is 1.3; an effective `c_A` is W5. |
| **3.21 Lattice to continuum prime towers** | New | Integer-lattice payments transferred to continuum prime towers. | Lattice odd ledger balanced; on `[1, X]` primes beyond `X` vanish identically; raw continuum towers carry negative edge energy of order `e^A`, excluding sub-half exponential `H¹` floors [S]; pole-neutralized width equivalence [S]. | Payment of the pole-neutralized full form (B3.8). |

Sources: [resonance](../../../formal/GaloisForLFunctions/ArithmeticCorrespondencePositivity/EllipticLocalizationIsResonance.lean), [elliptic localizers](../../../formal/GaloisForLFunctions/ArithmeticPolarization/TheEllipticLocalizers.lean), [twisted sectors](../../../formal/GaloisForLFunctions/ArithmeticPolarization/TwistedSectorsCollideQuartets.lean), [price and horizon](../../../formal/GaloisForLFunctions/ArithmeticPolarization/ThePriceOfEllipticLocalization.lean), [forcing half](../../../formal/GaloisForLFunctions/ArithmeticPolarization/TheForcingHalfOfEllipticLocalization.lean), [forcing gap](../../../formal/GaloisForLFunctions/ConjugateDiagonalGeometry/TheConductorForcingGap.lean), [coercivity](../../../formal/GaloisForLFunctions/ArithmeticPolarization/TheCollidedFormIsCoerciveAtEveryAperture.lean), [polarization](../../../formal/GaloisForLFunctions/ArithmeticPolarization/TheCollidedFormIsAPolarization.lean), [log-Sobolev](../../../formal/GaloisForLFunctions/ArithmeticPolarization/TheCollidedFormIsTheLogarithmicSobolevNorm.lean), [finite theta metric](../../../formal/GaloisForLFunctions/ConjugateDiagonalGeometry/FiniteThetaApertureMetric.lean), [Abel atoms](../../../formal/GaloisForLFunctions/ArithmeticCorrespondencePositivity/TheAbelEscapeAtomsOfZetaAreItsDominantZeros.lean), [Abel capacity](../../../formal/GaloisForLFunctions/ArithmeticCorrespondencePositivity/TheAbelEscapeCapacityOfTheDominantZeros.lean), [endpoint law](../../../formal/GaloisForLFunctions/ArithmeticCorrespondencePositivity/TheEscapeEnergyAtTheAbscissaPaysTheResidues.lean), [shadow law](../../../formal/GaloisForLFunctions/ArithmeticCorrespondencePositivity/TheBoundaryReceiverPaysTheCriticalShadows.lean), [unbounded orders](../../../formal/GaloisForLFunctions/ArithmeticCorrespondencePositivity/UnboundedVisibleOrdersForceAbelEscapeToInfiniteHeight.lean), [escape criterion](../../../formal/GaloisForLFunctions/ArithmeticCorrespondencePositivity/TheEscapeCompletenessCriterion.lean), [collided escape forms](../../../formal/GaloisForLFunctions/ArithmeticPolarization/EscapeKernelsAreCollidedForms.lean), [successor in `H²`](../../../formal/GaloisForLFunctions/ArithmeticCorrespondencePositivity/TheSuccessorDefectIsABoundedHardyPerturbation.lean), [visible successors](../../../formal/GaloisForLFunctions/ArithmeticPositiveDuality/EverySquareIntegrableWaveHasAVisibleSuccessor.lean), [polar-neutral collapse](../../../formal/GaloisForLFunctions/BiarithmeticGaugeGeometry/EuclideanCellRemainderAndPolarNeutralCollapse.lean), [continuum towers](../../../formal/GaloisForLFunctions/SelectivePositivityAndThresholdLaws/TwoPrimeCatalanSeparationAndContinuumTowerObstruction.lean), [local geometry](../../../formal/GaloisForLFunctions/ArithmeticCorrespondencePositivity/TheLocalGeometryOfAReflectionPair.lean), [non-localizing carrier](../../../formal/GaloisForLFunctions/ArithmeticCorrespondencePositivity/PositivityBeyondIsotropyDoesNotLocalize.lean), [zero ordinates](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/AlmostEveryZeroOrdinateIsWeilPositive.lean), [archimedean line](../../../formal/GaloisForLFunctions/ArithmeticCorrelationGeometry/TheThresholdIsThePriceOfTheArchimedeanLine.lean).

## 3. Wall 14 — realization, correspondences, counts, deformations and forcing

| Face | Status | Obstructed shortcut | Established boundary / survivor | Missing construction |
|---|---|---|---|---|
| **14.1 Capacity and limits** | Open | Fixed finite carriers; trace-class transport; fixed gaps. | Growing carriers; `det₂` renewal. | A source-preserving limit with orientation. |
| **14.2 Algebra without orientation** | Sharpened | Identities, integrality, the theorem of the square, the budget, the involution as forcing. | Layers L1–L3 free over `ℤ`; similitude + anisotropic eigenvector ⇒ unit modulus; Rosati form `≥ 0` iff unitary; over `𝔽_q` counting proves purity (hyperelliptic RH by Stepanov and Gauss sums). | Positivity of a computed trace (14.18, 14.21, 14.24). |
| **14.3 Detector without producer** | Open | A zero-indexed object proves its own input. | Exact depth diagnostics; zero-indexed depth functionals computable from `ξ`. | Construction first, sign second (B1.6). |
| **14.4 Effectivity** | Resolved | Counts, effectivity functions or majorants offered as weaker inputs. | Section count ⇔ Hodge; effectivity calculus; abundant classes; convex heights soft; polar box count ⇔ Hodge. | — Construction is 14.6, 14.18. |
| **14.5 Pre-divisor weld** | Open | Assuming reservoir data satisfy the identity. | Prime and Gamma reservoir. | Stabilization at every spectral point. |
| **14.6 Section selectivity** | Sharpened | Rank or count readings; Boolean `h⁰ ≤ 1`; rank-one and Künneth lattice counts; fibre-independent polarizations; large-sieve majorants. | Lattice counts on the square give boundary or determinant positivity; theta surface fibre-independent; node-twisted box counts violate RI on every polar surface; Jacobi–Hurwitz packets are blind on degree zero or inflate, large-sieve majorants inflate `q_P(z) ≥ \|z·z\|/2` [S]; sign-free Serre-dual box cohomology fails RR on the golden datum [S]. | A selective count of rank growing with the class (B3.35). |
| **14.7 Base-to-surface theta coupling** | Resolved | Base `h⁰` supplying the surface. | Theta `h⁰` of the degree has linear RR and no quadratic Riemann inequality. | — |
| **14.8 Blind-carrier exhaustion** | Sharpened | Positivity on a carrier blind by construction. | Maximal blind ideal `= ⊤ ⇔ RH`; left-blind ideal; non-localizing positivity source-blind. | A forcing law with input outside the exhausted classes (B1.6). |
| **14.9 Positivity–faithfulness dilemma** | Open | Operator-norm faithful positivity used for RH alone. | Faithful degree ⇔ RH + simple. | RH through trace-bounded data. |
| **14.10 Carrier positivity** | Sharpened | Forcing inside invariant quadratic positivity. | Blind, half-blind, isotropic; positivity beyond isotropy only without localization. | A localizing carrier with positivity not induced by invariance (3.18, 3.19). |
| **14.11 Multiplicative forcing** | Resolved | Imported regions; finite certificates beating growth. | Boundary forcing law; capacity `⌊k/2⌋`; Fejér barrier. | — |
| **14.12 Completeness of invariants** | Resolved | Assuming a full-invariant countermodel. | Degree-one rigidity; relaxation models. | — |
| **14.13 Zero–pole budget** | Resolved | Pole order as payment for `ζ`'s own zeros. | Conservation; pole order one rigid; `5d < 9κ`. | — Payment is 1.16. |
| **14.14 Base for coefficient systems** | Sharpened | Amplifying `ζ`; grading by pole order; multiplicative base axioms. | Fixed tensor loss ⇔ RH; `CompletedPositiveSystem 1 d = ℝ^× · ζ`; the golden datum satisfies the multiplicative base axioms and has no effectivity. | A structure whose tensor cost is independent of the power (B1.9). |
| **14.15 Successor coupling** | Resolved | Prescribing the successor to constrain Weil's correlation. | Affine positivity induced; Weil's extensions a box; successor unipotent on polar fibres; successor connection flat iff Euler vacuum. | — Its gauge use is 1.18. |
| **14.16 Correspondence ring with a theorem of the square** | Resolved | Hecke graphs as Weil's correspondences. | Normalized graphs obey the theorem of the square; Tate's limit. | — |
| **14.17 Local type at a reflection pair** | Resolved | Isotropy as a defect of particular carriers; elliptic localizers among multiplicative correspondences. | Boost law; resonance law; stabilizer `{id, σ_γ}`; sectors `±2\|G\|²`; dihedral dilemma. | — Forcing through `σ_γ` is 3.19. |
| **14.18 Polarization: the sign layer** | Sharpened | Expecting identities, the square theorem, a budget, an involution or a count to carry Weil's sign. | Rosati positivity ⇔ RH; six currencies one statement; naive heights are traces, not kernel orders (complex fake: kernel counts `≥ 0`, Rosati `−2304`); the polarization law isolates positivity as the whole content. | A structure computing a form that is both positive and equivariant (14.21, 14.24). |
| **14.19 Cost of zero contraction** | Resolved | Removing off-line zeros by positive multipliers in one system. | Real pairs at `Δκ = 0`; real-anchor law; anchored quartet ⇒ `κ ≥ 3`; planting `Δκ ≥ 2`. | — Last calibrations are W11. |
| **14.20 Collision and conductor** | Resolved | Colliding conjugate zeros in one-variable positive objects. | Height coupling at zero marginal pole cost; Fejér barrier; even real orders; the global collision has no analytic carrier; the coupled class is not rigid. | — Two-variable remainder is 14.21; centre is 14.22. |
| **14.21 Collided polarization** | Sharpened | Reading collided positivity as Rosati positivity. | `D ≥ 0`, faithful, coercive; `Re W = D − Δ`; RH ⇔ `W = D` ⇔ `D` Hecke invariant ⇔ one Hecke translation a similitude of `D`; `D` and every depth moment computed by the `ξ` current and finite theta prefixes; depth profile rate law; two-scale variance law; `E_D = E_Δ` [R]. | An inequality for the computed Hecke defect (B3.33), or equivariance of `D` (B1.11). |
| **14.22 Central order of the coupled class** | Sharpened | Two-sided rigidity of `HeightCoupledSystem 2 1 1 γ`; positive or rational deformations as forcing. | Rigidity fails at every zero ordinate; inward collapse not positive. Positive prime-mass rigidity at `γ` ⇔ no `ξ` zero at ordinate `γ`; positive chirality, positive and rational central ceilings at `γ` ⇔ no off-line zero at ordinate `γ`; RH ⇔ each at every `γ` [L]. Critical transfer law; critical conservation [S]. Arithmetic members: central excess ⇒ deficit abscissa `≥ 1/2` and Abel residue `≥` excess; zero residue and no central drop ⇒ `F = Kζ_γ`. | The full-class ceiling and two-sided rigidity at zero-free ordinates (B3.34). |
| **14.23 The positive polar-configuration cone** | Resolved | Positivity read from a family of sections; periodicity assumptions; odd collision on commensurable lines. | One section at one abscissa decides (`w ≥ 0`); leading line nonnegative almost-periodic sum; line hierarchy law; commensurable positive lines are `\|Q\|²` (couplings); lattice-sieved Post–Widder isolates the polar part. | — |
| **14.24 Torsion intersection and renormalization** | New | Treating the prime kernel as an indefinite datum, or torsion-energy positivity as Weil positivity. | `Λ(n) = Σ log\|1 − μ\|`; `I(m, mt) = φ(m)Λ(t)` (cyclotomic resultants, Hecke law); log-energy `gcd log lcm`; `G∘T_r ≥ 0` for `r < 1`; prime kernel + log-discriminant = −(renormalized limit); divergence `log(1/(1 − r))`. | A Hecke-compatible, positivity-preserving counterterm paid by the archimedean and polar terms (B3.37, Q2). |
| **14.25 Deformation principle** | Resolved | Positive relative-Laplace deformations moving off-line zeros; boundary zeros in powers of `ζ`. | Landau–Wronskian principle; Abel–Gram law (jumps even positive definite, bounded by the real jump); `ζ^d` deformations: `κ ≤ d` and sub-half deficit ⇒ `F = Kζ^d`; boundary capacity `2Σ ord_{1+it}Λ ≤ κ − d`. | — Its arithmetic use is 14.22. |

Sources: [naive heights](../../../formal/GaloisForLFunctions/ArithmeticEffectivityTheory/NaiveHeightsAreTraces.lean), [hyperelliptic calibration](../../../formal/GaloisForLFunctions/ArithmeticEffectivityTheory/TheHyperellipticCalibration.lean), [hyperelliptic RH](../../../formal/GaloisForLFunctions/RHTower/HyperellipticDescent.lean), [polar box](../../../formal/GaloisForLFunctions/ArithmeticEffectivityTheory/ThePolarBoxCount.lean), [Jacobi–Hurwitz](../../../formal/GaloisForLFunctions/SelectivePositivityAndThresholdLaws/JacobiHurwitzTorsionInflationAndShortCycleHeights.lean), [Serre-dual boxes](../../../formal/GaloisForLFunctions/SelectivePositivityAndThresholdLaws/SerreDualScalingCohomologyAndLargeSieveSections.lean), [torsion intersections](../../../formal/GaloisForLFunctions/ArithmeticEffectivityTheory/TheIntersectionOfTorsionOrbits.lean), [renormalized torsion energy](../../../formal/GaloisForLFunctions/ArithmeticEffectivityTheory/TheWeilPrimeKernelIsARenormalizedTorsionEnergy.lean), [log-energy](../../../formal/GaloisForLFunctions/ArithmeticEffectivityTheory/TheLogEnergyOfRootsOfUnity.lean), [effectivity calculus](../../../formal/GaloisForLFunctions/ArithmeticEffectivityTheory/TheEffectivityCalculus.lean), [polarization law](../../../formal/GaloisForLFunctions/ArithmeticPolarization/ThePolarizationLaw.lean), [selectivity battery](../../../formal/GaloisForLFunctions/ArithmeticPolarization/TheSelectivityBatteryOfPolarization.lean), [depth profile](../../../formal/GaloisForLFunctions/ArithmeticPolarization/TheDepthProfileCarriesTheGlobalCollision.lean), [two-scale rigidity](../../../formal/GaloisForLFunctions/ConjugateDiagonalGeometry/TwoScaleDepthRigidity.lean), [one section](../../../formal/GaloisForLFunctions/ArithmeticPolarization/OneVerticalSectionDecidesPositivity.lean), [leading line](../../../formal/GaloisForLFunctions/ArithmeticPolarization/TheLeadingLineIsPositive.lean), [line hierarchy](../../../formal/GaloisForLFunctions/ArithmeticPolarization/PositivityDescendsThroughTheZerosOfHigherLines.lean), [lattice lines](../../../formal/GaloisForLFunctions/ArithmeticPolarization/PositiveLatticeLinesAreCouplings.lean), [Landau–Wronskian](../../../formal/GaloisForLFunctions/BiarithmeticGaugeGeometry/TheLandauWronskianDeformationPrinciple.lean), [Abel–Gram](../../../formal/GaloisForLFunctions/BiarithmeticGaugeGeometry/TheAbelGramLawOfPositiveDeformations.lean), [critical transfer](../../../formal/GaloisForLFunctions/BiarithmeticGaugeGeometry/PositiveCoupledRigidityAndTheCriticalTransferLaw.lean), [positive ceiling](../../../formal/GaloisForLFunctions/BiarithmeticGaugeGeometry/PositivePrimeMassDeformationsAreRigidOffTheCriticalLine.lean), [rational ceiling](../../../formal/GaloisForLFunctions/BiarithmeticGaugeGeometry/RationalBochnerDeformationsOfTheHeightCoupledCarrier.lean), [strong multiplicity one](../../../formal/GaloisForLFunctions/BiarithmeticGaugeGeometry/StrongMultiplicityOneBelowTheSquareRootDeficit.lean), [deficit–excess](../../../formal/GaloisForLFunctions/BiarithmeticGaugeGeometry/TheDeficitResidueBoundsTheCentralExcess.lean), [powers of `ζ`](../../../formal/GaloisForLFunctions/BiarithmeticGaugeGeometry/StrongMultiplicityOneForPowersOfZeta.lean), [boundary capacity](../../../formal/GaloisForLFunctions/BiarithmeticGaugeGeometry/TheBoundaryCapacityOfDeformationsOfPowersOfZeta.lean), [critical conservation](../../../formal/GaloisForLFunctions/BiarithmeticGaugeGeometry/TheCriticalConservationLaw.lean), [coupled class](../../../formal/GaloisForLFunctions/BiarithmeticGaugeGeometry/ChiralDeformationAndNonRigidityOfHeightCoupledSystems.lean), [Fejér barrier](../../../formal/GaloisForLFunctions/ArithmeticPolarization/TheFejerBarrierForCoupledContraction.lean), [collision law](../../../formal/GaloisForLFunctions/ArithmeticPolarization/TheCollisionLaw.lean), [anchor cost](../../../formal/GaloisForLFunctions/ArithmeticCorrespondencePositivity/IntrinsicExteriorAndMinimumAnchorCost.lean), [κ = 1 class](../../../formal/GaloisForLFunctions/StripBochnerWeilForcing/TheSimplePoleClassIsZeta.lean), [maximal blind ideal](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/MaximalBlindIdealOfTheMeyerSource.lean), [theorem of the square](../../../formal/GaloisForLFunctions/ArithmeticCorrespondencePositivity/TheTheoremOfTheSquareIsFree.lean), [budget](../../../formal/GaloisForLFunctions/ArithmeticCorrespondencePositivity/TheBudgetIsFreeItsSufficiencyIsNot.lean).

## 4. Resolved local walls

A resolved local passage is not a research task.

| Local question | Disposition | Remaining wall |
|---|---|---|
| Summation-scope "defects" | Never existed. | — |
| Balanced Möbius, centred-prime band, Vaughan power improvements, escaped pairings at fixed `θ` ⇔ fixed strip | Established. | 1.0 |
| Energy-rate law at the zero abscissa | Both directions. | 1.0, 1.8 |
| Escape location; dominant classification; Abel atoms; infinite-height cases | Complete. | 3.15 |
| What computes `D` | The `ξ` current and finite theta prefixes. | 1.16, 14.21 |
| Norm of `D` | Faithful, coercive, sampling; Gårding; local Weyl law. | 3.20 |
| Negative index of `W` at one aperture | Finite. | 1.3 |
| Companion certificate vs conductor horizon | Disjoint at every height. | 3.19 |
| Twin at `181/500`; first non-archimedean twin at `23/40` | Negative witnesses with `ζ` positive [S]. | 1.18 |
| Short-window averaged positivity at `Γ^{99/100}`; zero-ordinate positivity for nonnegative tests | Complete. | 3.14 |
| Positivity beyond isotropy | Only on non-localizing carriers. | 3.18 |
| Elliptic localization in correspondence-closed carriers | Resonance only; `σ_γ` unique. | 3.19 |
| Section count, effectivity, naive and convex heights, one-sided count, horizon torsion, Farey potential | Each ⇔ RH. | 14.18, 1.1 |
| Kernel counts as naive heights | False (complex fake). | 14.18 |
| Budgets over `𝔽_q` | Slopes count the spectrum; genus one strict Hasse. | 1.19 |
| Purity over `𝔽_q` by counting | Hyperelliptic RH. | 14.2 |
| Theta `h⁰` through the degree; lattice counts on the square | Fail RI; boundary or determinant positivity. | 14.6 |
| Finite multiplicative lattice forms vs the Liouville vacuum | Unitarily equivalent. | 1.18 |
| First gauge charge | A height twist; edge resolved. | 1.18 |
| Theorem of the square; fixed budget over `ℤ` | Free; sufficiency is RH. | 14.18 |
| Kernel and coupled counts as effectivity | Collided. | 14.21 |
| Positive polar-configuration cone | Classified. | 14.23 |
| Complex quartet contraction in one system | Real anchor; `κ ≥ 3`; planting `Δκ ≥ 2`. | 14.19 |
| Height and Fejér coupling; global collision | Classical budget; Fejér barrier; no analytic carrier. | 14.20 |
| Two-sided rigidity of the coupled class at zero ordinates | False. | 14.22 |
| Positive and rational deformations of `ζ_γ` | Rigid exactly at zero-free ordinates; ceilings ⇔ RH per ordinate. | 14.22 |
| Positive deformations of `ζ^d` | Rigid without pole budget; boundary capacity `κ − d`. | 14.25 |
| The κ = 1 completed class | `ℝ^× · ζ`. | 14.14 |
| Successor coupling to Weil's correlation | None; successor defect in `H²`. | 3.16 |
| Depth homogeneity of moments, products, family averages; twists | Linear loss; twists neutral. | 1.15 |
| One-sided Lefschetz bounds | One prime, short cycles, one shift; local part holds. | 1.3 |
| AIP linear diagonal reserve | Cancels on the polar-neutral hyperplane. | 3.4 |
| Raw continuum prime towers | Negative edge energy `e^A` [S]. | 3.21 |

## 5. Scoped obstruction register and positive survivors

These distinctions govern which mechanisms may be proposed. None retires a live route.

| Mechanism excluded or limited | Positive survivor / permitted target |
|---|---|
| Collided positivity, coercivity, sampling or finite negative index as Weil's sign | The capacity identity; the computed Hecke defect as a target (14.21). |
| The computed `D` as a bound on its own defect | An inequality from a new structure (B3.33, Q2). |
| Companion certificate spliced with the conductor horizon | A sign beyond the horizon at zero ordinates (B3.36, Q1); a different detector. |
| Section counts, effectivity, naive or convex heights, one-sided counts, Farey sums, budgets as weaker inputs | The currencies as exact receivers; a selective count of growing rank (14.6). |
| Large-sieve or Cauchy–Schwarz majorants as sections | Signed, fibre-dependent counts (B3.35). |
| The theta surface's counting polarization as selective | Fibre-dependent counts. |
| Multiplicative correspondences as elliptic localizers | Resonant scales; `σ_γ`. |
| `σ_γ`-even sectors as forcing | `σ_γ`-odd sectors (3.19). |
| Two-sided rigidity of the coupled class | The ceiling at zero-free ordinates for the full class (14.22). |
| Positive or rational deformations as forcing | Non-positive members; arithmetic members with square-root deficit (B3.34). |
| Inward collapse of critical pairs | Outward splitting (Bochner positive). |
| Torsion-energy positivity at `r < 1` as Weil positivity | A positivity-preserving Hecke counterterm (14.24). |
| Finite multiplicative lattice forms as gauge selectors | Successor connection and holonomy; separating windows (1.18). |
| Height twists as gauge charge beyond the first prime | Non-archimedean charge with a margin law (Q3). |
| AIP diagonal reserve; raw continuum towers | Prime-weighted remainder payment of the pole-neutralized form (3.4, 3.21). |
| Single-channel, coupled point-stable, non-localizing carriers as forcing | Non-multiplicative localizers (3.18). |
| Positivity on nonnegative tests as `ζ`-specific | Sign-changing atoms. |
| Haar-typical cancellation as a bound at `0` | The a.e. law; pole-subtracted typicality. |
| Moments, family averages, tensor products, relative powers, twists as sublinear loss | A structure whose cost does not scale. |
| Pole order as payment for `ζ`'s own zeros | The capacity `Δ`; `E_D = E_Δ`. |
| Escape classification read as exclusion | Positive gauge mass; exterior tightness. |
| Average or almost-every-height positivity as exclusion of an individual zero | Exceptional sets below the zero spacing. |
| Completion at the arithmetic point | A period, or a mechanism that needs none (1.20). |
| Univariate integer polynomials as Stepanov auxiliaries over `ℤ` | Auxiliaries outside the one-prime Hecke algebra (B3.30). |
| Positive exponential aperture floors | Finite-aperture positivity; doubly exponentially vanishing floors. |
| Imported zero-free regions read as forcing | Classical regions with explicit growth input. |

### Catalogue crosswalk

The 44 mechanism codes of the [killed-routes catalogue](../rh-killed-routes.md) map as follows. This is navigation, not re-certification of legacy entries.

| Codes | Family | Faces |
|---|---|---|
| WIP, INT, DEF | Integrality, finite-rank purity, deformation-stable inequalities | 14.2, 14.12, 14.13, 14.18 |
| ODR, HCT, WHL | Drift, transport, endpoint poles | 3.5–3.7 |
| LGP, ADJ | Local payment; cross-prime majorants | 3.4, 3.21 |
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

- **Wall 1.** Insert a newly proved source estimate into an existing receiver with every tail and quantifier intact. Any graded gain beyond Vinogradov–Korobov is a fixed strip; a non-graded output (a non-isolation law, a gauge margin, a bound for the computed defect at a selected height) is progress of another kind. A new mechanism must contain a term that does not scale with amplification, must be gauge charged beyond the archimedean line, must read the arithmetic point, and for `ζ`'s own zeros must bound the capacity `Δ`.
- **Wall 3.** Prove a transfer, sharp boundary or reconstruction on a stated class, norm and limit, and show that the source satisfies its hypothesis. For 3.14, selection below the zero spacing. For 3.15, exclusion of infinite-height escape. For 3.18, a non-multiplicative localizer. For 3.19, the odd-sector sign beyond the conductor horizon at zero ordinates. For 3.21, payment of the pole-neutralized continuum form.
- **Wall 14.** Construct the arithmetic object independently and prove fidelity, then a forcing law with input outside every mapped class: invariant carrier positivity; resonance and below-horizon twists; non-localizing positivity; one-variable positive systems and their cone; positive and rational deformations; collided positivity, computed or not; counting reformulations of the sign; gauge-invariant data; identities, square theorem, budget, involution; positivity before renormalization. The law must fail on the relaxation models, the coupled-class deformations, the golden datum and complex fake, the sign and Liouville twins; it must reproduce the κ = 1 collapse, `κ ≥ 3`, `W = D − Δ`, the local Weyl law and the `𝔽_q` budget slopes; and it must supply a form that is positive and equivariant at once — through an inequality for the computed defect or a positivity-preserving Hecke counterterm.
