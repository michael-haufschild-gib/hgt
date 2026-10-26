# Walls ledger

Status: 2026-10-26, corpus `e889b7985` with the working tree of that day. Every obstacle in the corpus belongs to one of three core families:

- **Wall 1 — critical arithmetic sign.** Estimates, signs and oscillatory payment at the critical endpoint.
- **Wall 3 — transfer.** Readings, norms, completions, limits, shared budgets and selection.
- **Wall 14 — realization and forcing.** Faithful arithmetic objects, orientation, invariants, correspondences and the forcing of the actual source into its blind carrier.

**Organizing principle.** Every unconditional positivity theorem is positivity on a carrier that is blind, half-blind or isotropic at the off-line zeros, or positivity on average over heights. RH says that the actual source is itself blind. Wall 1 measures blindness as a rate, Wall 3 governs how it transfers between readings, limits and budgets, Wall 14 asks what forces the source into its blind carrier. Four exhaustion laws now bound every mechanism tested:

- **Gauge.** Multiplicative data determine a source up to its orbit under the gauge torus `(ℝ/ℤ)^{primes}`; whatever they prove holds at Haar-almost every twist, and the actual source is one point of the orbit (1.18, 3.1).
- **Isotropy.** Positivity on a single-channel ideal forces blindness or half-blindness; on coupled point-stable carriers it forces isotropy of the fibres at `ρ` and `1 − ρ̄`, never vanishing (14.10).
- **Linear loss.** A rate from an amplified observable needs a loss law `b_k = o(k)`; moments, tensor products and relative powers lose at least linearly (1.15, 1.17).
- **Pole order.** Pole order pays exactly for inserted zeros; ζ's own zeros, if paid, are paid by oscillation of the zero sum (1.16, 14.13).

Over `𝔽_q` one structure escapes all four: correspondences on `C × C`, with a theorem of the square, Riemann–Roch and the Hodge index, supplying a budget `2g` that does not grow with the power of Frobenius. Over `ℤ` the receiver side of that argument is complete (one prime, one test, `|c_m| ≤ c_0` ⇔ RH) and the budget is missing (14.16).

Companions: [complete report](hard-obstacles.md), [summary](hard-obstacles-summary.md), [route unification](route-unification-ledger.md). Evidence: corpus search and Lean statement reading, logged in `logs/review-2610/working-log.md`. No compilation. A countermodel excludes the mechanism it was built against, not every route that touches its wall.

**Markers.** `[S]`: working source not yet integrated. `[R]`: assessment or model calculation of the review, not a theorem. Q1–Q3 are the review's next questions: Q1 escape completeness (B3.2), Q2 positivity beyond isotropy (B3.17), Q3 a theorem of the square over `Spec ℤ` (B3.22).

**Status column.**

- *Open*: no answer; the boundary listed is the present one.
- *Sharpened*: still open, with a new exact boundary or survivor that changes what must be proved.
- *New*: a face not in the previous ledger.
- *Resolved*: the face's question is answered; the answer is recorded and the face carries no open task.

## 1. Wall 1 — critical arithmetic sign

With `Δ = sup_ρ |Re ρ − 1/2|`, a receiver bounded at a fixed rate `σ < 1/2` gives `Δ ≤ σ` (quasi-RH); RH is `Δ = 0`.

| Face | Status | Present obstacle | Established boundary / survivor | Missing input |
|---|---|---|---|---|
| **1.0 Quasi-RH first rung** | Sharpened | Graded receivers, multiplicative forcing and admission at fixed damping have no target between Vinogradov–Korobov and a fixed strip. | Fixed-strip equivalences: balanced statistic, centred-prime band, short windows, JAS level one, PBM abscissa, WL rate `σ`, RW/ACS floors, every Vaughan power improvement; one-sided Lefschetz bounds `±Re c_m = O(p^{θm})` at two primes [S]. Completed positive systems reach collars of width `≍ 1/(d log T)`. Unconditional regions: dlVP, Littlewood, VK. | A fixed zero-free strip (B2.1), or a handle that is not depth-homogeneous (1.15, 1.17). |
| **1.1 Critical signed cancellation** | Sharpened | Lag, Abel, history, series and bilinear bounds must reach rate zero with every counterterm and tail paid. | Exact endpoint laws; high-zero tail `O(1)`; all-modulus `Q^{−δ/32}`; Heath–Brown all-length; sharp `S₂`; `M(x) = Ω±(√x)`. Gauge form: the Möbius half-power law at the gauge point `0` is RH (1.18). | Source cancellation at every positive slack (B1.1). |
| **1.2 Axis orientation** | Open | A nonnegative defect, winding count or faithful spectrum does not force line support. | Ward cap and trace; cubic trace = winding; subharmonic Newton margin; KKL horizon. | Vanishing or a forcing all-height sign (B1.6). |
| **1.3 Complete Weil positivity** | Sharpened | Low and mixed sectors are unsigned pointwise at large aperture; the negative part at a height is `≥ −4(A+1)²e^A N² Φ(γ)`, with aperture cost `e^A`. | Windows `3/10` full, `181/500` odd, `(log 2+1/50)/2` primitive. Averaged positivity at `κ₀ log Γ` on every window `[Γ, Γ+H]`, `Γ^{99/100} ≤ H ≤ Γ/8`. Positivity for nonnegative tests at all but `CH/η` zero ordinates and on height sets of measure `≥ cH/(A+1) − CH/(η log Γ)`. Finite-level existence ⇔ RH. | Sign at every aperture (B1.3) or selection (3.14). |
| **1.4 Arithmetic cone membership** | Open | Identifying the source is not proving its positivity. | Pair tests recover every node; single-node perturbations fail; positive-measure rigidity identifies the source, stably in an `L¹` FE defect (14.12). | `Λ` in the full Weil cone, i.e. RH. |
| **1.5 Contrast equality** | Open | Exact Jensen, BSY and Li accounting leaves a residual. | BSY off-line sum nonnegative, zero on critical zeros; Li depth `≤ 1/431`, `β < 1/300`. | An arithmetic upper bound forcing the residual to zero (B1.7). |
| **1.6 Required uniformity** | Open | Fixed rank, order, history or height does not reach the receiver's quantifier. | All-rank orthant sign; PA order thresholds and the order-24 moment sign; fixed-rank coercivity. | All-rank or order-uniform estimates (B1.5, B3.12). |
| **1.7 Amplification of a receiver** | Resolved | Raising a receiver to a power multiplies its rate. | Exact exponent bookkeeping. | — (depth amplification is 1.15, the loss law 1.17) |
| **1.8 Critical pronic energy** | Open | Horizon-uniform signed energy at cofinally small damping. | Half damping: receiver bounded, Gram rank two, moving limits a rank-three ray. Above half: admission. Below half: leading order classified; power improvements are fixed strips. | Signed interior energy below `T^{1−2ε}` (B1.2). |
| **1.9 Signed continuation** | Open | Integrated signed loss must stay bounded uniformly in the horizon. | Canonical corrector; integer local exponents of paid patterns below half damping. | Flux control at closing damping (B1.2). |
| **1.10 Absolute compensation** | Open | A vanishing relative error coexists with unbounded raw energy. | Power-plus-bounded forcing; residual pairing → `−1` on escape; quantile and moving localizations; record-minimum limits with `K_pp ≥ p^{2ε−2}`. | Absolute energy bound (B1.2). |
| **1.11 Rates and clusters** | Open | Physical ground rate versus zero width. | `groundRate = polarRate`; form-norm and Birman–Schwinger rates `= Δ`; `RH ⇔ groundRate = 0`. | Physical `polarRate = Δ` (B3.1). |
| **1.12 Interior anti-alignment** | Open | The gap `θ(ε,t) < 1` between the proved collars. | High-height and small-damping collars; planted factors keep them. | Interior decorrelation (B1.1, B2.6). |
| **1.13 Aperture shell flux** | Open | A strictly decreasing ground energy can cross zero. | Zero birth jumps; RH ⇔ cumulative frozen relaxation `≤ μ(3/10)`; collar bound; frozen finite families fail. | Signed collar estimate along the moving ladder (B3.6). |
| **1.14 Actual divisor heat sign** | Open | Local repair costs do not sign actual Ξ heads. | Every positive heat repairs every high head; Hermite barrier and optimum; positive monomial reflectors; `Λ < 1/8`. | Zero-heat sign on the residual region (B1.5, B3.9). |
| **1.15 Depth homogeneity** | Sharpened | Every amplification, coupling or averaging over `ℤ` tested gains on a zero's depth as fast as it pays in arithmetic length. | Now a theorem for two classes: gauge Jensen `(∫|D|²)^k ≤ ∫|D|^{2k}` makes moment amplification lose linearly (`MultiplicativeAmplificationLosesLinearly`); product receivers of any order see depth only through total length (`ProductReceiversSeeDepthOnlyThroughTotalLength`). Relative powers move the gauge point and fix ζ. Følner coupling gains only through `1 − β`; Fejér budgets `b(½) ≥ 1` once `L ≥ 0.17`. | The remaining classes as theorems (W9); a term that does not scale (1.17). |
| **1.16 Payment of ζ's own zeros** | Open | Pole order pays only inserted zeros; ζ's own off-line zeros, if any, are paid by oscillation of the zero sum. | Index–pole conservation; the absolute budget is false; every deformation gives only lower bounds on `ind₋(W_ζ)`; κ = 1 rigidity (14.13). | An oscillatory capacity bounding ζ's interior zero charge. |
| **1.17 Loss law** | New | A zero of depth `δ` forces growth `kδ` in an order-`k` observable; a rate needs an arithmetic bound `b_k = o(k)`. | For the one-prime Lefschetz sequence `c_m = W(T_{p^m} g, g)`: one test reads `p^{Δm}` at every prime; RH ⇔ `|c_m| ≤ c_0` at one prime; two primes make one-sided bounds sufficient [S]. Over `𝔽_q` a fixed budget forces purity; the golden datum loses with slope `log φ` although all its Künneth counts are positive. Multiplicative data, moments and products cannot supply `b_k = o(k)`. | A fixed-budget correspondence (14.16) or gauge-charged structure beyond the square-root threshold (3.17) (B1.9). |
| **1.18 Gauge selection** | New | The actual source is one point of a gauge orbit on which the half-power law holds almost surely. | For `μ`: the half-power law holds at Haar-almost every twist, fails at the Liouville twin, and at the point `0` is RH [S]. Pair, successor and surplus statistics have gauge mean zero. The Möbius boundary of affine maps separates `μ` from its twin at PNT strength. | A gauge-charged estimate at the point `0` (B3.24); at RH strength, B1.1. |

Key sources: [endpoint](../../../formal/GaloisForLFunctions/BiScaleUncertainty/WeilLagCriticalDeficitEndpointAndLimitLaw.lean), [balanced statistic](../../../formal/GaloisForLFunctions/BezoutValuationIncidence/TheBalancedStatisticIsTheQuasiRiemannHypothesis.lean), [Vaughan power bounds](../../../formal/GaloisForLFunctions/BezoutValuationIncidence/UniformVaughanPowerBoundsAreFixedStrips.lean), [short-window averages](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/ShortWindowAveragedWeilPositivity.lean), [off-line field](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/AlmostEveryHeightIsNearlyWeilPositive.lean), [zero ordinates](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/AlmostEveryZeroOrdinateIsWeilPositive.lean), [rate equality](../../../formal/GaloisForLFunctions/ArithmeticContinuationAndCriticalEnergy/UnconditionalEqualityOfPolarAndFullGroundEnergyRates.lean), [shell ladder](../../../formal/GaloisForLFunctions/ArithmeticContinuationAndCriticalEnergy/ThresholdVanishingAndCollarDominanceOfThePrimeShell.lean), [radius head](../../../formal/GaloisForLFunctions/ArithmeticLocalDivisorGeometry/RadiusHeadHeatPositivity.lean), [VK region](../../../formal/GaloisForLFunctions/RHTower/Sieve/VinogradovKorobovZeroFree.lean), [linear loss](../../../formal/GaloisForLFunctions/ArithmeticCorrelationGeometry/MultiplicativeAmplificationLosesLinearly.lean), [total length](../../../formal/GaloisForLFunctions/ArithmeticKunnethTheory/ProductReceiversSeeDepthOnlyThroughTotalLength.lean), [Lefschetz growth](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/OneCycleReadsTheWidthAtEveryPrime.lean), [one-sided at two primes](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/OneSidedLefschetzBoundsAtTwoPrimesAreTheStrip.lean), [gauge trichotomy](../../../formal/GaloisForLFunctions/ArithmeticCorrelationGeometry/AlmostEveryGaugePointCancelsToTheSquareRoot.lean), [index–pole conservation](../../../formal/GaloisForLFunctions/RHTower/WeilIndexConservation.lean).

**Aperture ceiling.** `μ(A) ≤ K exp(11A/2 − πe^{2(A−2)})`. No positive exponential floor exists; finite-aperture positivity and doubly exponentially vanishing floors remain admissible.

## 2. Wall 3 — transfer: readings, norms, limits, budgets, selection

Closing a face here enables a route but supplies no Wall 1 sign. Three faces reduce to other walls: closedness of the blind ideal is zero-location data (3.3); selection below the zero spacing is RH-strength (3.14); escape exclusion at a fixed damping is a fixed strip (3.15) [R].

| Face | Status | Present limitation | Established boundary / survivor | Missing transfer |
|---|---|---|---|---|
| **3.1 Readings** | Sharpened | Magnitudes, orientation-blind samples, moment families, finite linear readings, and every multiplicative statistic erase the signed data at the actual source. | Exact recovery classifications; logarithmic moments; smooth detectors. Multiplicative observation is the gauge projection: a source is determined by its multiplicative data exactly up to a gauge twist. Künneth, Adams and symmetric-power count positivity collapse to point-count positivity. | Orientation-retaining, gauge-charged source readings. |
| **3.2 Aperture/height escape** | Open | Finite windows, radii and prefixes admit mimics. | Cofinal criteria; quantitative visibility. | Containment along the full exhaustion. |
| **3.3 Norms and completions** | Resolved | One norm does not replace another without a theorem; closure can lose payment. | Origin-`L²` supports no faithful reading; golden payment domain nonclosed with one-dimensional dual; the blind ideal is closed in the natural Fréchet topology, closed in critical-data topologies iff RH, and synthesized by jets plus the Poisson boundary (critical jets give the full-jet blind ideal; value-blind iff off-line zeros are simple). | — |
| **3.4 Shared signed resources** | Open | Local payments can spend one surplus twice. | Frustration and holonomy law; exact descent (excess `kB`); horizon-uniform Schur payment; two-tower box law. | One continuum budget (B1.3, B3.8). |
| **3.5 Endpoint logarithms** | Open | Pole cancellation alone does not pay the endpoint. | Partial-pole-sum logarithmic law; Dini thresholds. | The logarithmic remainder for a new source. |
| **3.6 Moving horizons and origins** | Open | Generic below-half interchange and unbounded drift fail. | Priced shifts; reset-origin limits `(K + cKmax)/(1+c)` faithful; raw moving origins add constant mass. | Source-specific moving-tail bounds. |
| **3.7 Damping topology** | Open | Hilbert–Schmidt and inverse estimates fail before boundedness does. | Chain bounded, not Hilbert–Schmidt, at half damping; hypercube endpoint bounded for all squarefree `P`; integer local exponents below half. | Signed sub-half estimates (B3.11). |
| **3.8 Multiplicity and index** | Open | Packet `m²`, Weil `m`, distinct index and reciprocal depth are different currencies. | Meyer: numerical = principal ⇔ simple; quotient index finite or continuum; synthesis separates full-jet and value-blind ideals exactly at multiple off-line zeros. | Keep trace data separate from operator-norm data. |
| **3.9 Observation cost** | Open | Recovery at arbitrary phase has no universal linear horizon. | Explicit recurrence recovery. | A source-specific horizon bound. |
| **3.10 Filters and hulls** | Open | Invertible critical-Wiener filters preserve admission classes. | Unit-orbit dictionaries; Möbius ≅ Liouville cofactor modules; visible-pole bounds transfer along unit orbits. | Non-unit repair preserving the source. |
| **3.11 Coupled quantifiers** | Open | Weil margin → heat-Hankel couples degree and time. | Exact bridges with costs kept. | Decoupling (B3.12). |
| **3.12 Residual reconstruction** | Open | Algebraic injectivity gives no bounded inverse. | Kernel of the renormalized residual `= ℝ q_ε`; contraction calculus; cofactor-graph closedness ⇔ a uniform estimate. | Quantitative inverse (B3.3). |
| **3.13 Joint orientation of families** | Open | Individually positive orbits can choose incompatible endpoints. | Common-endpoint classification; spline-orbit index ≤ 1 ⇔ RH. | A compatible source family (B3.10). |
| **3.14 Average to selected heights** | Sharpened | Averages and almost-every statements control windows and proportions, not every zero; the aperture cost `e^A` multiplies the off-line field. | Averaged positivity on every window `Γ^{99/100} ≤ H ≤ Γ/8`; the off-line field `Φ` reads the negative part at each height and exceeds `η` on measure `≤ CH/(η log Γ)`; nonnegative tests are positive at all but `CH/η` zero ordinates. A zero's witness persists on length `2(1 − r/Z)/A`, so at `A ≍ log Γ` exclusion needs exceptional sets below the zero spacing. | Selection to every height and signed test (B1.4). Windows `Γ^{1/2+ε}` are W6; shorter windows need B2.10. |
| **3.15 Escape states of actual limits** | Sharpened | Subsequential cofactor limits can differ along horizons; escape is classified only on finite exponent windows. | Record minima `K_pp ≥ p^{2ε−2}`; singleton or continuum; eigencharacters `p^{−s}`, `s ≥ ½`; visible-pole index; on power rows the renormalized cofactor acts by `ζ(s+ε)`, and on every finite window `F ⊂ {½ ≤ Re s < 1−ε}` its power-log eigenspace has dimension `Σ ord_{s+ε} ζ` (translated zeros); Euler laws at `2` and `3` fix the pole trace; the eta tail is a dilation-regularity question; white noise survives. | Completeness: are actual escape modules generated by these eigenstates (B3.2, Q1)? W8 first. |
| **3.16 Prime-to-spectral positivity** | Sharpened | Positivity is known on the prime side of the explicit formula and is the theorem on the spectral side. | Prime measure positive; spectral measures ⇔ RH; the prime-free gap lies on the positive side. Positive-definite dilation functions split into an archimedean part on the Kronecker line and a Kronecker-null part; integer and Bost–Connes successors see only the null part; Weil's atomic spectrum carries no successor [S]. | A self-dual identity with its gap on the spectral side, or a structure coupling the archimedean and null components (B3.23). |
| **3.17 Archimedean-line threshold** | New | The archimedean line computes gauge moments only below `2rX^k ≤ 1`; beyond it the excess is the near-incidence form, gauge charge whose value at the point `0` is unknown. | Windowed moment = gauge moment + near-incidence; nonnegative sources are the worst case of their orbit; the coalescent surplus meets every budget at Haar-almost every twist. | A gauge-charged estimate beyond the threshold at the point `0` (B3.20, B3.24). |

Sources: [origin obstruction](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/OriginHilbertCohomologyObstruction.lean), [blind-ideal topology](../../../formal/GaloisForLFunctions/ArithmeticPositiveDuality/TheBlindIdealIsClosedOnlyWhereOffLineZerosAreSeen.lean), [synthesis](../../../formal/GaloisForLFunctions/ArithmeticPositiveDuality/SpectralSynthesisInTheBlindIdeal.lean), [payment domain](../../../formal/GaloisForLFunctions/BiarithmeticGeometry/CriticalContinuousDual.lean), [shared budget](../../../formal/GaloisForLFunctions/BiarithmeticGeometry/SharedBudgetDescent.lean), [record minima](../../../formal/GaloisForLFunctions/ArithmeticDefectRigidity/RecordMinimaForceInfiniteCofactorLimits.lean), [eigenstates](../../../formal/GaloisForLFunctions/ArithmeticDefectRigidity/CofactorEigenstatesSplitOverTranslatedZeros.lean), [two Euler factors](../../../formal/GaloisForLFunctions/ArithmeticDefectRigidity/TwoEulerFactorsDetermineThePoleTrace.lean), [eta transform](../../../formal/GaloisForLFunctions/ArithmeticDefectRigidity/TheEtaRenormalizationIsPoleFree.lean), [witness persistence](../../../formal/GaloisForLFunctions/ArithmeticCorrelationGeometry/TheWitnessOfAZeroPersistsForTheReciprocalAperture.lean), [archimedean line](../../../formal/GaloisForLFunctions/ArithmeticCorrelationGeometry/TheThresholdIsThePriceOfTheArchimedeanLine.lean), [Kronecker split](../../../formal/GaloisForLFunctions/ArithmeticPositiveDuality/TheKroneckerDecompositionOfPositiveDefiniteFunctionsOnQ.lean), [both sides](../../../formal/GaloisForLFunctions/ArithmeticPositiveDuality/PositivityOnBothSidesOfTheExplicitFormula.lean), [Künneth collapse](../../../formal/GaloisForLFunctions/ArithmeticKunnethTheory/KunnethPositivityIsPointCountPositivity.lean).

## 3. Wall 14 — realization, invariants, correspondences and forcing

| Face | Status | Obstructed shortcut | Established boundary / survivor | Missing construction |
|---|---|---|---|---|
| **14.1 Capacity and limits** | Open | Fixed finite passive carriers; trace-class transport; a prescribed gap; finite-dimensional affine-unitary carriers. | Growing carriers; `det₂` renewal; nonlocal ports. | A source-preserving limit with orientation. |
| **14.2 Algebra without orientation** | Sharpened | Functional equation, integrality, finite-rank Frobenius, λ-ring or Rosati data, each separately; positivity of products of counts. | Rosati cones have Bézout without unitarity; genus-one Hasse = degree positivity of `ℤ[F]`; Hecke graphs of `ℤ` have no theorem of the square; integer positive-definite functions are sign characters; Künneth–Adams and symmetric-power count positivity = point-count positivity, passed by the golden datum. | An orientation principle; positivity of correspondences, not of products (14.16). |
| **14.3 Detector without producer** | Open | A zero-indexed object proves its own input. | Exact depth diagnostics. | Construction first, sign second (B1.6). |
| **14.4 Effectivity** | Open | Naming an ample cone or imposing RR as a field. | Exact source RR; reserve rigidity; majorants give Bézout, never RR; Meyer trace RR, Bézout ⇔ RH. | An independent effectivity source; the surface section law (B3.5), registering oscillatory payment. |
| **14.5 Pre-divisor weld** | Open | Assuming reservoir data satisfy the global identity. | Prime and Gamma reservoir; reflection identities. | Stabilization at every spectral point. |
| **14.6 Section selectivity** | Open | Rank or count readings; Boolean `h⁰ ≤ 1`. | Source-selection obstructions. | A selective section law. |
| **14.7 Base-to-surface theta coupling** | Open | Base `h⁰` supplying the surface cone. | Theta `h⁰(d) = log θ(e^{−2d})`; RR; Mellin to completed ζ. | Surface coupling (B3.5). |
| **14.8 Blind-carrier exhaustion** | Sharpened | Positivity on a carrier blind by construction; zero-free-region transfers. | Maximal blind ideal: all jets, restricted geometry, `= ⊤ ⇔ RH`, natural-closed, synthesized by jets plus the Poisson boundary. The left-blind ideal is positive, not blind, and `= ⊤ ⇔ RH`. `ArithmeticForcesBlindness` is a transfer from a zero-free region. | A forcing law with input outside 14.10–14.15 (B1.6). |
| **14.9 Positivity–faithfulness dilemma** | Open | Operator-norm faithful positivity used for RH alone. | Faithful degree ⇔ RH + simple; trace-bounded ideal reaches RH alone. | RH routes through trace-bounded data. |
| **14.10 Carrier positivity** | Sharpened | Forcing inside quadratic positivity on carriers. | Sharp-stable positive ideals are blind; positive ideals without sharp stability are half-blind; channels coupled by divisor multipliers on a point-stable carrier force isotropy for `K_ρ(a,b) = m_ρ conj τ_{ab}(ρ*) + m_{ρ*} τ_{ba}(ρ)`, and `K_ρ = 0` on all tuples. Height-side coupling splits into rational fibres; in completed systems it gives boundary capacity only. | Positivity on a carrier not closed under point convolution, with non-isotropic fibres, or a universal isotropy theorem (B3.17, Q2). |
| **14.11 Multiplicative forcing** | Resolved | Imported regions read as forced; finite or coupled certificates read as beating growth; quantization at the critical line. | Boundary: forcing law with each invariant necessary; capacity `⌊k/2⌋`; total mass `≤ D(0)/2`; Baire regularity; decay-exponent law; locally finite configurations realized by one Dirichlet series and by integral Euler products over the rational primes [S]; families: only the two-torsion (Siegel) exception, realized at every depth. Interior: Fejér barrier, width `(√B−√A)²/G`, cap `(3−2√2)/(2L)`, fibre splitting, dlVP optimal; quantum budget with no quantized inequality at the critical line. | — Better growth input (B2.8) lies outside multiplicative positivity. |
| **14.12 Completeness of invariants** | Resolved | Assuming a full-invariant countermodel exists, or that none does. | Positive measure on `[1,∞)` + degree-one theta law ⇒ ζ; finite order suffices (strip decay by Phragmén–Lindelöf); an `L¹` FE defect bounds off-lattice and tent masses; Beurling prime measure ⇒ `Λ/log`; discrete systems ⇒ rational primes. Relaxations: pole order 2 (real pair; refunded quartet, both as completed positive systems), pole order 3, strip poles, no FE, no positivity, and the Siegel datum `ζ(s)/ζ(s+1−β)` for the boundary invariants. | — |
| **14.13 Zero–pole budget** | Resolved | Pole order as irrelevant, as payment for ζ's own zeros, or as an absolute budget. | Conservation identity exact; absolute budget false; pole order one rigid, two admits every off-line type. Completed systems: `4 ord_{1/2} + 8Σ ord_x + 5d < 9κ`, so `κ = 1` forces `d = 1` and no real zeros; sharp `⌊κ/2⌋` collar capacity at finite height without separation; the κ = 1 collar is zero-free. Gauges without an archimedean factor are polynomials of degree `2κ`. | — Payment of ζ's own zeros is 1.16. |
| **14.14 Base for coefficient systems** | Sharpened | Amplifying ζ itself: harmonic twists, tensor powers, family averages; grading by pole order. | `5d < 9κ` excludes conductor at `κ = 1` (Dedekind ζ_K fails it); the κ = 1, d = 1 class is expected to be `{ζ}` [R] (W11); relative powers of ζ are ζ; products see depth only through total length. Over `𝔽_q` (Deligne): even tensor powers over a curve have nonnegative traces and a fixed base loss. | A base outside conductor-one completed positive systems, with nonnegative even tensor powers and computable pole part (B3.19). |
| **14.15 Successor coupling** | Resolved | Prescribing the successor of an affine positive-definite function to constrain Weil's dilation correlation. | Affine positivity is induced from the dilations; the integer successor forces the Hecke weight, is incompatible with dilation continuity and forces a Kronecker-null dilation spectrum; Hecke states are positive iff `s ≥ 1/2` and Haar-singular at `s ≤ 1/2` [S]; atomic archimedean spectra carry only trivial successors. | — The coupling of the archimedean and finite components is 3.16 (B3.23). |
| **14.16 Correspondence ring** | New | Using dilation or Hecke graphs over `ℤ` as Weil's correspondences on `C × C`. | Lefschetz sequences `c_m = W(T_{p^m} g, g)` are the analogue of `N_m − q^m − 1` and read `Δ` exactly; RH ⇔ the Castelnuovo–Severi inequality on `{g, T_{p^m} g}`. Genus-one graph classes satisfy the theorem of the square; the Hecke graphs of `ℤ` satisfy no parallelogram relation modulo fibres. | A ring of correspondences with a theorem of the square (B3.22, Q3), then a section count giving a fixed budget (B1.9). |

Sources: [maximal blind ideal](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/MaximalBlindIdealOfTheMeyerSource.lean), [isotropy](../../../formal/GaloisForLFunctions/ArithmeticPositiveDuality/CoupledPositivityIsIsotropy.lean), [forcing transfer](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/ArithmeticForcesBlindness.lean), [boundary completeness](../../../formal/GaloisForLFunctions/MultiplicativePositivityGeometry/BoundaryCompleteness.lean), [boundary capacity](../../../formal/GaloisForLFunctions/MultiplicativePositivityGeometry/BoundaryZeroCapacity.lean), [arithmetic Bochner](../../../formal/GaloisForLFunctions/MultiplicativePositivityGeometry/ArithmeticBochner.lean), [Siegel exception](../../../formal/GaloisForLFunctions/MultiplicativePositivityGeometry/SiegelException.lean), [growth-to-forcing](../../../formal/GaloisForLFunctions/MultiplicativePositivityGeometry/GrowthToForcing.lean), [quantum budget](../../../formal/GaloisForLFunctions/ArithmeticPositiveDuality/TheQuantumBudgetOfMultiplicativePositivity.lean), [sharp collar](../../../formal/GaloisForLFunctions/StripBochnerWeilForcing/SharpHalfPoleCollar.lean), [reflection rigidity](../../../formal/GaloisForLFunctions/StripBochnerWeilForcing/StripReflectionRigidity.lean), [gauge and refund rigidity](../../../formal/GaloisForLFunctions/StripBochnerWeilForcing/InfiniteGaugePoleRigidity.lean), [finite-order rigidity](../../../formal/GaloisForLFunctions/ArithmeticPositiveDuality/PositiveMeasureRigidityFromTheBareFunctionalEquation.lean), [FE stability](../../../formal/GaloisForLFunctions/ArithmeticPositiveDuality/ApproximateFunctionalEquationNearCounting.lean), [Hecke threshold](../../../formal/GaloisForLFunctions/ArithmeticPositiveDuality/TheCriticalLineIsThePositivityThresholdOfTheIntegerSuccessor.lean), [atomic successor blindness](../../../formal/GaloisForLFunctions/ArithmeticPositiveDuality/AnAtomicArchimedeanSpectrumBlindsTheSuccessor.lean), [graph degrees](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/TheDefectOfAGraphIsTwiceItsDegree.lean), [Lefschetz ratios](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/OffLineZerosAreLefschetzRatios.lean), [theta sections](../../../formal/GaloisForLFunctions/ArithmeticOrientationGeometry/TheThetaH0OfSpecZ.lean).

## 4. Resolved local walls

A resolved local passage is not a research task.

| Local question | Disposition | Remaining wall |
|---|---|---|
| Summation-scope "defects" (BVI, APT, ACS) | Never existed: Mathlib parses the `∑` body at precedence 67. | — |
| Balanced Möbius, centred-prime band, Vaughan power improvements ⇔ `Θ < 1` | Established. | 1.0 |
| Vaughan at and above half damping | Admission; Gram rank two; rank-three ray at `ε = 1/2`. | 1.8 below half |
| Filtered Weil coercivity on `[Γ, 2Γ]` | Complete. | 3.14 |
| Short-window averaged positivity, `Γ^{99/100} ≤ H ≤ Γ/8` | Complete. | 3.14 (W6 to `Γ^{1/2+ε}`) |
| Positivity at almost every zero ordinate for nonnegative tests | Complete, with the off-line-field floor. | 3.14, 1.3 |
| Polar versus full ground-energy rate | Equal. | 1.11 |
| Maximal sharp-stable positive Meyer ideal | Identified, maximal, natural-closed, synthesized. | 14.8 |
| Coupled positivity on point-stable carriers | Isotropy, not blindness. | 14.10 |
| Spectral synthesis in divisor-order ideals | Complete. | — |
| Boundary-line forcing, capacity, regularity, realization | Complete, each invariant necessary. | 14.11 |
| Interior multiplicative forcing by finite or coupled certificates | Excluded beyond growth input. | B2.8 |
| Quantum budget of multiplicative positivity | No quantized inequality at the critical line. | 14.16, 14.14 |
| Coupled height channels in completed systems | Sharp `⌊κ/2⌋` collar, no separation; κ = 1 collar zero-free. | 1.15, B3.18 |
| Real zeros of completed positive systems | `5d < 9κ` budget; none at `κ = 1`. | — |
| Absolute pole-order budget | False; conservation identity exact. | 1.16 |
| Rigidity threshold of positive relative deformations | Pole order one rigid; two admits every off-line type. | 1.16 |
| Invariant completeness in degree one | Rigidity, finite-order form, `L¹` stability, relaxation models. | 14.13 |
| Prescribed successor as a constraint on Weil's correlation | None: Kronecker-null spectra, atomic blindness. | 3.16 |
| Positive self-dual measures with a gap | Unit gap ⇒ Dirac comb; wider ⇒ zero; narrower ⇒ non-combs. | 3.16 |
| Augmentation as the escape picture | Excluded as unique state. | 3.15 |
| Translated zeros as escape eigenstates on finite windows | Complete. | 3.15 (completeness) |
| One Euler factor fixing the pole trace | False (periodic ghost); two factors suffice. | 3.12 |
| Depth homogeneity of moments and products | Proved. | 1.15 (other classes), 1.17 |
| Lefschetz receivers at one prime | Complete: growth `p^{Δm}`, ratios, one-sided at two primes [S], tower laws. | 1.17, 14.16 |
| Half-damping hypercube endpoint; integer local exponents below half | Bounded; proved. | 3.7 |
| Finite-level weight existence | ⇔ RH. | 1.3 |
| Large-height head repair; local divisor repair; Hermite barrier and optimum | Complete. | 1.14 |
| PA order-24 finite moment sign | Closed by kernel-checked rational enclosures. | 1.6 |
| SSA odd-shift `1/3`, lag-2 `1/4` floors | Exact. | B3.13 |

## 5. Scoped obstruction register and positive survivors

These distinctions govern which mechanisms may be proposed. None retires a live route.

| Mechanism excluded or limited | Positive survivor / permitted target |
|---|---|
| Positive exponential aperture floor | Finite-aperture positivity; doubly exponentially vanishing floors; graded negative floors. |
| Permanently freezing finitely many primes | The moving prime-threshold ladder. |
| Eventual all-height phase saving | Single-height phase-selective law; averaged positivity. |
| Average or almost-every-height positivity used to exclude an individual zero | Short-window averages, the off-line-field floor and zero-ordinate positivity; exclusion needs exceptional sets below the zero spacing (witness persistence `2(1 − r/Z)/A`). |
| Nonnegative-test positivity read as full-cone positivity | Zero-ordinate and positive-measure height positivity for nonnegative tests of bounded shape. |
| Single-channel sharp-stable positive ideal as forcing carrier | Half-blind and left-blind ideals; coupled carriers (14.10). |
| Coupled point-stable carriers as forcing carriers | Isotropy of off-line fibres; non-point-stable carriers (B3.17). |
| Multiplicative (gauge-invariant) data as a selector of the actual source | The gauge-charged structures: archimedean place, additive relations, boundary of finite presentations. |
| Haar-typical or almost-sure cancellation as a bound at the gauge point `0` | The a.e. square-root law and its exceptional representative (Liouville twin). |
| Moment amplification, tensor products or relative powers as a source of a rate | Linear-loss law; a fixed-budget correspondence or gauge-charged structure (1.17). |
| Künneth, Adams or symmetric-power count positivity as purity | Point-count positivity; correspondence positivity on spans. |
| Harmonic coupling, family averaging or absolute tensor powers as depth amplification | The loss law as a theorem per class (W9). |
| Prescribed integer or Bost–Connes successor as a constraint on Weil's correlation | Hecke threshold `s ≥ 1/2`; Kronecker split; continuous archimedean spectra (B3.23). |
| Free affine extension as forcing | Source-prescribed mixed data that couple archimedean and null components. |
| Absolute pole-order budget `ind₋ ≤ ord₁F − 1` | Conservation identity; lower bounds `ind₋(W_ζ) ≥ R_off − I_off`. |
| Pole order as payment for ζ's own off-line zeros | Dominated payment of inserted zeros; oscillatory payment (1.16). |
| Positive relative deformation of ξ at pole order one | `E = cξ`; pole order two admits every off-line type. |
| Completed positive systems at `κ = 1` as a family | Expected to be `{ζ}` (W11); a base must leave the class (14.14). |
| Multiplicative positivity as a source of a quantized strip inequality | Objects outside multiplicative positivity (14.14, 14.16). |
| Prime-side positivity plus the prime-free gap as spectral positivity | Uniform local mass bounds only; the two-prime Bochner receiver. |
| Harmonic positivity with a double pole or harmonic poles | Simple pole + pole isolation + integer orders force the boundary. |
| More finite frequencies against a fixed growth payment | Exact width `(√B−√A)²/G`; better growth input. |
| Imported zero-free collar or zero-free-region transfer read as forcing | Classical regions with explicit growth input; the κ = 1 completed-system collar. |
| `Λ ≥ 0` + exact FE without the simple pole or strip holomorphy | `CompletedPositiveSystem 2 1` realizations; strip-pole quartets. |
| Boundary invariants without the sign of ζ on `(0,1)` | The Siegel datum `ζ(s)/ζ(s+1−β)`; real-zero budget for completed systems. |
| Over-regular count with the FE | Counts fluctuate at least like `⌊x⌋`; positive measures with the theta law are rigid. |
| Signed coefficients with the theta law | Only `Σ a_n sinc²(λ_n) = 0` survives. |
| Non-monomial universal positive reflector | Source-specific cofactor information. |
| One Euler factor as pole-trace selector | Two incommensurable factors. |
| PSD + dilation + antipodality as escape exclusion | Finite-window eigenstate classification; completeness (B3.2). |
| Augmentation as unique escape state | Record-minimum limits with positive diagonals. |
| Raw moving origins as fixed-origin limits | Reset-origin faithful mixtures. |
| Finite-dimensional affine-unitary successor carrier | Infinite-dimensional carriers only. |
| Absolute Vaughan budget as power saving | Signed remainder `≤ CT^{1−2ε}`. |
| Finite readings (with mass) as Bézout source; positive quadratic majorant as RR | Infinitely many degrees; Bézout and ampleness only. |
| Origin-`L²` completion; Wiener closure of payment | Graph topology retaining jets and payment. |
| Finite-aperture negative index as global purity | `D` finite ⇔ eventual confinement; RH ⇔ `D < 2`. |
| Hecke graphs of `ℤ` as correspondences with a theorem of the square | Genus-one graph classes; an enlarged ring (B3.22). |
| Zero-indexed action (PW-B) as construction | Independent realization required. |

### Catalogue crosswalk

The 44 mechanism codes in the [killed-routes catalogue](../rh-killed-routes.md) map as follows. This is navigation, not re-certification of legacy entries.

| Codes | Family | Positive direction |
|---|---|---|
| WIP, INT, DEF | Integrality, finite-rank purity, deformation-stable inequalities | 14.2, 14.12, 14.13, 14.16 |
| ODR, HCT, WHL | Drift, transport, endpoint poles | 3.5–3.7 |
| LGP, ADJ | Local payment; cross-prime majorants | 3.4 |
| PAF | Positive aperture floors | 1.13 |
| AUT, SEL | Automorphic gaps and scattering poles | 14.1–14.3 |
| LLM, UCF, HUS | Averages or reflection-even readers | 3.1, 3.14 |
| GEN | Fixed-part localization | 3.8 |
| TEQ, CAL, JPR, HFR, CCP | Equilibrium, collisions, degree, parity | 1.2, 1.6 |
| TWN, NEV | Unconstructed roots, termwise signs | 1.5, 14.3 |
| ISG, FPR, TRC, GAP, PTR | Fixed or local carriers | 14.1 |
| SRP, APW, CRT | Pole weight, perturbed sources, finite mimics | 1.4, 3.2 |
| BAG, RAW | Finite Euler recurrence; unregularized series | 1.1, 1.2 |
| R1, R2, R3 | Trace, renewal or quantization forcing its own defect | 1.2, 14.3, 14.13 |
| BD, COS, POI | Markov kernels, local inversion, Poisson transport | 3.3, 14.1 |
| DSA, TOR, REF, CPF, TMD, TK | Legacy entries, not re-certified | — |

## 6. What counts as crossing a wall

- **Wall 1.** Insert a newly proved source estimate into an existing receiver with every tail and quantifier intact. Because of face 1.0, any graded gain beyond Vinogradov–Korobov is a fixed strip. A new mechanism must contain a term that does not scale with its amplification (1.15, 1.17), must be gauge charged (1.18), and for ζ's own zeros must measure oscillatory payment, not pole charge (1.16).
- **Wall 3.** Prove a transfer, sharp boundary or quantitative reconstruction on a stated class, norm and limit, and show that the source satisfies its hypothesis. For 3.14, selection below the zero spacing; a shorter window is graded progress. For 3.15, escape completeness; finite-window eigenstates are established. For 3.16, a structure coupling the archimedean and Kronecker-null components. For 3.17, a gauge-charged estimate at the point `0` beyond the threshold.
- **Wall 14.** Construct the arithmetic object independently and prove fidelity at the strength needed, then a forcing law placing the source in the maximal blind ideal with input outside every mapped class: blind, half-blind or isotropic carrier positivity (14.10); finite or height-coupled multiplicative positivity (14.11); linear rigidity in the coefficient measure (14.12); pole order (14.13); successor prescription (14.15); gauge-invariant data (1.18). The law must fail on the relaxation models and the Liouville twin, reproduce κ = 1 rigidity and `5d < 9κ`, and reach ζ's own zeros through a term that does not scale: a correspondence ring with a theorem of the square and a budget (14.16), a base (14.14) or Riemann–Roch on the scaling surface (14.4). Blindness of a sub-carrier does not cross the wall; neither does a transfer from a zero-free region.
