# Walls ledger

Status: 2026-10-25, corpus snapshot `0fa51c933`. Every obstacle in the corpus belongs to one of three core families:

- **Wall 1 — critical arithmetic sign.** Estimates and signs at the critical endpoint.
- **Wall 3 — transfer.** Readings, norms, completions, limits, shared budgets and selection.
- **Wall 14 — realization and forcing.** Faithful arithmetic objects, orientation, and the forcing of the actual source into its blind carrier.

**Organizing principle.** Every unconditional positivity theorem is positivity on a carrier blind to off-line zeros. For single-channel sharp-stable carriers this is now a theorem (14.10). RH says that the actual source is itself blind. Wall 1 measures blindness as a rate, Wall 3 governs how blindness transfers between readings and limits, and Wall 14 asks for the arithmetic mechanism that forces the source into its blind carrier. The only forcing mechanism proved so far is multiplicative and works on the boundary line (14.11); its interior continuation meets the first rung of Wall 1 (1.0).

Companions: [complete report](hard-obstacles.md), [summary](hard-obstacles-summary.md), [route unification](route-unification-ledger.md). Evidence: Lean corpus search, statement reading and umbrella reachability, logged in `logs/review-2510-update/`. No compilation. A countermodel excludes the mechanism it was built against, not every route that touches that wall.

**Status column.**

- *Open*: the wall stands unchanged.
- *Refined*: a new sharp boundary or survivor changes what must be proved.
- *New*: a face added since the morning version of this ledger.
- *Closed*: a local wall that is solved, retired, or shown never to have existed.

## 1. Wall 1 — critical arithmetic sign

With `Δ = sup_ρ |Re ρ − 1/2|`, a receiver bounded at a fixed rate `σ < 1/2` gives `Δ ≤ σ`, which is quasi-RH; RH is `Δ = 0`. Squared-energy receivers carry twice the exponent; Li reads reciprocal depth.

| Face | Status | Present obstacle | Established boundary / survivor | Missing input |
|---|---|---|---|---|
| **1.0 Quasi-RH first rung** | Refined | Graded cancellation receivers and the multiplicative forcing law have no target between Vinogradov–Korobov and a zero-free strip. | [L] fixed-strip equivalences: balanced Möbius statistic, centred-prime band, short-window Möbius/prime saving, Vaughan empty leg, JAS level-one budget, PBM graded abscissa, WL rate `σ`, RW/ACS rate-`σ` floors. [L] Unconditional regions: dlVP, Littlewood, VK. | A fixed zero-free strip (B2.1), or a non-graded (averaged, escape, rigidity) handle. |
| **1.1 Critical signed cancellation** | Open | Lag, Abel, history, series and bilinear bounds must reach rate zero with every counterterm and tail paid. | Exact endpoint laws; the high-zero tail is `O(1)`; all-modulus `Q^{−δ/32}` saving; Heath–Brown all-length and sharp `S₂`; `M(x) = Ω±(√x)`. | Source cancellation at every positive slack (B1.1). |
| **1.2 Axis orientation** | Open | A nonnegative defect, winding count or faithful spectrum does not force line support. | Ward cap and trace; cubic trace = winding; subharmonic Newton margin; KKL positive-time horizon. | Vanishing or a forcing all-height sign (B1.6). |
| **1.3 Complete Weil positivity** | Refined | The low and mixed sectors are unsigned pointwise at large aperture. | Pointwise windows `3/10` full, `181/500` odd, `(log 2+1/50)/2` primitive. Averaged positivity at aperture `κ₀ log Γ`; subpower coercivity up to `X ≤ Γ^{4/3}` [L]. Finite-level weight existence ⇔ RH [L]. | Sign at every aperture (B1.3), or selection (3.14). |
| **1.4 Arithmetic cone membership** | Open | Identifying the source is not proving its positivity. | Pair tests recover every node; every single-node perturbation fails; exact one-sided cone classification. | `Λ` in the full cone, i.e. RH. |
| **1.5 Contrast equality** | Open | Exact Jensen, BSY and Li accounting leaves a residual. | Contrast and zero-sum identities; reciprocal depth `≤ 1/431`, maximal `β < 1/300`. | Vanishing or a subexponential floor (B1.7). |
| **1.6 Required uniformity** | Open | Fixed rank, order, history or height does not reach the receiver's quantifier. | All-rank orthant sign; PA: RH ⇔ nonnegativity below each order's threshold; fixed-rank coercivity. | All-rank, order-uniform or common-time estimates (B1.5, B3.12). |
| **1.7 Amplification** | Closed as an obstruction | Raising a receiver to a power multiplies its rate. | Exact exponent bookkeeping. | New correlation information, not repetition. |
| **1.8 Critical pronic energy** | Refined | Horizon-uniform signed energy at cofinally small damping. | Vaughan: leading Gram paid. Subcritical moving-cutoff limits completely classified (rank ≤ 1, compact countable amplitude set, accumulation only at 0) [L]. Product horizon `o(T^{1−2ε})`; absolute budget has the trivial exponent. Size-cutoff receiver paid on the exterior and at `ε = 1/2` for every squarefree support [L]. | Signed interior energy below `T^{1−2ε}` (B1.2). |
| **1.9 Signed continuation** | Open | Integrated signed loss must stay bounded uniformly in the horizon. | Canonical corrector; log-height identity; integer local exponents of paid patterns below half damping [L]. | Flux control at closing damping (B1.2). |
| **1.10 Absolute compensation** | Refined | A vanishing relative error coexists with unbounded raw energy. | Forcing = power + bounded remainder; residual pairing → `−1` on escape; quantile and moving localizations keep the antipodal density. Zero-cofactor dichotomy and rank-one classification of actual limits [L]. | Absolute energy bound or escape exclusion (B1.2, B3.2). |
| **1.11 Rates and clusters** | Refined, nearly closed | Ground-energy rate versus zero width. | `groundRate = polarRate` unconditionally; `CompensatedWidthFloor(1/2)`; `RH ⇔ groundRate = 0` [L]. Bounded local depth mass gives `polarRate = Δ`. | Only `polarRate = Δ` remains (B3.1). |
| **1.12 Interior anti-alignment** | Open | The gap `θ(ε,t) < 1` between the proved collars. | High-height and small-damping collars; planted factors keep the collars. | Interior decorrelation (B1.1, B2.6). |
| **1.13 Aperture shell flux** | Open | A strictly decreasing ground energy can cross zero. | Prime-threshold ladder: zero birth jumps; RH ⇔ cumulative frozen relaxation `≤ μ(3/10)`; collar bound `e^{−a}[ψ(e^{2c})−ψ(e^{2a})]`; permanently frozen prime families are eventually negative. | Signed collar estimate along the moving ladder (B3.6). |
| **1.14 Actual divisor heat sign** | Open | Local repair costs do not sign actual Ξ heads. | Every positive heat repairs every sufficiently high head [L]; sharp Hermite barrier and optimum; universal reflectors are positive monomials; `Λ < 1/8`. | Zero-heat sign on the bounded-height × small-heat residual region (B1.5, B3.9). |
| **1.15 Selected-height estimates** | Merged into 3.14 | — | — | — |

Key sources: [endpoint](../../../formal/GaloisForLFunctions/BiScaleUncertainty/WeilLagCriticalDeficitEndpointAndLimitLaw.lean), [balanced statistic](../../../formal/GaloisForLFunctions/BezoutValuationIncidence/TheBalancedStatisticIsTheQuasiRiemannHypothesis.lean), [filtered Weil](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/ZeroDensityFilteredWeilPositivityAndCoercivity.lean), [rate equality](../../../formal/GaloisForLFunctions/ArithmeticContinuationAndCriticalEnergy/UnconditionalEqualityOfPolarAndFullGroundEnergyRates.lean), [shell ladder](../../../formal/GaloisForLFunctions/ArithmeticContinuationAndCriticalEnergy/ThresholdVanishingAndCollarDominanceOfThePrimeShell.lean), [radius head](../../../formal/GaloisForLFunctions/ArithmeticLocalDivisorGeometry/RadiusHeadHeatPositivity.lean), [Vaughan limit set](../../../formal/GaloisForLFunctions/BezoutValuationIncidence/TheSubcriticalVaughanGramLimitSet.lean), [VK region](../../../formal/GaloisForLFunctions/RHTower/Sieve/VinogradovKorobovZeroFree.lean).

**Aperture ceiling.** `μ(A) ≤ K exp(11A/2 − πe^{2(A−2)})`. No positive exponential floor exists. Finite-aperture positivity and doubly-exponentially vanishing floors remain admissible.

## 2. Wall 3 — transfer: readings, norms, limits, budgets, selection

This wall explains why an attractive estimate does not transfer. Closing a face here enables a route but supplies no Wall 1 sign.

| Face | Status | Present limitation | Established boundary / survivor | Missing transfer |
|---|---|---|---|---|
| **3.1 Readings** | Open | Magnitudes, orientation-blind samples, complete moment families and finite linear readings (even with exact `L²` mass and smoothness) erase the decisive signed data. Weil energy is unbounded on every finite reading kernel at every aperture. | Exact recovery classifications; logarithmic moments; smooth detectors. | Source readings that retain orientation, with affordable conditioning. |
| **3.2 Aperture/height escape** | Open | Finite windows, radii and prefixes admit mimics. | Cofinal criteria; quantitative visibility; admission-or-escape alternatives. | Containment along the full exhaustion. |
| **3.3 Norms and completions** | Refined | A derivative, mass, quotient or graph bound cannot replace another without a theorem. The origin-`L²` completion supports no continuous faithful reading [S]. | Fixed-aperture CHMD completion; sharp generator passage; compact-`L²` Suzuki limits; exact `H¹` floors. The maximal blind ideal is a complete algebraic carrier without any completion [L]. | A topology in which the maximal blind ideal is closed and exhaustion can be proved by limits (B3.4). |
| **3.4 Shared signed resources** | Open | Independent local payments can spend the same surplus twice. | Frustration and holonomy law. Exact shared-budget descent: excess `kB` on `k+1` cells. Horizon-uniform Schur payment down to a finite head. Two-tower box law. | One continuum budget (B1.3, B3.8). |
| **3.5 Endpoint logarithms** | Refined | Pole cancellation alone does not pay the endpoint. | Partial-pole-sum logarithmic law. Dini thresholds; the monotone-defect Dini law at `ε = 1/2` [L]. | The actual logarithmic remainder for a new source. |
| **3.6 Moving horizons and origins** | Open | Generic below-half interchange and unbounded drift fail. | Priced shifts; common-support limits; weighted moving-support criteria. | Source-specific moving-tail bounds. |
| **3.7 Damping topology** | Refined | Hilbert–Schmidt and inverse estimates fail before boundedness does. | Chain bounded but not Hilbert–Schmidt at `η = 1/2`. Signed hypercube form bounded at `ε = 1/2` for all squarefree `P`. Paid patterns below half damping have integer local exponents, exponent 0 off the real axis [L]. | Signed sub-half estimates in the admission norm (B3.11). |
| **3.8 Multiplicity and index** | Refined | Packet `m²`, Weil `m`, distinct-zero index and reciprocal depth are different currencies. Operator-norm faithful data additionally read simplicity. | Meyer: numerical = principal ⇔ simple; quotient index finite or continuum; finite cofactor index = joint multiplicity; collision mass `2(D+E)`. The trace-bounded maximal ideal keeps every jet and reads RH alone [L]. | Keep trace data (RH) separate from operator-norm faithful data (RH + simple). |
| **3.9 Observation cost** | Open | Recovery at arbitrary phase has no universal linear horizon. | Explicit recurrence recovery. | A source-specific horizon or conditioning bound. |
| **3.10 Filters and hulls** | Open | Invertible critical-Wiener filters preserve admission classes. | Unit-orbit and hull dictionaries; Möbius ≅ Liouville cofactor modules by unit transport; real Wiener convolution transports Grams. | Non-unit repair that preserves the source. |
| **3.11 Coupled quantifiers** | Open | Weil margin → heat-Hankel couples degree and time. | Exact bridges with the costs kept. | Decoupling, only where the receiver needs it (B3.12). |
| **3.12 Residual reconstruction and cofactor limits** | Refined | Algebraic injectivity gives no bounded inverse; coordinatewise limits do not justify infinite sums. | Common limit carries a cyclic Wiener module; full Wiener pairings pass to the limit; absolute word tail. Cofactor-graph range closed ⇔ uniform output ≤ C·input [L]. | Quantitative inverse and infinite tails (B3.3). |
| **3.13 Joint orientation of families** | Open | Individually positive orbits can choose incompatible endpoints. | Common-endpoint classification; exact finite-target index; spline-orbit index ≤ 1 ⇔ RH. | A compatible source-defined family (B3.10). |
| **3.14 Average to selected heights** | Open | The averaged side is solved at logarithmic aperture [L]. What remains is the passage to individual heights, in particular zero ordinates. Bad phases recur syndetically. | Phase-selective single-height law with explicit premises; positive-measure set of positive frequencies; bounded bad-frequency volume; eventual all-height saving is refuted. | A selection theorem (B1.4), with short windows as the graded path (B3.7, Q1). |

Sources: [origin obstruction](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/OriginHilbertCohomologyObstruction.lean), [finite readings](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/FiniteReadingsAndMassCannotSupplyBezout.lean), [shared budget](../../../formal/GaloisForLFunctions/BiarithmeticGeometry/SharedBudgetDescent.lean), [Meyer numerical radical](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/MeyerNumericalRadicalAndMultiplicity.lean), [phase-selective heights](../../../formal/GaloisForLFunctions/arithmetic-positivity-theory/SingleHeightPhaseSelectiveApertureAndPowerSaving.lean), [half-damping endpoint](../../../formal/GaloisForLFunctions/SignedSuccessorArithmetic/TheHypercubeFormIsBoundedAtHalfDamping.lean), [integer local exponents](../../../formal/GaloisForLFunctions/TransHorizonIncidenceMechanics/TheLocalExponentsBelowHalfDampingAreIntegers.lean).

## 3. Wall 14 — realization, orientation and forcing

| Face | Status | Obstructed shortcut | Established boundary / survivor | Missing construction |
|---|---|---|---|---|
| **14.1 Capacity and limits** | Open | Fixed finite passive carriers, trace-class transport, a prescribed permanent gap; finite-dimensional affine-unitary successor carriers are trivial. | Growing carriers; Hilbert–Schmidt `det₂` renewal; nonlocal ports; centered real-law limits. | A compatible source-preserving limit with orientation. |
| **14.2 Algebra without orientation** | Refined | Functional equation, integrality, finite-rank Frobenius data, λ-ring or Adams structure, Rosati positive mass, each taken separately. | Ghost and index laws. Rosati cones have Bézout without unitarity; RR is exactly the reflection condition. Genus-one Hasse = degree positivity of `ℤ[F]`; the Hecke graphs of `ℤ` satisfy no theorem of the square [L]. | An independent orientation principle; a ring of correspondences over `Spec ℤ`. |
| **14.3 Detector without producer** | Open | A zero-indexed or sign-coded object proves its own input. | Exact depth diagnostics; faithful representations. | Construction first, sign second (B1.6). |
| **14.4 Effectivity and Hasse–Weil** | Refined | Naming an ample cone, or imposing RR as a structure field. | Exact source RR at every aperture. Boundary rigidity: RR + Bézout on one cone ⇔ reserve = defect. Positive majorants give Bézout and ampleness, never RR. Meyer surface: trace RR [L]; Bézout ⇔ ampleness ⇔ RH; on the maximal blind ideal, all three hold unconditionally [L]. | An independent effectivity source; B3.5 for the surface section law. |
| **14.5 Pre-divisor weld** | Open | Assuming that reservoir data satisfy the global one-port identity. | Prime and Gamma reservoir; reflection and finite identities. | Stabilization at every spectral point. |
| **14.6 Section/count selectivity** | Open | Rank or count readings; sign-coded sections; Boolean `h⁰ ≤ 1`. | Source-selection obstructions. | A genuinely selective section law. |
| **14.7 Base-to-surface theta coupling** | Open | The base `h⁰` already supplying the surface cone. | Theta `h⁰(d) = log θ(e^{−2d})`; RR; Mellin to completed ζ. | A surface and test-component coupling (B3.5). |
| **14.8 Blind-carrier exhaustion** | Refined | Positivity on a carrier that is blind by construction (low-grid-blind tests, bounded orbits, jointly blind families, heated heads, averages). | The maximal blind carrier is identified: `meyerTraceBoundedIdeal`, all critical jets, restricted Hodge/RR/Bézout/ampleness/additive closure, `= ⊤ ⇔ RH` [L]. The operator-norm bounded carrier needs RH + simple [S]. | A **forcing law** placing the actual source in the maximal blind ideal (B1.6), with input outside 14.10. |
| **14.9 Positivity–faithfulness dilemma** | Refined | Using operator-norm faithful positivity to prove RH alone. | A faithful positive degree exists ⇔ RH + simple; Hilbert–Schmidt reserve RR ⇔ RH + simple [L]. Positive Hermitian degrees are blind [S]. The trace-bounded maximal ideal reaches RH alone with every jet retained [L]. | RH-only routes force through trace-bounded data; faithful routes must also prove simplicity (B2.3, B1.8). |
| **14.10 Single-channel exhaustion** | New | Seeking forcing inside single-channel quadratic positivity. | **Theorem [L]:** every sharp-stable right convolution ideal with nonnegative trace lies in the maximal blind ideal (`isGreatest_meyerSharpPositiveIdeal`); every scale-shift-invariant Weil-nonnegative test space is blind (`zeta_blindOffLine_of_scaleShift_subspace_weil_nonneg`). | An input outside this class: coupled channels, rigidity of invariants, or escape exclusion. |
| **14.11 Multiplicative forcing** | New | Treating an imported zero-free region as forced; finite-degree coupling against a non-simple pole or with harmonic poles. | **Theorem [L]:** harmonic positivity + simple pole + no harmonic poles + integer orders force zero order 0 on `Re s = 1` (`harmonic_quantized_zero_vanishing`); for ζ non-circularly. Sharpness models for both pole conditions; Fejér barrier `a₁ < 2a₀`. With growth input: dlVP, Littlewood and VK regions [L]. | Interior forcing beyond growth input (B3.14); the next graded rung is 1.0. |
| **14.12 Completeness of invariants** | New | Assuming that a countermodel with all of ζ's invariants exists, or that none does. | FE + decaying count error impossible; over-regular Beurling systems violate FE [L]. Hamburger for ordinary frequencies and the general-frequency Laplace step [L]; `Γ_R^d` abundance without Euler positivity [L]. No full-invariant countermodel in the corpus. | Uniqueness for FE + Beurling Euler positivity + simple pole, or a countermodel with an off-line zero (B3.15, Q2). |

Sources: [Meyer surface](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/MeyerSourceIntersectionSurface.lean), [maximal blind ideal](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/MaximalBlindIdealOfTheMeyerSource.lean), [harmonic coupling](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/HarmonicCouplingForcesSourceBlindness.lean), [faithful degrees](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/FaithfulPositiveMeyerDegrees.lean), [boundary rigidity](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/SourceConeBoundaryRigidity.lean), [graph degree](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/TheDefectOfAGraphIsTwiceItsDegree.lean), [theta sections](../../../formal/GaloisForLFunctions/ArithmeticOrientationGeometry/TheThetaH0OfSpecZ.lean), [FE and counts](../../../formal/GaloisForLFunctions/RHTower/RiemannFunctionalEquationForcesCountFluctuation.lean), [pre-divisor weld](../../../formal/GaloisForLFunctions/RHTower/XiPreDivisorReflectionDefectStabilization.lean).

## 4. Closed local walls

This table records present disposition. A solved local passage is not a research task.

| Local question | Disposition | Remaining wall |
|---|---|---|
| Summation-scope "defects" (BVI diagonal μ window, centred-prime Abel and block tails, dyadic tail, mean-rate, μ² mean, prime-channel union; ACS upper Lefschetz window sum) | **Never existed.** Mathlib parses the body of `∑` at precedence 67; under the alleged parse each statement is false and could not have been proved. | None. |
| Balanced Möbius and centred-prime band ⇔ `Θ < 1` | Established [L]. | 1.0. |
| Filtered Weil coercivity and averaged strict positivity | Complete [L]. | 3.14. |
| Polar versus full ground-energy rate | Equal unconditionally [L]. | 1.11, only `polarRate = Δ`. |
| Maximal sharp-stable positive Meyer ideal | Identified and proved maximal [L]. | 14.8, 14.10. |
| Nonvanishing on `Re s = 1` as a forcing law | Proved with sharpness models [L]. | 14.11 interior. |
| Half-damping signed hypercube endpoint (all squarefree `P`) | Bounded [L]. | 3.7 below half. |
| Local exponents of paid patterns below half damping | Integer; zero off the real axis [L]. | 3.7, B3.11. |
| Vaughan subcritical moving-cutoff Gram limits | Completely classified [L] (topology leaf [S]). | 1.8 residual. |
| Functional equation versus decaying count error | Incompatible [L]. | 14.12. |
| Sparse-spectrum annihilating tests | Constructed for `Σ|a|^{−s} < ∞`, `s < 1` [L]. | Not applicable to ζ zeros. |
| Finite-level weight existence | ⇔ RH [L]. | 1.3. |
| Large-height finite-head heat repair | Complete at every positive heat [L]. | 1.14 residual region. |
| Smoothed Landau formula | Assembled [L]. | — |
| Critical-deficit and Sobolev endpoints | Attained [L]. | 1.1, 1.3. |
| CHMD sharp windows and generator domain | Complete [L]. | Nodal sign (1.3). |
| Suzuki compact `L²`, moving window, collared noncompact limits, RH-complete tents | Complete [L]. | Sign (1.3). |
| Heath–Brown all-length and sharp `S₂` | Complete [L]. | 1.1. |
| Smooth detector at quadratic aperture | Complete [L]. | 3.1, 3.2. |
| Positive scale-stable family structure; global-index dictionary; spline-orbit index laws | Complete [L]. | 3.13, 14.8. |
| Base theta `h⁰` | Complete [L]. | 14.7. |
| Local divisor repair; Hermite barrier, optimum and extremizer | Complete [L]. | 1.14. |
| Residual/trace algebraic reconstruction; cofactor-graph closedness criterion | Complete [L]. | 3.12 (bounded inverse). |
| SSA odd-shift `1/3` and lag-2 `1/4` floors | Exact [L]. | B3.13 (complex floor). |
| Proof integrity | No `sorry`, `axiom`, `opaque` or `unsafe`. One route-adjacent `native_decide` (PA order-24 quadrature) is imported by no receiver. | W2. |

## 5. Scoped obstruction register and positive survivors

These distinctions govern which mechanisms may be proposed. None of them retires a live route.

| Mechanism excluded or limited | Positive survivor / permitted target |
|---|---|
| Positive exponential aperture floor | Finite-aperture positivity; doubly-exponentially vanishing floors; graded negative floors. |
| Permanently freezing finitely many primes | The moving prime-threshold ladder with zero birth jumps. |
| Eventual all-height phase saving | Single-height phase-selective law; averaged positivity. |
| Average used to sign a selected height | Short-window averages as a graded path (Q1). |
| Single-channel sharp-stable positive ideal as a forcing carrier | It lies in the maximal blind ideal; forcing must come from outside the class (14.10). |
| Harmonic positivity with a double pole or with harmonic poles | Simple pole + harmonic pole isolation + integer orders force zero order 0 on `Re s = 1`. |
| Imported zero-free collar read as forced | Classical regions with explicit growth input (W8(vi)). |
| Coupled off-line ceiling read as zero exclusion | Ceiling on an unsigned sum; a sign for off-line summands is still needed. |
| Over-regular count with the functional equation | Counts must fluctuate at least like `⌊x⌋`; over-regular zeros survive only without FE. |
| Non-monomial universal positive reflector | Source-specific cofactor information. |
| One-factor repair of arbitrary off-line pairs | Exact `δ² ≤ 3u²` boundary and multiplicity costs. |
| Extreme coefficient as the full heat price | Full Hermite cone optimum; masking ratio → 2. |
| Individual orbit positivity for a joint span | Common-endpoint compatibility; jointly seen index; scale-stable positive spaces are blind. |
| Finite readings (with mass, smooth) as a Bézout source | Infinitely many degrees, or exact source control. |
| Positive quadratic majorant as RR | Bézout and ampleness only; RR forces reserve = defect. |
| Origin-`L²` completion of Meyer cohomology | The algebraic maximal blind ideal; a jet-retaining topology (B3.4). |
| Positive Hermitian degree as an off-line detector | It is blind; faithful variants need simplicity. |
| PSD + dilation + antipodality as escape exclusion | Full paid-ideal annihilation and moving boundary (Q3). |
| Contraction laws + horizon order as Kronecker-point selection | Augmentation satisfies them; zero cofactor forces finite dimension; rank-one limits are augmentation or powers. |
| Diagonal power law as mixed homogeneity | Three-metric averaged repair. |
| Finite-dimensional affine-unitary successor carrier | Infinite-dimensional carriers only. |
| Absolute Vaughan budget as power saving | Signed remainder `≤ CT^{1−2ε}` with no matching lower bound. |
| Vaughan leading-order limits as residual control | Leading order fully classified; the residual below `T^{1−2ε}` is untouched. |
| Prime-subset hypercube divergence read as size-cutoff divergence | Size cutoff paid at `ε = 1/2`; forward interior open. |
| Dini or completely monotone defects below half damping | Unpaid at every `0 < ε < 1/2`; payable only at `ε = 1/2` through the Dini law. |
| Finite-aperture negative index as global purity | Index exit: `D` finite ⇔ eventual confinement; RH ⇔ `D < 2`. |
| Zero-indexed action (PW-B) as a pre-divisor construction | Exact action and exhaustion; independent realization still required. |
| Interfaces with stabilization or positivity fields | The conditional implication only. |

### Catalogue crosswalk

The 44 mechanism codes in the [killed-routes catalogue](../rh-killed-routes.md) map as follows. This is navigation, not re-certification of every legacy entry.

| Codes | Family | Positive direction |
|---|---|---|
| WIP, INT | Integrality / finite-rank purity | 14.2, 14.12 |
| ODR, HCT, WHL | Drift, transport, endpoint poles | 3.5–3.7 |
| LGP, ADJ | Local payment; unsigned cross-prime majorants | 3.4 |
| PAF | Positive aperture floors | 1.13 |
| AUT, SEL | Automorphic gaps used to locate scattering poles | 14.1–14.3 |
| LLM, UCF, HUS | Averages or reflection-even readers | 3.1, 3.14 |
| GEN | Fixed-part localization | 3.8 |
| TEQ, CAL, JPR, HFR, CCP | Equilibrium, collisions, automatic degree, parity | 1.2, 1.6 |
| TWN, NEV | Unconstructed roots, termwise signs | 1.5, 14.3 |
| ISG, FPR, TRC, GAP, PTR | Fixed or local carriers | 14.1 |
| SRP, APW, CRT, DEF | Pole weight, perturbed sources, finite mimics, deformation-blind selection | 1.4, 3.2, 14.2 |
| BAG, RAW | Finite Euler recurrence; unregularized series | 1.1, 1.2 |
| R1, R2, R3 | Trace, renewal or quantization forcing its own defect | 1.2, 14.3, 14.11 |
| BD, COS, POI | Markov kernels, local inversion, positive Poisson transport | 3.3, 14.1 |
| DSA, TOR, REF, CPF, TMD, TK | Legacy entries, not re-certified | — |

## 6. What counts as crossing a wall

- **Wall 1.** Insert a newly proved source estimate into an existing receiver with every tail and quantifier intact. A weaker estimate receives its exact weaker conclusion. Because of face 1.0, any graded gain beyond Vinogradov–Korobov is a zero-free strip.
- **Wall 3.** Prove a transfer, sharp boundary or quantitative reconstruction on a stated class, norm and limit, and show that the source satisfies the transferred hypothesis. For 3.14 this means a selection theorem; a shorter averaging window counts as graded progress.
- **Wall 14.** Construct the arithmetic object independently and prove fidelity at the strength needed: trace-bounded for RH, operator-norm faithful for RH + simple. Then prove a forcing law placing the source in the maximal blind ideal, using input outside the single-channel class (14.10). Blindness of a sub-carrier, however rich, does not cross the wall. A rigidity theorem for ζ's invariants (14.12) would not cross it either, but would make every forcing proposal that uses all invariants immune to countermodels.
