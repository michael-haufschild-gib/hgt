# Walls ledger

Status: 2026-10-25. Every obstacle in the corpus belongs to one of three core families:

- **Wall 1 — critical arithmetic sign.** Estimates and signs at the critical endpoint.
- **Wall 3 — transfer.** Readings, norms, completions, limits, shared budgets and selection.
- **Wall 14 — realization and forcing.** Faithful arithmetic objects, orientation and the exhaustion of blind carriers.

**Organizing principle.** Every unconditional positivity theorem is positivity on a carrier that is blind to off-line zeros. RH says that the actual source is blind. Wall 1 measures blindness as a rate, Wall 3 governs how blindness transfers between readings and limits, and Wall 14 asks for the arithmetic mechanism that forces the source into its blind carrier.

Companions: [complete report](hard-obstacles.md), [summary](hard-obstacles-summary.md), [route unification](route-unification-ledger.md). Evidence: Lean corpus search and source reading, logged in `logs/review-2510/`. No compilation. A countermodel excludes the mechanism it was built against, not every route that touches that wall.

**Status column.** *Open*: the wall stands as before. *Refined*: a new sharp boundary or survivor changes what must be proved. *New*: a face added in this review. *Closed*: a local wall that is now solved, retired or shown never to have existed.

## 1. Wall 1 — critical arithmetic sign

With `Δ = sup_ρ |Re ρ − 1/2|`, a receiver bounded at a fixed rate `σ < 1/2` gives `Δ ≤ σ`, which is quasi-RH; RH is `Δ = 0`. Squared-energy receivers carry twice the exponent; Li reads reciprocal depth.

| Face | Status | Present obstacle | Established boundary / survivor | Missing input |
|---|---|---|---|---|
| **1.0 Quasi-RH first rung** | **New** | Graded cancellation receivers have no target between Vinogradov–Korobov and a zero-free strip. | [L] equivalences with a fixed strip: balanced Möbius statistic, centred-prime band, short-window Möbius saving, Vaughan empty leg, JAS level-one budget, PBM graded abscissa, WL rate `σ`, RW/ACS rate-`σ` floors. | A fixed zero-free strip (B2.1), or a non-graded (averaged or escape) handle. |
| **1.1 Critical signed cancellation** | Open | Lag, Abel, history, series and bilinear bounds must reach rate zero with every counterterm and tail paid. | Exact endpoint laws. The high-zero tail is `O(1)`. All-modulus `Q^{−δ/32}` cross-scale saving. All-length Heath–Brown and sharp `S₂`. | Source cancellation at every positive slack (B1.1). |
| **1.2 Axis orientation** | Open | A nonnegative defect, winding count or faithful spectrum does not force line support. | Ward cap and trace; cubic trace = winding; Newton interior margin; KKL positive-time horizon. | Vanishing or a forcing all-height sign (B1.6). |
| **1.3 Complete Weil positivity** | Refined | The low and mixed sectors are unsigned pointwise at large aperture. | Pointwise windows: `3/10` full, `181/500` odd, `(log 2+1/50)/2` primitive. **Averaged positivity at aperture `κ₀ log Γ`, and subpower coercivity up to `X ≤ Γ^{4/3}` [L].** | Sign at every aperture (B1.3), or selection (3.14). |
| **1.4 Arithmetic cone membership** | Open | Identifying the source is not proving its positivity. | Pair tests recover every node; every single-node perturbation fails; exact one-sided cone classification. | `Λ` in the full cone, i.e. RH. |
| **1.5 Contrast equality** | Open | Exact Jensen, BSY and Li accounting leaves a residual. | Contrast and zero-sum identities; reciprocal depth `≤ 1/431`, maximal `β < 1/300`. | Vanishing or a subexponential floor (B1.7). |
| **1.6 Required uniformity** | Open | Fixed rank, order, history or height does not reach the receiver's quantifier. | All-rank orthant sign; PA: RH ⇔ nonnegativity below each order's threshold; fixed-rank coercivity. | All-rank, order-uniform or common-time estimates (B1.5, B3.12). |
| **1.7 Amplification** | Closed as an obstruction | Raising a receiver to a power multiplies its rate. | Exact exponent bookkeeping. | New correlation information, not repetition. |
| **1.8 Critical pronic energy** | Refined | Horizon-uniform signed energy at cofinally small damping. | Vaughan leading Gram paid; product-horizon `o(T^{1−2ε})`; absolute budget has the trivial exponent; size-cutoff receiver paid on the exterior and at `ε = 1/2`. | Signed interior energy (B1.2). |
| **1.9 Signed continuation** | Open | Integrated signed loss must stay bounded uniformly in the horizon. | Canonical corrector; log-height identity. | Flux control at closing damping (B1.2). |
| **1.10 Absolute compensation** | Refined | A vanishing relative error coexists with unbounded raw energy. | The forcing splits into a power plus a bounded remainder. Residual pairing tends to `−1` on escape. Quantile and moving localizations keep the antipodal density. A growing cofactor window keeps the forcing. | Absolute energy bound or escape exclusion (B1.2, B3.2). |
| **1.11 Rates and clusters** | **Refined, nearly closed** | Ground-energy rate versus zero width. | **[S]: `groundRate = polarRate` unconditionally; `CompensatedWidthFloor(1/2)`; `RH ⇔ groundRate = 0`.** Bounded local depth mass gives `polarRate = Δ`. | Only `polarRate = Δ` remains (B3.1). The compensated/uncompensated distinction is gone. |
| **1.12 Interior anti-alignment** | Open | The gap `θ(ε,t) < 1` between the proved collars. | High-height and small-damping collars; planted factors keep the collars. | Interior decorrelation (B1.1, B2.6). |
| **1.13 Aperture shell flux** | Refined | A strictly decreasing ground energy can cross zero. | Prime-threshold ladder: zero birth jumps; RH ⇔ cumulative frozen relaxation `≤ μ(3/10)`. Collar bound `e^{−a}[ψ(e^{2c})−ψ(e^{2a})]`. Permanently frozen finite prime families are eventually negative. | Signed collar estimate along the moving ladder (B3.6). |
| **1.14 Actual divisor heat sign** | Refined | Local repair costs do not sign actual Ξ heads. | **Every positive heat repairs every sufficiently high head (radius-head degree law) [L].** Sharp Hermite barrier and optimum; universal reflectors are positive monomials. | Zero-heat sign on the bounded-height × small-heat residual region, the de Bruijn–Newman core (B1.5, B3.9). |
| **1.15 Selected-height estimates** | Merged into 3.14 | — | — | — |

Key sources: [endpoint](../../../formal/GaloisForLFunctions/BiScaleUncertainty/WeilLagCriticalDeficitEndpointAndLimitLaw.lean), [balanced statistic](../../../formal/GaloisForLFunctions/BezoutValuationIncidence/TheBalancedStatisticIsTheQuasiRiemannHypothesis.lean), [filtered Weil](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/ZeroDensityFilteredWeilPositivityAndCoercivity.lean), [rate equality](../../../formal/GaloisForLFunctions/ArithmeticContinuationAndCriticalEnergy/UnconditionalEqualityOfPolarAndFullGroundEnergyRates.lean), [shell ladder](../../../formal/GaloisForLFunctions/ArithmeticContinuationAndCriticalEnergy/ThresholdVanishingAndCollarDominanceOfThePrimeShell.lean), [radius head](../../../formal/GaloisForLFunctions/ArithmeticLocalDivisorGeometry/RadiusHeadHeatPositivity.lean).

**Aperture ceiling.** `μ(A) ≤ K exp(11A/2 − πe^{2(A−2)})`. No positive exponential floor exists. Finite-aperture positivity and doubly-exponentially vanishing floors remain admissible.

## 2. Wall 3 — transfer: readings, norms, limits, budgets, selection

This wall explains why an attractive estimate does not transfer. Closing a face here enables a route but supplies no Wall 1 sign.

| Face | Status | Present limitation | Established boundary / survivor | Missing transfer |
|---|---|---|---|---|
| **3.1 Readings** | Refined | Magnitudes, orientation-blind samples, complete moment families and **finite linear readings, even with exact `L²` mass and smoothness,** erase the decisive signed data. Weil energy is unbounded on every finite reading kernel at every aperture. | Exact recovery classifications; logarithmic moments; smooth detectors. | Source readings that retain orientation, with affordable conditioning. |
| **3.2 Aperture/height escape** | Open | Finite windows, radii and prefixes admit mimics. | Cofinal criteria; quantitative visibility; admission-or-escape alternatives. | Containment along the full exhaustion. |
| **3.3 Norms and completions** | Refined, new subface | A derivative, mass, quotient or graph bound cannot replace another without a theorem. **The origin-`L²` completion supports no continuous faithful cohomological reading:** Poisson boundaries and all finite-jet graphs are dense in it. | Fixed-aperture CHMD completion; sharp generator passage; compact-`L²` Suzuki limits; exact `H¹` floors. | A jet-retaining completion with lower semicontinuity and tail control (B3.4). |
| **3.4 Shared signed resources** | Refined | Independent local payments can spend the same surplus twice. | Frustration and holonomy law. Exact shared-budget descent: excess `kB` on `k+1` cells. Horizon-uniform Schur payment down to a finite head. Two-tower box law. | One continuum budget (B1.3, B3.8). |
| **3.5 Endpoint logarithms** | Open | Pole cancellation alone does not pay the endpoint. | Partial-pole-sum logarithmic law. | The actual logarithmic remainder for a new source. |
| **3.6 Moving horizons and origins** | Open | Generic below-half interchange and unbounded drift fail. | Priced shifts; common-support limits; weighted moving-support criteria. | Source-specific moving-tail bounds. |
| **3.7 Damping topology** | Open | Hilbert–Schmidt and inverse estimates fail before boundedness does. | Chain bounded but not Hilbert–Schmidt at `η = 1/2`. | Signed sub-half estimates in the admission norm (B3.11). |
| **3.8 Multiplicity and index** | **Refined** | Packet `m²`, Weil `m`, distinct-zero index and reciprocal depth are different currencies. **Faithful (jet-retaining) data additionally read simplicity.** | Meyer: numerical = principal ⇔ simple; quotient index finite or continuum; finite cofactor index = joint multiplicity [S]; collision mass `2(D+E)`. | Keep RH (trace data) separate from RH + simple (faithful data). |
| **3.9 Observation cost** | Open | Recovery at arbitrary phase has no universal linear horizon. | Explicit recurrence recovery. | A source-specific horizon or conditioning bound. |
| **3.10 Filters and hulls** | Refined | Invertible critical-Wiener filters preserve admission classes. | Unit-orbit and hull dictionaries. Möbius ≅ Liouville cofactor modules by unit transport, and real Wiener convolution transports Grams [S]. | Non-unit repair that preserves the source. |
| **3.11 Coupled quantifiers** | Open | Weil margin → heat-Hankel couples degree and time. | Exact bridges with the costs kept. | Decoupling, only where the receiver needs it (B3.12). |
| **3.12 Residual reconstruction and cofactor limits** | Open | Algebraic injectivity gives no bounded inverse; coordinatewise limits do not justify infinite sums. | Common limit carries a cyclic Wiener module; full Wiener pairings pass to the limit; absolute word tail. | Quantitative inverse and infinite tails (B3.3). |
| **3.13 Joint orientation of families** | Open | Individually positive orbits can choose incompatible endpoints. | Common-endpoint classification; exact finite-target index. | A compatible source-defined family (B3.10). |
| **3.14 Average to selected heights** | **Refined: now the entire face** | **The averaged side is solved at logarithmic aperture [L].** What remains is the passage to individual heights, in particular zero ordinates. Bad phases recur syndetically. | Phase-selective single-height law with explicit premises; positive-measure set of positive frequencies; eventual all-height saving is refuted. | A selection theorem (B1.4), with short windows as the graded path (B3.7). |

Sources: [origin obstruction](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/OriginHilbertCohomologyObstruction.lean), [finite readings](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/FiniteReadingsAndMassCannotSupplyBezout.lean), [shared budget](../../../formal/GaloisForLFunctions/BiarithmeticGeometry/SharedBudgetDescent.lean), [Meyer numerical radical](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/MeyerNumericalRadicalAndMultiplicity.lean), [phase-selective heights](../../../formal/GaloisForLFunctions/arithmetic-positivity-theory/SingleHeightPhaseSelectiveApertureAndPowerSaving.lean).

## 3. Wall 14 — realization, orientation and forcing

| Face | Status | Obstructed shortcut | Established boundary / survivor | Missing construction |
|---|---|---|---|---|
| **14.1 Capacity and limits** | Open | Fixed finite passive carriers, trace-class transport, a prescribed permanent gap. **Finite-dimensional affine-unitary successor carriers are trivial.** | Growing carriers; Hilbert–Schmidt `det₂` renewal; nonlocal ports; centered real-law limits. | A compatible source-preserving limit with orientation. |
| **14.2 Algebra without orientation** | Open | Functional equation, integrality, finite-rank Frobenius data, λ-ring or Adams structure, Rosati positive mass. | Ghost and index laws. **Rosati cones have Bézout without unitarity; RR is exactly the reflection condition.** | An independent orientation principle. |
| **14.3 Detector without producer** | Open | A zero-indexed or sign-coded object proves its own input. | Exact depth diagnostics; faithful representations. | Construction first, sign second (B1.6). |
| **14.4 Effectivity and Hasse–Weil** | **Refined** | Naming an ample cone, or imposing RR as a structure field. | Exact arithmetic source RR at every aperture. Boundary rigidity: RR + Bézout on one cone ⇔ reserve = defect. Positive majorants give Bézout and ampleness, never RR. Genuine Meyer surface: trace RR [L]; Bézout ⇔ ampleness ⇔ RH. | An independent effectivity source. B3.5 for the surface section law. |
| **14.5 Pre-divisor weld** | Open | Assuming that reservoir data satisfy the global one-port identity. | Prime and Gamma reservoir; reflection and finite identities. | Stabilization at every spectral point. |
| **14.6 Section/count selectivity** | Open | Rank or count readings; sign-coded sections; Boolean `h⁰ ≤ 1`. | Source-selection obstructions. | A genuinely selective section law. |
| **14.7 Base-to-surface theta coupling** | Open | The base `h⁰` already supplying the surface cone. | Theta `h⁰(d) = log θ(e^{−2d})`; RR; Mellin to completed ζ. | A surface and test-component coupling (B3.5). |
| **14.8 Blind-carrier exhaustion** | **New, central** | Positivity on a carrier that is blind by construction. Examples: low-grid-blind tests, bounded Meyer orbits (= critical highest jets), jointly blind families, large-height heated heads, frequency averages. | **Bounded Meyer surface: RR + Bézout + ampleness unconditionally; carrier = all ⇔ RH + simple [S].** Every finite projector splits positive energy with a nonnegative complement [S]. No compact test is low-grid-blind at every aperture. | A **forcing law**: arithmetic places the actual source in the closure of its blind carrier (B1.6). Test question: can de la Vallée Poussin positivity be realized as carrier positivity (Q2)? |
| **14.9 Positivity–faithfulness dilemma** | **New** | Using faithful positivity to prove RH alone. | Positive Hermitian degrees annihilate off-line blocks and higher jets: they are blind. A faithful positive degree exists ⇔ RH + simple. Hilbert–Schmidt reserve: RR ⇔ RH + simple. Algebraic characters are Ξ evaluations. | RH-only routes must force through non-faithful trace data. Faithful routes must also prove simplicity (B2.3, B1.8). |

Sources: [Meyer surface](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/MeyerSourceIntersectionSurface.lean), [bounded surface](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/BoundedMeyerSourceSurface.lean), [positive degrees](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/PositiveMeyerDegreesSeeReducedCriticalJets.lean), [faithful degrees](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/FaithfulPositiveMeyerDegrees.lean), [boundary rigidity](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/SourceConeBoundaryRigidity.lean), [theta sections](../../../formal/GaloisForLFunctions/ArithmeticOrientationGeometry/TheThetaH0OfSpecZ.lean), [pre-divisor weld](../../../formal/GaloisForLFunctions/RHTower/XiPreDivisorReflectionDefectStabilization.lean).

## 4. Closed local walls

This table records present disposition. A solved local passage is not a research task.

| Local question | Disposition | Remaining wall |
|---|---|---|
| BVI/APT summation-scope "defects" (diagonal μ window, centred-prime Abel, dyadic tail, mean-rate, μ² mean, prime-channel union) | **Never existed.** Mathlib parses the body of `∑` at precedence 67; under the alleged parse each statement is false and could not have been proved. | The status records must be corrected (W3). |
| Balanced Möbius and centred-prime band ⇔ `Θ < 1` | Established [L]. | 1.0 (quasi-RH). |
| Filtered Weil coercivity and averaged strict positivity | Complete [L]. | 3.14 (selection). |
| Polar versus full ground-energy rate | Equal unconditionally [S]. | 1.11, only `polarRate = Δ`. |
| Large-height finite-head heat repair | Complete at every positive heat [L]. | 1.14 residual region. |
| Smoothed Landau formula | Assembled [S]. | Integration (W1). |
| Critical-deficit and Sobolev endpoints | Attained [L]. | 1.1, 1.3. |
| CHMD sharp windows and generator domain | Complete [L]. | Nodal sign (1.3). |
| Suzuki compact `L²`, moving window, collared noncompact limits, RH-complete tents | Complete [L]. | Sign (1.3). |
| Heath–Brown all-length and sharp `S₂` | Complete [L]. | 1.1. |
| Smooth detector at quadratic aperture | Complete [L]. | 3.1, 3.2. |
| Positive scale-stable family structure; global-index dictionary | Complete [L]. | 3.13, 14.8. |
| Base theta `h⁰` | Complete [L]. | 14.7. |
| Local divisor repair; Hermite barrier, optimum and extremizer | Complete [L]. | 1.14. |
| Residual/trace algebraic reconstruction | Complete [L]. | 3.12 (bounded inverse). |
| Meyer genuine RR; algebraic characters; positive-degree classification | Complete ([S] by integration). | 14.8, 14.9. |
| Proof integrity | No `sorry`, `axiom`, `opaque` or `unsafe` in the project. One route-adjacent `native_decide` (PA order-24 quadrature) is not imported by the receivers. | W2. |

## 5. Scoped obstruction register and positive survivors

These distinctions govern which mechanisms may be proposed. None of them retires a live route.

| Mechanism excluded or limited | Positive survivor / permitted target |
|---|---|
| Positive exponential aperture floor | Finite-aperture positivity; doubly-exponentially vanishing floors; graded negative floors. |
| Permanently freezing finitely many primes | The moving prime-threshold ladder with zero birth jumps. |
| Eventual all-height phase saving | Single-height phase-selective law; averaged positivity. |
| Average used to sign a selected height | Short-window averages as a graded path (Q1). |
| Non-monomial universal positive reflector | Source-specific cofactor information. |
| One-factor repair of arbitrary off-line pairs | Exact `δ² ≤ 3u²` boundary and multiplicity costs. |
| Extreme coefficient as the full heat price | Full Hermite cone optimum; masking ratio → 2. |
| Individual orbit positivity for a joint span | Common-endpoint compatibility; jointly seen index. |
| Finite readings (with mass, smooth) as a Bézout source | Infinitely many degrees, or exact source control. |
| Positive quadratic majorant as RR | Bézout and ampleness only; RR forces reserve = defect. |
| Origin-`L²` completion of Meyer cohomology | A jet-retaining completion (open, B3.4). |
| Positive Hermitian degree as an off-line detector | It is blind by theorem; faithful variants need simplicity. |
| PSD + dilation + antipodality as escape exclusion | Full paid-ideal annihilation and moving boundary (Q3). |
| Diagonal power law as mixed homogeneity | Three-metric averaged repair. |
| Finite-dimensional affine-unitary successor carrier | Infinite-dimensional carriers only. |
| Absolute Vaughan budget as power saving | Signed remainder `≤ CT^{1−2ε}` with no matching lower bound; cancellation remains possible. |
| Prime-subset hypercube divergence read as size-cutoff divergence | Size cutoff is paid at `ε = 1/2`; the forward interior is open. |
| Finite-aperture negative index as global purity | Index exit: `D` finite ⇔ eventual confinement; RH ⇔ `D < 2`. |
| Zero-indexed action (PW-B) as a pre-divisor construction | Exact action and exhaustion; independent realization still required. |
| Interfaces with stabilization or positivity fields | The conditional implication only. |

### Catalogue crosswalk

The 44 mechanism codes in the [killed-routes catalogue](../rh-killed-routes.md) map as follows. This is navigation, not re-certification of every legacy entry.

| Codes | Family | Positive direction |
|---|---|---|
| WIP, INT | Integrality / finite-rank purity | 14.2 |
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
| R1, R2, R3 | Trace, renewal or quantization forcing its own defect | 1.2, 14.3 |
| BD, COS, POI | Markov kernels, local inversion, positive Poisson transport | 3.3, 14.1 |
| DSA, TOR, REF, CPF, TMD, TK | Legacy entries, not re-certified | — |

## 6. What counts as crossing a wall

- **Wall 1.** Insert a newly proved source estimate into an existing receiver with every tail and quantifier intact. A weaker estimate receives its exact weaker conclusion. Because of face 1.0, any graded gain beyond Vinogradov–Korobov is a zero-free strip.
- **Wall 3.** Prove a transfer, sharp boundary or quantitative reconstruction on a stated class, norm and limit, and show that the source satisfies the transferred hypothesis. For 3.14 this means a selection theorem; a shorter averaging window counts as graded progress.
- **Wall 14.** Construct the arithmetic object independently, prove fidelity at the strength needed (trace for RH, faithful for RH + simple), and prove a forcing law placing the source in its blind carrier. Blindness of a sub-carrier, however rich, does not cross the wall.
