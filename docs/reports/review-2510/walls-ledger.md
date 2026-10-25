# Walls ledger

Status: 2026-10-25, corpus `eb175d946` plus the working tree of that day. Every obstacle in the corpus belongs to one of three core families:

- **Wall 1 — critical arithmetic sign.** Estimates and signs at the critical endpoint.
- **Wall 3 — transfer.** Readings, norms, completions, limits, shared budgets and selection.
- **Wall 14 — realization and forcing.** Faithful arithmetic objects, orientation, invariants and the forcing of the actual source into its blind carrier.

**Organizing principle.** Every unconditional positivity theorem is positivity on a carrier blind to off-line zeros; for single-channel sharp-stable carriers this is a theorem (14.10). RH says that the actual source is itself blind. Wall 1 measures blindness as a rate. Wall 3 governs how blindness transfers between readings and limits. Wall 14 asks what forces the source into its blind carrier. Two forcing laws are proved:

- Multiplicative positivity forces the boundary line, and inside the strip it forces only what growth input pays (14.11).
- Positivity, the functional equation and the simple pole force the coefficient measure to be ζ's (14.12). They do so linearly in the measure and do not locate zeros.

In every model tested, pole order is what pays for off-line zeros (14.13).

Companions: [complete report](hard-obstacles.md), [summary](hard-obstacles-summary.md), [route unification](route-unification-ledger.md). Evidence: corpus search and Lean statement reading, logged in `logs/review-2510-refresh/`. No compilation. A countermodel excludes the mechanism it was built against, not every route that touches that wall.

**Status column.**

- *Open*: the wall stands unchanged.
- *Refined*: a new sharp boundary or survivor changes what must be proved.
- *New*: a face added in this version.
- *Resolved*: the face's question is answered; the answer is recorded and the face no longer carries an open task.

## 1. Wall 1 — critical arithmetic sign

With `Δ = sup_ρ |Re ρ − 1/2|`, a receiver bounded at a fixed rate `σ < 1/2` gives `Δ ≤ σ` (quasi-RH); RH is `Δ = 0`.

| Face | Status | Present obstacle | Established boundary / survivor | Missing input |
|---|---|---|---|---|
| **1.0 Quasi-RH first rung** | Refined | Graded cancellation receivers and multiplicative forcing have no target between Vinogradov–Korobov and a fixed strip. | Fixed-strip equivalences: balanced statistic, centred-prime band, short windows, JAS level one, PBM abscissa, WL rate `σ`, RW/ACS floors, the Vaughan empty leg; now also uniform Vaughan convolution power cancellation, residual Gram power rates, factorial-order-one envelopes and reciprocal-tail gains at any damping [S]. Unconditional regions: dlVP, Littlewood, VK. | A fixed zero-free strip (B2.1) or a non-graded handle (selection, escape, coupled positivity). |
| **1.1 Critical signed cancellation** | Open | Lag, Abel, history, series and bilinear bounds must reach rate zero with every counterterm and tail paid. | Exact endpoint laws; high-zero tail `O(1)`; all-modulus `Q^{−δ/32}`; Heath–Brown all-length; sharp `S₂`; `M(x) = Ω±(√x)`. | Source cancellation at every positive slack (B1.1). |
| **1.2 Axis orientation** | Open | A nonnegative defect, winding count or faithful spectrum does not force line support. | Ward cap and trace; cubic trace = winding; subharmonic Newton margin; KKL horizon. | Vanishing or a forcing all-height sign (B1.6). |
| **1.3 Complete Weil positivity** | Open | Low and mixed sectors are unsigned pointwise at large aperture. | Windows `3/10` full, `181/500` odd, `(log 2+1/50)/2` primitive; averaged positivity at `κ₀ log Γ` on `[Γ, 2Γ]`; subpower coercivity to `Γ^{4/3}`; finite-level existence ⇔ RH. | Sign at every aperture (B1.3) or selection (3.14). |
| **1.4 Arithmetic cone membership** | Open | Identifying the source is not proving its positivity. | Pair tests recover every node; single-node perturbations fail; positive-measure rigidity identifies the source among all positive measures with the theta law (14.12). | `Λ` in the full Weil cone, i.e. RH. |
| **1.5 Contrast equality** | Open | Exact Jensen, BSY and Li accounting leaves a residual. | BSY: the off-line sum `Σ log|ρ/(1−ρ)|` is nonnegative and vanishes on critical zeros; Li depth `≤ 1/431`, `β < 1/300`. | An arithmetic upper bound forcing the residual to zero (B1.7). |
| **1.6 Required uniformity** | Open | Fixed rank, order, history or height does not reach the receiver's quantifier. | All-rank orthant sign; PA order thresholds; fixed-rank coercivity. | All-rank or order-uniform estimates (B1.5, B3.12). |
| **1.7 Amplification** | Resolved | Raising a receiver to a power multiplies its rate. | Exact exponent bookkeeping. | — |
| **1.8 Critical pronic energy** | Refined | Horizon-uniform signed energy at cofinally small damping. | Half damping: actual receiver bounded, actual Gram rank two, moving limits a rank-three ray. Above half: admission with a common critical-Wiener majorant. Below half: leading order fully classified; every power improvement of the residual is a fixed strip [S]. Size-cutoff receiver paid on the exterior and at `ε = 1/2`. | Signed interior energy below `T^{1−2ε}` (B1.2). |
| **1.9 Signed continuation** | Open | Integrated signed loss must stay bounded uniformly in the horizon. | Canonical corrector; integer local exponents of paid patterns below half damping. | Flux control at closing damping (B1.2). |
| **1.10 Absolute compensation** | Refined | A vanishing relative error coexists with unbounded raw energy. | Power-plus-bounded forcing; residual pairing → `−1` on escape; quantile and moving localizations keep the antipodal density; record-minimum limits with `K_pp ≥ p^{2ε−2}`. | Absolute energy bound or escape exclusion (B1.2, 3.15). |
| **1.11 Rates and clusters** | Refined | Physical ground rate versus zero width. | `groundRate = polarRate`; form-norm and Birman–Schwinger rates `= Δ`; `RH ⇔ groundRate = 0`; bounded local depth gives `polarRate = Δ`. | Physical `polarRate = Δ` (B3.1). |
| **1.12 Interior anti-alignment** | Open | The gap `θ(ε,t) < 1` between the proved collars. | High-height and small-damping collars; planted factors keep them. | Interior decorrelation (B1.1, B2.6). |
| **1.13 Aperture shell flux** | Open | A strictly decreasing ground energy can cross zero. | Zero birth jumps; RH ⇔ cumulative frozen relaxation `≤ μ(3/10)`; collar bound; frozen finite families fail. | Signed collar estimate along the moving ladder (B3.6). |
| **1.14 Actual divisor heat sign** | Open | Local repair costs do not sign actual Ξ heads. | Every positive heat repairs every high head; Hermite barrier and optimum; positive monomial reflectors; `Λ < 1/8`. | Zero-heat sign on the residual region (B1.5, B3.9). |

Key sources: [endpoint](../../../formal/GaloisForLFunctions/BiScaleUncertainty/WeilLagCriticalDeficitEndpointAndLimitLaw.lean), [balanced statistic](../../../formal/GaloisForLFunctions/BezoutValuationIncidence/TheBalancedStatisticIsTheQuasiRiemannHypothesis.lean), [Vaughan power bounds](../../../formal/GaloisForLFunctions/BezoutValuationIncidence/UniformVaughanPowerBoundsAreFixedStrips.lean), [half-damping Vaughan](../../../formal/GaloisForLFunctions/BezoutValuationIncidence/TheHalfDampingVaughanGramLimitsFormARankThreeRay.lean), [filtered Weil](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/ZeroDensityFilteredWeilPositivityAndCoercivity.lean), [rate equality](../../../formal/GaloisForLFunctions/ArithmeticContinuationAndCriticalEnergy/UnconditionalEqualityOfPolarAndFullGroundEnergyRates.lean), [shell ladder](../../../formal/GaloisForLFunctions/ArithmeticContinuationAndCriticalEnergy/ThresholdVanishingAndCollarDominanceOfThePrimeShell.lean), [radius head](../../../formal/GaloisForLFunctions/ArithmeticLocalDivisorGeometry/RadiusHeadHeatPositivity.lean), [VK region](../../../formal/GaloisForLFunctions/RHTower/Sieve/VinogradovKorobovZeroFree.lean).

**Aperture ceiling.** `μ(A) ≤ K exp(11A/2 − πe^{2(A−2)})`. No positive exponential floor exists; finite-aperture positivity and doubly exponentially vanishing floors remain admissible.

## 2. Wall 3 — transfer: readings, norms, limits, budgets, selection

Closing a face here enables a route but supplies no Wall 1 sign.

| Face | Status | Present limitation | Established boundary / survivor | Missing transfer |
|---|---|---|---|---|
| **3.1 Readings** | Open | Magnitudes, orientation-blind samples, moment families and finite linear readings (even with exact `L²` mass) erase the signed data. | Exact recovery classifications; logarithmic moments; smooth detectors. | Orientation-retaining source readings. |
| **3.2 Aperture/height escape** | Open | Finite windows, radii and prefixes admit mimics. | Cofinal criteria; quantitative visibility. | Containment along the full exhaustion. |
| **3.3 Norms and completions** | Refined | One norm does not replace another without a theorem; closure can lose payment. | Origin-`L²` completion supports no faithful reading. Golden one-prime payment domain: not closed, closure = kernel of total evaluation, reduced cokernel `≅ ℂ`, continuous dual one-dimensional, closure gap of dimension continuum. Graph norm retains payment. | A graph topology in which the maximal blind ideal is closed and exhaustion follows by limits (B3.4). |
| **3.4 Shared signed resources** | Open | Local payments can spend one surplus twice. | Frustration and holonomy law; exact descent (excess `kB`); horizon-uniform Schur payment; two-tower box law. | One continuum budget (B1.3, B3.8). |
| **3.5 Endpoint logarithms** | Open | Pole cancellation alone does not pay the endpoint. | Partial-pole-sum logarithmic law; Dini thresholds; monotone-defect Dini law. | The logarithmic remainder for a new source. |
| **3.6 Moving horizons and origins** | Refined | Generic below-half interchange and unbounded drift fail. | Priced shifts; reset-origin limits `(K + cKmax)/(1+c)` faithful; raw moving origins add constant mass and violate zero-origin contraction, so they are not fixed-origin limits. | Source-specific moving-tail bounds. |
| **3.7 Damping topology** | Refined | Hilbert–Schmidt and inverse estimates fail before boundedness does. | Chain bounded, not Hilbert–Schmidt, at half damping; hypercube endpoint bounded for all squarefree `P`; Vaughan admission at and above half damping; integer local exponents below half. | Signed sub-half estimates (B3.11). |
| **3.8 Multiplicity and index** | Open | Packet `m²`, Weil `m`, distinct index and reciprocal depth are different currencies. | Meyer: numerical = principal ⇔ simple; quotient index finite or continuum; trace-bounded ideal keeps every jet and reads RH alone. | Keep trace data separate from operator-norm data. |
| **3.9 Observation cost** | Open | Recovery at arbitrary phase has no universal linear horizon. | Explicit recurrence recovery. | A source-specific horizon bound. |
| **3.10 Filters and hulls** | Open | Invertible critical-Wiener filters preserve admission classes. | Unit-orbit dictionaries; Möbius ≅ Liouville cofactor modules. | Non-unit repair preserving the source. |
| **3.11 Coupled quantifiers** | Open | Weil margin → heat-Hankel couples degree and time. | Exact bridges with costs kept. | Decoupling where needed (B3.12). |
| **3.12 Residual reconstruction and cofactor limits** | Refined | Algebraic injectivity gives no bounded inverse. | Common limit carries a cyclic Wiener module; contraction calculus (closed dilation ranges, principal colon annihilators, multiplicative composition, index drop by nullity); cofactor-graph closedness ⇔ a uniform estimate. | Quantitative inverse (B3.3). |
| **3.13 Joint orientation of families** | Open | Individually positive orbits can choose incompatible endpoints. | Common-endpoint classification; spline-orbit index ≤ 1 ⇔ RH. | A compatible source family (B3.10). |
| **3.14 Average to selected heights** | Open | Averaged positivity at logarithmic aperture is proved on `[Γ, 2Γ]`; its main term is the local critical-zero weight. Bad phases recur syndetically. | Phase-selective single-height law; positive-measure positive frequencies; bad-frequency volume bound. | A selection theorem (B1.4); short windows as the graded path (B3.7, Q1). |
| **3.15 Escape states of actual limits** | New | Subsequential cofactor limits can differ along horizons. | Some actual limit has `K_pp ≥ p^{2ε−2}`; families are singleton or continuum; zero-diagonal limits force continuum and escape; augmentation is never the unique state; rank-one states are `η(p)p^{−s}`; white noise survives every proved constraint. | Nonzero paid ideal on escape (B3.16), then classification (B3.2). |

Sources: [origin obstruction](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/OriginHilbertCohomologyObstruction.lean), [payment domain](../../../formal/GaloisForLFunctions/BiarithmeticGeometry/CriticalContinuousDual.lean), [shared budget](../../../formal/GaloisForLFunctions/BiarithmeticGeometry/SharedBudgetDescent.lean), [record minima](../../../formal/GaloisForLFunctions/ArithmeticDefectRigidity/RecordMinimaForceInfiniteCofactorLimits.lean), [kernel families](../../../formal/GaloisForLFunctions/ArithmeticDefectRigidity/ActualCofactorKernelFamiliesAreSingletonOrContinuum.lean), [raw origins](../../../formal/GaloisForLFunctions/ArithmeticDefectRigidity/RawMovingOriginsAddConstantGramMass.lean), [phase-selective heights](../../../formal/GaloisForLFunctions/arithmetic-positivity-theory/SingleHeightPhaseSelectiveApertureAndPowerSaving.lean).

## 3. Wall 14 — realization, invariants and forcing

| Face | Status | Obstructed shortcut | Established boundary / survivor | Missing construction |
|---|---|---|---|---|
| **14.1 Capacity and limits** | Open | Fixed finite passive carriers; trace-class transport; a prescribed gap; finite-dimensional affine-unitary carriers. | Growing carriers; `det₂` renewal; nonlocal ports. | A source-preserving limit with orientation. |
| **14.2 Algebra without orientation** | Open | Functional equation, integrality, finite-rank Frobenius, λ-ring or Rosati data, each separately. | Rosati cones have Bézout without unitarity; genus-one Hasse = degree positivity of `ℤ[F]`; Hecke graphs of `ℤ` have no theorem of the square. | An orientation principle; a ring of correspondences over `Spec ℤ`. |
| **14.3 Detector without producer** | Open | A zero-indexed object proves its own input. | Exact depth diagnostics. | Construction first, sign second (B1.6). |
| **14.4 Effectivity** | Open | Naming an ample cone or imposing RR as a field. | Exact source RR; reserve rigidity; majorants give Bézout, never RR; Meyer trace RR, Bézout ⇔ RH. | An independent effectivity source; the surface section law (B3.5). |
| **14.5 Pre-divisor weld** | Open | Assuming reservoir data satisfy the global identity. | Prime and Gamma reservoir; reflection identities. | Stabilization at every spectral point. |
| **14.6 Section selectivity** | Open | Rank or count readings; Boolean `h⁰ ≤ 1`. | Source-selection obstructions. | A selective section law. |
| **14.7 Base-to-surface theta coupling** | Open | Base `h⁰` supplying the surface cone. | Theta `h⁰(d) = log θ(e^{−2d})`; RR; Mellin to completed ζ. | Surface coupling (B3.5). |
| **14.8 Blind-carrier exhaustion** | Refined | Positivity on a carrier blind by construction; zero-free-region transfers. | Maximal blind ideal identified, all jets, restricted geometry, `= ⊤ ⇔ RH`. `ArithmeticForcesBlindness` transfers sources supported outside a zero-free region into it; that is not forcing. | A forcing law with input outside 14.10–14.12 (B1.6). |
| **14.9 Positivity–faithfulness dilemma** | Open | Operator-norm faithful positivity used for RH alone. | Faithful degree ⇔ RH + simple; trace-bounded ideal reaches RH alone. | RH routes through trace-bounded data. |
| **14.10 Single-channel exhaustion** | Open | Forcing inside single-channel quadratic positivity. | Every sharp-stable positive convolution ideal lies in the blind ideal; scale-shift-invariant positive test spaces are blind. | Coupled positivity outside the class (B3.17, Q2). |
| **14.11 Multiplicative forcing** | Refined (mapped) | Imported regions read as forced; finite certificates read as beating growth. | Boundary: positive-definite divisor, simple-pole trichotomy, four-invariant forcing law with each invariant necessary, profile characterization; interior invisible to boundary data. Interior: exact Fejér barrier `2cos(π/(K+2))`; certified width `(√B−√A)²/G`; universal cap `(3−2√2)/(2L)` for every finite frequency set; multi-channel certificates split into one-channel problems on rational fibres; dlVP optimal for its input. | Better growth input (B2.8) or a non-finite, pole-sensitive mechanism (B1.9). |
| **14.12 Completeness of invariants** | Resolved | Assuming a full-invariant countermodel exists, or that none does. | Positive measure on `[1,∞)` + degree-one theta law ⇒ ζ; Beurling prime measure ⇒ `Λ/log`; discrete systems ⇒ rational primes [S]; Hamburger stability under sublinear critical-line defects. Relaxations: pole order 2 (real pair), pole order 3 (quartet), strip poles, no FE (over-regular), no positivity (non-uniqueness). | — The open part is 14.13. |
| **14.13 Zero–pole budget** | New | Treating pole order as irrelevant to zero location. | Boundary: zero order ≤ pole order; a zero at `u` forces a pole at `2u`. Interior, finite corrections of ζ: `ord₁F − 1` = inserted off-line multiplicity by frequency pairs; a complex quartet costs two. Critical zeros force `κ = d`, `T = ζ^d`. | An absolute budget inequality (B1.9; RH at pole order one), or one for an infinite class of corrections (W8(vii) first). |

Sources: [maximal blind ideal](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/MaximalBlindIdealOfTheMeyerSource.lean), [forcing transfer](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/ArithmeticForcesBlindness.lean), [boundary completeness](../../../formal/GaloisForLFunctions/MultiplicativePositivityGeometry/BoundaryCompleteness.lean), [growth-to-forcing](../../../formal/GaloisForLFunctions/MultiplicativePositivityGeometry/GrowthToForcing.lean), [multi-frequency cap](../../../formal/GaloisForLFunctions/MultiplicativePositivityGeometry/MultiFrequencyCap.lean), [positive-measure rigidity](../../../formal/GaloisForLFunctions/ArithmeticPositiveDuality/PositiveMeasureHamburgerRigidity.lean), [pole order two](../../../formal/GaloisForLFunctions/RHTower/PoleOrderTwoRealStray.lean), [entire FE model](../../../formal/GaloisForLFunctions/RHTower/EntireFunctionalEquationOffLine.lean), [strip-pole model](../../../formal/GaloisForLFunctions/RHTower/LambdaPositiveFunctionalEquationOffLine.lean), [pole-order rigidity](../../../formal/GaloisForLFunctions/RHTower/TwinRigidityPoleOrder.lean), [faithful degrees](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/FaithfulPositiveMeyerDegrees.lean), [theta sections](../../../formal/GaloisForLFunctions/ArithmeticOrientationGeometry/TheThetaH0OfSpecZ.lean).

## 4. Resolved local walls

A resolved local passage is not a research task.

| Local question | Disposition | Remaining wall |
|---|---|---|
| Summation-scope "defects" (BVI, APT, ACS) | Never existed: Mathlib parses the `∑` body at precedence 67, and the proofs use that reading. | — |
| Balanced Möbius and centred-prime band ⇔ `Θ < 1` | Established. | 1.0 |
| Vaughan power improvements ⇔ `Θ < 1` | Established [S]. | 1.0 |
| Vaughan at and above half damping | Admission; actual Gram rank two; rank-three ray at `ε = 1/2` [S]. | 1.8 below half |
| Filtered Weil coercivity, averaged positivity on `[Γ, 2Γ]` | Complete. | 3.14 |
| Polar versus full ground-energy rate | Equal. | 1.11 |
| Maximal sharp-stable positive Meyer ideal | Identified and maximal. | 14.8, 14.10 |
| Boundary-line nonvanishing as a forcing law | Complete, with necessity of each invariant. | 14.11 |
| Interior multiplicative forcing by finite certificates | Excluded beyond growth input. | 14.11, B2.8 |
| Invariant completeness in degree one | Resolved: rigidity plus relaxation models. | 14.13 |
| Augmentation as the escape picture | Excluded as unique state. | 3.15 |
| Half-damping hypercube endpoint | Bounded for all squarefree `P`. | 3.7 |
| Integer local exponents below half damping | Proved. | 3.7 |
| Vaughan subcritical leading-order limits | Classified. | 1.8 |
| Functional equation versus decaying count error | Incompatible. | 14.12 |
| Sparse-spectrum annihilators | Constructed for `Σ|a|^{−s} < ∞`, `s < 1`. | Not applicable to ζ zeros. |
| Finite-level weight existence | ⇔ RH. | 1.3 |
| Large-height head repair | Complete at every positive heat. | 1.14 |
| Smoothed Landau formula; endpoint attainment; CHMD domains; Suzuki limits; Heath–Brown; smooth detector | Complete. | 1.1, 1.3, 3.1 |
| Local divisor repair; Hermite barrier and optimum | Complete. | 1.14 |
| SSA odd-shift `1/3`, lag-2 `1/4` floors | Exact. | B3.13 |
| Proof integrity | No `sorry`, `axiom`, `opaque`, `unsafe`; two `native_decide` files, neither imported by a route receiver. | W2 |

## 5. Scoped obstruction register and positive survivors

These distinctions govern which mechanisms may be proposed. None retires a live route.

| Mechanism excluded or limited | Positive survivor / permitted target |
|---|---|
| Positive exponential aperture floor | Finite-aperture positivity; doubly exponentially vanishing floors; graded negative floors. |
| Permanently freezing finitely many primes | The moving prime-threshold ladder. |
| Eventual all-height phase saving | Single-height phase-selective law; averaged positivity. |
| Average used to sign a selected height | Short-window averages as a graded path (Q1). |
| Single-channel sharp-stable positive ideal as forcing carrier | Coupled carriers (Q2). |
| Harmonic positivity with a double pole or with harmonic poles | Simple pole + pole isolation + integer orders force the boundary. |
| More finite frequencies against a fixed growth payment | Exact width `(√B−√A)²/G`; better growth input. |
| Imported zero-free collar read as forced; zero-free-region transfer read as forcing | Classical regions with explicit growth input. |
| Coupled off-line ceiling read as exclusion | A sign for off-line summands. |
| `Λ ≥ 0` + exact FE without the simple pole | Pole-order budget: order 2 admits only real strays, order 3 admits quartets. |
| `Λ ≥ 0` + exact FE without strip holomorphy | Holomorphy of the completion is a required input. |
| Over-regular count with the FE | Counts fluctuate at least like `⌊x⌋`; positive measures with the theta law are rigid. |
| Signed coefficients with the theta law | Only `Σ a_n sinc²(λ_n) = 0` survives; positivity is essential. |
| Non-monomial universal positive reflector | Source-specific cofactor information. |
| One-factor repair of arbitrary off-line pairs | Exact `δ² ≤ 3u²` boundary and multiplicity costs. |
| Individual orbit positivity for a joint span | Common-endpoint compatibility. |
| Finite readings (with mass) as Bézout source | Infinitely many degrees, or exact source control. |
| Positive quadratic majorant as RR | Bézout and ampleness only. |
| Origin-`L²` completion; Wiener closure of payment | Graph topology retaining jets and payment. |
| Positive Hermitian degree as off-line detector | Faithful variants need simplicity. |
| PSD + dilation + antipodality as escape exclusion | Full paid-ideal annihilation (needs B3.16). |
| Augmentation as unique escape state | Record-minimum limits with positive diagonals. |
| Raw moving origins as fixed-origin limits | Reset-origin faithful mixtures; fixed-origin paid-ideal constraints. |
| Contraction laws + horizon order as Kronecker selection | Contraction calculus; rank-one sign law. |
| Diagonal power law as mixed homogeneity | Three-metric averaged repair. |
| Finite-dimensional affine-unitary successor carrier | Infinite-dimensional carriers only. |
| Absolute Vaughan budget as power saving | Signed remainder `≤ CT^{1−2ε}`. |
| Vaughan leading-order limits as residual control | Residual below `T^{1−2ε}` untouched. |
| Unique moving half-damping Vaughan limit | Harmonic subtraction; product horizon selects rank two. |
| Dini or completely monotone defects below half damping | Payable only at `ε = 1/2`. |
| Finite-aperture negative index as global purity | `D` finite ⇔ eventual confinement; RH ⇔ `D < 2`. |
| Zero-indexed action (PW-B) as construction | Independent realization required. |

### Catalogue crosswalk

The 44 mechanism codes in the [killed-routes catalogue](../rh-killed-routes.md) map as follows. This is navigation, not re-certification of legacy entries.

| Codes | Family | Positive direction |
|---|---|---|
| WIP, INT, DEF | Integrality, finite-rank purity, deformation-stable inequalities | 14.2, 14.12, 14.13 |
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

- **Wall 1.** Insert a newly proved source estimate into an existing receiver with every tail and quantifier intact. Because of face 1.0, any graded gain beyond Vinogradov–Korobov is a fixed strip.
- **Wall 3.** Prove a transfer, sharp boundary or quantitative reconstruction on a stated class, norm and limit, and show that the source satisfies its hypothesis. For 3.14, a selection theorem; a shorter averaging window is graded progress. For 3.15, a decision on the paid ideal at escape.
- **Wall 14.** Construct the arithmetic object independently and prove fidelity at the strength needed, then a forcing law placing the source in the maximal blind ideal with input outside the single-channel class (14.10), beyond finite certificates (14.11) and nonlinear in the coefficient measure (14.12). The law must see pole order (14.13): it must fail on the pole-order-2 and pole-order-3 models and on the strip-pole model. Blindness of a sub-carrier, however rich, does not cross the wall; neither does a transfer from a zero-free region.
