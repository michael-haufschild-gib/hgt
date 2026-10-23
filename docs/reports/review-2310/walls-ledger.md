# The walls ledger

**Status at 2026-10-23.** Three core problem families remain: **Wall 1, arithmetic estimates; Wall 3, information and norm transfer; Wall 14, faithful arithmetic realization.** None is closed globally. Numerous local walls are solved, several proposed strengthenings are now sharply refuted, and ACS exposes an additional effectivity problem within Wall 14.

Companions: [complete report](hard-obstacles.md), [routine work and research programme](hard-obstacles-summary.md), [route unification](route-unification-ledger.md). Inventory: 30 live routes, 18 standalone candidates and embedded PW-B. Programme names describe overlapping work, not additional independent RH routes.

## 1. How to read a wall

An **open estimate** is a missing arithmetic theorem. A **proved obstruction** excludes only its stated class. A **resolved local wall** has an exact positive theorem but may leave a stronger transfer open. A **candidate construction** has no completed producer. Every negative entry must retain its positive survivor.

The three families organize research; they are not proved equivalent as construction problems. A proposed method may meet all three. B-RH means a proved RH-sufficient target; B-C means a project-specific unresolved question, without a claim of worldwide novelty. Source and compiler distinctions follow the [evidence section](hard-obstacles.md#6-evidence-and-verification-limits).

## 2. Wall 1 — arithmetic estimates at the critical rate

Write `Δ=supρ|Reρ−1/2|`. RH is `Δ=0`. Exact receivers identify what must be bounded, but do not supply the bound. Positive-width improvements remain meaningful. LI's reciprocal-depth rate, heat time, aperture and negative index must not be substituted for `Δ`.

| Face | Present mathematical wall | Resolved part / strongest positive survivor | Required new input |
|---|---|---|---|
| **1.1 Critical signed cancellation** | Complete prime/Möbius lag, band, Abel, history, regularized-series or divisor-sum estimate remains unpaid. | Explicit universal probe, exact signed identities, fixed-modulus cancellation, actual-row improvements. | Arithmetic control of off-diagonal, high-LCM, inherited-history and tail terms at the receiver's rate. O1/O3. |
| **1.2 Axis orientation** | Symmetry, FE, a nonnegative defect or an integral count does not force line support or defect zero. | Exact Ward cap, spectral signs, cubic winding/index and collision receivers; independent diagnostic formulas. | All-height source sign, cap vanishing, sub-unit estimate, or pre-divisor forcing. O6/O8. |
| **1.3 Global Weil positivity** | A negative ground at some larger aperture remains possible under current estimates. | Full floor through `0.3`; odd floor through `0.362`; ACT one-shift completeness; RW/SZ completion; restricted APT families. | Complete signed allocation/nonnegative ground at cofinal apertures. O4. |
| **1.4 Arithmetic cone rigidity** | The full-positive weight, if one exists, must be `Λ`; uniqueness does not establish existence. | Singleton under RH/empty otherwise; pole weight forced to one; prime-power-node classification. | Positivity of literal `Λ`, complete blind infimum or valid even-sector producer. O4. |
| **1.5 Contrast equality** | KL/Jensen/likelihood accounting can leave a nonzero residual. | Exact BSY zero sum and adaptive reveal-cost accounting. | Arithmetic equality for the complete cofinal contrast. O9. |
| **1.6 All required quantifiers** | Fixed rank/degree/history or almost-everywhere data do not meet the complete receiver. | Continuous lag completeness, finite recovery, inner contour cancellation, zero-free-target recurrence. All-rank small-time orthant positivity is already proved. | Bound arbitrary signed tests and required tails, at the receiver's actual quantifiers. O6/O9. |
| **1.7 Amplification** | Powers of the same scalar error multiply its rate; they do not improve it. | Exact exponent bookkeeping. | New correlation or cancellation input, not reparameterization. O1/O3. |
| **1.8 Critical pronic energy** | `sup_T Eε(T)<∞` for cofinally small positive `ε` is unproved. | Half-damping admission, admission above width, near-half shrinking band; compensated diagonal/predecessor bounded; interior contraction iff energy bounded. | Actual compensated interior estimate or equivalent global approximation. O2. |
| **1.9 Signed continuation** | Full signed loss integral remains uncontrolled uniformly in horizon. | Exact admission equivalence; scalar/cutoff costs; positive-interval core debt equals a zeta-log ratio. | Cross-covariance, boundary flux and a comparable source-defined corrected energy. Global `W≥0` is false. O2. |
| **1.10 Relative versus absolute compensation** | Relative error can vanish super-logarithmically while an absolute power-scale factor remains. | Summable dyadic projection motion and relative transverse energy. | Absolute signed energy control and source-specific moving-tail estimates. O2/O3. |

Key evidence: [PrimeLagLowerBoundRH](../../../formal/GaloisForLFunctions/RHTower/PrimeLagLowerBoundRH.lean), [UniformRenormalizedInteriorEnergyRemainder](../../../formal/GaloisForLFunctions/BezoutValuationIncidence/UniformRenormalizedInteriorEnergyRemainder.lean), [TheAveragedBudgetIsExactlyAdmission](../../../formal/GaloisForLFunctions/ArithmeticContinuationAndCriticalEnergy/TheAveragedBudgetIsExactlyAdmission.lean), [TheCompensationDefectDecaysFasterThanEveryLogPower](../../../formal/GaloisForLFunctions/ArithmeticCompensationTheory/TheCompensationDefectDecaysFasterThanEveryLogPower.lean), [TheCoreDebtOnAPositiveIntervalIsAZetaLogRatio](../../../formal/GaloisForLFunctions/ArithmeticCompensationTheory/TheCoreDebtOnAPositiveIntervalIsAZetaLogRatio.lean).

### The sharpened floor constraint

For `A≥3`, the actual ground satisfies

`μ(A) ≤ K exp(11A/2 − πe^{2(A−2)})`.

A positive transported floor `m₀e^(−B(A))` requires

`B(A) ≥ πe^{2(A−2)} − 11A/2 + log(m₀/K)`.

Thus a fixed positive gap is impossible. Even the abstract harmonic-loss example cannot be realized as a positive floor along linearly growing actual apertures. **Survivor:** finite-aperture nonnegativity, sufficiently rapidly decaying positive floors if independently proved, or graded negative floors. An upper envelope tending to zero does not prove `μ(A)→0`; off RH, the ground eventually becomes negative and falls without bound. [TheApertureFloorMustDecayDoublyExponentially](../../../formal/GaloisForLFunctions/ArithmeticCompensationTheory/TheApertureFloorMustDecayDoublyExponentially.lean); [TheContactApertureOfTheGroundEnergyPath](../../../formal/GaloisForLFunctions/SquareRootThreshold/TheContactApertureOfTheGroundEnergyPath.lean).

### The actual-row boundary

The centered-prime range reaches `P^(1+δ)≤Q≤P^(30/17−δ)`, with the prescribed slack, centering and polynomial horizon. It improves the old `12/7` endpoint but excludes balanced scales. Generic Type-II threshold `6/5` and pronic-window threshold `1` use different parameterizations; neither is a universal numerical wall for arithmetic rows. [TheSeventeenThirtiethsWindowWidensTheCentredPrimeRowRange](../../../formal/GaloisForLFunctions/ArithmeticCompensationTheory/TheSeventeenThirtiethsWindowWidensTheCentredPrimeRowRange.lean).

## 3. Wall 3 — what readings, norms and local budgets lose

| Face | Proved limitation | Positive survivor | Open transfer |
|---|---|---|---|
| **3.1 Reading and phase loss** | Magnitudes, Ramanujan amplitudes and even all translated periodic moments can miss pronic admission. Prime signs/mean also miss oscillatory spectral amplitude. | Exact finite physical recovery; pronic/logarithmic probes distinguish relevant pairs; exact constant/oscillatory multiplicative laws. | Quantitative actual-source energy from a sufficiently informative reading, with observation costs. |
| **3.2 Aperture/height escape** | A true bounded-aperture positivity reading on tempered configurations remains compatible with depth `1/2`. Finite prime-prefix readings cannot select full `Λ` positivity. | Cofinal all-test positivity is complete; exact lattice and isolated-pair hiding thresholds. | Arithmetic exclusion of mimics or complete cofinal certificates, not a claimed finite height cutoff. |
| **3.3 Norm and cone transfer** | Derivative, logarithmic Fourier, mass, pronic and quotient norms are distinct; Toeplitz positivity is not Hankel positivity. | RW/SZ sign equivalence despite inequivalent derivative norm; CHMD graph/Weil norm equivalence at fixed aperture; weighted floors; mass floor under local squared-depth bound. | Whole-quotient lower bound/landing; signed mass-floor converse; complete-family APT transfer. |
| **3.4 Shared signed resources** | Separate local payments can reuse surplus. Unbalanced sign patterns can be PSD but locally unpayable. | Holonomy classification; sharp frustrated-cycle payment; packed nonlocal paths; one-signed/edge-profile cancellation. | Actual arithmetic supersolutions and paths, all Gamma/pole terms, continuum and aperture limits. |
| **3.5 Critical endpoint logarithms** | For critical-Wiener kernels, pole cancellation alone does not pay half-damped smooth powers. | Exact `Σ S_k(n)²/(n+1)` criterion; sharp absolute square-root-log class. | Comparable endpoint control for other signed kernels or actual small-damping energy. |
| **3.6 Horizon and origin changes** | Below half, an admitted infinite signed receiver can have unbounded centered finite rows. Unbounded origin drift fails on some admitted sequence. | Row interchange at/above half; critical-Wiener smooth-power subclass below half; sharp finite-shift cost and exact tail inequalities. | Actual-source cutoff covariance and moving-tail bounds. |
| **3.7 Semigroup topology** | Compact `c₀` dynamics do not give bounded backward transport in `c₀` or receiver `ℓ²`; no operator-norm continuity at zero. | Strong continuity, residue generator, dense modes, exact first-column receiver. Working `ℓ²` chain bound for `1/√2<η<1`. | Source-specific pronic control; quantitative spectral/core statements only where required. |
| **3.8 Multiplicity and index** | `m²` packet energy, `m` Weil energy and distinct-zero negative index cannot be identified. Periodic curve scaling repeats each outer eigenvalue infinitely. | Exact multiplicity ceiling, Hodge index count and finite Frobenius-span law. | A claimed norm/count transfer must pay its additional multiplicity or period assumptions. |

Evidence: [TheApertureCertificateIsBlindInEveryUnit](../../../formal/GaloisForLFunctions/ScaleSignedIncidenceCriticality/TheApertureCertificateIsBlindInEveryUnit.lean), [CHMDGraphNormIsTheWeilFormNormOnAnAperture](../../../formal/GaloisForLFunctions/RHTower/CHMDGraphNormIsTheWeilFormNormOnAnAperture.lean), [CycleHolonomyDecidesBalance](../../../formal/GaloisForLFunctions/SignedArithmeticEnergyIncidence/CycleHolonomyDecidesBalance.lean), [TheHalfDampedHyperplaneLawHasAnExactLogarithmicThreshold](../../../formal/GaloisForLFunctions/TransHorizonIncidenceMechanics/TheHalfDampedHyperplaneLawHasAnExactLogarithmicThreshold.lean), [TheHorizonLimitCommutesWithTheReceiverExactlyFromHalfDamping](../../../formal/GaloisForLFunctions/TransHorizonIncidenceMechanics/TheHorizonLimitCommutesWithTheReceiverExactlyFromHalfDamping.lean), [ADriftingOriginIsPricedByTheTailBeyondIt](../../../formal/GaloisForLFunctions/ArithmeticCompensationTheory/ADriftingOriginIsPricedByTheTailBeyondIt.lean), [MultiplicityCeilingLaw](../../../formal/GaloisForLFunctions/BiScaleUncertainty/MultiplicityCeilingLaw.lean).

The norm wall has narrowed, not disappeared. The derivative norm in Suzuki's primitive theorem is not CHMD's graph norm. Likewise, a continuous quotient map is not a lower norm bound or a proof that its image exhausts the quotient. Local compactness of negative directions is not uniform compactness over all apertures.

## 4. Wall 14 — faithful arithmetic realization

| Face | Obstructed architecture | Positive survivor | Required construction |
|---|---|---|---|
| **14.1 Capacity, ideals and limits** | Fixed finite passive carriers, trace-class transports, fixed spectral gaps, and strong-to-trace convergence shortcuts. | Growing carriers, `det₂`/Hilbert–Schmidt realization, singular comparisons, gapless nonlocal ports, centered real-law limits. | Preserve the actual source and its divisor through a limit with sufficient norm control. O7. |
| **14.2 Algebra without orientation** | Finite-rank integral Frobenius lattices, rank/Chern data, Witt integrality or FE symmetry used as automatic purity. | Exact radial characters, framed curvature, index and ghost identities; infinite-rank scaling geometry remains possible. | An independent arithmetic positivity/orientation law. O8/O10. |
| **14.3 Diagnostic without producer** | A zero-built carrier or a named vanishing interface is treated as a source mechanism. Local unitary/lossless models lack exact Ξ landing. | Exact source-independent formulas and conditional receivers; admitted squarefree/retarded/full-support objects. | Build the source object first and prove its landing, vanishing or sign without assuming the conclusion. O7/O8/O9. |
| **14.4 Effectivity and RR** | Positive Frobenius graph cone, product pole/test cone, or positive integral Euler data used as RR-compatible Hodge geometry. | Hodge defect equals distinct right-zero count; finite-curve span classification; ghost reconstruction and explicit golden Beurling system. | Coupled arithmetic effectivity with independently proved RR/ampleness/Bézout properties. O10. |

ACS makes the distinction exact: existence of the required effectivity structure is itself equivalent to Hodge index. A conditional classification of cones **after** Hodge index is assumed cannot be used as its producer. The golden `q=5` datum shows that even positive integral prime counts and FE leave the missing geometric inequality unpaid. [TheScalingSurface](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/TheScalingSurface.lean); [BezoutEffectivityAndTheBeurlingObstruction](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/BezoutEffectivityAndTheBeurlingObstruction.lean); [TheGoldenCurveIsABeurlingSystem](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/TheGoldenCurveIsABeurlingSystem.lean).

## 5. Changed and removed local walls

This comparison records current dispositions, not a research diary.

| Earlier unresolved or weaker formulation | Current disposition | Wall still present |
|---|---|---|
| Centered-prime range ending at `12/7` | Strengthened to `30/17` in the stated unbalanced regime. | Balanced scales and full tails, 1.1/1.8. |
| Relative compensator alignment | Super-logarithmic relative decay and summable dyadic motion proved. | Absolute energy, 1.10. |
| Core debt on positive damping intervals | Exact bounded zeta-log-ratio law. | Complete signed covariance, 1.9. |
| Global nonnegative work considered a possible sufficient input | Refuted by first-cell limit `−1/2`. | Signed integrated loss is the viable receiver. |
| Positive-part loss used as if necessary | Strictly stronger than admission in explicit smooth lacunary models. | Actual signed budget, 1.9. |
| Any decaying positive aperture floor considered viable | Doubly exponential necessary decay; harmonic transport along linear apertures also impossible. | Nonnegative or graded-negative floors, 1.3. |
| Free movement of receiver origin | Sharp quadratic fixed-shift cost; universal drift preservation iff bounded. | Actual moving-tail payment, 3.6. |
| Quarter-density threshold treated as heuristic | Exact theorems for constant/residue-class/subgroup families; oscillatory amplitude classification. | General spectral patterns, 3.1. |
| Pole hyperplane expected to suffice at half damping | Exact logarithmic partial-sum energy; sharp square-root-log class and counterexample. | New-source endpoint control, 3.5. |
| Infinite receiver expected to control every centered cutoff | Generic equivalence exactly at/above half; explicit failure below. | Source-specific interchange, 3.6. |
| Strong continuity only paper-level | Lean proof of strong continuity and unbounded residue generator. | Critical norm/backward transport, 3.7. |
| CHMD/Weil graph comparison left open | Fixed-aperture graph/form norm equivalence proved. | Quotient lower bound and global uniformity, 3.3. |
| Pairwise payment hoped universally complete | Exact balance/holonomy criterion; nonlocal sharp survivors. | Actual packed-path construction, 3.4. |
| Raw cross-prime aggregate expected polynomial | Exponential mean field; normalized comb/resolvent and inverse-square deficit proved. | Signed compensated charge, 1.1/3.4. |
| Geometric obstruction described only as missing positivity | ACS gives exact RR/effectivity and negative-index receivers; integral positive Beurling countermodel. | Arithmetic effectivity, 14.4. |
| Li described as having no graded law | Reciprocal-depth growth law with slack proved. | Rate zero, not raw-width identification. |
| Heat positivity described only as fixed-rank | All-rank small-time orthant positivity proved. | Arbitrary signed vectors, 1.6. |
| Packet/Weil energy difference informal | Exact multiplicity ceiling; compact-packet mean-square limit under RH. | Simplicity/other field asymptotics, 3.8. |
| Full bump problem treated as one unfinished bridge | Odd no-axis full-energy finite-error capstone exists. | Axis/self-energy extension and certification scope. |

## 6. Scoped no-go register: all 44 named mechanisms

“No-go” retires the mechanism in the second column, not every route using similar words. The [existing killed-route catalogue](../rh-killed-routes.md#dead-mechanisms) retains longer theorem inventories. The table below preserves scope and positive salvage. Statements supported only by legacy report references are marked **legacy evidence** rather than newly certified.

| Code | Excluded mechanism | Strongest retained positive statement / viable replacement |
|---|---|---|
| **WIP** | Witt integrality, positive integral Euler data and FE imply purity. | Golden Beurling counterexample; exact ghost reconstruction and finite-span outer-eigenvalue index. Independent RR effectivity required. |
| **ODR** | Every unbounded origin drift preserves all admitted sequences. | Fixed-shift sharp quadratic cost; moving energy bounded by its exact weighted tail; bounded drift iff universal preservation. |
| **LGP** | Every positive signed incidence form admits lossless pairwise payment. | Universal completeness iff balanced holonomy; sharp frustrated-cycle and packed-path payment. |
| **WHL** | Critical-Wiener pole cancellation alone pays the half-damped receiver. | Exact partial-pole-sum logarithmic energy and sharp square-root-log class. |
| **PAF** | Summably small relative losses preserve a positive fixed floor at unbounded apertures. | Doubly exponential necessary floor decay; finite-aperture nonnegativity remains viable. |
| **ADJ** | Polynomial raw cross-prime majorant or nonnegative stated resonator remainder. | Genuine Hecke Cartesian incidence, negative coefficient-gap formula, normalized resolvent and `r^(−2)` correction. No negative complete-Weil test follows. |
| **HCT** | Infinite signed admission automatically pays all centered rows below half; backward transport is bounded. | Exact half threshold; admitted critical-Wiener subclasses below half; first-column receiver and forward strong continuity. |
| **AUT** | L² automorphic Parseval positivity locates ζ scattering poles. | Kuznetsov/spectral sieve and finite-cell energy estimates; a separate scattering-source law is needed. |
| **LLM** | Mollified first/mean-square moments force every off-line zero away. | Near-line density, explicit class-dependent mean-square floor and conditional mollifier optima; individual-zero control remains. |
| **GEN** | Fixed-part localization detects free orbits. | Exact support=fixed+twice-left count; retain unlocalized boundary. |
| **UCF** | Average/reflection-even data or critical Sobolev control pay the angular sub-quantum gate. | Exact angular quantization and isolated-zero Hermite detector; actual angular source bound needed. |
| **TEQ** | Theta equilibrium plus an unavailable maximum principle automatically confines zeros. | Equilibrium with an attained maximum gives a valid receiver; source equilibrium and escape control remain. |
| **CAL** | Negative-time collisions refute RH or give automatic backward monotonicity. | Positive-time multiple zeros refute RH; nonreal-count/right-limit laws. Exclude the initial nonzero branch independently. |
| **DSA** | Integral escape indicator automatically vanishes. | Pre-divisor transgression and genuine sub-unit bound would pay it. **Legacy evidence** for the named retired indicator. |
| **INT** | The stated finite-rank integral lattice carries compatible prime Frobenius actions at nonreal zeros. | Exact finite-rank obstruction and torsion law; infinite-rank geometry remains outside it. |
| **TWN** | Twin factorization gives the analytic square root it already requires. | Root-tower/nonvanishing receiver; global continuation/monodromy is the task. |
| **NEV** | Termwise Nevanlinna/Hermite–Biehler sign on an unknown zero-free domain proves that domain. | Exact source sign receiver; supply independent sign. |
| **ISG** | Balanced prime trees, constant normalization, or the specified harmonic/anchored chains yield a Ξ limit. | Centered ferromagnetic characteristic-function convergence suffices; field must diverge and center correctly. Other graph sequences remain possible. |
| **SRP** | Full-positive pole-weight cones at `β>1` approach the critical cone. | Full positivity forces `β=1` for arbitrary weights. Even-only super-residue question is distinct. |
| **FPR** | A fixed finite passive realization is exact for the source. | Growing passive carriers and the complete passivity receiver remain. |
| **DEF** | Estimates stable under the stated Euler deformation select ζ's line. | Exact deformation counterexample identifies the need for source-sensitive cross-modulus rigidity. |
| **CRT** | True finite-aperture positivity or finite prime-prefix agreement implies full positivity. | Exact on-line-shadow/Nyquist models; cofinal complete positivity decides width zero. Models are synthetic. |
| **TRC** | Trace-class bounded transport faithfully realizes the source inverse or its exact smooth counting remainder. | Hilbert–Schmidt/`det₂` carrier, correct singular-value capacity and nonintegrable counting fluctuation. |
| **APW** | Approximate/admixture weights provide another full-positive weight. | Unconditional rigidity of `Λ`, finite-block excess-mass budget; finite-window readings retain only a finite prime prefix. |
| **JPR** | Automatic high-shift Jensen hyperbolicity decides all degrees. | Explicit automatic regime and lower bound on first possible failure degree. |
| **TOR** | Independent torus/Steinhaus phase statistics equal the physical ζ orbit law. | Exact deterministic phase-law target. **Legacy evidence** for the original proposed transport. |
| **REF** | Toeplitz translation positivity automatically gives reflection/Hankel positivity. | Retain valuation grading and the actual reflected sign. **Legacy evidence** for the named counterexamples. |
| **CPF** | One radial Carleman pole form dominates the complete prime/polar source. | Exact signed rate measures; seek joint compensation in another admitted domain. **Legacy evidence**. |
| **TMD** | A global formation primitive is an independent easy input. | Integral formation/compact-descent receiver; primitive existence still needs source proof. **Legacy evidence**. |
| **TK** | Changing thermal ensemble eliminates the PA scalar defect. | Exact PA receiver; complete signed sign still required. **Legacy evidence**. |
| **BAG** | Finite Euler recurrence, nonvanishing targets or cofactor recurrence prove recurrence of a target containing zeros. | Local recurrence iff nonvanishing; sharp distance-to-nonvanishing-target return threshold; actual fixed-base tail remains. |
| **SEL** | A Selberg Laplace eigenvalue gap locates scattering poles. | Arithmetic spectral gaps remain valid; scattering input is separate. |
| **R1** | The specified anchored weak chiral-loss passage supplies a sub-unit defect. | Cubic=winding and seam bounds; matrix-complete source transgression remains. |
| **R2** | Prime-2 renewal self-similarity forces zero winding. | Arbitrary odd winding counterexamples; polynomial theta rigidity and modular cusp survivors. Full RN remains live. |
| **R3** | Holomorphic two-prime quantum slack supplies the missing growth bound. | Quantization, high-order slice receivers and mixed-class detection; low-order signed control remains. |
| **RAW** | Positive raw prime Dirichlet series converge to the critical boundary. | Raw abscissa is one; pole-subtracted signed coefficients have the RH convergence receiver. |
| **BD** | The specified even screw kernel remains Markov/Beurling–Deny at cofinal apertures after a scalar shift. | Exact boundary `2a≤log(plastic constant)`; non-Markov ground mechanisms remain possible. |
| **PTR** | Local Maxwell collars or the stated fixed critical stacks admit the exact prime conormals. | Lossless finite real-zero theorem, product-limit RH equivalence, thin-slab/nonlocal ports. |
| **HFR** | Fixed-rank heat-Hankel positivity or bounded rank-window constant decides RH. | Matched-rank inertia and positive-node witnesses; growing-window/all-signed receiver. |
| **HUS** | Averaged Husimi positivity forces pointwise slice sign. | Exact uncertainty-priced averaged identity; direct mixed-class detector. |
| **GAP** | A lossless realization with a fixed resonance-free gap lands on Ξ. | Exact gapless sech/Poisson handoff; resonances must accumulate arbitrarily near the axis. |
| **CCP** | Even ground-state parity selects RH in the stated finite-top/high-cluster classes. | Exact finite-top exponential ground law and Cauchy/Takagi phases. General infinite-spectrum parity is not classified. |
| **COS** | The stated finite differential/shift/compactly carried ports invert cosine shift exactly. | Exact nonlocal sech/Poisson source map and positive-depth defect-density bounds. |
| **POI** | Positive Poisson transport preserves real zeros for every real-rooted source. | Sharp two-tone threshold; actual-source map is exact, injective and dense-range. Ξ-specific zero-loss remains open. |

Directly inspected boundary examples include [WeilPoleWeightForcedOne](../../../formal/GaloisForLFunctions/RHTower/WeilPoleWeightForcedOne.lean), [SourceInverseTraceIdealNoGo](../../../formal/GaloisForLFunctions/RHTower/SourceInverseTraceIdealNoGo.lean), [IsingGraphCenteringLaw](../../../formal/GaloisForLFunctions/RHTower/IsingGraphCenteringLaw.lean), [PoissonPortTwoToneZeroLoss](../../../formal/GaloisForLFunctions/RHTower/PoissonPortTwoToneZeroLoss.lean), and the new families linked above. No legacy-only row is promoted to a fresh dependency audit by this table.

### Retired aliases are not additional live routes

The catalogue also retains 19 historical labels. Their status is architectural retirement or merger, not 19 independently established impossibility theorems about RH. Where only REF identifiers remain, locating the precise theorem is evidence-recovery work; it does not revive the old mechanism.

| Labels | Present mathematical survivor / home |
|---|---|
| A, C2/I, D1, N | Phase/trace/moment receivers and continued source signs; PA and related actual-source routes. |
| AF | Charged boundary separation; a singular cusp or global charged aggregate would be a changed producer. |
| AP, IW | Witt/scaling or cyclic clock classifications; source-compatible global existence remains the missing input. |
| B, F, M | Relative/singular carrier and graph-boundary constructions; no recovered bounded positive transport. |
| FD2 | Actual Ξ occurrence with persistent nonnormality; GTA's uniform Schur target. |
| G2, H | Marked Ward boundary and indefinite relation primitives; WD/orientation branch. |
| HB | Retarded weak/action realization survives native-L² failure; PM/PW-B. |
| J | Residual jets/determinants survive the unrenormalized logarithmic energy obstruction. |
| K | Infinite operators with reciprocal-Ξ capacity; TH/RN. |
| R | Marked wall class and external tensor curvature; CDC/JAS/WBF/TG. |
| RBH | Nonseparated, nonlinear or singular source data remain possible; PM. |
| SNR | A genuinely source-defined aperture invariant is required. |

## 7. What would count as removal of a core wall?

- **Wall 1:** a complete source-derived bound inserted into an existing receiver, with all required tails and quantifiers.
- **Wall 3:** an exact new transfer or sharp classification on a specified class and norm. It removes a methodological obstruction; it proves RH only if the source also satisfies the transferred estimate.
- **Wall 14:** an independently constructed arithmetic carrier/effectivity object with faithful landing and the required sign, followed by the proved receiver implication.

Local progress should be recorded at its actual scale. A larger certified window, a sharper signed sampling theorem or a new actual-row range is valuable without claiming that the entire family has disappeared.
