# Hard mathematical obstacles: current research frontier

Status: 2026-10-24. This report covers all 31 named routes, 17 standalone candidates, PW-B, and the supporting programmes that change their prospects. Companion documents: [task and research summary](hard-obstacles-summary.md), [walls](walls-ledger.md), [route unification](route-unification-ledger.md).

## Evidence and classification

The six specified reports supplied the inventory. Corpus searches and inspection of Lean statements and proof text supplied the corrections. The audit record is in `logs/review-2410-current-audit/`: saved searches, source inspection manifest, and working findings. No builds, Lean compilation, or executable axiom checks were run. “Established” below means supported by inspected source, not newly kernel-verified in this review. Conditional theorems retain their hypotheses; an interface containing the desired estimate is not a construction of that estimate. Specific source defects and unfinished modules are identified below.

Each route distinguishes:

- **(a) Known-method work:** finite calculations, explicit regularity and support checks, repairs of known identities, and applications of existing theorems once their independently justified premises are available.
- **(b) Open closing input:** an estimate, positivity theorem, or construction sufficient for RH, often proved equivalent to RH. These are mathematical research problems, not formalization tasks.
- **Auxiliary research:** a narrower question not settled by the inspected corpus. Absence here does not establish that nobody elsewhere knows a solution. Such questions are not silently promoted to worldwide open problems.
- **Excluded mechanism:** a proposition already contradicted by a theorem or countermodel. It belongs in neither backlog.

Write `Δ = supρ |Re ρ − 1/2|` and `Θ = 1/2 + Δ`. A receiver reading `Δ` at rate `σ` gives a fixed strip when `σ < 1/2`; closing RH requires `Δ = 0`. This logical implication is not a claim that every intermediate strip question is globally unsolved. Reciprocal depth, heat time, negative index and multiplicity energy are different invariants.

## 1. Results that determine the present frontier

### Exact critical endpoints and the complete Weil form

The critical incoming deficit has an absolutely convergent reciprocal-square zero expansion. Its pointwise exponential rate and its squared-energy rate attain the width endpoint; the latter has twice the exponent. RH is equivalent to bounded critical energy and to a lower bound for the corresponding coprime cross-work. The two-prime test uses mixed lags `k log p + l log q`, not two unrelated one-dimensional grids. The constant `C₄ = Σdistinct ρ mρ² / |ρ|⁴` is finite and positive unconditionally; the stated mean law tending to `C₄` assumes RH. An infimum for the linear-band slope does not by itself prove that the optimal slope is attained. [Critical endpoint and limit law](../../../formal/GaloisForLFunctions/BiScaleUncertainty/WeilLagCriticalDeficitEndpointAndLimitLaw.lean)

For every real compact `C²` test, with no parity or vanishing-moment restriction, the full Weil form has the exact decomposition

`Q(F) = (γ₀ − 2) mass(F) + Lévy(F) + 4 horizonEnergy(F) + 2∫ incoming · doubleGaugeDerivative(autocorrelation(F))`.

The all-parity Vinogradov–Korobov floor and the full/odd `H¹` floor-rate classifications are present. With the source's normalization, both admissible rate sets are the closed ray `[Δ, ∞)`; a uniform `H¹` floor is RH-equivalent. Transferring this to a mass-only floor requires a fixed second-gauge-to-mass bound. There is no unrestricted `L²` equivalence hidden in the Sobolev result. [All-parity identity and endpoint Sobolev laws](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/AllParityCriticalDeficitAndEndpointSobolevLaws.lean)

### Mass floors, clusters and aperture flow

A **compensated** negative-energy floor is exactly a ground-energy floor. An **uncompensated** negative-energy bound is equivalent to bounded local off-line depth mass. Bounded local depth mass is sufficient for the desired ground-rate equality; failure of that equality forces unbounded local depth mass. The converse is not established: unbounded local mass need not defeat compensation. Thus “ground rate equals width iff no collapsed clusters” is too strong. [Compensated width floors](../../../formal/GaloisForLFunctions/ArithmeticContinuationAndCriticalEnergy/CompensatedWidthFloorAndGroundEnergyRate.lean)

The aperture ground energy strictly decreases. RH is equivalent to strict positivity at every finite aperture; otherwise there is a unique zero crossing. Freezing the prime powers below the initial aperture separates the drop into a nonnegative geometric relaxation and an arithmetic shell jump, with opposite boundary-collar correlations bounding that jump. The missing information is the arithmetic payment of the shell flux. A nonnegative relative-flow law is RH-equivalent. [Non-stalling flow](../../../formal/GaloisForLFunctions/ArithmeticContinuationAndCriticalEnergy/TheApertureFlowNeverStalls.lean), [prime-shell beta function](../../../formal/GaloisForLFunctions/ArithmeticContinuationAndCriticalEnergy/ThePrimeShellBetaFunction.lean)

For large `A`, the upper ceiling has the form `μ(A) ≤ K exp(11A/2 − π exp(2(A−2)))`. A positive exponential lower floor is impossible. The ceiling alone does not prove `μ(A) → 0`; a negative decreasing function also lies below it. Admissible programmes include finite-aperture positivity, suitably vanishing positive floors, and graded negative floors.

### Fixed-aperture operator and Suzuki passages

CHMD's sharp windows and generator-domain passage are present in source and imported. Sharp cuts preserve the full generator domain; the commutator is bounded and skew-adjoint, uniformly in cut location. Expanding windows recover graph norm, positive/negative parts, the signed nodal pairing and the `oneL` defect. These are no longer paper-only blockers. The remaining nodal sign is mathematical. Aperture-uniform quotient constants are a separate possible strengthening, not an extra requirement if sign is proved directly at every aperture. [Sharp generator domain](../../../formal/GaloisForLFunctions/RHTower/CHMDSharpGeneratorDomain.lean), [nodal convergence](../../../formal/GaloisForLFunctions/RHTower/CHMDSharpWindowNodalConvergence.lean)

Suzuki's extended first variation covers every compact real `L²` source, including infinite Lévy energy. Common-support strong-`L²` liminf and recovery, and the literal high-dyadic deficit, are also present. Growing support and noncompact sources have explicit additional premises: real-lag autocorrelation decay faster than `e^(−t/2)`, or a weighted cutoff error such as `e^(2A_j)‖f_j−g‖₂ → 0`. An integer-dilation estimate does not supply real-lag decay. Common-shift theorems require their stated family bounds or floors. None supplies the missing Weil sign. [Extended first variation](../../../formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiCriticalL2FirstVariation.lean), [moving-window limits](../../../formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiCriticalMovingWindowDeficit.lean), [moving aperture](../../../formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiCriticalMovingAperture.lean)

### Orientation, index and sections

For a functional-equation-symmetric tempered divisor configuration, orbit Hodge positivity, the orbit Hasse–Weil bound, and blindness to off-line pairs are equivalent. Generic real compact tests exist; one generic actual-zeta orbit decides RH. Its orientation growth reads `Δ`. Positive scale-stable families are classified by a common endpoint choice for each off-line pair. Finite-target detection has an exact index law, but a separately chosen member for every finite target is not one member seeing infinitely many targets. The Riemann–Roch theorem still requires an ample cone of nonnegative degree. [Orientation of a cycle](../../../formal/GaloisForLFunctions/ArithmeticOrientationGeometry/TheOrientationOfACycle.lean), [orientation rate](../../../formal/GaloisForLFunctions/ArithmeticOrientationGeometry/TheOrientationRateIsTheDepthOfTheDeepestSeenZero.lean), [scale-stable families](../../../formal/GaloisForLFunctions/ArithmeticOrientationGeometry/TheOrientationOfScaleStableFamilies.lean)

The global index `D` counts distinct right-hand off-line zeros. Its finiteness is equivalent to eventual critical-line confinement and to the stated uniform heat/collision/window-count bounds. It implies a fixed zero-free strip but is stronger than that statement. When finite, `D` is even and RH is equivalent to `D < 2`. Small-time collision mass also includes excess multiplicity. Finite index at each aperture does not prove finite global index. [Index exit](../../../formal/GaloisForLFunctions/ArithmeticOrientationGeometry/TheIndexExit.lean)

The base arithmetic theta section functional already exists: `h⁰(d) = log θ(exp(−2d))`, with positivity, monotonicity, `h⁰(d)−h⁰(−d)=d`, asymptotics, and the completed-zeta Mellin identity in its domain. The missing object is the coupling to test components on the arithmetic surface that supplies effectivity and the required sign. Recreating the base theta identity would not advance that obstruction. [Theta h⁰ of Spec Z](../../../formal/GaloisForLFunctions/ArithmeticOrientationGeometry/TheThetaH0OfSpecZ.lean)

### Source qualifications that affect the backlog

| Source | Present finding | Consequence |
|---|---|---|
| `BezoutValuationIncidence/TheDiagonalDualNormIsArchimedean` | `sum_range_moebiusWindowRow` has an unparenthesized outer finite sum; the literal statement fails at `Q=3, x=0`. | Repair the intended identity before certifying the actual-Möbius diagonal specialization or downstream every-modulus claims. The abstract balanced estimate is separate. |
| `BezoutValuationIncidence/TheMeanValueIsTheLeadingCoefficientOfTheReceiver` | Mean-error expressions place `−L*x` inside the sum; the displayed algebra does not establish the intended statement. | Known-identity repair; dependent exact mean claims remain qualified. |
| `BezoutValuationIncidence/TheParityPairAtTheLeadingExponent` | The squarefree mean branch has the same summation-scope problem. | Do not count its dependent exact `μ²` coefficient as verified. |
| `ArithmeticCastelnuovoSeveri/ZeroDensityFilteredWeilPositivityAndCoercivity` | Quadrature, Plancherel and sum–integral majorants are present. Headline averaged coercivity/strict-positivity conclusions are absent. | Partial development; neither a finished theorem nor automatically routine remaining work. |
| `BiScaleUncertainty/ZeroDensityFilteredCriticalDeficitLaw` | The audited slab exponent is `3γ₀`, exactly: `(3a/4)(θ/2)=3aθ/8`. | The previously reported factor-two deficit is not a current obstacle. This checks that calculation, not every dependency in the module. |
| Import integration | CHMD sharp windows/generator, compact-`L²` Suzuki, moving-window limits, smooth detector, explicit kernel shape, Heath–Brown all-length and Guth–Maynard sharp `S₂` modules are imported. | Do not leave their old implementation tasks in the backlog. Theta `h⁰` and filtered coercivity require their own integration/status check. |

## 2. Known-method work register

These IDs are shared by the companion reports. They classify genuine work without smuggling an open estimate into a “routine” premise.

| ID | Work | Completion criterion |
|---|---|---|
| **J1** | Repair the three summation-scope chains above and recheck their dependants. | Correct literal statements, proofs of the intended elementary identities, then a dependency audit. |
| **J2** | Reconcile imports, declarations and documentation for current working modules. | Report only declarations actually present; integrate finished modules when authorized. Completing an absent positivity theorem is not included. |
| **J3** | Instantiate finite identities and certificates: Gram matrices, moment blocks, divisor polynomials, trace identities, finite schedules, finite incidence allocations. | Every finite term and error accounted for. A finite computation is not an all-height theorem. |
| **J4** | Check explicit support, smoothness, integrability, domain and norm premises for a specified source/family. | Prove exactly the hypotheses needed by an available transfer. An unknown uniform family bound belongs to research. |
| **J5** | Transport an independently established estimate through exact dictionaries, with the correct quantifiers. | Preserve damping, aperture, degree, height and horizon dependence; state the resulting conclusion at its actual strength. |
| **J6** | Calculate explicit constants, finite tower extrema and finite low-sector matrices within proved regimes. | Certified finite result, including mixed terms where relevant. Uniform extrapolation remains separate. |
| **J7** | Check transitive proof dependencies and kernel acceptance after repairs/integration. | A dedicated authorized verification pass. Not performed here: user requested no builds. |

## 3. The 31 routes

### WL — Weil lag function

**Present result.** Universal-spline, one-sided lag, incoming-deficit, critical-energy and coprime-cross-work receivers identify the same zero-width endpoint. Endpoint attainment is now explicit; the RH mean law retains its RH premise. The reciprocal-square expansion makes cancellation exact before estimation. [Endpoint source](../../../formal/GaloisForLFunctions/BiScaleUncertainty/WeilLagCriticalDeficitEndpointAndLimitLaw.lean)

**(a)** J3–J5: specialize the probe, compute its prime/polar terms and transport a supplied estimate. **(b)** Prove bounded critical energy, the equivalent cross-work lower bound, or a sufficient one-sided arithmetic lag estimate. Available zero-free-region savings do not supply the critical endpoint. Raising a deficit to a power multiplies its rate; it does not improve the normalized width. **Walls:** 1.1, 1.7, 3.8.

### RW — restricted Weil ground energy

**Present result.** RH iff the ground energy is positive at every finite aperture. Full and odd `H¹` floor rates attain `Δ`. The full mass-normalized problem retains compensation and local-depth-mass distinctions. Strict aperture flow and the shell decomposition expose where arithmetic input must enter. [All-parity laws](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/AllParityCriticalDeficitAndEndpointSobolevLaws.lean), [shell law](../../../formal/GaloisForLFunctions/ArithmeticContinuationAndCriticalEnergy/ThePrimeShellBetaFunction.lean)

**(a)** J3–J6: fixed-aperture forms, regularity, explicit low-sector matrices, and transport of a supplied graded step bound. **(b)** Sign the complete low-frequency sector and its mixed terms at every aperture, or control the total shell loss. **Auxiliary:** arithmetic local-depth-mass bounds and quantitative compensation. Their equivalence to every desired mass-floor statement is not proved. Fixed positive or exponential floors are excluded. **Walls:** 1.3, 1.11, 1.13, 3.2–3.3.

### FU — CCM-FU signed prime scheduling

**Present result.** An upper bound for the completed Möbius–divisor Abel moment is RH-equivalent. Prime-clock synthesis and source-energy completion identify an off-diagonal producer; cheap diagonal approximants do not sign it. [One-sided Abel receiver](../../../formal/GaloisForLFunctions/RHTower/CCM/CCMFUSuzukiMobiusDivisorOneSided.lean)

**(a)** J3–J5: finite schedules, clock kernels and the complete Abel identity. **(b)** Bound the completed moment including inherited action, inter-block covariance and moving endpoints, or sign the completed off-diagonal form. Vanishing diagonal cost allows escape and does not imply graph compactness. **Walls:** 1.1, 1.6, 3.2, 14.1.

### RP — Route-P / SP-E history floor

**Present result.** An eventual floor `−B(K+2)` for the literal matched-quantile history is RH-equivalent. Partial hyperbola, centroid and square-debt identities isolate rather than pay the complete history. [Linear-floor criterion](../../../formal/GaloisForLFunctions/RHTower/SPEQuantileRieszRoutePLinearFloorCriterion.lean)

**(a)** J3–J5: finite-history bookkeeping and application of a separately proved floor. **(b)** One full-history bound paying high-LCM interactions, centroid/square debt, core drift and singular transport. Strong operator convergence does not give trace-norm convergence or control the missing noncompact tails. **Walls:** 1.1, 1.8, 3.6, 14.1.

### PA — prime–archimedean source passivity

**Present result.** The prescribed high-positive-frequency current criterion, and even a signed compact measure reproducing all required moments, decide RH. Each fixed finite moment block can be positive beyond a block-dependent threshold. That is not positivity of all orders at a common threshold. [Frequency accretivity](../../../formal/GaloisForLFunctions/RHTower/PrimeArchEndpointFrequencyAccretivity.lean), [signed moment completion](../../../formal/GaloisForLFunctions/RHTower/PrimeArchSignedCompactCompletionCollapse.lean)

**(a)** J3, J6: specified Hausdorff blocks and saddle-band calculations. **(b)** An order-uniform sign or a complete moment realization; positive saddle bands leave their complement unpaid. **Auxiliary:** quantitative order dependence useful enough to survive the receiver's limit. Finite atom repairs and fixed finite passive carriers do not provide that limit. **Walls:** 1.5–1.6, 14.1.

### MC — Möbius cancellation at half power

**Present result.** The square-root-with-slack Mertens bound remains the closing estimate. An exact alternative is `θ(ε,t)<1` for every `0<ε<1/2`, `t≠0`, in the long-sawtooth/tail gap. High-height Vinogradov–Korobov collars and bounded-height small-`ε` collars are proved. Heath–Brown all-length pair sums and the sharp all-`k` Guth–Maynard `S₂` input are already in source. [Gap and collars](../../../formal/GaloisForLFunctions/TransHorizonIncidenceMechanics/OscillatingProbeSourceEstimatesEnergyGapAndCollarLimitations.lean)

**(a)** J1, J3–J5: repair affected row specializations and apply independent estimates in their actual ranges. **(b)** Global cancellation or interior anti-alignment between the collars, with principal counterterms and high-product remainders jointly controlled. **Auxiliary:** balanced-scale source correlations. Planted Euler factors preserve the collars; invertible Wiener filters preserve admission classes. Neither supplies the missing interior sign. **Walls:** 1.1, 1.12, 3.10.

### TT — theta-tail and heat–Cassini currents

**Present result.** The directed Wold receiver bounds **`D_t(N)+Q_t(N)/2`**, for every `0<t<1/2`. Omitting the diagonal term changes the statement. Full odd Weil positivity is another closing formulation. Inner-chamber positivity and seam identities do not cover the whole source. [Directed covariance criterion](../../../formal/GaloisForLFunctions/RHTower/PaperWoldDirectedCovarianceRH.lean)

**(a)** J3, J5–J6: exact chamber identities and complete covariance bookkeeping. **(b)** The signed nonlocal covariance bound at every required parameter, or complete odd positivity. Translation averages and successively larger fixed chambers do not alone resolve depth or uniformity. **Walls:** 1.3, 1.6, 3.2, 3.4.

### LA — line anchor

**Present result.** Critical-time Laguerre/Jensen/log-derivative signs and heat confinement remain closing receivers. Positive-time reality and simplicity now hold beyond an explicit horizon of scale `exp((27/40+ε)/t)` for `0<t≤1/8`. This horizon diverges as `t↓0`. Gaussian tails and fixed-degree limits do not give all-degree critical-time sign. [Interior Lindelöf horizon](../../../formal/GaloisForLFunctions/RHTower/KiKimLeeInteriorLindelofHorizon.lean)

**(a)** J3–J6: finite Jensen matrices and rigorous use of the positive-time horizon. **(b)** All-height, all-degree sign at the critical endpoint. **Auxiliary:** uniform error control near clusters and a passage from positive heat to zero heat. The present positive-time theorem does not furnish that passage. **Walls:** 1.2, 1.6, 1.11.

### TG — topological sub-unit gate

**Present result.** The anchored cubic trace equals winding and the corresponding zero count. An integral nonnegative residual below one must vanish, but the trace identity does not establish its sign or the bound below one. [Cubic specialization](../../../formal/GaloisForLFunctions/RHTower/FormationAnchoredCubicSpecialization.lean)

**(a)** J3, J5: trace/index bookkeeping and the final integer argument. **(b)** A source-derived matrix-complete residual sign and all-disc sub-unit estimate, or the stated central-gap substitute. Integral counts are detectors, not arithmetic orientation. **Walls:** 1.2, 14.2–14.3.

### HF — positive Hodge form / prime-window ceiling

**Present result.** Exact forcing-sign dictionaries connect the full pairing to arithmetic receivers. The ceiling `c(L)≤e^(L/2)+B(1+L)` implies the reflected prime–polar AIP allocation directly. Finite negative index and positive high-frequency complements leave the low sector. Rigidity selecting `Λ` from the full-positive cone is not existence of positivity. [Forcing-sign dictionary](../../../formal/GaloisForLFunctions/ArithmeticOrientationTheory/PoleSubtractionAndTheForcingSignDictionary.lean)

**(a)** J3–J6: collar partitions, finite Gram data and ceiling-to-allocation transfer. **(b)** The complete pairing sign or the `O(L)` ceiling remainder. **Auxiliary:** TTPC's actual coalescent surplus estimate; a bound `≤(1/18+o(1))N` in that certificate gives a `3/4` line proportion, not RH. **Walls:** 1.3–1.4, 3.4, 14.4.

### CHMD — causal hyperbolic–modular duality

**Present result.** The odd-resolvent obstruction is a sign-changing eigenstate above `1/2`; its nodal criterion compares `sourceEnergy(absGraph)` with `4 sourcePair(posGraph,negGraph)`. Fixed-aperture completion, sharp cuts, generator-domain preservation and signed nodal convergence are established. [Generator domain](../../../formal/GaloisForLFunctions/RHTower/CHMDSharpGeneratorDomain.lean), [nodal limits](../../../formal/GaloisForLFunctions/RHTower/CHMDSharpWindowNodalConvergence.lean)

**(a)** J4–J5: move a concrete vector through those completed domains. **(b)** The nodal/reflected-prime inequality excluding every obstructing eigenstate. **Auxiliary:** aperture-uniform quotient estimates, if a chosen proof needs them. They are not necessary additional work for a direct all-aperture sign proof. **Walls:** 1.3, 3.3–3.4.

### TH — theta moment positivity

**Present result.** Small-time positivity on the nonnegative coefficient orthant holds at all ranks. It is weaker than positivity for arbitrary signed coefficient vectors. Fixed-rank coercivity and the Weil-margin bridge with degree/time coupling do not give all ranks at one common admissible time. [Orthant positivity](../../../formal/GaloisForLFunctions/RHTower/XiHeatHankelFormOrthantPositivity.lean)

**(a)** J3, J6: finite-rank matrices and explicit rank/time constants. **(b)** Full signed heat-Hankel positivity with the receiver's common-time quantifier. **Auxiliary:** decoupling degree from the time window in the Weil-margin bridge. **Walls:** 1.6, 3.11.

### RN — theta renewal and singular comparison

**Present result.** A compact Hilbert–Schmidt cone-preserving renewal operator realizes the literal denominator through an exponential factor and `det₂`, with the prescribed divisor correspondence. Cone preservation is not self-adjointness or confinement of complex resonances. [Positive Fredholm realization](../../../formal/GaloisForLFunctions/RHTower/ThetaRenewalPositiveFredholm.lean)

**(a)** J3–J5: determinant normalizations and resonance bookkeeping. **(b)** The boundary-current orientation or comparison sign that confines the faithful divisor. The existing realization removes a representation problem, not the zero-location problem. **Walls:** 1.2, 14.1, 14.3.

### WD — Ward orientation and horizontal collision

**Present result.** A nonnegative global cap measures off-line defect. Saturation of the arithmetic Euler trace by the critical-line sum at one permitted positive parameter decides RH. Shifted finite-head heat cones read width exactly; the explicit pure-quadratic sufficient heat is proportional to `δ₀²/log(180|t|)`. Local divisor geometry supplies sharp model repair costs, not actual-zeta coefficient signs. The prime-Cesàro first-coefficient formula retains `XiC(t)≠0`. [Global cap and finite-head arithmetic](../../../formal/GaloisForLFunctions/RHTower/XiWardGlobalCapAndFiniteHeadArithmetic.lean)

**(a)** J3–J6: finite polynomial heat transforms and the exact trace identities, checking normalization and central zeros. **(b)** Arithmetic cap vanishing/trace saturation or actual heated-slice coefficient positivity at closing scales. **Auxiliary:** source-selective cofactor repair. Positive model multipliers do not universally reflect the coefficient cone. **Walls:** 1.2, 1.14, 3.4.

### LI — Li even-cross clock

**Present result.** The clock reads reciprocal depth `|β−1/2|/(γ²+(β−1/2)²)`, with the corpus bound `≤1/431`. RH is equivalent to the appropriate subexponential lower floor. This rate is not `Δ`. [Actual clock growth law](../../../formal/GaloisForLFunctions/RHTower/LiEvenCrossActualClockGrowthLaw.lean)

**(a)** J3–J6: finite Li/Jensen data with a justified tail. **(b)** The all-time subexponential lower floor. **Auxiliary:** a stronger positive reciprocal-depth bound; it is a height-weighted improvement, not a fixed zero-free strip. **Walls:** 1.5, 3.1, 3.8.

### SZ — Suzuki screw and shifted-kernel limits

**Present result.** Compact-`L²` first variation, infinite-energy handling, common-support joint liminf/recovery and literal high-dyadic deficits are established. Noncompact and moving-support versions retain explicit quantitative hypotheses. The all-test deficit criterion is RH-equivalent. [First variation](../../../formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiCriticalL2FirstVariation.lean), [moving-window deficit](../../../formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiCriticalMovingWindowDeficit.lean)

**(a)** J4–J5: verify a specified family's cutoff, support and correlation assumptions; then apply the limit or common-shift theorem. **(b)** The complete deficit sign for all compact tests, equivalently RW. **Auxiliary:** stronger noncompact families with controlled real-lag tails. Growing support is optional, not a prerequisite for closing the compact criterion. **Walls:** 1.3, 3.3, 3.6.

### PM — pronic Möbius energy

**Present result.** Critical admission is a uniform horizon bound at cofinally small positive damping. A canonical arithmetic corrector is already constructed; its height `H=1+dualResidual` is comparable to `1+energy` within explicit factors. The integrated signed loss is a log-height difference. Cofinal control is RH-equivalent. [Arithmetic corrector](../../../formal/GaloisForLFunctions/ArithmeticCompensationTheory/ConstructingAnArithmeticCorrector.lean)

**(a)** J3–J5: calculate the corrector and use the exact continuation identity. **(b)** Bound the signed loss uniformly in horizon as damping approaches zero, or directly bound pronic energy. **Auxiliary:** absolute compensation, non-unit repair and exclusion of energy escape. Requiring nonnegative work everywhere is false; bounding only positive-part loss is stronger than the exact criterion. **Walls:** 1.8–1.10, 3.6–3.7, 3.10.

### JAS — joint ancestry budget

**Present result.** The specified level-one positive-power budget reads a fixed strip; the half-power endpoint reads RH. The endpoint is stronger than merely obtaining some positive power. [Budget zero-free law](../../../formal/GaloisForLFunctions/RHTower/JointAncestryBudgetZeroFreeLaw.lean)

**(a)** J3–J5: finite ancestry budgets and exponent bookkeeping. **(b)** The critical half-power budget with uniform history/horizon control. An unquantified improvement cannot be substituted for that endpoint. **Walls:** 1.1, 1.6, 3.4.

### CTF — cofactor test family / dual approximation

**Present result.** The dual residual is `(1−readout)² + centeredGramEnergy`. Its smallness requires **readout tending to one and centered energy tending to zero**. The Rayleigh quotient, variance criterion and primal/dual budget equivalences are present. Fixed-damping bounded energy and approximation along varying damping have different quantifiers. [Dual quotient and cusp laws](../../../formal/GaloisForLFunctions/BezoutValuationIncidence/TheDualProblemRayleighQuotientAndCofactorCuspLaws.lean)

**(a)** J3–J6: finite coefficient optimization and use of supplied variance bounds. **(b)** Produce actual arithmetic cofactor coefficients meeting the complete small-residual criterion at closing damping scales. **Auxiliary:** bounded inverse control from residual and pole trace; algebraic injectivity does not give it. **Walls:** 1.8–1.10, 3.12.

### HCF — heat covariance factorization

**Present result.** The two-prime source-sampling criterion on the specified polar hyperplanes, for all degrees, is RH-equivalent. Finite samples and fixed degrees do not provide the complete covariance factorization. [Two-prime source sampling](../../../formal/GaloisForLFunctions/RHTower/XiGaussianHeatTwoPrimeSourceSampling.lean)

**(a)** J3–J6: explicit finite Gram factorizations and polar constraints. **(b)** A source-derived positive factorization for every required degree and parameter. Similarity to TH does not remove its sampling and uniformity obligations. **Walls:** 1.6, 3.4, 3.11.

### XN — xi Newton disc

**Present result.** The useful Newton source margin is an **interior-disc** bound/self-map condition. Boundary control alone does not imply it. [Disc source margin](../../../formal/GaloisForLFunctions/RHTower/XiNewtonDiscSourceMargin.lean)

**(a)** J3–J5: finite-disc identities and application of a valid interior margin. **(b)** Obtain the required all-disc interior source control and compatibility, sufficient to exclude off-line zeros. **Walls:** 1.2, 3.2, 14.3.

### BAG — Bohr almost-periodic/strong recurrence

**Present result.** Strong recurrence on every compact set of the relevant right strip is RH-equivalent; the local criterion is tied to nonvanishing on that compact. [Compact strong recurrence](../../../formal/GaloisForLFunctions/RHTower/ZetaStrongRecurrenceOnCompactSets.lean)

**(a)** J4–J5: check a particular compact and transport an independently available recurrence estimate. **(b)** Actual-zeta recurrence on all required compacts without presupposing the missing nonvanishing. Universality or recurrence on selected compacts is insufficient. **Walls:** 1.2, 3.2, 14.3.

### EWU — even Weil universality / variational sign

**Present result.** The relevant constrained minimum is attained. Attainment does not determine its sign, and quadratic constraints cannot be treated as a linear subspace without proof. [Blind variational attainment](../../../formal/GaloisForLFunctions/RHTower/EvenSectorBlindVariationalAttainment.lean)

**(a)** J3–J6: explicit admissibility, compactness applications and finite constrained calculations. **(b)** Nonnegativity of the attained minimum throughout the required family, including polar and mixed contributions. **Walls:** 1.3, 3.3–3.4.

### GTA — Gaussian tail / Hedenmalm–Schur decay

**Present result.** Uniform decay of the Schur quartic spectral quantity is RH-equivalent. Pointwise or finite-rank Gaussian-tail control is weaker. [Quartic spectral decay equivalence](../../../formal/GaloisForLFunctions/RHTower/Hedenmalm/HedenmalmThetaSchurQuarticSpectralDecayEquivalence.lean)

**(a)** J3–J5: finite Schur data and exact transform identities. **(b)** The full uniform decay with the theorem's rank and tail quantifiers. **Walls:** 1.2, 1.6, 3.2.

### OWU — odd Weil universality

**Present result.** Complete odd compact-test positivity is an RH criterion; explicit Markov-pole and hyperbolic formulas isolate a negative polar contribution. Finite positive windows do not pay that term for every test. The odd incidence theorem gives an exact alternative allocation formulation. [Global incidence allocation](../../../formal/GaloisForLFunctions/ArithmeticIncidencePositivity/GlobalIncidenceAllocationCondition.lean)

**(a)** J3–J6: odd-test identities, finite windows and testwise allocation dictionaries. **(b)** Complete odd positivity, or its exact shared-budget allocation. **Walls:** 1.3, 3.4.

### PBM — prime-bias Mellin / regularized logarithm

**Present result.** Convergence throughout `Re s>1/2` of the specified regularized coefficients `(Λ(n)−1)/log n`, and the corresponding prime formulation, is RH-equivalent. Raw positive prime series are not the receiver. [Regularized log-zeta abscissa](../../../formal/GaloisForLFunctions/RHTower/RegularizedLogZetaAbscissa.lean)

**(a)** J3–J5: regularization and partial-summation identities. **(b)** The cancellation required for convergence on the whole half-plane. Dropping the subtraction changes a convergent cancellation problem into a divergent positive one. **Walls:** 1.1, 1.5.

### RB — Robin bound

**Present result.** The eventual strict Robin inequality on colossally abundant integers is equivalent to RH. Finite verification does not establish an eventual tail. [Colossally abundant reduction](../../../formal/GaloisForLFunctions/RHTower/RobinColossallyAbundantReduction.lean)

**(a)** J3, J6: specified finite divisor sums and extremal comparisons. **(b)** An arithmetic proof of the strict inequality for the complete eventual extremal sequence. **Walls:** 1.1, 1.6.

### SRT — square-root threshold and smooth detection

**Present result.** A smooth Weil detector for an off-line zero has a **quadratic** aperture bound `C δ^(−2)(4+|γ|)²`; the degree-38 statement is a weaker corollary. This detector is already implemented and imported. It identifies a witness, not positivity of the source. [Polynomial-aperture detector](../../../formal/GaloisForLFunctions/SquareRootThreshold/SmoothWeilDetectorPolynomialAperture.lean)

**(a)** J3–J6: instantiate the witness and its explicit norms. **(b)** An arithmetic estimate controlling those detector tests at the required horizons, or the corresponding source sign. **Auxiliary:** sharper observability constants and actual source readings across the square-root threshold. **Walls:** 1.1, 3.1–3.2.

### ACT — arithmetic criticality / single-shift completeness

**Present result.** Any one fixed positive shift, tested against all even compact profiles, decides RH; the criterion remains complete with profiles vanishing near the origin. The shift quantifier has already been reduced. [Single-shift completeness](../../../formal/GaloisForLFunctions/ArithmeticCriticalityTheory/SingleShiftCompleteness.lean)

**(a)** J3–J5: fixed-shift source identities and profile regularity. **(b)** The required sign for the entire profile class at that shift. Proving it for a finite or positive-coefficient subclass does not suffice. **Walls:** 1.3, 3.1, 3.4.

### AIP — arithmetic incidence positivity

**Present result.** For each odd compact `C²` test, the full allocation condition is equivalent to nonnegativity of its complete zero form. All-test allocation is equivalent to RH; one suitable plateau per test suffices in the stated formulation. The axis/self-energy extension is not the remaining gap. [Exact allocation condition](../../../formal/GaloisForLFunctions/ArithmeticIncidencePositivity/GlobalIncidenceAllocationCondition.lean)

**(a)** J3–J6: finite ledgers, plateau choices and transport of an already valid global allocation. **(b)** Construct the shared signed budget for every test, retaining Gamma, pole, mixed terms and all prime incidences. Local payments that reuse surplus do not satisfy this condition. **Walls:** 1.3, 3.4.

### ACS — arithmetic Castelnuovo–Severi / arithmetic Hodge geometry

**Present result.** Finite-aperture negative index, positivity away from the low grid, all-parity endpoint floors, orientation classification and base theta sections are available. A generic cycle's Hasse–Weil bound already decides RH. The source-defined ample/effective cone and its positivity are not constructed by naming the cone or imposing its sign as a field. [All-parity floors](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/AllParityCriticalDeficitAndEndpointSobolevLaws.lean), [cycle orientation](../../../formal/GaloisForLFunctions/ArithmeticOrientationGeometry/TheOrientationOfACycle.lean)

**(a)** J2–J6: apply existing index/Riemann–Roch identities with genuinely supplied hypotheses, and connect completed base theta data to explicit finite constructions. **(b)** An independent arithmetic effectivity or Hasse–Weil principle controlling the actual test components; equivalently the required full orientation/sign. **Auxiliary:** filtered coercivity completion and quantitative family/index bounds. The filtered module's advertised final conclusions are still absent. **Walls:** 1.3, 3.8, 3.13, 14.4, 14.6–14.7.

## 4. The 17 candidates and PW-B

A candidate is not a proof route merely because its final interface implies RH. The table identifies what exists before that interface and what still has to be produced.

| Candidate | Present construction / exact boundary | (a) Known-method work | (b) Missing closing mathematics |
|---|---|---|---|
| **APF — adelic/Fourier reconstruction** | Countable Fourier data reconstruct the cycle outside one common null set. Reconstruction does not force its off-line component to vanish. [Source](../../../formal/GaloisForLFunctions/RHTower/PaperZetaCycleFourierReconstruction.lean) | J3–J5: specialize the reconstruction and justify a concrete countable family. | An arithmetic annihilation/orientation law for the reconstructed cycle. |
| **BSH — framed-mate curvature** | The specified curvature components detect critical-line support. The curvature receiver is not a construction of a flat arithmetic mate. [Source](../../../formal/GaloisForLFunctions/RHTower/Deninger/DeningerOneSidedFramedMateCurvatureTransgression.lean) | J3–J5: curvature/transgression identities for supplied data. | Produce the relevant curvature vanishing or sign from the actual arithmetic source. |
| **CDC — constitutive dagger confluence** | A descending, calibrated pre-divisor potential implies the desired line condition. Descent and calibration are input obligations. [Source](../../../formal/GaloisForLFunctions/RHTower/ConstitutiveDaggerConfluence.lean) | J3–J5: check finite confluence and normalization identities. | A globally descending, source-defined calibrated potential without embedding the desired orientation in its definition. |
| **DR — dyadic roots** | Symmetric Littlewood/cusp constructions provide local root data. A compatible global root system is stronger. [Source](../../../formal/GaloisForLFunctions/RHTower/XiSymmetricLittlewoodZeroFreeCuspDyadicRoots.lean) | J3–J4: finite root compatibility and domain checks. | Global compatible roots across the required domain, with zero obstructions removed arithmetically. |
| **EGC — Euler/gamma contour correction** | Complete correction on fixed vertical lines is available. It does not bound expanding outer contours. [Source](../../../formal/GaloisForLFunctions/RHTower/PaperEGCCompleteCorrection.lean) | J3–J5: fixed-contour correction and tail formulas in proved ranges. | Uniform outer-boundary control sufficient to pass to the closing contour limit. |
| **EWJ — Euler–Wold compact character** | Compactness is classified by `c=0` or `−a+b+2d=0` in the model. This identifies the exact algebraic locus. [Source](../../../formal/GaloisForLFunctions/RHTower/PaperEulerWoldCompactCharacter.lean) | J3: evaluate a proposed character and its normalization. | A faithful actual-arithmetic realization on the admissible locus that supplies the needed sign. |
| **FEL — free-energy/likelihood contrast** | The BSY identity expresses the contrast as an off-line zero sum. An exact identity does not show the contrast is zero. [Source](../../../formal/GaloisForLFunctions/RHTower/BalazardSaiasYorZeroSum.lean) | J3–J5: regularized contrast accounting. | Arithmetic vanishing of the full cofinal contrast, including its residual. |
| **HJ — pre-divisor reflection stabilization** | Prime/Gamma reservoir and reflection data exist before zero selection. The global one-port interface contains unconstructed forward and reflected stabilization fields. [Source](../../../formal/GaloisForLFunctions/RHTower/XiPreDivisorReflectionDefectStabilization.lean) | J3–J4: finite reservoir identities and reflection checks. | Prove the global stabilization weld at every spectral point. Supplying an instance with that field is the hard theorem. |
| **IRK — completed inverse rotation kernel** | The completed relation is invertible off the critical line. This is not an independent lift of the original arithmetic source into the required kernel. [Source](../../../formal/GaloisForLFunctions/RHTower/PrimeRotationXiCompletedResolution.lean) | J3–J5: resolvent and completion identities. | Construct the source lift/landing and extract its orientation without assuming zero confinement. |
| **MSC — squarefree Hilbert source** | An unweighted squarefree `L²` source exists. Square summability alone is not the required Sonin/Weil positivity. [Source](../../../formal/GaloisForLFunctions/BiScaleUncertainty/SquarefreeUnweightedHilbertSource.lean) | J3–J4: source membership and explicit transforms. | The correct positive landing or arithmetic pairing sign. |
| **PCS — chronological dilation carrier** | The unilateral-shift carrier retains a defect under the proposed dilation. Enlarging a carrier does not erase that defect automatically. [Source](../../../formal/GaloisForLFunctions/RHTower/PCSChronologicalDilationCarrierObstruction.lean) | J3–J4: finite carrier and dilation calculations. | A faithful larger realization with controlled defect, boundary transport and closing orientation. |
| **PTR — photonic lossless ports** | Locally uniform finite-port approximation is RH-equivalent in the stated product model. A converse built from the zeros is not a pre-divisor producer. [Source](../../../formal/GaloisForLFunctions/RHTower/PhotonicLosslessProductPortRH.lean) | J3–J4: finite port products and explicit approximation errors. | A source-derived compatible approximating family with local uniformity and divisor fidelity. |
| **RFHM — survival information** | Energy probabilities erase grade; the phase complement retains additional information. An unsigned information statistic cannot recover discarded orientation. [Source](../../../formal/GaloisForLFunctions/RHTower/PaperRFHMSurvivalInformation.lean) | J3: exact finite energy/phase decompositions. | A realizable phase-sensitive invariant and a source law controlling it strongly enough to orient the divisor. |
| **SC — scattering completion** | Recovery of the prescribed wall is equivalent to vanishing of the wall vector. The completion theorem does not prove that vector vanishes. [Source](../../../formal/GaloisForLFunctions/RHTower/PaperKreinWallFourierCompletion.lean) | J3–J5: completion identities and domain checks. | Arithmetic wall-vector vanishing or a faithful positive source construction forcing it. |
| **SEC — time-one gamma-jet Fock source** | Time-one Fock boundedness is a line-support criterion. Pre-divisor reservoir data do not yet prove the complete bounded source law. [Source](../../../formal/GaloisForLFunctions/RHTower/TimeOneGammaJetFockRHCriterion.lean) | J3–J4: finite jets, Fock norms and normalization. | The all-jet boundedness/landing estimate from the source, with the global weld justified. |
| **W1C — Ising law convergence** | Centered real compact-uniform characteristic-law convergence is a sufficient criterion; the existing Lee–Yang mechanism handles the needed off-real passage. Do not add an unnecessary independent complex-convergence premise. [Source](../../../formal/GaloisForLFunctions/RHTower/IsingLawConvergenceRH.lean) | J3–J5: finite characteristic functions and application of the convergence theorem. | Construct the actual centered laws and prove the required real compact-uniform limit. |
| **WBF — genealogy Gram completion** | The completion criterion is square summability of the genealogy coefficients. The full compact construction's cost is not automatically finite. [Source](../../../formal/GaloisForLFunctions/HTGeometry/PaperGenealogyGramCompletion.lean) | J3–J4: finite genealogy and Gram identities. | A faithful arithmetic stream with the required summable cost and positive landing. |

**PW-B — native two-response action (PM branch).** The action and exhaustion identities are present, but the construction is indexed by `XiZeroCopy`. This is a faithful diagnostic of a supplied divisor, not an independent pre-divisor mechanism. **(a)** J3–J5: specialize its exact action. **(b)** Build an arithmetic source that produces the same controlled action without importing its zero orientation. [Native action](../../../formal/GaloisForLFunctions/RHTower/ThetaCusp/ThetaCuspHawkingBMPWNativeTwoResponseAction.lean)

## 5. Supporting programmes and their remaining research

These programmes refine the producers above. Their unsolved auxiliary questions are local research targets unless the row explicitly identifies an RH-strength endpoint. They are not all independent obstacles, nor are they all necessary for every route.

| Programme | Established positive content | Remaining task and status |
|---|---|---|
| **APT: full Weil cone and source selection** | Pair tests recover every coordinate, including composite non-prime-power nodes. Every nonzero single-node perturbation is excluded. One-sided cone membership is exactly RH plus the relevant coordinate order. | Identifying `Λ` and proving its positivity are different. Full-cone existence is an RH-strength input; coordinate calculations are J3. |
| **APT: visibility and finite low sector** | Quantitative grid-tent visibility and height reduction have explicit premises. Finite-aperture defect and a positive high-frequency complement are available. | Pay the actual finite low sector and mixed terms at every aperture. A finite calculation is J6; a uniform arithmetic proof is open. Do not relabel the existing visibility theorem as missing. |
| **APT: phase-selective heights** | Smooth interferometers and syndetic phase alignment refute even eventual all-height power-saving assertions of the proposed type. A single-height implication survives with explicit isolation and size bounds; the polar term decays as height to the power `−4`. | Obtain the phase-selective estimate at the relevant arithmetic height with all premises paid. A small bad-height measure does not show that zero ordinates avoid the bad set. The uniform all-height claim is refuted, not open. |
| **BiScale: lag, packet and multiplicity** | Exact width endpoints and critical-energy laws; multiplicity-sensitive packet limits and square-root detector horizons. | Critical arithmetic cancellation remains open. Transferring packet `m²` information to Weil `m` information requires an explicit argument. |
| **BiScale / ACS: zero-density filtering** | Averaged cosine and incoming-deficit estimates in the stated `A≤α log Γ`, `α<2/3`, regime; quadrature and depth-difference majorants for the filtered full form. | Complete the missing averaged coercivity/strict-positivity conclusions with their actual hypotheses. Even a successful average does not imply selected-height or all-test positivity. The previously alleged factor-two slab gap is absent. |
| **THIM: selective incidence and collars** | Bézout-type incidence distinguishes arithmetic structures that universal conservation laws do not; MC's outer and small-damping collars are signed. | Actual interior anti-alignment/cross-covariance. Generic conservation or planted-factor-resistant collars do not replace this RH-strength input. |
| **BVI: row cancellation** | Actual `μ` and `Λ−1` subdiagonal prime rows have saving `Q^(−δ/4)` for `Q^δ≤p≤Q^(1−δ)`, `N≥2Q`; composite-modulus ranges and smaller savings are developed. Abstract balanced estimates and independent centered-prime branches survive. | J1 repairs qualify the Möbius diagonal and combined every-modulus chain. After repair, uniform control of all terms in a closing energy estimate remains research; a row bound alone is not that estimate. |
| **BVI: dual problem** | Exact Rayleigh quotient, variance criterion and cofactor residual. | Produce readout near one with small centered energy at closing damping. Finite optimization is J3/J6; the actual cofinal family is an RH-strength producer. |
| **ACCE / arithmetic compensation** | Ground-floor equivalence, strict aperture flow, shell decomposition, canonical corrector and exact signed continuation criterion. | Critical signed loss, shell-flux payment and source-specific compensation. An absolute-value loss bound may be unnecessarily strong. Positive exponential aperture floors are excluded. |
| **ADR: residual and trace reconstruction** | The residual plus pole trace determines the row exactly through the floor transform; the map is injective. Actual cofactor renormalization has the proved bounded pronic residual. | A quantitative inverse in the norms required for admission. Algebraic reconstruction does not bound raw receiver energy; generic domain invariance cannot be inferred from the actual-source theorem. |
| **ADR: covariance limits and escape** | One common subsequence retains countably many cofactor covariances, finite-packet PSD, normalized diagonal and simultaneous dilation contraction. Fixed-word errors have an absolute horizon tail with explicit boundary cost. | Pass infinite cofactor sums through the limit, or exclude the remaining escape profile. For moving words, boundary cost must be paid against the shrinking tail. Finite-packet compactness does not do this automatically. |
| **SAEI: shared resources** | Frustrated cycles have exact PSD and local-payment thresholds. On fixed boxes, a strictly smaller joint first-power cap is classified by missing box points, with positive unequal weights. | Quantitative cofinal/all-power improvement for actual prime towers and a continuum shared budget. Fixed-support existential gaps do not yield the needed uniform saving. |
| **SAEI: damping and cutoff** | The chain is bounded at damping `1/2`; Hilbert–Schmidt control requires strictly greater damping. Generic below-half interchange fails. | Actual signed sub-half estimates and moving-tail control. Generic failure does not prove actual Möbius divergence. |
| **AOT: readings, hulls and width functor** | Threshold-receiver category, reading obstructions, hull criteria and unit-filter invariance. | A realizable, quantitatively conditioned arithmetic reading or non-unit repair. Isomorphic threshold objects do not identify their finite observations or producers. |
| **SRT / SSIC / DCI: detection and escape** | Quadratic smooth-detector aperture, explicit visibility and admission-or-escape alternatives. | Contain the actual arithmetic escape or pay detector norms uniformly. Detection of an assumed off-line zero is not a source sign proof. |
| **AOG: orientation and global index** | Generic single-orbit criterion, common-endpoint classification of positive scale-stable families, finite-target index and global index exit. | Source-derived Hasse–Weil orientation; quantitative compatible-family/index control. A finite global index would be substantial but would not alone give RH without the final `D<2` bound. |
| **AOG: theta sections** | Base theta `h⁰`, Poisson/Riemann–Roch identity and zeta Mellin bridge. | A source-defined surface/test-component section law producing an ample nonnegative-degree cone. Base section arithmetic is established; the coupling is open. |
| **ALDG: local divisor and heat geometry** | One-factor repair iff `δ²≤3u²`; exact higher-multiplicity thresholds; sharp Hermite first-heat optimum and equality structure. Only positive monomials universally reflect the coefficient cone. Full-copy monic divisor polynomials handle central zeros. | Arithmetic positivity of the actual heated divisor/cofactor at the required scale. The local model optimization is solved. A universal positive multiplier is excluded; source-selective repair remains a research candidate. |
| **SignedSuccessorArithmetic** | Complex-floor bounds bracket the leading constant between `−1/2` and `−1/3`; the lag-two agreement constant lies between `1/6` and `1/4`. Exact Kloosterman second-moment counts are available. | Sharp constants and source-selective cancellation remain local questions. Failure of exact pointwise cube-root equality does not decide asymptotic sharpness. Complete-field second moments do not imply balanced-moduli cancellation. |
| **Natural size-cutoff Möbius energy** | The size-truncated hypercube form is an exact weighted integral of a squared Möbius Dirichlet polynomial, hence nonnegative. The stated absolute bound is proved for damping `>1/2`. | Uniform signed bounds below that range. Divergence for prime-subset cutoffs does not establish divergence for natural size cutoffs. |
| **TTPC: coalescent prime pairs** | Proper powers are `o(N)`; prime `2`, parity and even shifts are separated. Signed trapezoidal Ramanujan transfer and close-pair-energy exchange formulas are proved. | The coherent actual prime-pair error/surplus estimate. The unsigned inner-lobe substitution is obstructed. The `1/18` surplus target in the existing certificate yields a `3/4` proportion, a partial result rather than RH. |

Source anchors for these programme-level distinctions:

- [Full-cone source selection](../../../formal/GaloisForLFunctions/arithmetic-positivity-theory/SourceSelectionInTheFullWeilCone.lean), [phase-selective aperture](../../../formal/GaloisForLFunctions/arithmetic-positivity-theory/SingleHeightPhaseSelectiveApertureAndPowerSaving.lean), [zero-density filtered deficit](../../../formal/GaloisForLFunctions/BiScaleUncertainty/ZeroDensityFilteredCriticalDeficitLaw.lean), [unfinished filtered Weil development](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/ZeroDensityFilteredWeilPositivityAndCoercivity.lean).
- [Residual/trace reconstruction](../../../formal/GaloisForLFunctions/ArithmeticDefectRigidity/TheResidualAndPoleTraceDetermineTheRow.lean), [common covariance limit](../../../formal/GaloisForLFunctions/ArithmeticDefectRigidity/CountableCofactorCovariancesHaveACommonLimit.lean), [absolute word tail](../../../formal/GaloisForLFunctions/ArithmeticDefectRigidity/BoundedWordErrorsHaveAnAbsoluteHorizonTail.lean).
- [Two-tower box law](../../../formal/GaloisForLFunctions/SignedArithmeticEnergyIncidence/TwoTowersAddExactlyOnBoxes.lean), [width functor](../../../formal/GaloisForLFunctions/ArithmeticOrientationTheory/TheWidthFunctor.lean), [optimal local heat](../../../formal/GaloisForLFunctions/ArithmeticLocalDivisorGeometry/HermiteOptimalHeat.lean), [universal reflector classification](../../../formal/GaloisForLFunctions/ArithmeticLocalDivisorGeometry/UniversalReflectors.lean).
- [Complex successor floor](../../../formal/GaloisForLFunctions/SignedSuccessorArithmetic/TheComplexSuccessorFloor.lean), [shift parity](../../../formal/GaloisForLFunctions/SignedSuccessorArithmetic/TheFloorReadsTheParityOfTheShift.lean), [size-truncated energy](../../../formal/GaloisForLFunctions/SignedSuccessorArithmetic/TheSizeTruncatedHypercubeForm.lean), [coalescent prime reduction](../../../formal/GaloisForLFunctions/TransThresholdPairCorrelation/CoalescentPrimeReductionAndParitySieve.lean).

## 6. What must not return as an open task

The following are completed local results or excluded shortcuts, not missing RH proofs:

- CHMD sharp-window convergence and generator-domain admission; compact-`L²` Suzuki first variation and common-support passage; all-length Heath–Brown and sharp all-`k` `S₂` inputs; smooth detector construction; the explicit kernel-shape identity and its formerly duplicated name.
- Width endpoint attainment for the critical deficit and full/odd Sobolev floors; classification of positive scale-stable orientation families; construction of the base theta `h⁰`; sharp local Hermite heat optimization.
- Obtaining a positive exponential aperture floor; obtaining the refuted eventual all-height phase saving; universally repairing the coefficient cone by a non-monomial positive multiplier; recovering orientation from a statistic proved invariant under orientation flips.
- Replacing full signed positivity by orthant positivity, cone-preserving spectrum by self-adjoint confinement, finite rank by all ranks, local payments by one global budget, or a finite-index theorem by zero index.
- Treating a zero-indexed representation as a pre-divisor construction, a `Prop`/structure field as its own proof, or an algebraic inverse as a bounded inverse.

The [walls ledger](walls-ledger.md) retains the scoped negative results and their positive survivors. The [unification ledger](route-unification-ledger.md) specifies which remaining problems are literally shared and which merely have equivalent RH endpoints.
