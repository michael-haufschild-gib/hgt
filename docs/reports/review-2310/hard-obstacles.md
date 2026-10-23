# Hard mathematical obstacles on every RH route

**Status at 2026-10-23:** 30 live routes, 18 standalone candidates, and PM's embedded PW-B candidate. No reviewed route has an unconditional, source-derived closing estimate. Several receiver, completion, local-positivity and cancellation problems are solved; the remaining global arithmetic estimates are not.

Companions: [summary and research programme](hard-obstacles-summary.md), [walls ledger](walls-ledger.md), [route unification](route-unification-ledger.md). Route names follow the [current frontier map](../rh-current-frontier-map.md). This is a status report, not a sequence of research updates.

## 1. Scope and meaning of “open”

The six user-specified reports supply the inventory. Current corpus searches, direct Lean statements and selected proof/dependency checks determine the mathematical status. No other existing Markdown was read: no programme README, pipeline proof card, or status file is evidence for this review. Primary external sources are used only to calibrate claims about internationally open mathematics.

| Label | Meaning |
|---|---|
| **Established [L]** | Statement and relevant premises inspected in Lean source. This label does not claim a fresh compilation of every linked module. |
| **Working source [S]** | A proof declaration exists in current working or unintegrated source; independent integration/compiler certification is distinguished from its stated mathematics. |
| **Candidate [C]** | Missing construction, estimate, or transfer. A conditional theorem does not discharge its premises. |
| **(a) Just work** | Known-method specialization, explicit regularity argument, supplied finite-certificate verification, or integration of an existing proof. No unknown sign is included. |
| **(b) B-RH** | An unresolved target with a proved implication to RH; equivalence is stated only where proved. |
| **(b) B-C** | An unresolved project-specific mathematical question. It may be weaker, stronger, false, or incompletely formulated; this label does not assert worldwide novelty. |
| **Refuted / restricted** | A proposal fails in the specified class. Its strongest established positive survivor remains relevant. |

RH remains listed as unsolved by the [Clay Mathematics Institute](https://www.claymath.org/millennium/riemann-hypothesis/). Thus no accepted unconditional solution is known for an RH-sufficient closing target. That conclusion does not establish that every auxiliary B-C question is internationally unsolved. Nor does a repository theorem named “criterion”, “completion”, or “equivalence” supply its arithmetic input.

“No routine closing step” does not mean “no useful routine work.” It means the corpus supplies no dependency-closed plan using known inputs that finishes any route. Shared routine tasks J1–J7 and open topics O1–O10 are defined in the [summary](hard-obstacles-summary.md).

### Current mathematical boundaries

Write `Δ = supρ |Re ρ − 1/2| = Θ − 1/2`. RH is `Δ = 0`.

1. **Full and odd windows differ.** The complete Weil form has floor `(1/5000)‖F‖₂²` for all compact `C²` tests supported in `[−3/10,3/10]`. For odd tests the floor is `(1/1000)‖F‖₂²` through `181/500 = 0.362`, with the prime-2 charge included and without an extra polar-moment condition. The odd result is not an all-test result. [ThreeTenthsSharpGaugeWeilPositivity](../../../formal/GaloisForLFunctions/ArithmeticCriticalityTheory/ThreeTenthsSharpGaugeWeilPositivity.lean); [SchurLendingOddWindowThreeHundredSixtyTwoThousandths](../../../formal/GaloisForLFunctions/ArithmeticIncidencePositivity/SchurLendingOddWindowThreeHundredSixtyTwoThousandths.lean).
2. **The ground-energy limit is conditional.** An unconditional upper envelope tends to zero. It is not an unconditional proof that `μ(A)→0`. Nonnegativity at every aperture, and the stated limit itself, are RH-equivalent. Under failure of RH the contact law supplies an aperture `A*≥3/10` with `μ(A*)=0`, nonnegativity below and negativity above; it does not assert strict positivity everywhere below. [TheContactApertureOfTheGroundEnergyPath](../../../formal/GaloisForLFunctions/SquareRootThreshold/TheContactApertureOfTheGroundEnergyPath.lean).
3. **Uniqueness is not existence.** Every full-positive arithmetic weight must be `Λ`. Thus the full cone is contained in `{Λ}`; it equals `{Λ}` under RH and is empty otherwise. Unconditional rigidity does not establish positivity of `Λ`. [WeilConeUniquenessUnconditional](../../../formal/GaloisForLFunctions/RHTower/WeilConeUniquenessUnconditional.lean).
4. **Damping now reads the width exactly.** Admission holds for every `ε>Δ`. The infimum of accumulation points of admitted dampings equals `Δ`. Cofinal admission as `ε↓0` is RH-equivalent; one isolated admitted `ε<1/2` is not individually identified with RH. [AdmissionBelowHalfDampingAboveTheZeroWidth](../../../formal/GaloisForLFunctions/RHTower/AdmissionBelowHalfDampingAboveTheZeroWidth.lean).
5. **The completed sign transfer is solved.** Suzuki's primitive has dense, proper image in the Weil form domain. The norms are not equivalent, yet density transfers nonnegativity in both directions at fixed aperture. The CHMD graph norm is now equivalent to the Weil form norm on each fixed-aperture common core. A lower bound for the quotient norm and identification of the whole quotient remain separate. [CHMDGraphNormIsTheWeilFormNormOnAnAperture](../../../formal/GaloisForLFunctions/RHTower/CHMDGraphNormIsTheWeilFormNormOnAnAperture.lean). [SuzukiScrewCompletionInsideTheWeilFormDomain](../../../formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiScrewCompletionInsideTheWeilFormDomain.lean).
6. **AIP is a live route.** The complete shared-incidence allocation condition is RH-equivalent. Local strip payments and exact algebra are established; the global allocation is not. [GlobalIncidenceAllocationCondition](../../../formal/GaloisForLFunctions/ArithmeticIncidencePositivity/GlobalIncidenceAllocationCondition.lean).
7. **Actual arithmetic rows beat some generic barriers.** Fixed-modulus Möbius cancellation and restricted short-window improvements for actual Möbius and centered-prime rows are established. Generic Type-II counterexamples do not refute these results; neither result controls all growing moduli and all remaining tails. [SingleModulusCancellationOfTheMoebiusBlock](../../../formal/GaloisForLFunctions/BezoutValuationIncidence/SingleModulusCancellationOfTheMoebiusBlock.lean); [DualNormOfTheActualRowsBeatsTheLargeSieve](../../../formal/GaloisForLFunctions/BezoutValuationIncidence/DualNormOfTheActualRowsBeatsTheLargeSieve.lean).
8. **Weighted and unweighted floors remain different.** Width controls a derivative-normalized floor and a logarithmic Fourier-energy floor. A uniform local squared-depth bound supplies a sharp mass-only floor. The unrestricted mass-only converse has not been established. [TheWidthBoundsTheEnergyNormalisedWeilFloor](../../../formal/GaloisForLFunctions/SquareRootThreshold/TheWidthBoundsTheEnergyNormalisedWeilFloor.lean); [TheUnconditionalWeilFloorInTheArchimedeanNormalisation](../../../formal/GaloisForLFunctions/SquareRootThreshold/TheUnconditionalWeilFloorInTheArchimedeanNormalisation.lean); [TheWidthIsTheGroundEnergyRateWhenOffLineZerosDoNotCluster](../../../formal/GaloisForLFunctions/SquareRootThreshold/TheWidthIsTheGroundEnergyRateWhenOffLineZerosDoNotCluster.lean).

9. **A positive floor has a compulsory scale.** For `A≥3`, `μ(A)≤K exp(11A/2−πe^{2(A−2)})`. Any positive lower floor `m₀e^{−B(A)}` therefore requires `B(A)≥πe^{2(A−2)}−11A/2+log(m₀/K)`. Neither a fixed positive gap nor a harmonic floor along linearly growing apertures is viable. This is an upper bound, not unconditional convergence of `μ` to zero. [TheApertureFloorMustDecayDoublyExponentially](../../../formal/GaloisForLFunctions/ArithmeticCompensationTheory/TheApertureFloorMustDecayDoublyExponentially.lean).
10. **Index, depth and multiplicity are different measurements.** The Weil test form’s negative index, equivalently the scaling surface’s excess positive index above its one pole-plane direction, counts distinct right zeros; the Weil sum counts multiplicities `m`; packet mean-square counts `m²`. LI has a proved exponential-rate dictionary for reciprocal depth `|β−1/2|/(γ²+(β−1/2)²)`, not the raw width `Δ`. [TheHodgeDefectCountsTheRightZeros](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/TheHodgeDefectCountsTheRightZeros.lean); [LiEvenCrossActualClockGrowthLaw](../../../formal/GaloisForLFunctions/RHTower/LiEvenCrossActualClockGrowthLaw.lean); [MultiplicityCeilingLaw](../../../formal/GaloisForLFunctions/BiScaleUncertainty/MultiplicityCeilingLaw.lean).
11. **Endpoint cancellation has an exact extra cost.** For critical-Wiener `k`, admission of `k⋆d^(−1/2)` is equivalent to `Σ_n(Σ_{j≤n}k(j)/√j)²/(n+1)<∞`. Pole cancellation alone fails; absolute `√(1+log j)` weighted summability is a sharp sufficient class. Generic finite-row/infinite-receiver interchange holds exactly at damping `ε≥1/2`. [Partial-pole-sum law](../../../formal/GaloisForLFunctions/TransHorizonIncidenceMechanics/TheHalfDampedReceiverIsTheLogarithmicEnergyOfThePartialPoleSums.lean); [horizon law](../../../formal/GaloisForLFunctions/TransHorizonIncidenceMechanics/TheHorizonLimitCommutesWithTheReceiverExactlyFromHalfDamping.lean).

## 2. Live routes

### WL — Weil lag function

- **Receiver and established work [L].** Either appropriate one-sided prime-lag bound, a one-sided integrated Chebyshev-deficit bound, or eventual boundedness of the universal spline packet implies RH; the corpus gives equivalences in the corresponding formulations. The packet-band criterion is linear mean-square growth. Exact prime/Gamma/polar identities, visibility, recurrence and Vinogradov–Korobov envelopes are established. [PrimeLagLowerBoundRH](../../../formal/GaloisForLFunctions/RHTower/PrimeLagLowerBoundRH.lean); [CubicSplineUniversalProbe](../../../formal/GaloisForLFunctions/BiScaleUncertainty/CubicSplineUniversalProbe.lean); [PacketBandLaw](../../../formal/GaloisForLFunctions/BiScaleUncertainty/PacketBandLaw.lean).
- **(a) Just work.** J3: specialize existing transport identities to a chosen compact source, keeping endpoint terms and exponent slack. This does not supply the source bound.
- **(b) B-RH.** Prove an arithmetic upper bound for the universal packet at every positive exponential slack, or the equivalent critical band estimate. The integrated deficit must have exponent `1/2` plus arbitrary positive slack instead of the current unconditional exponent near `1`. Signed correlations, not reconstruction of the observable, are missing.
- **Boundary.** Littlewood-type pointwise oscillation excludes an unconditional `O(√x)` target for the raw Chebyshev error; that is a different quantity from the integrated or packet receiver. Wall 1.1.

### RW — Restricted Weil ground energy

- **Receiver and established work [L].** `μ(A)≥0` for every aperture is RH-equivalent. Small-window floors, the contact law, the upper envelope, self-adjoint realization and the SZ completion sign transfer are established. Derivative-normalized and logarithmic Fourier-energy floors are available; uniform local off-line depth mass gives the sharp mass-only rate. [TheContactApertureOfTheGroundEnergyPath](../../../formal/GaloisForLFunctions/SquareRootThreshold/TheContactApertureOfTheGroundEnergyPath.lean); [UnsignedDepthSamplingDetectsLocalMass](../../../formal/GaloisForLFunctions/SquareRootThreshold/UnsignedDepthSamplingDetectsLocalMass.lean).
- **(a) Just work.** J2: discharge the explicit Fourier-integrability premises for a concrete compact `C²` source using its decay estimates, and package the resulting weighted-floor specialization. J1 applies to new supporting source.
- **(b) B-RH.** Exclude a zero crossing of `μ` at arbitrary support. **B-C:** prove a width-to-unrestricted-`L²` floor without an unproved clustering bound, or characterize the signed cancellations that replace that bound.
- **Boundary.** Extending the all-test radius from `3/10` to `log 2/2` is a real inequality problem, not a guaranteed finite calculation. A small-window theorem, an upper envelope tending to zero and a weighted lower bound do not combine into global positivity. Walls 1.3, 3.2–3.3.

### FU — CCM-FU signed prime scheduling

- **Receiver and established work [L].** A bounded-above completed Abel moment gives RH. Helper cores, decreasing complete cutoff clocks and low-diagonal prime synthesis are available; negative off-diagonal interactions can be exposed conditionally on an offending spectral direction. [CCMFUSuzukiMobiusDivisorOneSided](../../../formal/GaloisForLFunctions/RHTower/CCM/CCMFUSuzukiMobiusDivisorOneSided.lean).
- **(a) Just work.** J3: assemble the already established finite-clock identities for a specified schedule.
- **(b) B-RH.** Bound the completed Abel moment with seed energy, inherited action, inter-block covariance and moving endpoints all included. The needed arithmetic interaction estimate is not implied by positive helper increments.
- **Boundary.** Bounded norm and vanishing diagonal do not give compactness or nonnegative total covariance. Walls 1.1, 1.6, 14.1.

### RP — Route-P / SP-E history floor

- **Receiver and established work [L].** An eventual linear lower floor for the literal matched-quantile history is RH-equivalent. Signed hyperbola, centroid, square-debt and low-LCM decompositions are established. Burnol shells converge strongly to zero while retaining nonzero limiting trace. [SPEQuantileRieszRoutePLinearFloorCriterion](../../../formal/GaloisForLFunctions/RHTower/SPEQuantileRieszRoutePLinearFloorCriterion.lean).
- **(a) Just work.** No route-specific mathematical gap currently certified routine; J3 covers fixed-history bookkeeping.
- **(b) B-RH.** Pay high-LCM interactions, centroid and square debt, moving-core drift and singular-domain transport in one complete-history bound.
- **Boundary.** Absolute-fibre estimates and strong convergence do not pay the signed full history or imply trace-norm convergence. Walls 1.1, 1.8, 14.1.

### PA — Prime–archimedean source passivity

- **Receiver and established work [L].** Continued exact trace, high-frequency passivity and signed compact-moment criteria connect to RH. Every fixed Hausdorff order is eventually nonnegative; any finite set of orders has a common threshold. The WL/PA trace identity is established. [PrimeArchEndpointFrequencyAccretivity](../../../formal/GaloisForLFunctions/RHTower/PrimeArchEndpointFrequencyAccretivity.lean); [PrimeArchWeilLagReceiverIdentity](../../../formal/GaloisForLFunctions/RHTower/PrimeArchWeilLagReceiverIdentity.lean).
- **(a) Just work.** J4: evaluate a specified finite list of moment differences or verify an already proposed finite certificate. A favorable outcome is not promised.
- **(b) B-RH.** Prove the complete current sign, an adequate order-uniform moment estimate, or the signed complement of the positive saddle band. Dependence of the threshold on order is the unresolved quantifier.
- **Boundary.** A positive saddle contribution does not sign its complement. Fixed finite passive realizations and finitely many repaired atoms cannot close the route. Walls 1.5–1.6, 14.1.

### MC — Möbius cancellation at half power

- **Receiver and established work [L].** `M(x)=Oε(x^(1/2+ε))` for every `ε>0` is an RH receiver; Hilbert, Liouville and divisor-source formulations are connected. Exact Vaughan/Gram decompositions retain all signed entries. Fixed-prime residue cancellation and actual-row short-window savings are available. [MobiusHilbertFormEquivalence](../../../formal/GaloisForLFunctions/RHTower/MobiusHilbertFormEquivalence.lean); [MoebiusBlockBeatsTheTypeTwoBarrier](../../../formal/GaloisForLFunctions/BezoutValuationIncidence/MoebiusBlockBeatsTheTypeTwoBarrier.lean); [CentredPrimeBlockBeatsTheLargeSieve](../../../formal/GaloisForLFunctions/BezoutValuationIncidence/CentredPrimeBlockBeatsTheLargeSieve.lean).
- **(a) Just work.** J3: apply the actual-row lemmas within their stated window, support and modulus ranges; retain mass and higher-order remainders.
- **(b) B-RH.** Obtain the complete signed bound at half-power precision, uniformly through the horizons and moduli used by the receiver. **B-C:** extend restricted actual-row savings while controlling their tails; a strict power saving in the relevant short-window criterion already has quasi-RH strength.
- **Boundary.** Generic `ℓ²` Type-II impossibility is a statement about a coefficient class, not about the literal Möbius row. Fixed-modulus cancellation is solved; uniform growing-modulus cancellation and full-energy control are not. Walls 1.1, 1.8–1.9.

### TT — Theta-tail and heat–Cassini currents

- **Receiver and established work [L].** Natural Wold-energy or directed covariance bounds, and full odd Weil positivity, imply RH. Seam, odd-four, tail and reflected-prime identities are established. [PaperWoldDirectedCovarianceWidthSpectrum](../../../formal/GaloisForLFunctions/RHTower/PaperWoldDirectedCovarianceWidthSpectrum.lean); [WeilMarkovOddPositivity](../../../formal/GaloisForLFunctions/RHTower/WeilMarkovOddPositivity.lean).
- **(a) Just work.** J3–J4 for fixed source/chamber identities and a supplied certificate.
- **(b) B-RH.** Control directed signed covariance at every required radius or prove the complete odd-form sign across all scales.
- **Boundary.** Enlarging a positive inner chamber is not known to close the full region. Translation averages lose depth information; abstract Ruelle continuation has no automatic identification with ζ. Walls 1.6, 3.2–3.3.

### LA — Line anchor

- **Receiver and established work [L].** All-height logarithmic-derivative, Laguerre or Jensen signs select the line. The corpus defines the nonnegative-axis constant `Λ₊`, the classical heat constant truncated at zero and rescaled; `0≤Λ₊<1/8`, and RH is `Λ₊=0`. Its nonnegativity is definitional, not a formalization of Rodgers–Tao. Fixed-degree, sufficiently shifted Jensen hyperbolicity is established. [DeBruijnNewmanStrictBound](../../../formal/GaloisForLFunctions/RHTower/DeBruijnNewmanStrictBound.lean); [XiLogDerivReStripBound](../../../formal/GaloisForLFunctions/RHTower/XiLogDerivReStripBound.lean).
- **(a) Just work.** J4 applies to specified finite moment/Jensen instances, not the all-degree statement.
- **(b) B-RH.** Prove the arithmetic sign at all heights and all relevant degrees at the same critical heat time, including near-multiple clusters.
- **Boundary.** A fixed-degree asymptotic does not commute with the all-degree quantifier. Collision identities detect an offending cluster but do not exclude one. Walls 1.2, 1.6, 3.2.

### TG — Topological sub-unit gate

- **Receiver and established work [L].** Boundary winding/index and source-sensitive cubic transgression are established. An appropriate nonnegative residual plus integral trace strictly below one closes the receiver. [FormationAnchoredCubicSpecialization](../../../formal/GaloisForLFunctions/RHTower/FormationAnchoredCubicSpecialization.lean); [GaussianCentralGapExplicitCriterion](../../../formal/GaloisForLFunctions/RHTower/GaussianCentralGapExplicitCriterion.lean).
- **(a) Just work.** Once the required positive-residual and sub-unit estimates are supplied, the integral-index deduction is already routine and largely encoded.
- **(b) B-RH / B-C.** Construct the matrix-complete source decomposition and prove its residual sign and all-disc sub-unit bound. The alternative central-gap estimate at critical exponent is also unresolved.
- **Boundary.** Integer-valuedness alone gives no upper bound. Finite-scale or compact-ideal diagnostics do not orient the full prime−Gamma source. Walls 1.2, 1.6, 14.

### HF — Positive Hodge form on arithmetic cohomology

- **Receiver and established work [L].** Full-positive weights are rigidly `Λ`; prime-blind positivity has exact node-deletion constraints. Meyer/Paugam source, divisor, trace and determinant constructions are substantial but do not make the pairing positive. The alternate window ceiling `e^(L/2)+O(L)` is sufficient for RH. [WeilPositivityPrimeBlindDuality](../../../formal/GaloisForLFunctions/RHTower/WeilPositivityPrimeBlindDuality.lean); [PrimePowerZeroPoleNodeCriticality](../../../formal/GaloisForLFunctions/BiScaleUncertainty/PrimePowerZeroPoleNodeCriticality.lean); [PrimeWindowCeilingRHCriterion](../../../formal/GaloisForLFunctions/BiScaleUncertainty/PrimeWindowCeilingRHCriterion.lean).
- **(a) Just work.** J3–J4: instantiate established finite collar partitions, transport and dual bounds. Identifying an optimal finite-dimensional extremum still requires proof; it is not automatically routine.
- **(b) B-RH.** Produce a positive arithmetic pairing or the stated complete window ceiling. **B-C:** control the full variational tower beyond restricted cones without inserting zero simplicity or a zero-built positive form.
- **Boundary.** Full-cone uniqueness does not supply its member. The window excess exponent is only pinched by `Δ≤θ*≤Δ/2+1/4`; equality and an RH converse to the `O(L)` ceiling are not established. Finite node density misses prime-power incidence. Walls 1.3–1.4, 3.3, 14.

### CHMD — Causal Hyperbolic–Modular Duality

- **Receiver and established work [L].** Exact quotient coordinates, source norm and spectral criterion are available. One-signed odd sources exclude the offending direction in their restricted class; sign-changing sources remain. Common-core equality, completed RW/SZ sign transfer, and fixed-aperture CHMD graph/Weil form norm equivalence are solved. Quotient-coordinate continuity is proved; a quotient lower bound and whole-quotient surjectivity are not supplied. [CHMDSpectralRiemannCriterion](../../../formal/GaloisForLFunctions/RHTower/CHMDSpectralRiemannCriterion.lean); [CHMDComplexQuotientSourceCoordinates](../../../formal/GaloisForLFunctions/RHTower/CHMDComplexQuotientSourceCoordinates.lean); [SuzukiScrewCompletionInsideTheWeilFormDomain](../../../formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiScrewCompletionInsideTheWeilFormDomain.lean).
- **(a) Just work.** J3: transport a theorem on the actual common-core closure with the established maps.
- **(b) B-RH.** Prove the complete cross-nodal/Poincaré sign or the required one-sided deficit for arbitrary source profiles.
- **Boundary.** The closure of the common-core image is not automatically the entire CHMD quotient. Suzuki derivative/Weil norm inequivalence does not prevent sign transfer; CHMD graph/Weil norm equivalence is a different proved statement. Walls 1.3, 3.4, 14.3.

### TH — Theta moment positivity

- **Receiver and established work [L].** Hankel/Bezout and thermal moment formulations read the zero configuration. Each fixed rank can be positive in a nonselective regime. [XiHeatHankelFormOrthantPositivity](../../../formal/GaloisForLFunctions/RHTower/XiHeatHankelFormOrthantPositivity.lean); [XiThermalProjectiveMomentSpectrum](../../../formal/GaloisForLFunctions/RHTower/XiThermalProjectiveMomentSpectrum.lean).
- **Additional established boundary [L].** All ranks are positive on the nonnegative coefficient orthant at one sufficiently small heat time. The unresolved task is positivity on arbitrary signed vectors; merely increasing rank inside that orthant supplies no new detector. [XiHeatHankelFormOrthantPositivity](../../../formal/GaloisForLFunctions/RHTower/XiHeatHankelFormOrthantPositivity.lean).
- **(a) Just work.** J4 for a specified finite-rank matrix or exact finite moment identity.
- **(b) B-RH.** Establish all-rank positivity at one admissible critical time, with rank-independent control.
- **Boundary.** Choosing a later time separately for every rank proves a different statement. Walls 1.2, 1.6, 3.2.

### RN — Theta renewal and singular comparison

- **Receiver and established work [L].** Native source solvers and multiplicity-preserving packets exist. The actual renewal operator is compact, Hilbert–Schmidt and cone-positive; its regularized determinant and resonance multiplicities match the renewal denominator. [ThetaRenewalFredholmSpectrum](../../../formal/GaloisForLFunctions/RHTower/ThetaRenewalFredholmSpectrum.lean).
- **(a) Just work.** J3: specialize determinant/resonance identities on an established domain.
- **(b) B-RH / B-C.** Derive the required boundary-work orientation, comparison sign or source-faithful spectral restriction. Establishing the correct spectrum is not yet proving that it lies on the required line.
- **Boundary.** Cone-positive compact operators can have nonreal nonprincipal spectrum. Unregularized native topology and whole-quotient extension are separately constrained. Walls 1.2, 14.1, 14.3.

### WD — Ward orientation and horizontal collision

- **Receiver and established work [L].** The global cap is integrable, nonnegative, and vanishes exactly under RH; multiplicities and finite mixed-range routing are retained. [XiWardGlobalCapRightZeroSum](../../../formal/GaloisForLFunctions/RHTower/XiWardGlobalCapRightZeroSum.lean).
- **(a) Just work.** J3 for a specified finite block's routing identity.
- **(b) B-RH.** Prove arithmetic vanishing of the entire cap, or a complete signed prime−Gamma contraction with owner/absorber bounds uniform over all blocks.
- **Boundary.** Constructing a nonnegative defect is not proving it zero. Averaged identities and one block's gain do not bound the global cap. Walls 1.2, 1.6, 3.4.

### LI — Li even-cross clock

- **Receiver and established work [L].** For the literal completed clock response `R(t)`, every reciprocal depth `bρ=|β−1/2|/(γ²+(β−1/2)²)` is at most `r` iff `R(t)≥−C exp(r′t)` eventually for every `r′>r`. At `r=0` this is RH. Unconditionally `bρ≤1/431`; hence every rate above `1/431` is available. [LiEvenCrossActualClockGrowthLaw](../../../formal/GaloisForLFunctions/RHTower/LiEvenCrossActualClockGrowthLaw.lean).
- **(a) Just work.** J3–J4: use the exact clock identities and verify supplied finite Li/Jensen data with their certified tails.
- **(b) B-RH.** Prove the actual subexponential lower floor at every positive slack. A stronger eventual nonnegative response would also suffice but is not needed by this receiver.
- **Boundary.** Positive reciprocal-depth bounds constrain a height-dependent lens, not a uniform raw-depth strip. This route has a graded law, but its parameter must not be substituted for `Δ`. Finite initial Li signs do not pay all orders. Walls 1.5, 3.1–3.2.

### SZ — Suzuki screw and shifted-kernel limits

- **Receiver and established work [L].** Screw and shifted-Ξ criteria, actual positive-shift Hankel admission, graph closure and source reconstruction are available. Dense-range completion gives equivalence of the Suzuki and RW signs at fixed aperture. [SuzukiScrewCompletionInsideTheWeilFormDomain](../../../formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiScrewCompletionInsideTheWeilFormDomain.lean); [SuzukiCanonicalPositiveShiftHankel](../../../formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiCanonicalPositiveShiftHankel.lean).
- **(a) Just work.** J3: use the proved completion transfer; it is no longer an open norm-identification task.
- **(b) B-RH.** Prove a source Wronskian law paying the moving infinite head and shell leakage, or a cusp-preserving passage to the unshifted limit with the needed sign.
- **Boundary.** Positive-shift admission and almost-everywhere reconstruction do not imply sign or uniformity as the shift vanishes. The derivative norm and Weil norm are provably inequivalent. Walls 1.3, 1.6, 14.3.

### PM — Physical model: FZZ-P Haar approximation

- **Receiver and established work [L].** Global `L²(0,1]` approximation of the Haar target is RH-equivalent. Local density on every `(δ,1]`, exact cell/Gram decompositions and half-damping admission are established. For the damped energy `Eε(T)`, every `ε>Δ` is admitted, and cofinal admission at zero is equivalent to RH. [FermiNymanHaarApproximationEquivalence](../../../formal/GaloisForLFunctions/RHTower/FermiNymanHaarApproximationEquivalence.lean); [AdmissionBelowHalfDampingAboveTheZeroWidth](../../../formal/GaloisForLFunctions/RHTower/AdmissionBelowHalfDampingAboveTheZeroWidth.lean).
- **Established continuation boundary [L].** For an admitted right endpoint `c`, a horizon-uniform averaged relative-loss budget on `[a,c]` is equivalent to admission at `a`. The scalar tangent budget is paid; cutoff-shell summability follows from admission. [TheAveragedBudgetIsExactlyAdmission](../../../formal/GaloisForLFunctions/ArithmeticContinuationAndCriticalEnergy/TheAveragedBudgetIsExactlyAdmission.lean).
- **(a) Just work.** J1 for new dilation/entrance-law sources; J3 for literal energy, block-energy and averaged-continuation translations. The Hardy block equivalence is already supplied [S] by [TheDilationHardyInequalityOnThePronicMeasure](../../../formal/GaloisForLFunctions/ArithmeticContinuationAndCriticalEnergy/TheDilationHardyInequalityOnThePronicMeasure.lean).
- **(b) B-RH.** Bound the complete actual energy for dampings arbitrarily close to zero, uniformly in horizon for each damping. Equivalently, pay the signed averaged loss from `1/2` to cofinally small `a`. The bound may depend on `a`; uniformity in damping is not required.
- **Boundary.** Local Haar approximation does not control the origin. A band shrinking toward `1/2` is not cofinal at zero. Absolute dilation estimates stop at half damping. The `c₀` compact semigroup and its residue eigenvalues do not bound the critical pronic energy. Global nonnegative signed work is false: at horizon one, `W(ε,1)→−1/2` as `ε↓0`. The sufficient Poincaré sign in [TheDilationDirichletFormOfTheWork](../../../formal/GaloisForLFunctions/ArithmeticContinuationAndCriticalEnergy/TheDilationDirichletFormOfTheWork.lean) is therefore too strong as stated; use the signed averaged budget. The exact source theorem is [TheFirstCellCarriesAdverseWork](../../../formal/GaloisForLFunctions/ArithmeticCompensationTheory/TheFirstCellCarriesAdverseWork.lean). Walls 1.8–1.9, 14.3.

### JAS — Joint ancestry

- **Receiver and established work [L].** Exact phase, shell and amplitude dictionaries give RH receivers. A logarithmic source budget, typical-phase bounds and finite-shell descriptions are available. [JointAncestryLogBudgetProducer](../../../formal/GaloisForLFunctions/RHTower/JointAncestryLogBudgetProducer.lean); [JointAncestrySquareShellFinitePowerCriterion](../../../formal/GaloisForLFunctions/RHTower/JointAncestrySquareShellFinitePowerCriterion.lean).
- **(a) Just work.** J3: specialize finite shell/phase identities and their constants.
- **(b) B-RH.** Obtain the required subpower complete shell budget or exceptional-phase control at every relevant scale. The logarithmic budget in its current normalization does not pay the receiver's power-scale demand.
- **Boundary.** Typical caps and random-phase estimates do not bound the deterministic exceptional orbit. Walls 1.1, 1.6, 3.2.

### CTF — Chronological tail / Báez–Duarte approximation

- **Receiver and established work [L].** Vanishing approximation distance is RH-equivalent. The residual decomposes into squared readout error plus centered pronic energy. The natural readout approaches its required value; the energy need not. [BaezDuarteCriterionHardDirection](../../../formal/GaloisForLFunctions/RHTower/BaezDuarteCriterionHardDirection.lean); [BaezDuarteEnergyOfThePowerDampedMobiusRows](../../../formal/GaloisForLFunctions/BezoutValuationIncidence/BaezDuarteEnergyOfThePowerDampedMobiusRows.lean).
- **(a) Just work.** J3–J4: evaluate a specified finite Gram problem and preserve its full residual.
- **(b) B-RH.** Construct source rows whose complete residual tends to zero, including centered energy and compatible damping/cutoff limits.
- **Boundary.** A lower floor of order `1/log N` does not obstruct convergence to zero. Solved readout convergence is not solved approximation. Native PCS co-shift cannot be identified with invertible chronological dilation. Walls 1.8–1.9, 14.3.

### HCF — Gaussian heat trace / critical feature variance

- **Receiver and established work [L].** Two literal source grids, at `log 2` and `log 3`, with all-degree sign requirements on the stated polar hyperplanes characterize RH. Parity and Hurwitz residual dictionaries are available. [XiGaussianHeatTwoPrimeSourceSampling](../../../formal/GaloisForLFunctions/RHTower/XiGaussianHeatTwoPrimeSourceSampling.lean).
- **(a) Just work.** J3–J4 for finitely many moments and exact parity transports.
- **(b) B-RH.** Prove the two-grid signs at every required degree from the source.
- **Boundary.** One grid aliases configurations; finite rank and marginal moment positivity do not supply the complete mixed condition. Walls 1.6, 3.1–3.3.

### XN — Xi Newton invariant discs

- **Receiver and established work [L].** Newton/logarithmic-derivative geometry, boundary curvature and critical-pole exclusion are established. [XiNewtonDiscCurvature](../../../formal/GaloisForLFunctions/RHTower/XiNewtonDiscCurvature.lean); [XiNewtonCriticalPoleExclusion](../../../formal/GaloisForLFunctions/RHTower/XiNewtonCriticalPoleExclusion.lean).
- **(a) Just work.** J3: verify a supplied disc's explicit algebraic/analytic hypotheses.
- **(b) B-RH / B-C.** Produce a source-derived disc or Green-potential control that covers every relevant zero and proves the required interior margin.
- **Boundary.** Boundary positivity does not establish interior positivity; a disc construction assuming zero exclusion is circular. Walls 1.2, 1.6.

### BAG — Deterministic zeta self-return

- **Receiver and established work [L].** Strong recurrence on a zero-free disc is established; recurrence at every strict-right point gives the width/RH criterion. Discs containing zeros have an obstruction measured by their distance to nonvanishing targets, with multiplicity-sensitive scale. [ZetaDiscRecurrenceOnZeroFreeDiscs](../../../formal/GaloisForLFunctions/RHTower/ZetaDiscRecurrenceOnZeroFreeDiscs.lean); [ZetaRecurrenceAtEveryPointModuloItsZeros](../../../formal/GaloisForLFunctions/RHTower/ZetaRecurrenceAtEveryPointModuloItsZeros.lean).
- **(a) Just work.** J3: apply the local recurrence theorem on a disc already known to be zero-free; J4 for explicit finite approximants.
- **(b) B-RH.** Establish the required deterministic returns without assuming zero-freeness on the target discs, or supply the conditioned-tail estimate that forces it.
- **Boundary.** Finite Euler approximation and universality for nonvanishing targets do not give recurrence to an arbitrary possibly vanishing target. Walls 1.2, 1.6, 3.2.

### EWU — Even pole-weight uniqueness

- **Receiver and established work [L].** Blind minima and even-sector positivity have exact variational and spectral coordinates. Restricted factorial/ramp families and explicit block thresholds are already controlled; their large-scale positivity has an archimedean subsidy. [EvenSectorBlindVariationalAttainment](../../../formal/GaloisForLFunctions/RHTower/EvenSectorBlindVariationalAttainment.lean); [EvenSectorFullPositivity](../../../formal/GaloisForLFunctions/RHTower/EvenSectorFullPositivity.lean).
- **(a) Just work.** J3–J4 for a specified existing family. Finding the already proved block thresholds is not an outstanding research problem.
- **(b) B-RH.** Prove the blind-minimum/full-even sign at arbitrary aperture, or a form-norm approximation that transfers restricted-family estimates with uniform control.
- **Boundary.** A positive restricted family is not dense with a usable uniform margin merely because it is large. Low-mode penalties remain. Walls 1.3–1.4, 3.3.

### GTA — Transverse Schur charge

- **Receiver and established work [L].** Rank-uniform decay of actual theta-stage quartic Schur packets is RH-equivalent; finite truncations converge strongly even off RH. [HedenmalmThetaSchurQuarticSpectralDecayEquivalence](../../../formal/GaloisForLFunctions/RHTower/Hedenmalm/HedenmalmThetaSchurQuarticSpectralDecayEquivalence.lean).
- **(a) Just work.** J3–J4 for finite Schur identities.
- **(b) B-RH.** Prove source-derived transverse-energy decay uniformly in rank and late stage.
- **Boundary.** Positive feature kernels, symmetrization and strong convergence do not establish the required norm decay. Walls 1.6, 14.1.

### OWU — Odd Weil-weight uniqueness

- **Receiver and established work [L].** Actual `Λ` odd positivity, or the full odd sinh-capacity inequality, is RH-equivalent. Ground attainment, rigidity and finite negative-capacity structure are established. The complete odd form is positive through `0.362`. [WeilMarkovOddPositivity](../../../formal/GaloisForLFunctions/RHTower/WeilMarkovOddPositivity.lean); [WeilMarkovPoleCapacity](../../../formal/GaloisForLFunctions/RHTower/WeilMarkovPoleCapacity.lean); [SchurLendingOddWindowThreeHundredSixtyTwoThousandths](../../../formal/GaloisForLFunctions/ArithmeticIncidencePositivity/SchurLendingOddWindowThreeHundredSixtyTwoThousandths.lean).
- **(a) Just work.** J3: specialize the closed odd/AIP dictionaries; J4: check a concrete proposed local certificate.
- **(b) B-RH.** Pay the sinh-pole charge and all reflected prime charges for arbitrary odd profiles and arbitrary support, retaining cross-nodal cancellation.
- **Boundary.** Finite negative index does not mean zero negative index. One-signed half-line profiles and a few paid strips do not cover sign-changing profiles. Walls 1.3–1.4, 3.4.

### PBM — Prime boundary monodromy / regularized log-ζ

- **Receiver and established work [L].** Convergence of the pole-regularized prime/log-ζ series at every real `σ>1/2` is RH-equivalent; graded abscissa versions are established. [RegularizedLogZetaAbscissa](../../../formal/GaloisForLFunctions/RHTower/RegularizedLogZetaAbscissa.lean).
- **(a) Just work.** J3: match a concrete regularization to the existing abscissa theorem.
- **(b) B-RH.** Prove convergence of the actual signed regularized coefficients throughout the strict-right half-plane.
- **Boundary.** The raw positive prime series has the wrong convergence boundary. Analytic continuation is not ordinary convergence of the proposed series. Walls 1.1–1.2, 1.8.

### RB — Robin/Nicolas divisor-sum criteria

- **Receiver and established work [L].** Robin/Nicolas criteria and reductions to extremal arithmetic families are established. [RobinCriterionRiemann](../../../formal/GaloisForLFunctions/RHTower/RobinCriterionRiemann.lean); [RobinExtremalNumbers](../../../formal/GaloisForLFunctions/RHTower/RobinExtremalNumbers.lean).
- **(a) Just work.** J4: verify a specified finite range or exact extremal-family reduction.
- **(b) B-RH.** Control the eventual inequality uniformly along the prime-saturated extremal sequence, including the near-equality remainder.
- **Boundary.** Finite verification and monotonicity reductions do not control the infinite extremal tail; the needed prime-error estimate remains critical. Walls 1.1, 1.6.

### SRT — Prime-side one-parameter lag localization

- **Receiver and established work [L].** For one generic width, eventual nonnegativity of the complete prime-window lag family is RH-equivalent. Continuous lag rates read `Δ`. Explicit visibility laws address near-top zeros; discrete grids retain top-attainment qualifications. [OneParameterLagFamilyDecidesTheCriticalLine](../../../formal/GaloisForLFunctions/SquareRootThreshold/OneParameterLagFamilyDecidesTheCriticalLine.lean); [OneParameterLagFamilyMeasuresTheAbscissa](../../../formal/GaloisForLFunctions/SquareRootThreshold/OneParameterLagFamilyMeasuresTheAbscissa.lean); [OneParameterLagFamilySeesNearTopZerosAtAnExplicitLag](../../../formal/GaloisForLFunctions/SquareRootThreshold/OneParameterLagFamilySeesNearTopZerosAtAnExplicitLag.lean).
- **(a) Just work.** J3: specialize visibility constants to a prescribed width and configuration satisfying the theorem's hypotheses.
- **(b) B-RH.** Prove the arithmetic eventual lag sign. **B-C:** close a proposed grid's attainment/tail hypothesis without smuggling in zero confinement.
- **Boundary.** The current unconditional floor still has leading exponential rate `1/2`. A cofinal-invariant result for convex growth profiles is not automatically a sampling theorem for oscillatory lag values. Walls 1.1, 1.6, 3.1–3.2.

### ACT — Arithmetic criticality / single-shift variation

- **Receiver and established work [L].** The fixed-shift variation inequality for all required even compact multipliers is RH-equivalent. Gauge identities, endpoint laws and small-window certificates are established. [ThreeTenthsSharpGaugeWeilPositivity](../../../formal/GaloisForLFunctions/ArithmeticCriticalityTheory/ThreeTenthsSharpGaugeWeilPositivity.lean).
- **(a) Just work.** J3: transfer the precise existing variation/gauge identity to a specified source; J4 for an explicit finite certificate.
- **(b) B-RH.** Prove the full arithmetic variation sign at every required profile. **B-C:** an asserted converse from a shift average to a pointwise shift law requires its own estimate.
- **Boundary.** Nonnegative pointwise folded gauges fail at the specified endpoints. Signed gauges enlarge the admissible algebra, but conservation leaves the complete prime charge unchanged. Walls 1.3–1.4, 3.3–3.4.

### AIP — Arithmetic incidence positivity

- **Receiver and established work [L].** Global incidence allocation is RH-equivalent, including the version with an existential plateau. For odd compact `F` supported in `[−r,r]`, the exact accounting has the form

  `Z(F) = pool + crossing + Σ evenGain − Σ oddCost + remainder − pole.`

  The pole is `2(∫F(x)sinh(x/2)dx)²`. Surplus may be spent once. Prime-2/3 overlapping-strip payment, nested-strip payment, the quarter-point classification, collar-end second-order law and bump-to-full-prime-energy bridge are established. [GlobalIncidenceAllocationCondition](../../../formal/GaloisForLFunctions/ArithmeticIncidencePositivity/GlobalIncidenceAllocationCondition.lean); [OverlappingPrimeStripsTwentyThreeFortieths](../../../formal/GaloisForLFunctions/ArithmeticIncidencePositivity/OverlappingPrimeStripsTwentyThreeFortieths.lean); [QuarterPointClassification](../../../formal/GaloisForLFunctions/ArithmeticIncidencePositivity/QuarterPointClassification.lean); [CollarEndSecondOrderLaw](../../../formal/GaloisForLFunctions/ArithmeticIncidencePositivity/CollarEndSecondOrderLaw.lean); [BumpBridgeOfThePrimeJumpEnergy](../../../formal/GaloisForLFunctions/ArithmeticIncidencePositivity/BumpBridgeOfThePrimeJumpEnergy.lean).
- **Established [S], signed-gauge refinement.** Arbitrary signed collars preserve the exact prime autocorrelation charge. For odd profiles of one sign on the positive half-line, trans-half-width net prime charges are nonnegative. For edge-supported profiles, the net charge vanishes on the specified thin band; the cost-only sharing obstruction persists when favorable gain is discarded. [MasterSignChangingScrewGaugeTheorem](../../../formal/GaloisForLFunctions/SignChangingScrewGauge/MasterSignChangingScrewGaugeTheorem.lean). The compact-test Abel identity rewrites prime minus two-pole density as a Chebyshev-defect pairing; it supplies no sign. Its locally named `weilForm` omits the Gamma channel and must not be equated with complete Weil energy without that term. [LagChebyshevAbelSummation](../../../formal/GaloisForLFunctions/ArithmeticIncidencePositivity/LagChebyshevAbelSummation.lean).
- **(a) Just work.** J1: integrate/audit the new source; J3: apply the complete allocation identity and its closed local certificates.
- **(b) B-RH.** Construct one all-scale budget paying every cost, pole and remainder from the available gains without double spending, for arbitrary sign-changing odd profiles. Graded deficit bounds give width bounds; the zero-rate target remains RH-strength.
- **Boundary.** Separate payment of individual strips does not imply simultaneous payment. Local negative-collar improvement is compensated elsewhere. Edge-tent net cancellation resolves that example, not the full allocation problem. Walls 1.3, 3.4.

## 3. Standalone route candidates

These entries identify both the missing source construction and any remaining transfer. A zero-indexed equivalence can be fully proved while the proposed source mechanism is still a candidate.

### ACS — Arithmetic Castelnuovo–Severi / scaling-surface effectivity

- **Receiver and established work [L/S].** Cycles `aH+bV+f` carry the pole-plane intersection pairing minus the actual Weil form. Hodge index on this scaling surface is RH-equivalent. Existence of an ample, Riemann–Roch-compatible effectivity structure is likewise equivalent; this is a receiver, not a construction. The negative index of the Weil test form, equivalently the surface’s positive index in excess of one, is exactly the number of **distinct** right zeros, and aperture-filtered indices exhaust it. [TheScalingSurface](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/TheScalingSurface.lean); [TheHodgeDefectCountsTheRightZeros](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/TheHodgeDefectCountsTheRightZeros.lean); [TheDegreeFiltrationOfTheHodgeDefect](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/TheDegreeFiltrationOfTheHodgeDefect.lean).
- **(a) Just work.** J3–J4: compute a specified finite Frobenius Gram/index, use the established ghost reconstruction, or specialize the exact surface/Weil identity. J1 concerns completed working proofs. None constructs effectivity.
- **(b) B-RH.** Construct effectivity from arithmetic data and prove RR and the required positivity/ampleness or Bézout laws independently of Hodge index. **B-C:** identify the correct incidence objects and coupled pole/test cone, plus a source argument excluding adverse index at growing aperture.
- **Obstruction and survivor.** A product positive-pole quadrant times a proper scaling-closed test cone cannot satisfy the required RR property. Positive Frobenius graph cones have ample/Bézout properties but fail RR. Integral Witt data, the functional equation and even nonnegative integral Beurling primes do not imply purity: the golden `q=5`, `P=1−5X+5X²` datum is a counterexample. Its finite Frobenius defect is one, while its periodic scaling configuration has infinite defect. [BezoutEffectivityAndTheBeurlingObstruction](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/BezoutEffectivityAndTheBeurlingObstruction.lean); [TheGoldenCurveIsABeurlingSystem](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/TheGoldenCurveIsABeurlingSystem.lean); [TheScalingSurfaceOfACurve](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/TheScalingSurfaceOfACurve.lean). Walls 1.3, 3.2, 14.4; O10.

### APF — Arithmetic paired Fredholm

- **Established [L].** Exact Fredholm index and cycle-trace Fourier reconstruction. [PaperZetaCycleFourierReconstruction](../../../formal/GaloisForLFunctions/RHTower/PaperZetaCycleFourierReconstruction.lean).
- **(a) Just work.** J3–J4 for finite cycle coefficients.
- **(b) B-C / B-RH target.** Produce a zero-independent arithmetic exhaustion with all required Fourier trace coefficients vanishing. Reconstructing coefficients that encode off-line zeros does not make them vanish. Walls 1.6, 14.1.

### BSH — Arithmetic mate curvature

- **Established [L].** Framed curvature and compact-ideal diagnostics detect the radial character `n^(2 Re s−1)`; finite cutoffs are trace-blind. [DeningerOneSidedFramedMateCurvatureTransgression](../../../formal/GaloisForLFunctions/RHTower/Deninger/DeningerOneSidedFramedMateCurvatureTransgression.lean).
- **(a) Just work.** J3 for a specified fibre's diagnostic.
- **(b) B-C.** Construct a prime−Gamma section before choosing a zero, and a mate identity coupling it to `Ξ(s)=0` without assuming the radial character vanishes. Wall 14.2–14.3.

### CDC — Constitutive dagger

- **Established [L].** Calibrated confluence is equivalent to `Re s=1/2`. Finite entropy/curvature accounting has vanishing individual defects but nonvanishing total exchange work. [ConstitutiveDaggerConfluence](../../../formal/GaloisForLFunctions/RHTower/ConstitutiveDaggerConfluence.lean); [PaperCompletionInformationCost](../../../formal/GaloisForLFunctions/RHTower/PaperCompletionInformationCost.lean).
- **(a) Just work.** J3–J4 for finite defect accounting.
- **(b) B-C.** Construct a source-defined potential descending on every closed error fibre, with a noncircular coupling to actual Ξ zeros. Pointwise defect decay does not give a zero total budget. Walls 1.6, 14.3.

### DR — Dyadic Xi roots

- **Established [L].** Zero-free cusp roots, finite monodromy data and capped atlases; regularized-series abscissa receiver. [XiSymmetricLittlewoodZeroFreeCuspDyadicRoots](../../../formal/GaloisForLFunctions/RHTower/XiSymmetricLittlewoodZeroFreeCuspDyadicRoots.lean); [RegularizedLogZetaAbscissa](../../../formal/GaloisForLFunctions/RHTower/RegularizedLogZetaAbscissa.lean).
- **(a) Just work.** J3–J4 for compatible roots on a specified known zero-free finite atlas.
- **(b) B-C / B-RH.** Prove global root compatibility, monodromy control and source convergence on the whole strict-right domain. Finite covers do not supply a global root. Walls 1.2, 1.6.

### EGC — Pole-safe contour

- **Established [L].** Cofinal inner rectangles enclose prescribed poles and finite zero packets; complete mass-subtracted inner cancellation is solved. The source ray has a prime-2 sign, while the complete Gamma correction retains a reciprocal floor. [PaperEGCEnclosedPoleCancellation](../../../formal/GaloisForLFunctions/RHTower/PaperEGCEnclosedPoleCancellation.lean); [PaperEGCArithmeticRay](../../../formal/GaloisForLFunctions/RHTower/PaperEGCArithmeticRay.lean); [PaperEGCSourceRayBaseline](../../../formal/GaloisForLFunctions/RHTower/PaperEGCSourceRayBaseline.lean).
- **(a) Just work.** J3: apply the existing inner-contour theorem; inner cancellation is not an open task.
- **(b) B-C / B-RH target.** Bound the exterior expanding-contour covariance with the sign that excludes off-line copies. The inner cancellation retains every zero and cannot perform that exclusion. Walls 1.6, 1.8.

### EWJ — Euler/Wold jets

- **Established [L].** Exact finite-depth jets and compact-quotient character. [PaperEulerWoldDepthHistory](../../../formal/GaloisForLFunctions/RHTower/PaperEulerWoldDepthHistory.lean).
- **(a) Just work.** J3–J4 for specified finite jets.
- **(b) B-C.** Give zero-independent admission and norm exhaustion for the full source. Fixed-history recovery does not control transverse operator gaps. Walls 1.6, 14.1.

### FEL — Theta likelihood

- **Established [L].** Conditional KL and adaptive observation budgets, plus the exact BSY zero-sum identity. [BalazardSaiasYorZeroSum](../../../formal/GaloisForLFunctions/RHTower/BalazardSaiasYorZeroSum.lean); [PaperCircleAdaptiveHistory](../../../formal/GaloisForLFunctions/RHTower/PaperCircleAdaptiveHistory.lean).
- **(a) Just work.** J3: specialize a finite likelihood history with its full reveal cost.
- **(b) B-C / B-RH target.** Prove the cofinal source contrast balance or Jensen equality. Correct entropy accounting does not force its residual to vanish. Wall 1.5.

### HJ — Hurwitz reflection

- **Established [L].** The prime-2 reflection residual `2^(ρ−2)−2^(−conjρ−1)` vanishes exactly on the line. Its all-divisor vanishing matches HCF's two-grid signs. FE-even transport preserves the negative witness; parity restriction does not remove it. [PrimeTailSeedHurwitzReflection](../../../formal/GaloisForLFunctions/RHTower/PrimeTailSeedHurwitzReflection.lean); [XiHurwitzFunctionalEquationEvenWitness](../../../formal/GaloisForLFunctions/RHTower/XiHurwitzFunctionalEquationEvenWitness.lean).
- **(a) Just work.** J3: use the closed residual/parity dictionaries.
- **(b) B-C / B-RH target.** Force the residual to vanish at actual Ξ zeros from pre-divisor arithmetic data. Constructing zero-indexed witnesses is not that forcing mechanism. Walls 1.2, 3.3, 14.3.

### IRK — Rotation-algebra trace

- **Established [L].** Finite trace/winding data and completed Xi-jet inverse off the line, including nilpotent jets; failure of a left inverse on the line. [PrimeRotationXiCompletedResolution](../../../formal/GaloisForLFunctions/RHTower/PrimeRotationXiCompletedResolution.lean).
- **(a) Just work.** J3–J4 for a specified finite word or local winding.
- **(b) B-C.** Build the global arithmetic Poisson/projective lift with an integral analytic count and the correct original source defect. Rank plus Chern data and completion of a zero relation do not orient the source. Walls 14.1–14.3.

### MSC — Möbius–Sonin transport

- **Established [L].** A fixed squarefree discrepancy source is admitted in the unweighted critical logarithmic `L²` space and preserves the relevant evaluation/divisor information. [SquarefreeUnweightedHilbertSource](../../../formal/GaloisForLFunctions/BiScaleUncertainty/SquarefreeUnweightedHilbertSource.lean).
- **(a) Just work.** J3: use the actual evaluation columns and established norm identity.
- **(b) B-C.** Construct a source-faithful transport to nonnegative Sonin/Weil energy. The admitted source is not itself a positive energy representation; naive riggings move the divisor. Walls 1.3, 14.3.

### PCS — Singular co-shift

- **Established [L].** Explicit singular ground and persistent compact-ideal gap. The native shift/co-shift defects are incompatible with intertwining the whole carrier with invertible chronological dilation. [PCSChronologicalDilationCarrierObstruction](../../../formal/GaloisForLFunctions/RHTower/PCSChronologicalDilationCarrierObstruction.lean).
- **(a) Just work.** J3: use the surviving shift-plus-defect identities.
- **(b) B-C.** Obtain source-natural wall-class annihilation while preserving the forward mode. Any CTF bridge must carry the defect instead of identifying incompatible operators. Wall 14.3.

### PTR — Photonic source

- **Established [L].** Finite lossless stacks have real-rooted transfer entries. The proved RH equivalence with a locally uniform Ξ limit has a converse built from unknown Ξ zeros. The continuum Poisson port has unit operator/Calkin gap at every positive depth. [PhotonicLosslessProductPortRH](../../../formal/GaloisForLFunctions/RHTower/PhotonicLosslessProductPortRH.lean); [PaperPoissonCompletionGap](../../../formal/GaloisForLFunctions/RHTower/PaperPoissonCompletionGap.lean).
- **(a) Just work.** J4 for a specified finite stack; the source-faithful limit is not finite bookkeeping.
- **(b) B-C / B-RH target.** Construct a pre-divisor, nonlocal, prime-faithful port with exact Ξ landing and zero-loss control. Local finite Euler ports and a fixed-depth resonance-free handoff do not suffice. Walls 3.2, 14.1–14.3.

### RFHM — Support grade

- **Established [L].** Simultaneous finite-support/phase admission at unbounded Mellin grade and completed forward creation are solved. Reversible sewing remains inverse-covariant. [GammaThetaFullSupportCreation](../../../formal/GaloisForLFunctions/RHTower/GammaThetaFullSupportCreation.lean).
- **(a) Just work.** J3: apply the completed source/creation theorem; admission is not the missing task.
- **(b) B-C.** Find a source-defined phase/depth/compound law that breaks the relevant inverse covariance and selects the wall. Existing reversible transport does not orient real parts. Wall 14.3.

### SC — Stokes/Witt–Krein

- **Established [L].** Chamber-constant rigged fibres, common-null-set Fourier reconstruction and finite Witt/Selberg coordinates. [PaperKreinWallFourierCompletion](../../../formal/GaloisForLFunctions/RHTower/PaperKreinWallFourierCompletion.lean); [WittSelbergReceiverCoordinates](../../../formal/GaloisForLFunctions/BezoutValuationIncidence/WittSelbergReceiverCoordinates.lean).
- **(a) Just work.** J3 for finite ghost-coordinate transport at the actual cutoff.
- **(b) B-C.** Construct the source-fixed cross-fibre indefinite restriction/index that survives the wall-singular polarization and forces orientation. Wall 14.2–14.3.

### SEC — Adjacent prime seam

- **Established [L].** Essential norm equals seam charge; exact compactness and time-one factorial-Fock boundedness on every actual divisor point characterize line selection. Large-prime asymptotic smallness is nonselective. [TimeOneGammaJetFockRHCriterion](../../../formal/GaloisForLFunctions/RHTower/TimeOneGammaJetFockRHCriterion.lean).
- **(a) Just work.** J3–J4 for finite jets and the exact seam formula.
- **(b) B-C / B-RH target.** Derive exact eventual compactness or the complete Fock bound from a pre-divisor source. A charge tending to zero does not make it exactly zero. Walls 1.6, 14.1.

### W1C — Clifford–Dirac / centered Lee–Yang

- **Established [L].** Finite ferromagnetic Lee–Yang and real-rooted pencil results are available. Bare operator, simple prime-Ising and local Euler-pencil proposals have scoped obstructions. A centered magnetization limit equal to Ξ would close the receiver. [IsingLawConvergenceRH](../../../formal/GaloisForLFunctions/RHTower/IsingLawConvergenceRH.lean); [HermitianPencilEulerFactorObstruction](../../../formal/GaloisForLFunctions/RHTower/HermitianPencilEulerFactorObstruction.lean).
- **(a) Just work.** J4 for a specified finite graph and its exact partition law.
- **(b) B-C / B-RH target.** Construct arithmetic couplings with the required centered critical scaling limit, or a faithful scattering denominator. Finite real-rootedness gives no identification of the limit with Ξ. Wall 14.1–14.3.

### WBF — Source certificates

- **Established [L].** Abstract bounded scalar genealogies have Gram, determinant and completion theorems. These modules do not yet contain arithmetic coupling to primes or Ξ. [PaperCriticalGenealogyCompletion](../../../formal/GaloisForLFunctions/HTGeometry/PaperCriticalGenealogyCompletion.lean).
- **(a) Just work.** J3: instantiate the abstract theorem once an actual stream satisfying its hypotheses is supplied.
- **(b) B-C.** Define an arithmetic certificate stream and a depth-uniform positive completion with faithful Ξ/Weil landing. This missing object is not supplied by renaming scalar coefficients. Walls 1.6, 14.1, 14.3.

## 4. PM's embedded candidate

### PW-B — Hawking–BM cusp forcing

- **Established [L].** Weak retarded realization, compact-cutoff two-response identities, corrected action and original forcing/response admission at every positive damping. The construction remains indexed by `XiZeroCopy`. Eisenstein value factorization has two L-factors and does not by itself isolate ζ. [ThetaCuspHawkingBMPWNativeTwoResponseAction](../../../formal/GaloisForLFunctions/RHTower/ThetaCusp/ThetaCuspHawkingBMPWNativeTwoResponseAction.lean).
- **(a) Just work.** J3: use the existing fixed-positive-damping and cutoff identities.
- **(b) B-C.** Give a pre-divisor source formulation, control the complete energy as damping vanishes, and prove the missing action-to-optical-magnitude/ordered-cap/all-divisor-extinction landing.
- **Boundary.** Positive-damping admission is solved; zero-damping uniform control and the receiver landing are not. Walls 1.6, 1.9, 14.3.

## 5. Research programmes: achieved mathematics and actual frontier

These are overlapping programmes, not additional independent RH routes. ACT means Arithmetic Criticality Theory; ACCC below means Arithmetic Compensation Theory. Their results must be composed with their actual domains, normalizations and quantifiers. The linked Lean declarations determine the scopes reported below; intended programmes are not additional RH proofs.

### 5.1 Arithmetic positivity theory — restricted positive families and the prime channel

**Aim and objects.** **APT** constructs arithmetic test families whose full Weil form can be controlled without assuming RH. Its factorial-corrected tails, dilation families, compact truncations, prime cell kernels and grid tents serve EWU, HF, RW and the universal positivity routes. The main distinction is between positivity of a large explicit family and positivity of a family complete in the norm required by a receiver.

**What is established.**

- The physical source and its normalization are understood: logarithmic sampling has mass of order `log N/N`, not `1/N`; the independent source norm in the Krein estimate cannot be replaced by a spectral norm. The pole readout is rank one on the relevant family, and its kernel is a genuine hyperplane. These facts prevent a normalization or pole-removal argument from silently proving positivity.
- High-scale factorial families have explicit coercivity. At the critical exponent `1/2`, admission uses oscillation and an extra saving from dilation; absolute summability of the raw `Λ(n)/n` channel is unavailable.
- The limiting critical prime kernel is **negative definite on every finite coefficient pattern**, with the cell bound `R(t)≤−1/7000` and the corresponding coefficient-energy margin. In the full Weil convention this negative prime pairing helps positivity. The finite-scale prime pairing is eventually negative uniformly in coefficients **for each fixed support**. Its scale threshold still depends on that support. [FactorialCriticalPrimeKernelNegativeDefinite](../../../formal/GaloisForLFunctions/arithmetic-positivity-theory/FactorialCriticalPrimeKernelNegativeDefinite.lean); [FactorialCriticalPrimeFiniteScaleNegativity](../../../formal/GaloisForLFunctions/arithmetic-positivity-theory/FactorialCriticalPrimeFiniteScaleNegativity.lean).
- The sharp abstract Rayleigh range is already identified with `(4/π⁴)` times the cell kernel's infimum/supremum, using cosine/sine patterns that approach each value. What remains in APT-7 is explicit determination of the extrema and shape, not the range-to-symbol theorem. [FactorialCriticalPrimeToeplitzSymbolRange](../../../formal/GaloisForLFunctions/arithmetic-positivity-theory/FactorialCriticalPrimeToeplitzSymbolRange.lean).
- Uniform control is substantially beyond fixed finite patterns. There is high-dyadic-block positivity for arbitrary support size; polynomial windows `[M,LM]` with `L≤M^δ` for a positive `δ`; a compact-test version uniform in sufficiently large truncation `V`; and positive lacunary unions with successive blocks satisfying the stated eighth-power separation. The compact polynomial-window capstone gives a margin proportional to `log M` times coefficient mass, followed by a smooth reflected-test realization. [CompactCriticalPolynomialWindowAndTemperednessBridge](../../../formal/GaloisForLFunctions/arithmetic-positivity-theory/CompactCriticalPolynomialWindowAndTemperednessBridge.lean); [LacunaryCriticalBlockPositivity](../../../formal/GaloisForLFunctions/arithmetic-positivity-theory/LacunaryCriticalBlockPositivity.lean).
- The old `ℓ¹`-to-`ℓ²` prime-budget problem is resolved in the collared setting and at the uncollared endpoint by the corpus's Montgomery–Vaughan input. Grid-tent interpolation and full-form stability give a complete testing language. They do **not** identify all those tents with the particular positive high-scale families.

**What is still unpaid.**

| ID | Exact task | Classification and completion condition |
|---|---|---|
| APT-1 | Control low scales and densely adjacent blocks outside the proved high-scale/polynomial/lacunary regimes. | **B-C.** A full estimate must include cross-block terms; arbitrary cardinality inside one permitted window does not remove the window restriction. |
| APT-2 | Give an explicit growing-support range in which the **actual prime channel itself** remains negative. | **B-C.** Fixed-support eventual negativity is proved; full-form positivity subsidized by growing archimedean energy is not this assertion. |
| APT-3 | Determine the sharp cost of increasing window width and admitting nonlacunary scale unions. | **B-C.** Specify dependence on `M,L,V` and coefficients, including the low-mode interaction. |
| APT-4 | Connect the proved positive families to a complete Weil/ground-energy receiver with controlled norm loss. | **B-RH** at an all-test positivity conclusion; **B-C** for partial bridges. Ordinary density, or positivity gained from a large `log M` archimedean term, is insufficient without a uniform bound after transport. |
| APT-5 | Quantify grid/tent detection in depth and height, retaining the prime cutoff beyond the observation horizon. | **B-C.** The qualitative complete family exists. The missing result is a usable detection/cost bound, not a new definition of a tent. |
| APT-6 | Find additional admitted sources or cell kernels, and a source-faithful operator realization of the positive family. | **B-C.** A new source must retain the actual prime and polar terms and specify its landing in a receiver. |
| APT-7 | Determine the cell kernel's exact extrema, their locations, first couplings and monotonicity on the half-cell. | **B-C.** The proved negative bound is sufficient for existing positivity, but does not supply the optimal constant or these shape classifications. |
| APT-8 | Obtain a single-height prime-phase saving enlarging the certified aperture beyond the present `log log T` range. | **B-C**, shared with SR-5. Height-uniform coefficient-size estimates have their own sharp ceiling; the proposed improvement must use the actual height-dependent phases. |

**(a) Just work.** Evaluate already proved threshold formulas after explicit collar/derivative bounds have been supplied; specialize compactification and finite-support negativity to a fixed family; package the existing grid interpolation with its stated stability norm. These are J2, J3 and J6. Constructing positivity at an unproved scale, or removing the stability norm, is not included.

**Boundary of the no-go results.** Failure of the temperedness premise for shifted-pair deformations is a failure of that bridge's input, not a proof that every conclusion about those deformations is false. Full-positive weight rigidity says the cone is contained in `{Λ}`; existence of that member remains RH-strength. Walls 1.3–1.4, 3.2 and 14.3.

### 5.2 BiScale Uncertainty — the critical band, blind cones and recovery

**Aim and objects.** **BiScale** compares the signed prime packet, normalized logarithmic Chebyshev error, Laplace Gram energy and frequency-band energy. It also develops arithmetic observation and blind-cone extremal problems. Its principal closing target is an estimate on the actual prime source, not reconstruction of the equivalent observables.

**What is established.**

- The critical mean-square band grows linearly **if and only if RH**. A subexponential bound self-improves to the linear one through that equivalence. The outer-frequency contribution is paid; the unpaid part is the band of width proportional to `√N`. Hardy's theorem supplies a positive lower slope, so an `o(L)` target is false. [PacketBandLaw](../../../formal/GaloisForLFunctions/BiScaleUncertainty/PacketBandLaw.lean).
- Packet growth reads the deepest detected zero. One-sided control suffices. The universal probe is already explicit: the boosted cubic-spline construction closes the earlier “make the boost explicit” construction problem. Its arithmetic eventual bound remains open. [CubicSplineUniversalProbe](../../../formal/GaloisForLFunctions/BiScaleUncertainty/CubicSplineUniversalProbe.lean).
- Packet mean-square energy weights a zero of multiplicity `m` by `m²`, while the Weil functional weights it by `m`. Equating these energies imports critical-zero simplicity; RH alone does not give that equality. Under RH, the Cramér liminf is at least the complete zero energy, and a linear upper bound is proved. The raw normalized-Chebyshev limiting constant is not supplied by those two bounds. For each fixed compact packet, the mean-square limit under RH is already proved: it is the `m²`-weighted critical packet energy. The optimal uniform packet/Weil comparison constant equals the maximal critical multiplicity. [MultiplicityCeilingLaw](../../../formal/GaloisForLFunctions/BiScaleUncertainty/MultiplicityCeilingLaw.lean). [CramerLiminfLaw](../../../formal/GaloisForLFunctions/BiScaleUncertainty/CramerLiminfLaw.lean); [CramerChebyshevMeanSquare](../../../formal/GaloisForLFunctions/RHTower/CramerChebyshevMeanSquare.lean).
- The blind slack on the powers of one integer is solved as a circle moment problem, including deletion variants. An independent additional node gives a strict gain. For two towers the line-law constraints, certificates and explicit convolution designs give an **enclosure**, not the exact optimum. Prime-power node positivity is equivalent to **RH together with containing every prime power**. Deleting `4` is fatal to that node criterion; deleting a non-prime-power such as `6` is irrelevant to it, although `6` can matter to a different tower extremum. [PrimePowerZeroPoleNodeCriticality](../../../formal/GaloisForLFunctions/BiScaleUncertainty/PrimePowerZeroPoleNodeCriticality.lean).
- Observation recovery goes beyond a qualitative sign classification. Fifth and sixth translated moments determine the finite sieve signal up to physical translation, including the half-period companion. Across mixed support strata, moment errors at most `ε∈[0,1]` imply physical error at most `3(Σ_{q≤N}φ(q)) ε^(1/6)` after a translation. Thus global sixth-root stability is already solved; its constant depends on the cutoff. [SievePhysicalTranslationStability](../../../formal/GaloisForLFunctions/BiScaleUncertainty/SievePhysicalTranslationStability.lean), `exists_physical_translate_holder`.
- Finite triangular Gram estimates have exact numerical-radius constants. Discarded lower-triangular entries remain actual error terms, and the gain degenerates as matrix size grows. Finite-dimensional gain is not an all-family bound.
- The Müntz correction tail identifies a specific completion obstruction: the omitted negative-logarithmic tail costs archimedean energy of order `(1/2)log(n+1)` against an `O(1/(n+1))` prime/pole contribution in that construction. Improving seed regularity or its already exact diagonal readout does not remove this cost. A different bounded-cost completion would have to redistribute the archimedean energy.

| ID | Exact task | Classification and completion condition |
|---|---|---|
| BS-1 | Bound the actual critical band by `C(1+L)`, or prove the equivalent subexponential/one-sided universal packet bound. | **B-RH.** Complete source, every required horizon, no omitted endpoint. |
| BS-2 | Identify the limiting raw normalized-Chebyshev band constant and quantitative finite-cutoff errors; do not reopen the established compact-packet mean-square limit. | **B-C.** For the raw field, upgrade the reviewed liminf/upper bounds to the stated exact limit or identify an existing classical theorem and its hypotheses; preserve multiplicities. This is a project gap, not an established worldwide open problem. |
| BS-3 | Solve the two-tower blind slack and the prime-power-only blind cone; control the full blind polar infimum. | **B-C** for restricted extrema; **B-RH** when the resulting full archimedean positivity criterion is discharged. |
| BS-4 | Sharpen recovery constants/exponents in stated support strata, or recover from fewer/windowed observations with a quantified cutoff cost. | **B-C.** Global sixth-root existence is not an open item. Exact algebraic recovery does not bound receiver energy. |
| BS-5 | Obtain a bounded completion cost for actual arithmetic observation families and a sign or useful bound for prime-clock edge-minus-mass. | **B-C.** Clock kernels retain center and cutoff, so a lag-only convolution model is not justified. |
| BS-6 | Produce a finite-prime certificate whose tail control reaches the complete packet/band receiver. | **B-RH** at closure. Finite interpolation and fixed grids are established infrastructure. |
| BS-7 | Determine whether finite prime data with a justified tail can test `E(U)=W(U)`, and bound Weil energy from one linear packet without assuming its one-sided control. | **B-C** for the proposed certification/inequality; its strength depends on the precise receiver. The equality includes a multiplicity/simplicity issue beyond RH alone. |

**(a) Just work.** Instantiate the explicit probe, exact one-tower formulas, finite recovery theorem and already proved source transports. Compute no new theorem from a favorable finite example. The alternate HF window ceiling `e^(L/2)+O(L)` is sufficient for RH; its excess exponent is only pinched by `Δ≤θ*≤Δ/2+1/4`, and is not an established exact width dictionary. Walls 1.1, 1.4, 1.6 and 3.

### 5.3 Trans-Horizon Incidence Mechanics — which arithmetic observations retain the sign?

**Aim and objects.** **THIM** studies finite divisor rows, their periodic responses, primitives, prefix defects and passage between observation horizons. It separates period-torus information from the pronic prefix energy that PM actually needs. Its odd-source graph is also a bridge to CHMD/ACT.

**What is established.**

- Dirichlet polarization and the boundary-square decomposition are exact. The unit-response envelope has sharp ratio `5`; small-horizon certificates and quotient ladders are established. These constants concern specified finite classes.
- **Global prefix-defect sign is already proved at all sufficiently large sieve horizons**, uniformly over damping `ε∈[0,1]` and the prefix parameter. The rough-prime boundary argument and the cofactor-row theorem go beyond low-depth certificates. This is a sign of a particular defect, not boundedness of the complete primitive energy. [RoughPrimeBoundaryUniformDampingDefectSign](../../../formal/GaloisForLFunctions/TransHorizonIncidenceMechanics/RoughPrimeBoundaryUniformDampingDefectSign.lean); [PMCofactorRowGlobalDefectSign](../../../formal/GaloisForLFunctions/TransHorizonIncidenceMechanics/PMCofactorRowGlobalDefectSign.lean).
- Period response variance is bounded for each positive damping, while primitive mean-square discrepancy diverges in the subcritical regime. Period comparison therefore cannot pay the actual pronic prefix energy. Möbius variance escapes any fixed set of moduli; damping restores tightness. Small-damping response and reserve have leading term `ε/2`, and lag-one covariance has leading term `−ε²`. The prime crossover has an explicit rapidly escaping location.
- The **response-level** pronic observable already commutes with the damping limit by a summable divisor-count majorant and tends to `1/2`. This concerns `Σs_N(n)²/[n(n+1)]`, not the receiver's centered **primitive**. It must not be reopened as a general limit problem or mistaken for primitive admission. [PronicEnergyCommutesWithDamping](../../../formal/GaloisForLFunctions/TransHorizonIncidenceMechanics/PronicEnergyCommutesWithDamping.lean).
- Buchstab/smooth-core and cofinal quotient profiles are constructed. **Monotonicity of the cofinal quadratic profile `P(B)` is already proved** in BVI, including the exact values at `B=1,2`; this is not an outstanding monotonicity problem. Concavity, further band laws and broader sign classifications are separate questions. [CofinalMobiusQuadraticQuotientProfile](../../../formal/GaloisForLFunctions/BezoutValuationIncidence/CofinalMobiusQuadraticQuotientProfile.lean).
- Schedule injectivity is classified by missing slots; sharp one-gap observability constants and a separate actual squarefree-row law are available. They are statements on different source classes, not interchangeable constants.
- Odd-source energy has a canonical polar moment and an exact Weil-plus-polar-square decomposition. Shifting the gauge does not tune that moment freely. Local lobe estimates and correction/confinement laws survive failed derivative cosh/sinh absorption, but no uniform positive primitive gap is available.
- Magnitudes and Ramanujan amplitudes cannot decide the below-half receiver on the full damped coefficient class. More strongly, an even parity flip can preserve **all translated moments of all orders** of the squarefree periodic signal while changing admission. Pronic observations retain information those periodic readings lose: the first such moment reads prime powers, and the logarithmic hierarchy separates the relevant pairs. Separation is not an energy bound. Critical Wiener kernels with `Σ|g(q)|q^(−1/2)<∞` give a genuine admission-preserving class.
- For bounded multiplicative weights taking value `−1` at every prime, the damped receiver inherits Möbius admission and is admitted at half damping. Nonnegative bounded multiplicative weights taking value `+1` at every prime are not admitted for `0<ε≤1/2`. Intermediate classes now have exact results described below; they do not yield a universal classification by sign density. [ReceiverOfMultiplicativeWeightsIsDecidedAtThePrimes](../../../formal/GaloisForLFunctions/TransHorizonIncidenceMechanics/ReceiverOfMultiplicativeWeightsIsDecidedAtThePrimes.lean).

- **Exact multiplicative thresholds [L/S].** For the completely multiplicative constant-prime family `z^Ω(n)`, `−1≤z≤1`, admission occurs iff `ε>1/2`, or `ε=1/2` and `z<1/2`, or `z=0`, or `z=−1` and the actual Möbius receiver is admitted. Negative residue-class density at most `1/4` is nonadmitted at half damping; subgroup-complement flips have positive admission theorems. These are genuine classifications in their stated classes. [ThePhaseDiagramOfTheConstantSignPattern](../../../formal/GaloisForLFunctions/TransHorizonIncidenceMechanics/ThePhaseDiagramOfTheConstantSignPattern.lean); [TheQuarterBoundaryOfResidueClassFlips](../../../formal/GaloisForLFunctions/TransHorizonIncidenceMechanics/TheQuarterBoundaryOfResidueClassFlips.lean); [SubgroupFlipsArePaidAtHalfDamping](../../../formal/GaloisForLFunctions/TransHorizonIncidenceMechanics/SubgroupFlipsArePaidAtHalfDamping.lean).
- **Spectral amplitude matters [L/S].** For prime values `a cos(t₀ log p)`, `−1≤a≤1`, half-damped admission is exactly `(t₀=0 and a<1/2)` or `(t₀≠0 and (a<1 or ζ(1/2+it₀)=0))`. Matching prime signs and prime mean can still leave different admission. Additive log-power probes read successive ζ derivatives; this spectroscopy is not an estimate for the actual Möbius row. [OscillatingPrimePatternsArePaidExactlyAtTheCriticalZeros](../../../formal/GaloisForLFunctions/TransHorizonIncidenceMechanics/OscillatingPrimePatternsArePaidExactlyAtTheCriticalZeros.lean); [AllFrequencyLogPowerReceiverAndMultiplicityLaws](../../../formal/GaloisForLFunctions/TransHorizonIncidenceMechanics/AllFrequencyLogPowerReceiverAndMultiplicityLaws.lean).
- **Quantitative probe calibration [S].** For `t≠0`, the half-damped smooth-power cosine probe satisfies `E_T/log T → |ζ(1/2+it)|²/(2|1/2+it|²)`. Below half its leading term is an explicit oscillatory profile times `T^(1−2ε)`. This evaluates a spectral probe, not the energy of the actual Möbius source. [TheProbeReceiverEnergyMeasuresTheModulusOfZeta](../../../formal/GaloisForLFunctions/TransHorizonIncidenceMechanics/TheProbeReceiverEnergyMeasuresTheModulusOfZeta.lean).
- **Endpoint and cutoff laws [L/S].** Critical-Wiener perturbations below half are paid exactly by their pole-hyperplane condition and have uniformly paid centered rows. At half the exact criterion is the logarithmic square energy of partial pole sums; the absolute square-root-log sufficient class is sharp. For general damped signed weights, admission and uniform dyadic-row admission are equivalent only at/above half. [TheHalfDampedHyperplaneLawHasAnExactLogarithmicThreshold](../../../formal/GaloisForLFunctions/TransHorizonIncidenceMechanics/TheHalfDampedHyperplaneLawHasAnExactLogarithmicThreshold.lean); [CriticalWienerPerturbationsOfTheSmoothPowerHaveUniformlyPaidRows](../../../formal/GaloisForLFunctions/TransHorizonIncidenceMechanics/CriticalWienerPerturbationsOfTheSmoothPowerHaveUniformlyPaidRows.lean).
- **Actual small damping [S].** Möbius and Liouville have the same positive admission set and the same width accumulation threshold. Uniform estimates on the horizon-dependent near-half band extend to every fixed positive damping floor. This still does not give a fixed below-half bound for all horizons. [SmallDampingMoebiusAndLiouvilleCancellationLaws](../../../formal/GaloisForLFunctions/TransHorizonIncidenceMechanics/SmallDampingMoebiusAndLiouvilleCancellationLaws.lean).

| ID | Exact task | Classification and completion condition |
|---|---|---|
| THIM-1 | Bound actual signed pronic primitive energy uniformly in horizon at cofinally small positive damping. | **B-RH.** The large-horizon prefix-defect sign is a proved input, not this bound. |
| THIM-2 | Convert a signed, non-periodic moment hierarchy into a quantitative receiver bound. | **B-C.** Name the norm and observation cost; injectivity alone is insufficient. |
| THIM-3 | Pay cross-lobe terms for arbitrary sign-changing odd sources, with the canonical pole correction retained. | **B-RH** at full odd positivity; **B-C** for a new restricted class or decomposition. |
| THIM-4 | Complete low-horizon defect classification, all-band Buchstab asymptotics, profile concavity and negative-core classification. | **B-C.** Eventual sign and profile monotonicity are solved. Finite outstanding cases become J4 only after a concrete finite reduction/certificate is supplied. |
| THIM-5 | Classify odd-prime/multiple-gap schedules and sharp least-squares observability; classify which parity transformations preserve receiver admission. | **B-C.** Existing one-gap and even-flip results delimit these questions rather than answer them. |
| THIM-6 | Extend the exact smooth-power and critical-Wiener endpoint classifications to other signed kernels and sources. | **B-C.** At half damping, the exact replacement is already the logarithmic energy of partial pole sums; a general-source extension is separate. |
| THIM-7 | Resolve slope signs inside the additive crossover window and terms beyond second order in variance/reserve; classify remaining multiplicative spectra and source-specific primitive limit passages. | **B-C.** The quarter boundary is proved for the specified constant and residue-class families; general frequency-dependent patterns require more information than negative-prime density. Specify centering, uniform bounds and limit order; response-level commutation is already solved. |

**(a) Just work.** Reuse the now-global defect theorem, exact polarization, schedule formulas and already established Wiener transport. It is not necessary to rebuild those identities before studying the remaining signed primitive. Walls 1.8–1.9, 3.3–3.4.

### 5.4 Bézout–Valuation Incidence — the interior martingale and actual arithmetic rows

**Aim and objects.** **BVI** provides a finite incidence calculus and the exact energy accounting for

`Eε(T)=Σ_{n≤T} Aε(n)²/[n(n+1)]`.

Its Selberg/Ramanujan coordinates, cotangent–sawtooth Gram, adjacent-divisor conditional means and damping chain are concrete arithmetic objects. The critical question is what their signed interaction does before a full period, uniformly in the physical horizon.

**What is established.**

- Cross-depth hypercube cancellation, reciprocity and the Gram are explicit. The sharp reciprocity remainder has its stated `h(1+log(p/h))` cost. Exact observation has linear recurrence dimension `Φ(N)`, while quadratic mean-square transfer requires horizon `N²` in the sharp class; degree-`m` observation has its own polynomial horizon. Exact recovery and a short-window energy estimate are different problems.
- The energy splits into active-deleted diagonal, predecessor-peak martingale and Bézout interior martingale. After subtracting canonical logarithmic drifts, the first two pieces are **bounded for each fixed positive damping**, not merely `o(log T)`. The compensated-remainder theorems give this uniform bound. The remaining horizon dependence is the compensated interior term. [UniformActiveDeletedCompensatedRemainder](../../../formal/GaloisForLFunctions/BezoutValuationIncidence/UniformActiveDeletedCompensatedRemainder.lean); [UniformAdjacentDivisorCompensatedRemainder](../../../formal/GaloisForLFunctions/BezoutValuationIncidence/UniformAdjacentDivisorCompensatedRemainder.lean); [CompensatedHarmonicPredecessorPeakDriftAndDiagonalBudget](../../../formal/GaloisForLFunctions/BezoutValuationIncidence/CompensatedHarmonicPredecessorPeakDriftAndDiagonalBudget.lean).
- More precisely, `|2M_int(T)+2 Counterterm·H_comp(T)−Eε(T)|≤Cε`, and strict interior contraction is equivalent to bounded energy. This is a bounded-error reduction to one signed term, not a small relative error proving contraction. [UniformRenormalizedInteriorEnergyRemainder](../../../formal/GaloisForLFunctions/BezoutValuationIncidence/UniformRenormalizedInteriorEnergyRemainder.lean).
- The interior and full energy control each other. A strict interior contraction closes admission; summation by parts in the same variable returns energy with coefficient **one**, giving a conservation identity rather than that contraction. The required small-damping cancellation slope is explicit and at least `7/24`.
- On the dual side the Báez–Duarte residual is exactly a readout defect squared plus centered Gram energy. Its unconditional lower floor is `κ/log N`. Making readout close to one while centered energy also tends to zero is the missing construction; neither objective can be omitted.
- Generic cross-scale Type-II control has the sharp `Q≥P^(5/3)` threshold, or `θ=2log P/log Q=6/5`. The pronic short-window obstruction uses `θ=2log P/log X` and threshold `1`. These are **different parameterizations and different classes**. Smooth Type-I improvements require smoothness not automatically possessed by the actual rows.
- Actual arithmetic rows already beat parts of the generic loss. Fixed-prime Möbius statistics are `o(1/Q)`. The omitted-class prime statistic has an explicit **nonzero** leading bias, which must be centered. Centered prime block equidistribution reaches the stated range `P^(1+δ)≤Q≤P^(30/17−δ)`. The low-frequency dual-norm estimates use a Möbius averaging window `H=⌊log₂Q⌋`, or a prime window `H=⌈(2Q)^α⌉` with `17/30<α<1` in the strengthened short-interval regime; primes must exceed the corresponding `H` or `H log²Q` threshold. The displayed bound still contains block mass and the `n^(−3),n^(−4)` tails. [SingleModulusCancellationOfTheMoebiusBlock](../../../formal/GaloisForLFunctions/BezoutValuationIncidence/SingleModulusCancellationOfTheMoebiusBlock.lean); [MoebiusBlockBeatsTheTypeTwoBarrier](../../../formal/GaloisForLFunctions/BezoutValuationIncidence/MoebiusBlockBeatsTheTypeTwoBarrier.lean); [CentredPrimeBlockBeatsTheLargeSieve](../../../formal/GaloisForLFunctions/BezoutValuationIncidence/CentredPrimeBlockBeatsTheLargeSieve.lean); [DualNormOfTheActualRowsBeatsTheLargeSieve](../../../formal/GaloisForLFunctions/BezoutValuationIncidence/DualNormOfTheActualRowsBeatsTheLargeSieve.lean).
- Vinogradov–Korobov input gives a uniform receiver bound on a **shrinking horizon-dependent band**
  `ε≥1/2−κσ(T)/(480 log T)`, with `σ(T)=(log T)^(3/5)(log log T)^(−5/3)` in the stated range. This separates actual arithmetic from a positive twin. It does not admit any fixed `ε<1/2` for all horizons. Size alone admits `ε>1/2`; the actual endpoint `ε=1/2` uses arithmetic cancellation.

The stronger centered-prime range uses the `17/30` short-interval exponent: `P^(1+δ)≤Q≤P^(30/17−δ)` with its prescribed positive slack, polynomial horizon and centered row. [TheSeventeenThirtiethsWindowWidensTheCentredPrimeRowRange](../../../formal/GaloisForLFunctions/ArithmeticCompensationTheory/TheSeventeenThirtiethsWindowWidensTheCentredPrimeRowRange.lean). This advances the admissible unbalanced range; it does not control `Q≈P` or remove the displayed remainders. The analytic input is consistent with [Guth–Maynard's large-value and short-interval work](https://arxiv.org/abs/2405.20552).

**Damping-chain frontier, with proof status kept separate.** The centered positive-time operator `Cη` is compact on `c₀` and forms a semigroup. The normalized residue modes

`v_d(n)=floor((n+1)/d)/(n+1)−1/d, d≥2`

have dense span in `c₀`. Density is a theorem in [ResidueModeCompleteness](../../../formal/GaloisForLFunctions/BezoutValuationIncidence/ResidueModeCompleteness.lean), not an assumption about a spectral expansion. Strong continuity at zero, the estimate `‖Cη−I‖≥1` for `η>0`, residue derivatives `Av_d=−log(d)v_d`, and absence of a bounded generator are established in [DampingIsStronglyContinuousWithUnboundedGenerator](../../../formal/GaloisForLFunctions/SignedArithmeticEnergyIncidence/DampingIsStronglyContinuousWithUnboundedGenerator.lean). These do not supply a Schauder basis, bounded spectral projections, backward stability, or a critical-pronic estimate. The directly inspected [real-spectrum Lean draft](../../drafts/pipeline/1-in-progress/thim-bvi-250/pending-lean/ArithmeticDampingCenteredSpectrum.lean) supplies explicit proofs of spectrum `{0}∪{d^(−η):d≥2}`, one-dimensional nonzero eigenspaces and injectivity; integration and certification are J5. A full generator graph-core theorem is not established by that draft and remains a separate BV-5/SAEI-5 obligation if a method needs it.

| ID | Exact task | Classification and completion condition |
|---|---|---|
| BV-1 | Bound the compensated interior martingale, or prove its strict contraction against the full energy. | **B-RH** for cofinal zero damping. Canonical diagonal and predecessor compensation are solved. |
| BV-2 | Bound the growing-modulus actual-row dual norm with all centering, mass and higher-order tails, particularly balanced scales. | **B-C** for specific new ranges/rates; **B-RH** when sufficient for the receiver. Fixed-modulus cancellation is not the outstanding task. |
| BV-3 | Construct dual rows with both vanishing readout defect and centered energy; determine whether the `1/log N` floor is attained. | **B-RH** at the complete approximation target; quantitative optimality is a further problem. |
| BV-4 | Transfer the damping-chain structure from `c₀` to a signed estimate in the actual pronic energy space. | **B-C**, with **B-RH** closure if it yields cofinal admission. The entrance-law pronic dual norm is finite exactly for `η>1/2`; reciprocal weighting supplies a different admitted class at all `η>0`. [PronicDualNormOfTheEntranceLaw](../../../formal/GaloisForLFunctions/BezoutValuationIncidence/PronicDualNormOfTheEntranceLaw.lean). |
| BV-5 | Obtain sharp finite-window observation/stability costs and bounded projection/basis properties where needed. | **B-C.** Dense residue span and sixth-root recovery are already proved; neither supplies these stronger quantitative properties. |
| BV-6 | Control a general signed prime packet and its complementary lags; obtain cofinal profile rates uniform in band ratio, mixed-level residue-cell covariance bounds and the additive window-incidence laws needed to couple divisor edges. | **B-C.** Exact nearby-prime seed values and positivity of special same-start/common-factor cells do not sign the full packet. |

For BV-5, the specific observation questions include the gap between the quadratic universal horizon and linear special-horizon recovery, and the sharp sandwich constant currently bracketed by `Φ(N)−2` and `N(N−1)`. These are not all solved by the exact recurrence length `Φ(N)`.

**(a) Just work.** Integrate the existing real-spectrum draft and strong-continuity/residue-generator statements; specialize them on their proved domains (J5). A full graph-core or spectral-expansion theorem needs its own checked proof. Apply the actual-row bounds within their stated ranges and the bounded compensated-remainder results (J3). Proof integration is distinct from proving the pronic-space estimate. Walls 1.8–1.9, 3.1 and 14.3.

### 5.5 Arithmetic Criticality Theory — one shift is complete, but the gauge must pay its remainder

**Aim and objects.** **ACT** writes tests as `F=Θv` and compares shift variation, surplus and potential. The Markov form, odd zero form and full Weil form differ by explicit sinh/cosh polar moments. Choosing a gauge changes the decomposition, not the complete arithmetic charge.

**What is established.**

- For **one fixed shift `a>0`**, the required variation inequality on all even compact `C²` multipliers is equivalent to RH. It is unnecessary to prove a separate independent receiver for every shift. The archimedean part satisfies its variation bound; the remaining nontrivial sign lies on the prime antidiagonals with their pole terms. [SingleShiftCompleteness](../../../formal/GaloisForLFunctions/ArithmeticCriticalityTheory/SingleShiftCompleteness.lean).
- A two-moment law obstructs a precise class of positive folded gauges. For `C¹` gauges `M` with `M(0)=0` and the stated `e^(−8|y|)` bounds, origin and infinity read `−2∫M dm` and `−2∫M cosh` in the respective normalizations. A nonzero nonnegative `M` fails at both ends. Signed gauges can repair the endpoint signs, but the remainder across their nodes is not automatically nonnegative. [FoldedSourceOriginJumpMomentLaw](../../../formal/GaloisForLFunctions/ArithmeticCriticalityTheory/FoldedSourceOriginJumpMomentLaw.lean).
- The harmonic theta direction is a radical; translated ground states carry an exact Lorentz law. Quantitative plateau/null approximation is already available, including the proved exponential rates. Reopening “find any quantitative null approach” overlooks these results. [HarmonicThetaSpanRadical](../../../formal/GaloisForLFunctions/ArithmeticCriticalityTheory/HarmonicThetaSpanRadical.lean); [ShiftedGroundStateSpanPlateauLaw](../../../formal/GaloisForLFunctions/ArithmeticCriticalityTheory/ShiftedGroundStateSpanPlateauLaw.lean).
- The full window `A=0.3` and odd window `A=0.362` are established with explicit floors. The full-window argument pays some negative folded conductances through a hub; it does not prove every conductance nonnegative. The even unit-cosh-moment slice beyond the full window remains separate from odd positivity.
- Uniform positive Hardy improvements on the original radical-containing space are refuted, and prime rates/variance terms have sharpness laws. This excludes a fixed positive margin, not every subexponential loss or every quotient-space estimate.

| ID | Exact task | Classification and completion condition |
|---|---|---|
| AC-1 | Prove the fixed-shift variation inequality for every required multiplier. | **B-RH.** Keep surplus, potential and both polar corrections in the stated normalization. |
| AC-2 | Build a signed gauge with global nodal-remainder control, or a usable replacement for the failed monotone-fold domination. | **B-C** until the complete all-profile inequality is reached. Endpoint repair alone is insufficient. |
| AC-3 | Formulate and prove a Hardy/coercivity law after removing the radical in an explicitly chosen quotient norm. | **B-C.** The quotient, domain and norm cannot be inferred from the failed original-space inequality. |
| AC-4 | Enlarge the even unit-cosh slice/full positivity window and control arbitrary cross-lobe profiles. | **B-C** locally; **B-RH** at all apertures. Odd-window improvement does not settle this. |
| AC-5 | Prove a valid quantitative relation between an averaged shift law and the pointwise fixed-shift receiver. | **B-C.** Depth-blindness of a specified averaged reading needs a theorem on that reading; it is not a universal no-go for shift methods. |
| AC-6 | Prevent a ground-energy crossing using a floor allowed to decay with aperture. | **B-RH** at global nonnegativity. A positive aperture-independent floor is incompatible with the established upper ceiling. |
| AC-7 | Determine sharp capacity-ratio approach rates and usable arithmetic Harnack propagation across prime shifts. | **B-C.** Explicit collar/moment laws and quantitative null sequences do not supply these global propagation or sharpness statements. |

**(a) Just work.** Use the existing one-shift completeness, null-rate estimates and exact gauge identities. Specializing their constants is J3/J6; proving a new gauge sign is not. Walls 1.3, 3.3–3.4.

### 5.6 Arithmetic Incidence Positivity — local payments are substantial; global sharing is the problem

**Aim and objects.** **AIP** resolves the odd Weil form into one shared surplus, crossing gains, even-part gains, prime-strip costs, a signed archimedean remainder and the polar square. The source of difficulty is allocation across overlapping strips and changing signs, rather than lack of an exact identity.

**What is established.**

- Atom-versus-density comparisons and their dimensions are explicit. The lattice symbol changes sign between `log 5` and `log 6`. The atom exceeds the pole even at the midpoint exactly for `{2,3,4,5,7}`; including the archimedean density enlarges the unpaid list to `{2,3,4,5,7,8,9,11,13}`. Quarter-point and collar-end classifications are closed, including second-order collar asymptotics. They are exact local classifications, not positivity of the continuum form.
- Each prime atom has a paid own microstrip within the stated `1/12` extension. Nested strips cannot all spend that same surplus. Retaining the even-part gain and lending between origin, strip and middle gives **full odd positivity through `0.362`**. [SharpMicroFoldHarnack](../../../formal/GaloisForLFunctions/ArithmeticIncidencePositivity/SharpMicroFoldHarnack.lean); [SchurLendingOddWindowThreeHundredSixtyTwoThousandths](../../../formal/GaloisForLFunctions/ArithmeticIncidencePositivity/SchurLendingOddWindowThreeHundredSixtyTwoThousandths.lean).
- The joint prime-2/3 **strip costs** are paid through `23/40=0.575` with a strict margin. This closes that local allocation subproblem beyond earlier constants; it is **not** full odd Weil positivity at `0.575`. Chain allocations can succeed where a union estimate fails. At large radius a sufficiently thin light-cone band is paid, without paying the rest of the form. [OverlappingPrimeStripsTwentyThreeFortieths](../../../formal/GaloisForLFunctions/ArithmeticIncidencePositivity/OverlappingPrimeStripsTwentyThreeFortieths.lean).
- Odd-part-only payment is false, already for a single prime near its first threshold and for edge profiles. The signed-screw refinement [S] proves conservation under signed collars, nonnegative trans-half-width net charge for half-line one-signed odd profiles, and exactly zero thin-band net charge for the specified edge profiles. These are positive survivors of failed cost-only estimates. [FirstPrimeOddPartPaymentWall](../../../formal/GaloisForLFunctions/ArithmeticIncidencePositivity/FirstPrimeOddPartPaymentWall.lean); [MasterSignChangingScrewGaugeTheorem](../../../formal/GaloisForLFunctions/SignChangingScrewGauge/MasterSignChangingScrewGaugeTheorem.lean).
- Global incidence allocation, with all terms and the plateau quantifier retained, is RH-equivalent. A graded deficit `C e^(2σr)` times mass implies `Δ≤σ`. The all-scale zero-rate condition is therefore the real closing target; a positive-width estimate remains useful weaker progress. [GlobalIncidenceAllocationCondition](../../../formal/GaloisForLFunctions/ArithmeticIncidencePositivity/GlobalIncidenceAllocationCondition.lean).
- Translation calculus reduces a prime-power tower to a first-power term with its Euler diagonal discount. Resonant trains attain the one-tower envelope; bi-lattice trains can resonate at two towers together. A Möbius comb can be blind precisely on a maximally charged mode. Prime-comb Cauchy gives a diagonal plus a cross-prime aggregate: the diagonal has the advertised manageable bound, but a nonpositive cross aggregate is false. A uniform polynomial bound on that complete aggregate is refuted by its exponential mean-field growth; normalized resolvent and signed-charge estimates are the viable replacements.
- The prime-only bump bridge and compact-test prime-minus-pole Abel identity are established. The full odd narrow-bump calibration is stated with a proof in [ArithmeticIncidenceNarrowBumpBridge](../../../formal/GaloisForLFunctions/RHTower/ArithmeticIncidenceNarrowBumpBridge.lean) [S]. Its current source includes exact prime sampling, the full-energy/prime-matrix identity and the capstone `fullEnergy_latticeTrain_uniform` for an odd lattice starting at integer label `2`. At `j=128(N+2)^4(k+1)` it states `|(Q(T_N,j,c)−2E(c)Q(β_j))/M_j+2I_N(c)|≤E(c)/(k+1)`. This review inspects the statement but does not claim fresh leaf certification of that module. The origin/axis extension and explicit self-energy asymptotic remain separate open problems; the displayed source theorem does not close them.

| ID | Exact task | Classification and completion condition |
|---|---|---|
| AI-1 | Construct one shared budget for all strips, the pole and signed remainder on every odd compact profile. | **B-RH.** No duplicated surplus; all favorable gains retained. |
| AI-2 | Classify adverse sign-changing profiles and determine optimal nested-strip/chain allocation. | **B-C.** One-signed and edge-supported cases are already constrained; the general cross-nodal profile remains. |
| AI-3 | Prove usable integrated atom-versus-density bounds beyond the finite local classifications and optimize the large-radius light-cone band. | **B-C.** Pointwise lattice signs do not imply domination of a measure. |
| AI-4 | Extend the proved odd lattice full-energy calibration to the origin/axis packet and establish the requested explicit self-energy asymptotic and complete conductance matrix. | **B-C** for the axis/asymptotic extension; **J1** for certification of the existing odd capstone. `fullEnergy_latticeTrain_uniform` includes prime ratio/product interactions and regular archimedean/polar terms at explicit resolution `128(N+2)^4(k+1)`. Its lattice labels start at 2; it is not an origin-complete theorem. |
| AI-5 | Control normalized, compensated cross-window interactions and signed first-power prime charges; use the exact Hecke Cartesian-incidence law. | **B-C**, **B-RH** if strong enough for the global receiver. A raw polynomial cross-prime aggregate bound is refuted: its mean-field scale is exponential. The normalized comb/resolvent and inverse-square correction survive. |
| AI-6 | Turn the exact prime-minus-two-pole Chebyshev-defect pairing into a sign or critical-rate estimate. | **B-RH** at the complete target. The Abel identity itself is solved. |

**(a) Just work.** Apply the completed local classifiers, one-prime microstrip law, joint `2/3` certificate and exact allocation dictionary. A final audit of a completed candidate is J1; an unfinished normalization, axis extension or missing uniform error theorem must remain research/proof work until its argument is supplied. Walls 1.3, 1.6, 3.4.

### 5.7 Arithmetic Continuation and Critical Energy — exact continuation needs signed integrated work

**Aim and objects.** **ACCE** treats the actual centered Möbius source as a damping-dependent vector in pronic energy. It differentiates the energy, exposes its arithmetic tangent/dilation law, and seeks an estimate transporting an admitted damping to smaller dampings.

For fixed horizon, write `Eε(T)≥0` and `∂εEε(T)=2Wε(T)`. The exact relative loss is **signed**:

`Lε(T)=−2Wε(T)/(1+Eε(T)),    ∫_a^c Lε(T)dε=log(1+Ea(T))−log(1+Ec(T)).`

For admitted `c`, a horizon-uniform upper bound on this integral is equivalent to admission at `a`. Constants may depend on `a>0`. Cofinal admission as `a↓0` is RH-equivalent. [TheDampingAverageOfTheRelativeLossSuffices](../../../formal/GaloisForLFunctions/ArithmeticContinuationAndCriticalEnergy/TheDampingAverageOfTheRelativeLossSuffices.lean); [TheAveragedBudgetIsExactlyAdmission](../../../formal/GaloisForLFunctions/ArithmeticContinuationAndCriticalEnergy/TheAveragedBudgetIsExactlyAdmission.lean).

**What is established.**

- Scalar damping work is paid on compact positive damping intervals. Renormalized residuals, source energies and cutoff shells have exact comparisons; the extra physical cutoff costs nothing beyond admission. Horizon monotonicity also gives the precise sparse-horizon and averaged-horizon criteria.
- Tangent, autocorrelation, max-kernel, window-mean and dilation representations are exact. Their scalar neutrality does not automatically pay the two linear cross terms. The quotient-incidence kernel is indefinite, even though several diagonal Gram quantities are nonnegative.
- Dilation has sharp pronic scaling. The Dirichlet-form and Hardy results [S] identify a fixed-dilation block-energy formulation of admission. This is a useful coordinate change with two-sided control; no arithmetic cancellation follows from the change alone. [TheDilationDirichletFormOfTheWork](../../../formal/GaloisForLFunctions/ArithmeticContinuationAndCriticalEnergy/TheDilationDirichletFormOfTheWork.lean); [TheDilationHardyInequalityOnThePronicMeasure](../../../formal/GaloisForLFunctions/ArithmeticContinuationAndCriticalEnergy/TheDilationHardyInequalityOnThePronicMeasure.lean).
- Finite horizons have a free zero-damping limit, and the half-damping endpoint is admitted. Those facts do not make the two-parameter limit uniform. The residual has a linear small-damping cusp at some escaping horizons, ruling out a uniform `o(ε)` estimate.
- The self-improving inversion identity gives another viable target: upper bounds of the stated sublinear form on its two one-sided pairings can close energy admission. This is distinct from proving the derivative everywhere nonnegative. [TheSelfImprovingEnergyIdentity](../../../formal/GaloisForLFunctions/ArithmeticContinuationAndCriticalEnergy/TheSelfImprovingEnergyIdentity.lean).

**Targets requiring correction before they enter a research backlog.**

1. Replacing `Lε` by its **positive part** gives a stronger sufficient condition, not the proved equivalence. The strict distinction is witnessed by the admitted lacunary families in ACCC.
2. Global `Wε(T)≥0` is false: the BVI horizon-one limit gives `Wε(1)→−1/2` as `ε↓0` in ACCE's normalization. Thus universal core-dominance or dilation-Poincaré premises which imply that global sign are unusable as stated. This is formalized in [TheFirstCellCarriesAdverseWork](../../../formal/GaloisForLFunctions/ArithmeticCompensationTheory/TheFirstCellCarriesAdverseWork.lean).
3. The core's prime-harmonic `log log T` debt is proved for an integral **starting at damping zero**. On every fixed positive interval `[a,c]`, ACCC instead proves bounded core debt and its exact zeta-log-ratio limit. [TheCoreDebtIsThePrimeHarmonicSeries](../../../formal/GaloisForLFunctions/ArithmeticContinuationAndCriticalEnergy/TheCoreDebtIsThePrimeHarmonicSeries.lean).
4. Half-summable aperture losses would preserve a positive lower floor independent of aperture, contradicting the known ceiling tending to zero along unbounded apertures. The finite-product identity survives abstractly. For the actual source, a harmonic positive floor along linearly growing apertures is also impossible; any transported positive floor must respect the doubly exponential ceiling. [TheApertureFloorTransportFromTheCertifiedEndpoint](../../../formal/GaloisForLFunctions/ArithmeticContinuationAndCriticalEnergy/TheApertureFloorTransportFromTheCertifiedEndpoint.lean).
5. Abstract smooth spike families separate pointwise loss control from admission. They do not prove that a specific pointwise estimate cannot follow from RH for the literal Möbius source. Angle, convexity and single-sign-change conditions are sufficient routes with different hypotheses, not an established list of interchangeable equivalences.

| ID | Exact task | Classification and completion condition |
|---|---|---|
| CE-1 | Bound the signed relative-loss integral uniformly in horizon on intervals reaching cofinally small positive dampings. | **B-RH.** This is the exact continuation target. |
| CE-2 | Control actual tangent anti-alignment/covariance while retaining boundary flux, both linear terms, quadratic term and polar forcing. | **B-C** for a usable partial bound, **B-RH** at CE-1. Local negative work is allowed. |
| CE-3 | Establish the one-sided sublinear inversion-pairing estimates, or a genuine cross-sector contraction. | **B-RH** when they supply cofinal admission; particular ranges are **B-C**. |
| CE-4 | Develop source-specific convexity/no-interior-bump or single-sign-change estimates with a viable horizon/damping domain. | **B-C.** Necessity for the actual arithmetic source is not proved; generic countermodels require their scope. |
| CE-5 | Transport finite-aperture nonnegativity, or a positive floor with loss at least as fast as the proved doubly exponential ceiling permits. | **B-RH** at all-aperture nonnegativity. A uniform positive gap, and even a merely harmonic positive floor along linearly increasing apertures, are impossible. |
| CE-6 | Quantify signed observation stability and a positive-minus-negative spectral floor in a norm that transfers to the receiver. | **B-C.** A weighted floor is not automatically a mass-only floor. |

Concrete forms of CE-2/CE-3 include the level-sum/prime-pair cancellation at the explicit boundary's relative `1/T` precision, and a second compatible scale transition `F_(j+1)≤q_j F_j+r_j` with all cross terms paid. The compensated-floor target in CE-6 is `E_−(u)≤E_+(u)+Cσ e^(2σA)‖u‖₂²` for `σ>Δ` without a local depth-mass premise; it would complete a width dictionary, not prove that its common rate is zero.

**(a) Just work.** Use the exact continuation equivalence, scalar budgets, cutoff transport and block-energy dictionary. The `𝔽_q[T]` constant-prefix model is solved. General finite-curve receivers are controlled above their assumed spectral width; that conditional transport does not prove curve purity. Walls 1.8–1.9, 3.3–3.4.

### 5.8 Square Root Threshold — exact width dictionaries and the remaining normalization gap

**Aim and objects.** **SRT** determines what a prime-side lag, aperture, norm or sampling scheme measures about zero width. The central task is to obtain a source bound at a smaller rate, after the receiver and visibility laws are understood.

**What is established.**

- One generic continuous lag family decides RH; its exponential negativity rate reads the zero width. The continuous criterion does not require an attained top. Explicit near-top visibility laws quantify lag and depth; discrete grid theorems carry their actual attainment/tail hypotheses.
- The full/odd finite windows are as above. A named older odd-lag corollary still uses `0.353`; the stronger `0.362` odd-form theorem is available. Transferring it through the existing source/norm bridge is a specific corollary task, not a new positive-window conjecture.
- The aperture dictionary has **different arrow directions**: full positivity is equivalent to even and odd positivity together; odd positivity is equivalent to capacity; full positivity implies the even blind minimum; odd positivity implies the ACT Markov statement; nonnegative ground energy implies the relevant lag signs. These are not all equivalent readings at a single fixed aperture. [TheRoutesMeasureOneAperture](../../../formal/GaloisForLFunctions/SquareRootThreshold/TheRoutesMeasureOneAperture.lean).
- Width controls derivative-normalized and logarithmic Fourier-energy floors unconditionally. The sharp plain-mass converse is proved under a uniform off-line count bound, and under the weaker uniform local squared-depth-mass hypothesis. Unsigned sampling reads exactly that local depth-mass condition. The unrestricted signed `L²` converse remains open. [TheWidthIsTheGroundEnergyRateWhenOffLineZerosDoNotCluster](../../../formal/GaloisForLFunctions/SquareRootThreshold/TheWidthIsTheGroundEnergyRateWhenOffLineZerosDoNotCluster.lean); [UnsignedDepthSamplingDetectsLocalMass](../../../formal/GaloisForLFunctions/SquareRootThreshold/UnsignedDepthSamplingDetectsLocalMass.lean).
- Nyquist, sign-blind and height-average countermodels have sharp positive survivors in their stated classes. The unconditional lag bound still has rate `1/2`. A large lower bound on the height of a possible adverse cluster is not a height cutoff.
- Prime-height coupling retains Gamma and polar terms. Freezing those terms, discarding the beyond-horizon phase, or using a positive high-height archimedean range as an all-height argument loses the actual receiver. Conditioned rough-head decoupling in BAG does not make its deterministic tail small.

| ID | Exact task | Classification and completion condition |
|---|---|---|
| SR-1 | Prove the actual eventual lag sign or a subexponential lower floor. | **B-RH.** All required lags and source tails. |
| SR-2 | Complete a discrete grid's top/visibility/tail argument and quantify depth-height detection. | **B-C.** Continuous completeness is already proved. |
| SR-3 | Prove the unrestricted mass-floor/width converse or a precise signed replacement for local depth-mass control. | **B-C.** An exact dictionary at positive width would not itself prove width zero. |
| SR-4 | Obtain arithmetic control beyond the polynomial-length/height horizon, including the required pair-correlation range beyond `λ=1`. | **B-C**, **B-RH** at a closing estimate. An averaged family result is not an individual-source estimate. |
| SR-5 | Prove a source-dependent gain from joint prime-height/Gamma-phase coupling with the pole retained. | **B-C.** The open term must be specified on the complete expression. |

SR-2 includes the residual near-top alternative involving close twins and zeros beyond each finite horizon. SR-4/5 also include translating AIP's doubling/tripling/consecutive-power incidence into the actual lag-window charges. The BAG interface requires the conditioned rough tail itself to return; its mean-square decoupling from the head is already proved.

**(a) Just work.** Transfer the established odd-window constant through the existing lag theorem after checking its test norm (J7); instantiate visibility and weighted-floor theorems without changing their hypotheses (J2/J3). Walls 1.1, 1.3, 3.1–3.3.

### 5.9 Scale-Signed Incidence Criticality — classify a reading before assigning it a resolution limit

**Aim and objects.** **SSIC** formalizes a reading `r:D→O`, the fibre of objects sharing an observation, and the maximal width compatible with that fibre. It is a language for comparing information retained by methods, not a source estimate proving RH.

**What is established.**

- Refining a reading shrinks its compatible class and cannot worsen its resolution limit. The invariant is defined on an explicit domain of configurations or arithmetic rows; changing the domain changes the conclusion. General interval bounds on the invariant do not mean every intermediate value is attained. [TheResolutionLimitOfAReading](../../../formal/GaloisForLFunctions/ScaleSignedIncidenceCriticality/TheResolutionLimitOfAReading.lean).
- On the broad tempered-configuration class, a **true bounded-aperture positivity certificate** remains compatible with width `1/2`. A false certificate can refute positivity. The theorem does not say bounded data cannot disprove RH, or that every conceivable source argument at bounded aperture is forbidden. A cofinal unbounded-aperture positivity family does force width zero.
- Node-positive sets form the stated principal upward-closed class **under RH**; without RH the positive class may be empty. This is the incidence distinction between prime powers and generic node density.
- In the first Nyquist band of the specified lattice model, the exact tolerance threshold is `2L(cosh(δL)−1)` and the resolution is `min(1/2, acosh(1+η/(2L))/L)`. Its square-root approximation is a small-`δL` regime, not an unconditional global lower barrier. Two/three-band inversion distinguishes model depth from mass; those model formulas are not an actual-ζ reconstruction theorem. [ThreeBandsDefeatTheMass](../../../formal/GaloisForLFunctions/ScaleSignedIncidenceCriticality/ThreeBandsDefeatTheMass.lean).
- Periodic signed observations can retain more than magnitudes and still lose receiver information, as THIM's all-orders parity example shows. Conversely, exact signed physical recovery at fixed cutoff is now available through BiScale. Information recovery and energy control must therefore be separate entries in the ledger.

| ID | Exact task | Classification and completion condition |
|---|---|---|
| SI-1 | Define and analyze actual-ζ multi-aperture/finite-precision readings with realizable source certificates. | **B-C.** Model inversion alone does not supply arithmetic access or a tail bound. |
| SI-2 | Determine sharp resolution limits of the **specified** Gram/dispersion reading and its allowed coefficient class. | **B-C.** There is no justified universal “`θ=2` wall” before those choices; BVI's proved `1` and `6/5` thresholds use different units. |
| SI-3 | Classify parity/refinement mechanisms that retain enough signed pronic information for admission. | **B-C.** All translated periodic moments can still be insufficient. |
| SI-4 | Quantify the cost of upgrading local certificates to one complete shared ledger, including cross-prime and cross-scale terms. | **B-C**, **B-RH** when a complete source positivity criterion follows. |
| SI-5 | Classify sparse rate readings and price the extra local depth/mass information needed for a faithful ground-rate reading. | **B-C.** Cofinal invariance in a specified monotone/convex class is not automatically a theorem for oscillatory lag data; the weaker squared-depth hypothesis must be used instead of demanding an unnecessarily strong local count. |
| SI-6 | Determine how much hiding/dilution remains possible after the full arithmetic polar, trivial-zero and functional-equation constraints are imposed, and which aperture/precision policies are realizable at growing density. | **B-C.** A synthetic lattice and its first-band precision formula do not establish either arithmetic compatibility or a universal actual-ζ precision law. |

**(a) Just work.** Instantiate the existing reading/fibre definitions for an exactly specified map and apply an already proved refinement or model threshold. Proving a new fibre classification or transferring it to actual ζ is not mere terminology. Walls 3 and 14.3.

### 5.10 Arithmetic Compensation Theory — relative alignment is solved; absolute critical energy is not

The actual Möbius sector and its compensator admit a projection coefficient and a transverse residual. For each fixed `0<ε<1/2`, the squared coefficient mismatch and relative transverse energy decay faster than every logarithmic power. Along dyadic scales, coefficient motion and relative transverse energies are summable. These are proved alignment laws, not a strict contraction of the full receiver: the absolute upper bound still contains a power-scale factor `P^(1−2ε)`. It permits growth; it does not prove growth. [TheCompensationDefectDecaysFasterThanEveryLogPower](../../../formal/GaloisForLFunctions/ArithmeticCompensationTheory/TheCompensationDefectDecaysFasterThanEveryLogPower.lean); [TheCompensatingProjectionMovesSummablyAcrossScales](../../../formal/GaloisForLFunctions/ArithmeticCompensationTheory/TheCompensatingProjectionMovesSummablyAcrossScales.lean).

The integrated core debt on `0<η≤ε` has the exact horizon limit `log ζ(1+η)−log ζ(1+ε)` and is bounded there. Global nonnegative work is false: the first-cell work tends to `−1/2` as damping decreases to zero. An admitted smooth monotone-in-horizon model can have divergent positive-part relative loss on every nondegenerate interval; signed integrated loss is strictly weaker. [TheCoreDebtOnAPositiveIntervalIsAZetaLogRatio](../../../formal/GaloisForLFunctions/ArithmeticCompensationTheory/TheCoreDebtOnAPositiveIntervalIsAZetaLogRatio.lean); [TheFirstCellCarriesAdverseWork](../../../formal/GaloisForLFunctions/ArithmeticCompensationTheory/TheFirstCellCarriesAdverseWork.lean); [TheSignedBudgetIsStrictlyWeakerThanThePositivePart](../../../formal/GaloisForLFunctions/ArithmeticCompensationTheory/TheSignedBudgetIsStrictlyWeakerThanThePositivePart.lean).

A comparable adapted energy with bounded signed integrated loss is equivalent to admission. Its corrector must be constructed independently and remain comparable to `1+E`; setting an unrelated energy constant proves nothing. A fixed origin shift `k` costs exactly at most `(k+1)(k+2)/2`, sharply. Moving shifts are priced by the tail `E(T+k)−E(k)`; preservation for **every** admitted sequence holds iff the drift is bounded. [TheAdaptedEnergyIsExactlyAdmission](../../../formal/GaloisForLFunctions/ArithmeticCompensationTheory/TheAdaptedEnergyIsExactlyAdmission.lean); [AChangeOfOriginCostsAQuadraticConstant](../../../formal/GaloisForLFunctions/ArithmeticCompensationTheory/AChangeOfOriginCostsAQuadraticConstant.lean); [ADriftingOriginIsPricedByTheTailBeyondIt](../../../formal/GaloisForLFunctions/ArithmeticCompensationTheory/ADriftingOriginIsPricedByTheTailBeyondIt.lean).

The prime-comb normalization is also understood: fixed tests see an exponential resolvent; slowly varying tests see translation with first deficit `4∫|f′|²/r²`, while the prime error is `O(exp(−c√r))`. The complete prime-minus-polar residual has the PNT saving but retains exponential rate `1/2`. Neither a large raw cross-prime square nor a small relative error determines its adverse signed charge. [TheTranslationLawHasAnInverseSquareDeficit](../../../formal/GaloisForLFunctions/ArithmeticCompensationTheory/TheTranslationLawHasAnInverseSquareDeficit.lean); [ThePrimePolarResidualHasTheDeLaValleePoussinSaving](../../../formal/GaloisForLFunctions/ArithmeticCompensationTheory/ThePrimePolarResidualHasTheDeLaValleePoussinSaving.lean).

| ID | Exact remaining task | Classification |
|---|---|---|
| ACCC-1 | Upgrade relative projection control to an absolute signed bound in the actual receiver norm, with all scale interactions. | **B-C** in a restricted range; **B-RH** at cofinal admission. |
| ACCC-2 | Construct a comparable arithmetic corrector/adapted energy with horizon-uniform integrated loss for each required positive endpoint. | **B-RH** at cofinally small endpoints. |
| ACCC-3 | Exclude adverse moving-horizon profiles using the actual source's tail, not generic shift invariance. | **B-C**, **B-RH** if it pays the receiver. |
| ACCC-4 | Transfer positivity with the compulsory doubly exponential possible floor decay, or prove every-positive-rate negative floors directly. | **B-RH** at the all-aperture/zero-rate target; fixed positive and harmonic transported margins are refuted. |
| ACCC-5 | Improve the compensated prime–polar exponent through actual arithmetic; control balanced growing-modulus rows. | **B-C** at positive-width improvement; **B-RH** at critical rate. |

**(a) Just work.** Specialize the exact projection, positive-interval debt, finite-shift and normalized-comb identities; verify their explicit test regularity and constants. No further proof of “relative alignment exists” is required.

### 5.11 Signed Arithmetic Energy Incidence — nonlocal payment and topology

For symmetric finite incidence forms, local pairwise payment is universally complete precisely for balanced sign patterns, equivalently positive holonomy around every closed walk. A frustrated `k`-cycle is positive iff `2t cos(π/k)≤1`, while local payment requires `t≤1/2`. The sharp survivor is nonlocal payment along a half-sine path. General canonical paths can share aligned edges only through an explicit packing budget, and require a positive signed supersolution. The sampled odd archimedean–polar kernel is aligned; a frustrated odd-Weil cycle must use prime-sum edges. This locates arithmetic frustration without giving a negative full-Weil test. [CycleHolonomyDecidesBalance](../../../formal/GaloisForLFunctions/SignedArithmeticEnergyIncidence/CycleHolonomyDecidesBalance.lean); [FrustratedCyclesSpoilLocalPayment](../../../formal/GaloisForLFunctions/SignedArithmeticEnergyIncidence/FrustratedCyclesSpoilLocalPayment.lean); [FrustrationIsPaidAlongCanonicalPaths](../../../formal/GaloisForLFunctions/SignedArithmeticEnergyIncidence/FrustrationIsPaidAlongCanonicalPaths.lean); [TheOddWeilLedgerIsFrustratedOnlyByPrimes](../../../formal/GaloisForLFunctions/SignedArithmeticEnergyIncidence/TheOddWeilLedgerIsFrustratedOnlyByPrimes.lean).

On a fixed aperture the restricted Weil form is a positive form norm plus a compactly observed bounded perturbation. A bounded weakly convergent adverse sequence cannot disappear in the weak limit. The constants and compactness are aperture-dependent; this is not exclusion of adverse profiles as aperture grows. In a polynomial local model, on-line companions pay off-line derivative depth at the explicit Lagrange interpolation price; smooth sources inherit a Taylor-remainder version. Actual ζ still needs controlled companion placement and summed approximation errors. [TheRestrictedWeilFormIsCompactlyNegative](../../../formal/GaloisForLFunctions/SignedArithmeticEnergyIncidence/TheRestrictedWeilFormIsCompactlyNegative.lean); [OnLineCompanionsPayOffLineDepth](../../../formal/GaloisForLFunctions/SignedArithmeticEnergyIncidence/OnLineCompanionsPayOffLineDepth.lean); [SmoothSourcesPayAtTheTaylorPrice](../../../formal/GaloisForLFunctions/SignedArithmeticEnergyIncidence/SmoothSourcesPayAtTheTaylorPrice.lean).

For damping, residue modes have receiver norm squared between `(d−1)/d²` and `2/d`; backward stability fails in both `c₀` and receiver `ℓ²`. The sign-blind residue series converges exactly above damping `1/2`. The chain's **first column** is the actual receiver; a bound for the whole operator is stronger than required. Working source supplies an `ℓ²` chain bound for `1/√2<η<1`; its unresolved intermediate range concerns short-interval discrepancy at height `N/K` on lengths `N/K²`. This is not cofinal small-damping admission. [ResidueModesAndBackwardContinuation](../../../formal/GaloisForLFunctions/SignedArithmeticEnergyIncidence/ResidueModesAndBackwardContinuation.lean); [TheFirstColumnOfTheChainIsTheReceiver](../../../formal/GaloisForLFunctions/SignedArithmeticEnergyIncidence/TheFirstColumnOfTheChainIsTheReceiver.lean); [TheChainIsHilbertSchmidtAboveInverseRootTwo](../../../formal/GaloisForLFunctions/SignedArithmeticEnergyIncidence/TheChainIsHilbertSchmidtAboveInverseRootTwo.lean).

| ID | Exact remaining task | Classification |
|---|---|---|
| SAEI-1 | Construct supersolutions and packed nonlocal paths for the actual complete arithmetic incidence form, with continuum limit and pole/Gamma terms. | **B-C**, **B-RH** at full positivity. |
| SAEI-2 | Control adverse profiles uniformly as aperture increases; rule out their source-compatible escape or concentration. | **B-C**, **B-RH** if it proves nonnegativity everywhere. |
| SAEI-3 | Transfer the companion/interpolation estimate to actual ζ sampling, including heights, depth, multiplicities and summable Taylor tails. | **B-C**; a sharp signed floor alone need not force width zero. |
| SAEI-4 | Prove an actual-source first-column/pronic estimate below half damping, or stronger operator estimates where genuinely useful. | **B-RH** at cofinal zero damping; the `ℓ²` operator range above half is auxiliary **B-C**. |
| SAEI-5 | Identify the exact generator domain, graph core and quantitative projections required by a proposed transport, with the correct topology. | **B-C** unless a dependency-closed proof is supplied; eigenvectors and density alone do not settle it. |

**(a) Just work.** Check a supplied finite path certificate; instantiate proved cycle thresholds and polynomial companion formulas; integrate completed source proofs. Searching for an arithmetic supersolution is mathematical research.

### 5.12 ACS and signed gauges — arithmetic geometry must produce its own positivity

ACS contributes a new geometric receiver, not a new independent solution of the Weil sign. Its exact negative-index law and finite-degree filtration turn “Hodge defect” into a measurable arithmetic obstruction. Finite-curve calibration distinguishes three objects: a finite Frobenius span, its periodically repeated zero configuration, and the aperiodic ζ scaling surface. A finite index theorem in the first does not give finite index in the second or third.

| ID | Exact remaining task | Classification |
|---|---|---|
| ACS-1 | Construct arithmetic effectivity satisfying RR and the required ample/Bézout laws, independently of the desired Hodge index. | **B-RH** for the actual scaling surface. |
| ACS-2 | Identify coupled prime, pole and archimedean cycles whose intersection rules exclude the golden Beurling countermodel. | **B-C**; positivity/integrality/FE alone are insufficient. |
| ACS-3 | Give actual-source bounds for the aperture degree at which nonzero index would appear; distinguish count, depth and multiplicity. | **B-C**. Synthetic isolated-pair visibility is a calibration, not a ζ height cutoff. |
| SCG-1 | Use a sign-changing gauge to pay the full form for arbitrary profiles while conserving the exact autocorrelation charge. | **B-RH** at full positivity. Negative collars, one-signed half-line rigidity and edge-band cancellation are already solved inputs. |

**(a) Just work.** Specialize ghost, index, gauge and finite-curve transport identities; compute specified finite Gram data. General curve admission under an assumed spectral circle is not an unconditional proof of that circle.

### 5.13 How the programmes meet

| Interface | Already available | Exact missing transfer |
|---|---|---|
| APT → AIP/ACT/RW | Positive high-scale families, prime-kernel negativity, compact polynomial-window and lacunary estimates, complete tent language. | A complete-family positivity estimate with controlled norm and no unaccounted archimedean subsidy. |
| THIM/BVI → ACCE/PM | Exact signed rows, compensated drifts, defect signs, actual-row short-window improvements and damping calculus. | Horizon-uniform signed energy/continuation at fixed smaller damping, cofinally approaching zero. |
| AIP/ACT → RW/SZ/OWU | Exact allocation/variation receivers, local payments and completed RW/SZ sign transfer. | Global payment for arbitrary profiles and apertures. |
| BiScale/SRT → WL/MC/PM | Packet/band/lag/damping width dictionaries and visibility. | A new arithmetic bound reducing the admissible rate. |
| SRT/pincer → RW | Weighted floors, local-depth hypotheses and height lower bounds. | Unrestricted signed mass-floor converse; no height upper cutoff is supplied. |
| BVI `c₀` dynamics → critical energy | Compact semigroup, dense residue modes, strong continuity and unbounded residue generator. | An actual-source theorem in the pronic norm; first-column admission suffices, full operator control is stronger. |
| SSIC → all programmes | Scoped reading/refinement and model resolution laws. | A source mechanism adding the information or bound that a given receiver lacks. |

These interfaces explain why “the remaining problem is a sign” is too coarse. The unproved work concerns specific shared-resource inequalities, particular growing-modulus tails, exact norm transfers, observation costs, and source-faithful constructions. They are not interchangeable merely because several complete versions would imply RH.

### 5.14 Shared selectivity and calibration questions

All these programmes require a distinction between a universal identity and an estimate exploiting the literal arithmetic source. Current useful models include Beurling systems, shifted pairs `ζ(s−a)ζ(s+a)`, Liouville/parity twists and `𝔽_q[T]`. A proposed source estimate should be transported only where its definitions and hypotheses make sense; failure for one model is not a universal prerequisite imposed on every possible RH proof.

The open audit is theorem-specific: which APT positivity conclusions survive when the proved temperedness input fails; which ACT/AIP gauge and translation identities remain universal; which THIM/BVI conservation laws use integer incidence; and which sign-reading continuation estimates distinguish the actual Möbius row from a non-arithmetic twin. The known shifted-pair failure of an APT input is not a conclusion-level counterexample. The function-field constant-prefix calibration is not general curve purity.

For source construction, the corresponding question is what exposed data distinguish `Λ` from single-index perturbations, without mistaking uniqueness for existence of the full-positive weight. For SSIC it is the quantitative cost of adding such source information to a reading. These are **B-C calibration/classification tasks** until they supply a closing source estimate; applying an already established exact model identity is J3.


## 6. Evidence and verification limits

### Research coverage

The inventory was reconciled against all six authorized reports. Corpus research covered every live route and standalone candidate, their receiver statements and missing producer; the nine established programme task inventories; the additional ACCC, SAEI, ACS and signed-gauge interfaces; and the named no-go families. The review preserves **30 live routes, 18 standalone candidates, embedded PW-B, 44 named failed mechanisms and 19 retired aliases**. Failed mechanisms and aliases are registered with their positive survivors in the [walls ledger](walls-ledger.md#6-scoped-no-go-register-all-44-named-mechanisms), rather than counted as additional live routes.

There are **79 saved corpus-query records** and direct statement/hash records for **111 Lean files**, plus relevant proof-body/context reads. Searches used both natural-language mechanisms and exact names/module filters. This includes older receiver capstones and supporting proofs, not just recently edited files. The durable [research log](../../../logs/review-2310/research-log.txt), [source evidence](../../../logs/review-2310/source-evidence.jsonl) and [report audit](../../../logs/review-2310/report-audit.json) distinguish source observations from deductions. Source inspection is a targeted research audit, not a claim to have checked every theorem in the repository.

No other existing Markdown was read. A pending spectrum **Lean** file explicitly named by an authorized report was inspected directly; its accompanying paper card was not read. Secondary catalogue entries with only historical identifiers remain legacy evidence, explicitly marked in the wall register. No unlocated legacy claim is used as a new global impossibility theorem.

### Compiler and dependency evidence

A foreground `lake --old env lean` scratch audit imported nine key capstones and ran `#print axioms`. It completed successfully for:

- WL's prime-lag equivalence;
- RP's eventual full-history floor;
- FU's normalized divisor-Abel upper-bound equivalence;
- PA's positive-frequency criterion above `161/40`;
- MC's Hilbert-form subpower criterion;
- TT's directed-covariance criterion;
- ACS's actual-zeta Hodge-defect law;
- SAEI's sign-blind residue threshold;
- THIM's oscillating-prime half-damping classification.

All nine reported only `propext`, `Classical.choice` and `Quot.sound`. This checks the transitive dependencies of those **compiled declarations**; it does not certify later source edits or every linked file. The [audit input](../../../logs/review-2310/core-axiom-audit.lean) and [result record](../../../logs/review-2310/compiler-audit.txt) are retained.

A separate fresh foreground leaf check of `TheApertureFloorMustDecayDoublyExponentially.lean` completed with exit zero and no diagnostics. No `lake build`, umbrella compilation, new axiom, Lean-source edit or olean rebuild was used for this review. A current `.olean` and its freshness are metadata, not substitutes for checking theorem hypotheses.

The workspace contains concurrent research changes. Source hashes were recorded and changed inspected files re-read before finalization. The checkout observed at the final audit was `7f877d94dcf1f71082fd8d95ee17648701c651f4`, with substantial working-tree material; that hash alone is not the snapshot of uncommitted proofs. Labels [L]/[S] distinguish Lean-backed results and working-source material, while the evidence log carries the finer inspection/freshness record.

### Mathematical interpretation

The review distinguishes an exact identity, an equivalence to RH, a sufficient construction, a theorem conditional on a spectral bound, a synthetic counterexample, and an actual arithmetic estimate. Stronger claims are not inferred merely from docstrings or theorem names. In particular, the curve-model admission theorem assumes its spectral bound, the ACS effectivity classification does not construct effectivity, and no diagnostic at a divisor point is itself an arithmetic proof of line support.

International status is calibrated by [Clay's RH problem page](https://www.claymath.org/millennium/riemann-hypothesis/). Primary context includes [Báez–Duarte](https://arxiv.org/abs/math/0202141), [Suzuki](https://arxiv.org/abs/2206.03682), [Guth–Maynard](https://arxiv.org/abs/2405.20552) and [Rodgers–Tao](https://arxiv.org/abs/1801.05914). These support the recognized problem/method context; they do not establish worldwide novelty of each project-specific B-C task.
