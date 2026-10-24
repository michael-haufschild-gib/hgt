# Hard mathematical obstacles on every RH route

**Status at 2026-10-24.** 31 live routes, 17 standalone candidates, and PM's embedded PW-B candidate. No route has an unconditional, source-derived closing estimate. On most routes the remaining obstruction is localized to an exact equivalence, a finite-dimensional sector at each aperture, or a single missing arithmetic estimate; that closing input is missing on every route.

Companions: [summary and research programme](hard-obstacles-summary.md), [walls ledger](walls-ledger.md), [route unification](route-unification-ledger.md). Route names follow the [frontier map](../rh-current-frontier-map.md).

## 1. Scope, labels and evidence

The inventory comes from the six named reports. Mathematical status comes from corpus searches with `scripts/formal_tools.py research` and from reading the Lean statements they surfaced. No other Markdown file was opened; formalized pipeline cards and `formal/` READMEs were seen only as search-tool passages. Nothing was compiled for this review: "[L]" means an integrated declaration whose statement and hypotheses were read, not a fresh kernel audit.

| Label | Meaning |
|---|---|
| **[L]** | Integrated Lean declaration; statement and premises inspected. |
| **[S]** | Proof present in working or unintegrated source (untracked, unwired or blocked by a name clash). |
| **[P]** | Paper proof only. |
| **(a) Just work** | The method and all inputs exist: integration, formalization of a known proof, explicit regularity, a supplied finite certificate, or application of a proved dictionary. No unknown sign or estimate. |
| **(b) B-RH** | Open target proved sufficient for RH (often equivalent). RH is open, so no solution is known anywhere. |
| **(b) B-C** | Open auxiliary question without a known method. It may be weaker, stronger, or false; worldwide novelty is not claimed. |

Source codes: R = `RHTower`, B = `BiScaleUncertainty`, V = `BezoutValuationIncidence`, T = `TransHorizonIncidenceMechanics`, A = `arithmetic-positivity-theory`, C = `ArithmeticContinuationAndCriticalEnergy`, I = `ArithmeticIncidencePositivity`, Q = `ScaleSignedIncidenceCriticality`, S = `SquareRootThreshold`, G = `ArithmeticCriticalityTheory`, K = `ArithmeticCastelnuovoSeveri`, M = `ArithmeticCompensationTheory`, E = `SignedArithmeticEnergyIncidence`, O = `ArithmeticOrientationTheory`, P = `TransThresholdPairCorrelation`, D = `DilutionCrystallizationPincer`, H = `HTGeometry`; all under [`formal/GaloisForLFunctions/`](../../../formal/GaloisForLFunctions/).

## 2. Common mathematical boundaries

Write `Δ = sup_ρ |Re ρ − 1/2| = Θ − 1/2`; RH is `Δ = 0`.

1. **Every graded receiver reads the same width, and its first improvement is quasi-RH.** Spectral width, zero abscissa, Möbius and Liouville damping thresholds, the ξ half-plane bound and Suzuki formation energy are isomorphic objects of one receiver category; the width functor is full, faithful and isomorphism-reflecting (O:TheWidthFunctor, `zetaReceivers_widthVal_eq`). For every route whose graded receiver reads `Δ` (lag, packet, deficit primitive, ground floor, Sobolev allocation, damping, short window, JAS level-one budget), a bound at any fixed rate `σ < 1/2` is a fixed zero-free strip `Θ < 1`, i.e. quasi-RH. LI's reciprocal depth and HF's ceiling exponent `θ*` are the exceptions: they are different currencies. Every unconditional receiver estimate in the corpus sits at rate exactly `1/2` with de la Vallée Poussin or Vinogradov–Korobov savings: `e^{r−c√r}` (I:ReflectedPrimePolarAllocation), `e^{L/2−κL^a}`, `a<3/5` (B:PrimeWindowCeilingVinogradovKorobovRemainder), `exp(v/2−v^a)` (S:ZetaLagFamilyVinogradovKorobovEnvelope).
2. **Windows.** Full complex `C²` Weil form: margin `1/5000` through radius `3/10`, `1/1000` through `29/100` (G:ThreeTenthsSharpGaugeWeilPositivity, G:PastPlasticFoldWeilPositivity). Odd form: margin `1/1000` through `181/500`, transferred to the lag family (S:SharperOddWindowAndPhaseSelectiveSingleHeightLaw). Polar-free/primitive smooth tests: `1/1000` through `(log 2+1/50)/2`, `1/20` when both polar moments vanish (K:SourceDeterminantalSectionsAndArithmeticRiemannRoch). Joint 2/3 strip cost at `23/40` is not full positivity.
3. **All-aperture floors are rate 1/2.** `μ₀(A) ≥ −(10+68e^A)` and `≥ −[Cε+(4+ε)e^A]`; full real tests `W ≥ −(10+72e^r)∫F²` (S:PolarGroundEnergyAndPoleFreeLagAbscissaBridge, K:SourceDeterminantalSectionsAndArithmeticRiemannRoch). Graded allocation `(σ,C) = (1/2,75)` (I:SharedDerivativeEnergyAndGlobalAllocationSynthesis). Positive floors must decay doubly exponentially: `μ(A) ≤ K exp(11A/2 − πe^{2(A−2)})`, `A ≥ 3` (M:TheApertureFloorMustDecayDoublyExponentially).
4. **At each aperture the obstruction is finite-dimensional.** The Hodge defect of ζ is finite at every aperture, bounded by `⌊1 + 2·horizonFreq(a)(2a+2)/π⌋`, where `horizonFreq(a) = 4(e^{2E}−1)` with `E` exponential in `a` (K:TheHodgeDefectOfZetaIsFiniteAtEveryDegree, `hodgeDefectAt_zeta_lt_top`). Tests whose transforms vanish at the pole and on an explicit finite low-frequency grid have `Re W_ζ ≥ 0` (K:TheHodgeIndexOfZetaHoldsAwayFromLowFrequencies, `re_W_zeta_nonneg_of_lowGrid`), and the low-blind subsurface has RR, ampleness and Hodge index at every `a > 0` (K:SourceRiemannRochAwayFromTheLowFrequencyDivisor, `lowBlindTests_effectivity`). The dimension of the omitted sector grows doubly exponentially in `a`; no aperture-uniform payment of it is known.
5. **Mass floors and the width are tied exactly to clustering.** The compensated floor `E_−(u) ≤ E_+(u) + B‖u‖²` is equivalent to `μ(a) ≥ −B`; the uncompensated floor is equivalent to bounded local off-line depth mass; `∀σ>Δ` compensated floors hold iff the ground-energy rate equals `Δ`; unconditionally either that holds or local depth mass is unbounded (C:CompensatedWidthFloorAndGroundEnergyRate). A tempered model with ζ-type local counts and multiplicity `⌊log γ⌋` at fixed depth defeats every exponent (R:OffLineClusterWeilUnbounded). The DCI pincer shows a rate excess requires collapsed clusters at heights `180|T| > exp(e^{εA}/(40Δ²))` (D:MasterDCIPincerTheorem).
6. **Damping.** Every `ε > Δ` is admitted; cofinal admission at zero is RH. The centered chain is bounded on finite-support `ℓ²` uniformly for `1/2 ≤ η < 1`, Hilbert–Schmidt exactly for `η > 1/2`, and norm-continuous as `η ↓ 1/2` (E:TheChainIsBoundedAtHalfDamping, E:TheChainIsHilbertSchmidtAboveHalfDamping, E:TheChainIsNormContinuousAtHalfDamping). Admission is equivalent to an empty Bohr obstruction hull and to zero quotient rank of the repairing ideal; invertible critical-Wiener filters preserve both admitted and unadmitted classes (O:AnIndexFormulaForTheActualReceiver, O:UnitsOfTheWienerMonoidPreservePayment).
7. **Actual rows.** Fixed-modulus Möbius cancellation; centered-prime rows on `P^{1+δ} ≤ Q ≤ P^{30/17−δ}`; balanced `P ≤ Q ≤ BP` bilinear/dual-norm bounds with arbitrarily small leading coefficient but retained cubic/quartic tails (M:TheBalancedRegimeAndTheOmittedResidueClassLaw). Guth–Maynard large values are formalized unconditionally (R:Sieve/GuthMaynardTheoremOneOne), giving zero density `30/13` and primes in `(x, x+x^α]`, `α > 17/30`. Any fixed short-window power saving is equivalent to `Θ < 1`.
8. **Readings.** In the depth-lattice model classes, every orientation-faithful or depth-certifying reading crosses the Nyquist aperture, reads a magnitude, or adds mass/dilution/first-moment data; sub-Nyquist sign readings are invisible to every orientation flip (O:TheTrichotomyOfReadings). Finite-radius Weil readings see only `λ(n)` with `log n < 2R` and admit non-positive mimics (S:CertificateRadiusReadsAFinitePrimeWindow).
9. **Index, depth, multiplicity.** Weil negative index counts distinct right zeros; the Weil sum counts `m`; packet mean square counts `m²`; LI reads reciprocal depth `|β−1/2|/(γ²+(β−1/2)²)`, unconditionally `≤ 1/431`. None of these is `Δ`.

## 3. Live routes

### WL — Weil lag function

- **Receiver [L].** RH iff one explicit compact `C²` universal spline obeys `splinePrimeSum(τ) ≤ splinePolarMass(τ) + K e^τ` for every `τ > 4`; exponent `1+β` reads width `≤ β` (B:SplineProbeFiniteShiftBounds). Equivalent one-sided prime-lag, deficit-primitive, packet and linear-band criteria hold; the band slope bounds `Σ m_ρ²/|ρ|²`. The zero width is the infimum of admissible deficit and band exponents (S:TheZeroWidthIsALandauExponent).
- **Established [L].** Unconditional deficit envelope `|D(T)| ≤ Ce^{T−κT^a}`, `a < 3/5`; compensated prime residual `K exp(S/2 − c√S)`. Euler-comb filtering diagonalizes sequential payment; raw charge `≤` mass plus an unsigned cross-charge (I:LagChebyshevAbelSummation). Multiplicity readout: universal-probe defect tends to `Σ m(m−1)|f̂|²`; RH ∧ simplicity is a defect-vanishing statement (B:EffectiveTranslatedPairingAndMultiplicityDefect). Odd Chebyshev correction equals pole charge plus prime-node correlation (O:NyquistRiemannRochBeyondRankNullity).
- **(a) Just work.** Specialize the finite-shift spline receiver and transport identities to a given compact source with explicit constants (J7).
- **(b) B-RH.** A one-sided upper bound for the universal spline packet at every positive exponential slack, equivalently the critical deficit bound `±D(T) ≤ B(1+T)e^{(1/2+α)T}` for all `α > 0`. **B-C:** the first fixed rate below `1/2`, which is already quasi-RH; an arithmetic sign for the Euler-comb cross-charge.
- **Boundary.** Exact cancellation precedes estimation and leaves rate `1/2`. Littlewood oscillation excludes a pointwise `O(√x)` target, not the integrated receiver. Walls 1.1, 1.7.

### RW — Restricted Weil ground energy

- **Receiver [L].** `μ(A) ≥ 0` for all `A` is RH; so is `μ₀(A) ≥ −C_σ e^{2σA}` for every `σ > 0`, an eventual constant floor, or `μ → 0` from above. Aperture spectral jumps telescope; along a cofinal nested aperture sequence RH iff their sum exhausts the initial ground energy (O:TransportInApertureAndTheCeilingLyapunovIdentity).
- **Established [L].** Windows and all-aperture floors of §2. Fixed-aperture compactness (adverse mass cannot vanish weakly). H¹-normalized defect floors have infimal rate exactly `Δ` with no density premise (K:WhatTheFailureOfTheHodgeIndexMeasures); derivative-normalized and logarithmic Fourier floors are unconditional. Finite-aperture negative index is finite (§2.4). Relative aperture loss `R(A) = 1 − μ₀(A)/μ₀(A₀)` reads RH as `R ≤ 1` (Q:TheBandRecipeForZeta). Mass floor at rate `σ` is exactly the ground floor at rate `σ` (C:CompensatedWidthFloorAndGroundEnergyRate). Along any monotone unbounded aperture sequence starting at or below `3/10`, RH is equivalent to the spectral jumps summing to at most `μ(A₀)`; a fixed positive margin or half-summable relative loss is excluded by the ceiling, the ceiling-renormalized ground energy `e^{β_ceil(A)}μ(A)` is unconditionally `≤ K` on `A ≥ 3`, and its monotonicity along the sequence gives RH with an explicit doubly exponential floor; a discrete graded step inequality with bounded leakage and bounded aperture gaps gives the continuous compensated floor at rate `σ`, hence `Δ ≤ σ` (C:VanishingApertureFloorAndGradedTransport).
- **(a) Just work.** Discharge Fourier-integrability premises for a concrete compact source (J6); transport a supplied step estimate along an aperture sequence (J7).
- **(b) B-RH.** All-aperture nonnegativity, equivalently paying the finite low-frequency sector and its mixed terms uniformly in `a`. **B-C:** exclude collapsed off-line multiplicity clusters at doubly exponential heights (which is exactly what an unrestricted mass-rate equality needs); construct a source floor decaying at the compulsory doubly exponential rate.
- **Boundary.** A fixed positive gap, harmonic floor along linear apertures, or half-summable relative loss are impossible. Count-only zero data cannot give a mass floor (R:OffLineClusterWeilUnbounded). Walls 1.3, 1.11, 3.2, 3.3.

### FU — CCM-FU signed prime scheduling

- **Receiver [L].** A bounded-above completed Möbius–divisor Abel moment gives RH; one-sided power bounds give `Θ ≤ 1/2 + max(0,c)` (R:QuasiRHDilationTailHyperbolaAndOutgoingPotentialAbscissaLaw).
- **Established [L].** Positive helper cores, clock-cone closure, off-diagonal prime-clock synthesis of any fixed graph vector at vanishing diagonal cost; a resolvent eigenvector above `1/2` forces strictly negative off-diagonal interaction (B:PrimeGraphClockOffDiagonalSynthesisAndStationaryEnergyProducer). [S]: the off-diagonal sum is an exact weighted sum of prime-clock edge-minus-mass kernels at center `log(N/q)` and lag `log(q/p)`; it approximates the source energy of every graph vector, and its asymptotic nonnegativity is equivalent to nonnegativity of every source energy (B:ProducerCompletionAndPrimeClockKernelSynthesis). The isolated critical prime channel is uniformly negative on linear-width windows `N ≤ m+1 ≤ (1+δ)N` (A:TheLinearWindowOfTheCriticalPrimeChannel, `exists_linearWindow_criticalPrimeEnergy_le`).
- **(a) Just work.** Assemble finite-clock identities for a specified schedule (J7).
- **(b) B-RH.** Bound the completed Abel moment with seed energy, inherited action, inter-block covariance and moving endpoints. **B-C:** a sign for the off-diagonal prime-clock form on low-diagonal approximants (it would exclude eigenvalues above `1/2`).
- **Boundary.** Low diagonal cost is not graph compactness; packets can escape with energy tending to zero. Walls 1.1, 1.6, 14.1.

### RP — Route-P / SP-E history floor

- **Receiver [L].** Eventual linear lower floor of the literal matched-quantile history is RH-equivalent.
- **Established [L].** Signed hyperbola, centroid, square-debt and low-LCM payments; Burnol first-jet shells (trace `log(c)/4` while operators tend strongly to zero).
- **(a) Just work.** Fixed-history bookkeeping only (J7).
- **(b) B-RH.** One complete-history floor paying high-LCM interactions, centroid and square debt, moving-core drift and singular transport.
- **Boundary.** Strong convergence is not trace-norm convergence; compact repairs cannot sign noncompact Cayley tails. Walls 1.1, 1.8, 14.1.

### PA — Prime–archimedean source passivity

- **Receiver [L].** High-frequency current positivity, thin Bernstein mismatch envelopes, or the signed compact moment completion give RH.
- **Established [L].** Every fixed Hausdorff order, and every finite block of orders, is nonnegative beyond an order-dependent shift; quadratic saddle bands contribute half their absolute mass with positive sign uniformly for `r ≥ A(k+1)²` (R:PrimeArchQuadraticSaddleBands); an RH-or-tomography alternative recovers any finite maximal off-line packet.
- **(a) Just work.** Evaluate a specified finite list of moment differences (J8).
- **(b) B-RH.** An order-uniform shift threshold, or the sign of the complement of the saddle band. **B-C:** any quantitative order dependence of the threshold.
- **Boundary.** Positive saddle bands do not sign their complement; finite passive realizations and finite atom repairs fail. Walls 1.5, 1.6, 14.1.

### MC — Möbius cancellation at half power

- **Receiver [L].** `M(x) = O_ε(x^{1/2+ε})` and its Hilbert, Liouville, quotient-head and first-octave forms. Alternative exact form: RH iff for every `0 < ε < 1/2`, `t ≠ 0`, the long-sawtooth/tail quadratic anti-alignment gap satisfies `θ(ε,t) < 1` (T:OscillatingProbeSourceEstimatesEnergyGapAndCollarLimitations, `riemannHypothesis_iff_forall_ne_zero_longSawtoothTailGapTheta_lt_one`).
- **Established [L].** The strict gap holds unconditionally on the Vinogradov–Korobov high-height collar and on every bounded-height small-`ε` collar (`longSawtoothTailGapTheta_lt_one_vk_and_box`). Complete half-damped classifications: residue flips are paid iff `φ(q) < 4|S ∩ units|`; finite-frequency prime patterns; oscillating prime patterns below half damping are admitted only at amplitude zero. Off-line zeros give Bohr obstruction points of the damped receiver (O:TheOffLineZerosObstructTheMoebiusReceiver). Rows: §2.7.
- **(a) Just work.** Apply the row lemmas within their stated ranges (J7); formalize the all-length Heath-Brown pair-sum bound and the sharp all-`k` S₂ family behind Guth–Maynard Prop. 12.1 (J3).
- **(b) B-RH.** The global signed bilinear bound (principal counterterm and high-product remainder jointly), or `θ(ε,t) < 1` on the interior region between the proved collars. **B-C:** balanced-scale row cancellation with the cubic/quartic tails paid; a source-derived decorrelation or amplitude mismatch for the finite Euler–Maclaurin packet.
- **Boundary.** Generic Type-II countermodels concern coefficient classes; planted Euler factors keep every collar and still admit an interior probe; invertible Wiener filtering cannot create cancellation; any fixed power saving is quasi-RH. Walls 1.1, 1.12, 3.10.

### TT — Theta-tail and heat–Cassini currents

- **Receiver [L].** Bounded directed Wold covariance at every `0 < t < 1/2`, or full odd Weil positivity, is RH.
- **Established [L].** Seam/odd-four identities; theta inner-chamber current positive at action `≥ 710e⁴`; double-exponentially decaying even sources vanishing at all simple critical zeros vanish (K:WhatAGramFunctionalCertifiesWithoutEffectivity). Numerous theta-cusp micro-obstructions (kinetic concavity, fixed control boxes, ordinary absorbed coefficients) are proved and scoped.
- **(a) Just work.** Fixed chamber identities and supplied certificates (J8).
- **(b) B-RH.** Signed nonlocal covariance at all rapidities, or complete odd positivity.
- **Boundary.** Enlarging an inner chamber does not close the region; translation averages are depth-blind. Walls 1.6, 3.2.

### LA — Line anchor

- **Receiver [L].** All-height log-derivative/Laguerre/Jensen sign at the critical heat time; truncated heat constant `Λ₊ = 0` iff RH.
- **Established [L].** Heat zeros obey `(Im z)² ≤ max(Δ²−2t, 0)` (S:LagRateBoundsTheDeBruijnNewmanHeatTime). Normalized ξ slice tails converge to `exp(z²)` after deleting nearby zeros, with explicit tail bounds (R:XiSliceGaussianTailLimit); dense-background and global real-axis Gaussian bracketing (R:XiSliceDenseGaussianTail, R:XiSliceGaussianTailRealBounds). Fixed-degree Jensen limits.
- **(a) Just work.** Specified finite Jensen instances (J8).
- **(b) B-RH.** All-degree, all-height sign at one critical heat time, including near-multiple clusters. **B-C:** transfer from the Gaussian-tail approximation to coefficient signs with errors paid uniformly.
- **Boundary.** Fixed-degree asymptotics do not commute with the all-degree quantifier. Walls 1.2, 1.6, 1.11.

### TG — Topological sub-unit gate

- **Receiver [L].** Nonnegative matrix-complete residual plus integral trace strictly below one gives RH; central-gap alternative.
- **(a) Just work.** The integral-index deduction once both estimates are supplied.
- **(b) B-RH / B-C.** Construct the matrix-complete source decomposition, prove the residual sign and the all-disc sub-unit bound.
- **Boundary.** Integrality gives no upper bound; finite-scale diagnostics do not orient the prime−Gamma source. Walls 1.2, 14.3.

### HF — Positive Hodge form / prime-window ceiling

- **Receiver [L].** Full-positive weights are rigidly `Λ`; prime-blind positivity on prime powers is RH; the window ceiling `c(L) ≤ e^{L/2} + B(1+L)` implies RH and, directly, AIP's reflected prime–polar allocation (O:PoleSubtractionAndTheForcingSignDictionary, `reflectedPrimePolarAllocation_of_windowCeiling_le`).
- **Established [L].** `|c(L) − e^{L/2}| ≤ Ce^{L/2−κ√L}` and the VK version; Liouville mirror for the floor; `Δ ≤ θ* ≤ Δ/2 + 1/4`. Finite index at every aperture (§2.4). Prime-power deletion prices are exact. Prime-blind primitive tests satisfy `S/L > 45` (R:MarkovTwoCellTelescopingAndFortyFiveRatioPBAP). Unconditional smooth-window certificate: `N₀*(T,2T) ≥ (29/36 − ε)N(T,2T) − coalescentSurplus` (P:SmoothWeightedCertificateAtFourThirds, `zeta_coalescent_certificate`).
- **(a) Just work.** Instantiate collar partitions, transports and finite Gram data (J8).
- **(b) B-RH.** Positivity of the complete prime−polar pairing on the blind high-ratio sector, or the arithmetic `O(L)` ceiling remainder. **B-C:** a coalescent prime-pair surplus bound `≤ (1/18 + o(1))N` (it would give a `3/4` critical-line proportion, not RH); exact full-grid tower deletion extrema.
- **Boundary.** Uniqueness of `Λ` is not existence; finite index is not zero index; sampling rank–nullity and section counts cannot distinguish `Λ` from a shifted pair. Walls 1.4, 3.3, 14.4.

### CHMD — Causal Hyperbolic–Modular Duality

- **Receiver [L].** No odd resolvent eigenstate above `1/2`; equivalently `sourceEnergy(absGraph) ≥ 4·sourcePair(posGraph, negGraph)` for each odd eigenvector; odd bound-state space finite-dimensional iff finitely many off-line zeros.
- **Established [L].** At every fixed aperture the real smooth core completes with closed range into the signed quotient with a quotient lower bound, and the completion is exactly the maximal graph with physical support in the closed aperture (R:CHMDFixedApertureQuotientLanding, `exists_aperture_quotient_lower_bound`; R:CHMDSupportedApertureDomain, `mem_apertureGraphCompletion_iff_supported`). Positive/negative parts and modulus stay in the domain. Extensive nodal-lobe, Bessel and Riesz–resolvent identities. Sharp spatial cuts preserve the full graph uniformly in cut position (R:CHMDSharpSpatialCut). [S]: expanding windows recover the full signed cross-pairing, Weil energy and `oneL` defect (R:CHMDSharpWindowNodalConvergence). [P]: sharp-cut generator-domain admission with a bounded arithmetic commutator.
- **(a) Just work.** Transport theorems through the fixed-aperture completion (J7); wire the sharp-window module (J1); formalize the [P] generator-domain theorem (J4).
- **(b) B-RH.** The nodal/reflected-prime sign excluding sign-changing odd eigenstates above `1/2`, or a uniform one-sided bound for `∫ ∂_sK_y Δ`. **B-C:** aperture-uniform quotient constants.
- **Boundary.** One-signed eigenstates are excluded, sign-changing ones are not; any fixed uncorrected `θ` fails to absorb cosh mass; no uniform coercivity relative to the graph norm. Walls 1.3, 3.3, 3.4.

### TH — Theta moment positivity

- **Receiver [L].** All-rank heat-Hankel positivity at one heat time.
- **Established [L].** Positivity for every rank on the nonnegative orthant at small time; each fixed rank is eventually positive and coercive in scaled coefficients (R:XiHeatFiniteUniformPositivity). Bridge from Weil margins: `μ₀(A) > 0` and `K < A²/4` give heat-Hankel positivity for degree `≤ n` at all times `≤ K/n` on the pole hyperplane (R:XiGaussianHeatWindowFromWeilMargin).
- **(a) Just work.** Finite-rank matrices (J8).
- **(b) B-RH.** All ranks at one fixed time for arbitrary signed vectors. **B-C:** remove the rank–time coupling `a ≍ A²/n` in the Weil-margin bridge.
- **Boundary.** A later time per rank proves a different statement. Walls 1.6, 3.2, 3.11.

### RN — Theta renewal and singular comparison

- **Receiver [L].** Divisor-faithful boundary orientation; fixed Cauchy-pole quartet defect vanishes iff RH.
- **Established [L].** Compact Hilbert–Schmidt cone-positive renewal operator with `det₂` equal to the renewal denominator and matching resonance multiplicities.
- **(a) Just work.** Determinant/resonance specializations (J7).
- **(b) B-RH / B-C.** The boundary-current orientation or comparison sign confining resonances.
- **Boundary.** Cone positivity does not confine complex spectrum; the Stokes winding is not a zero-location law. Walls 1.2, 14.1.

### WD — Ward orientation and horizontal collision

- **Receiver [L].** The integrable nonnegative global cap vanishes a.e. iff RH (R:XiWardGlobalCapRightZeroSum).
- **Established [L].** Compensated ξ-tail bounds with explicit `A, B, C`; sharp model heat threshold `aλ ≥ 1/4`. Heated-slice detection: a zero at offset `δ ≥ δ₀` and height `t ≥ t₁` forces a negative heated slice coefficient at every heat `κ/log t` with `κ ≤ κ₀(δ₀) = δ₀²/(100(log(2/δ₀)+1))`, independent of local clustering (R:XiSliceKKLScaleOffLineDetection); unconditionally the even-index coefficients are positive once the heat is at least `100/log t` (R:XiSliceHeatEffectiveKKL).
- **(a) Just work.** Finite-block routing identities (J7).
- **(b) B-RH.** Arithmetic vanishing of the cap, or a complete signed prime−Gamma contraction uniform over all blocks. **B-C:** heated-slice positivity at heat `κ₀(δ₀)/log t` for one fixed `δ₀`; this is a zero-free strip, so it sits behind the quasi-RH entry barrier.
- **Boundary.** Building a nonnegative defect is not proving it zero. Walls 1.2, 3.4.

### LI — Li even-cross clock

- **Receiver [L].** All reciprocal depths `≤ r` iff a lower floor `−C e^{r′t}` for every `r′ > r`; RH at `r = 0`.
- **Established [L].** Unconditionally `b_ρ ≤ 1/431`; off-line zeros force cofinal negative response.
- **(a) Just work.** Supplied finite Li/Jensen data with certified tails (J8).
- **(b) B-RH.** The subexponential lower floor. **B-C:** any rate below `1/431` (a height-weighted improvement, not a strip).
- **Boundary.** Reciprocal depth is not `Δ`. Walls 1.5, 3.1.

### SZ — Suzuki screw and shifted-kernel limits

- **Receiver [L].** Screw positivity on the completed form domain is equivalent to restricted Weil positivity.
- **Established [L].** For every real compact `C²` source, `(C(0) − sourcePairing(f,ω))/ω → Re W_Λ(f,f)` as `ω ↓ 0`, retaining the Gamma atom, both polar branches and every prime-power cusp (R:Suzuki/SuzukiCriticalFirstVariation, R:Suzuki/SuzukiCriticalPolePairing). For every compact real `L²` source the full extended first variation is `J + γ₀‖f‖² − 2 fullPairing(C_f)` with every prime and polar term; only the nonnegative Lévy energy `J` can be infinite, and then the literal pairing is strictly below the mass [S] (R:Suzuki/SuzukiCriticalL2Pole, SuzukiCriticalL2Arithmetic, SuzukiCriticalL2WeilNormalization, SuzukiCriticalL2FirstVariation). [P]: a joint common-window Gamma-liminf with constant recovery, and the literal high-dyadic-family deficit without smoothing. Unconditional `≥ 2/3` simple critical zeros give cutoff uniqueness.
- **(a) Just work.** Wire the `L²` first-variation module (J1); formalize the two [P] results (J4).
- **(b) B-RH.** The sign of the complete first variation, which is the Weil sign; growing-support uniformity as `ω ↓ 0`.
- **Boundary.** SZ carries no sign obligation beyond RW's; its own remaining content is uniformity of the passage. Walls 1.3, 1.6.

### PM — Physical model: FZZ-P Haar approximation (PW-B in §4)

- **Receiver [L].** Global Haar approximation; cofinal admission `ε ↓ 0`; horizon-uniform signed relative-loss or Bézout-corrected loss budgets from `1/2` to cofinally small `a` (M:ConstructingAnArithmeticCorrector, `riemannHypothesis_iff_cofinal_bezoutCorrected_loss`).
- **Established [L].** Damping facts of §2.6. Corrected energy `= 1 + dual residual`, comparable within factor 3. At each fixed `0 < ε < 1/2`: relative compensation defects decay faster than every log power, dyadic motion is summable, energy `≤ D(1+T^{1−2ε})`, and either admission holds or normalized mass escapes beyond `E^{θ/(1−2ε)}` (M:TheNormalizedReceiverBlowUpProfile). Two-scale compensation rate `CTP^{−4β}`. Admission propagates multiplicities: `ord_ρ ζ ≤ ord_{ρ−ε} ζ`. Uniform VK-band budgets; actual and positive-parity twin separate there.
- **(a) Just work.** Literal energy, block and averaged-continuation translations (J7).
- **(b) B-RH.** A horizon-uniform signed energy or loss budget at arbitrarily small fixed `ε > 0` (constants may depend on `ε`). **B-C:** the actual tangent covariance with both linear terms, quadratic term and polar forcing; an arithmetic corrector independent of admission; exclusion of horizon escape.
- **Boundary.** Global `W ≥ 0` is false; positive-part loss is strictly stronger; absolute majorants fail at and below half damping; the chain is not Hilbert–Schmidt at `η ≤ 1/2`; residue modes are Bessel but not Riesz. Walls 1.8–1.10, 3.7.

### JAS — Joint ancestry

- **Receiver [L].** Level-one prime-product positivity at the power budget, or subpower square-shell Riesz bounds; quasi-RH iff level-one budget positivity with some `λ > 0` (R:JointAncestryBudgetZeroFreeLaw).
- **Established [L].** Positivity on large-prime sets with budget `((log y)/(128·10⁸))^{3/2}/(log log y)⁴` (R:JointAncestryEndpointBudgetProducer).
- **(a) Just work.** Finite shell identities and constants (J7).
- **(b) B-RH.** The `y^{1/2}` power budget. **B-C:** any power budget `y^λ`, which is already quasi-RH.
- **Boundary.** Typical-phase bounds do not control exceptional orbits. Walls 1.1, 1.6.

### CTF — Chronological tail / Báez–Duarte

- **Receiver [L].** Vanishing approximation distance; residual = readout defect² + centered pronic Gram; vanishing cofactor residual iff small variance at arbitrarily small `ε` and large cutoff.
- **Established [L].** Readout of `−μ_N` tends to `1`; residual floor `κ/log N`; rows keeping μ through `N/2` have Selberg diagonal `≥ 1/2359296`; a critical zero forces residual `≥ ε/(4|ρ|²)`.
- **(a) Just work.** Finite Gram problems (J8).
- **(b) B-RH.** Rows with both readout defect and centered energy tending to zero.
- **Boundary.** Readout convergence is not approximation; diagonal-only decay is impossible for literal-μ rows. Walls 1.8, 14.3.

### HCF — Gaussian heat trace / critical feature variance

- **Receiver [L].** Complete Hankel positivity on two literal prime-log source grids; RH iff `EventualFilteredCentralGapSubexponential ∧ AsymptoticAbscissaLaw`.
- **Established [L].** Seven-way heat capstone at fixed time; the RW→heat window bridge (see TH). **[P]:** a centered-heat detector giving a negative compact Weil witness for any off-line zero at aperture `≤ Cδ^{−2}(4+|γ|)^{38}`, without near-top or separation premises.
- **(a) Just work.** Formalize the [P] detector (J4); finite moments (J8).
- **(b) B-RH.** Both grid signs at all degrees on their polar hyperplanes.
- **Boundary.** One grid aliases; finite offsets sharing a step alias. Walls 1.6, 3.1.

### XN — Xi Newton invariant discs

- **Receiver [L].** Disc coverage with nonnegative interior margin; `ΔQ = 4(r² − |z−c|²)|ξ″|² ≥ 0`.
- **(a) Just work.** Check a supplied disc (J8).
- **(b) B-RH / B-C.** A source-derived disc family with interior margin; subharmonicity gives no minimum principle.
- **Boundary.** Walls 1.2, 1.6.

### BAG — Deterministic zeta self-return

- **Receiver [L].** RH iff ζ is strongly recurrent on every compact `K ⊂ {1/2 < Re s < 1}` (R:ZetaStrongRecurrenceOnCompactSets); every-point recurrence right of `1/2+σ` is the lag floor at rate `σ`.
- **Established [L].** Voronin universality on compact sets with connected complement; recurrence near `z₀` iff `ζ(z₀) ≠ 0`; return threshold equals the distance to nonvanishing targets, scaling with vanishing order; Haar-mass criterion for twisted heads; cofactor returns modulo the local divisor.
- **(a) Just work.** Apply local recurrence on known zero-free discs (J7).
- **(b) B-RH.** Recurrence near every point without assuming nonvanishing, i.e. uniform Haar mass of target-ζ head twists on every doubled-strip disc.
- **Boundary.** Locally the receiver is the nonvanishing statement itself; universality and cofactor return cannot cross a target zero. Walls 1.2, 3.2.

### EWU — Even pole-weight uniqueness

- **Receiver [L].** The even blind minimum is nonnegative at every aperture iff RH; below the first prime it equals the even polar ground energy.
- **Established [L].** Admixtures `tΛ + (1−t)λ₀` are full-positive only for `λ₀ = Λ`; shifted pairs leave the cone. High-scale, polynomial-window, lacunary and dense-window factorial families are positive; graded `L²`-RR coefficients obey the doubly exponential ceiling. Grid tents approximate every odd `C²` receiver; full-energy floors transfer with mass loss `78e^r`, or `(8+ε)e^r + C` (A:FromTheCriticalFamilyToTheReceiver).
- **(a) Just work.** Existing restricted families (J7).
- **(b) B-RH.** The blind-minimum sign at arbitrary aperture; complete low/mixed-mode control. **B-C:** a norm-controlled transfer from positive restricted families to an RH-complete cone.
- **Boundary.** Low/high bounds retain `−K_low E_low`; dense two-band positivity assumes high-energy dominance. Walls 1.3, 1.4, 3.3.

### GTA — Transverse Schur charge

- **Receiver [L].** Rank-uniform decay of quartic Schur charges is RH; an off-line zero forces an eventual positive charge floor.
- **(a) Just work.** Finite Schur identities (J8).
- **(b) B-RH.** Source-derived uniform transverse decay.
- **Boundary.** Strong truncation convergence is not norm decay. Walls 1.6, 14.1.

### OWU — Odd Weil-weight uniqueness

- **Receiver [L].** Odd positivity of `Λ` iff RH; odd positivity iff `sinhPairing² ≤ 2·markovEnergy`.
- **Established [L].** Odd window `181/500`; odd cost `≤ [(3+ε)e^r + Cε]E`; the certificate at `181/500` reads only `Λ(2)` (S:WindowCertificatesAndThePrimeWeight).
- **(a) Just work.** Closed odd/AIP dictionaries (J7).
- **(b) B-RH.** Arbitrary-aperture odd sign for sign-changing profiles.
- **Boundary.** No fixed uncorrected `θ` absorbs the cosh mass; finite negative index is not zero index. Walls 1.3, 3.4.

### PBM — Prime boundary / regularized log-ζ abscissa

- **Receiver [L].** Convergence of the pole-regularized prime or log-ζ series at every real `σ > 1/2`.
- **(a) Just work.** Match a regularization to the abscissa theorem (J7).
- **(b) B-RH.** That convergence; equivalently an admissible prime-gap exponent `≤ 1/2` with zero-freeness.
- **Boundary.** Regularization is not cancellation. Walls 1.1.

### RB — Robin/Nicolas

- **Receiver [L].** Eventual Robin inequality, reducible to colossally abundant integers.
- **Established [L].** Large counterexamples must be divisible by every integer `m ≤ η log log n` (B:RobinMovingValuationDefect).
- **(a) Just work.** Finite ranges (J8).
- **(b) B-RH.** The inequality along the prime-saturated extremal sequence at square-root remainder scale.
- **Boundary.** Walls 1.1.

### SRT — Prime-side one-parameter lag localization

- **Receiver [L].** One generic width; a single dyadic prime-window inequality per lag decides RH; pole-free variant; lag values determine the configuration.
- **Established [L].** Explicit visibility for near-top and attained-top zeros, twins and clusters; the horizon-escape law: positivity on `[0,V]` forces every hidden zero's deeper successor beyond the horizon. Ordinary floor `−O(exp(v/2 − v^a))`.
- **(a) Just work.** Instantiate visibility constants (J7).
- **(b) B-RH.** The arithmetic lag sign at every positive slack. **B-C:** horizon containment of deeper zeros; exclusion of escape to growing heights or tiny transform amplitude.
- **Boundary.** Grid receivers need `ZerosApproachLine`; bounded zero-count remainder is impossible. Walls 1.1, 1.11, 3.2.

### ACT — Arithmetic criticality / single-shift variation

- **Receiver [L].** For one fixed `a > 0`, `D_a ≤ 2S_a + V_a` on all even compact profiles is RH.
- **Established [L].** Short-profile and mean-zero windows through `(log 2+1/50)/2`; all-aperture mean-zero variation with mass loss `Cε + (4+ε)e^A`; exact integrated atom–pole laws for log-concave gauges; finite jump forms are positive iff a positive supersolution exists.
- **(a) Just work.** Specialize gauge identities and constants (J7).
- **(b) B-RH.** Zero-loss all-profile variation. **B-C:** a signed gauge with controlled middle region and ground remainder.
- **Boundary.** Positive gauges, two-shift superpositions and one extra jump all fail pointwise at an end. Walls 1.3, 3.3, 3.4.

### AIP — Arithmetic incidence positivity

- **Receiver [L].** All-aperture `GlobalIncidenceAllocation` iff RH; a constant or every-positive-rate mass deficit, or every-positive-rate pole-tilted Sobolev deficit, suffices; one rate `< 1/2` is a fixed zero-free strip (M:TheCompensatedRemainderOfTheFullLedger).
- **Established [L].** Local joint allocation through `181/500`; continuum single-tower reflection Cholesky `log p·mass + p-tower ≥ 0` for every prime (O:ContinuumTowerReflectionCholesky); integer-log lattice ledger is balanced; the off-lattice prime triangle has frustration index 2; signed Cheeger bound; two-tower joint capacity is strictly smaller than the sum iff the support misses a box point; archimedean bump self-energy asymptotic and fine-resolution positivity of every fixed lattice train (I:ArchimedeanBumpBridgeAndSelfEnergyAsymptotic, I:LatticeConductanceFixedWidthAndOriginAxisJets).
- **(a) Just work.** Apply local certificates and the allocation dictionary; verify supplied path certificates (J7, J8).
- **(b) B-RH.** One all-scale budget paying every reflected-prime cost and the pole without double spending. **B-C:** a source-calibrated continuum supersolution with packed paths; a quantitative cofinal two-tower saving.
- **Boundary.** Fixed-width signed strip-only payment is false; reserve production for unrestricted tests is unpaid; Gram positivity and finite canonical paths do not supply shared resources. Walls 1.3, 3.4.

### ACS — Arithmetic Castelnuovo–Severi effectivity

- **Receiver [L].** Hodge index on the scaling surface, RR+ample effectivity, every intersection Gram with one positive square, zero sector defects at every aperture, and zero H¹ defect-floor rate are all RH (O:TheWidthDictionary, `castelnuovoSeveriMetrologyAndWidthDictionary_tfae`).
- **Established [L].** Finite defect at every aperture; low-blind RR+ample+Hodge; local RR/Bézout through `181/500` (odd) and `3/10` (full); the RR correction is pole charge plus prime-node correlation; one generic orbit or two prime generators detect the full index; one-prime towers see every outer class when right-zero real parts are well-founded. Coalescent certificate and conditional `3/4` (shared with HF). [S] (K:LambdaRingEffectivityAndHeckeLefschetzRigidity): the exact arithmetic Lefschetz–adjunction identity `L(x,a) − ((a+1)/2)(x·x) = ((√a−1)²/2)·defect(x,x) + (√a/2)·defect(ψ^a x − x)`, the scaling-surface form of Weil's point-count decomposition; the cone of nef cycles obeying the Hasse–Weil bound `|L(x,a) − ((a+1)/2)x·x| ≤ √a·x·x` for all `a > 0` is Hecke- and Adams-stable, and RH ⇔ its RR ⇔ its equality with the positive cone; on curves the Rosati source cone has RR iff the datum is unitary, and the golden datum violates it.
- **(a) Just work.** Wire the λ-ring/Hecke–Lefschetz module (J1); compute finite Frobenius Grams and tower indices; specialize ghost, Adams and curve identities (J8).
- **(b) B-RH.** Arithmetic RR for source-defined cones at all apertures with ampleness, i.e. payment of the finite low-frequency sector and mixed terms uniformly in aperture; equivalently the arithmetic Hasse–Weil bound for Lefschetz numbers on the scaling surface. **B-C:** an independent arithmetic section-count or intersection law that forces this; well-foundedness or top attainment for ζ's right-zero real parts.
- **Boundary.** Product cones, nonpositive grades and fixed Hardy weights are excluded; sign-coded sections read the sign; section counts are identical for `Λ` and a shifted pair; compensated surfaces change the pairing; Hecke or Adams stability of a cone does not replace the missing inequality — RR on such a cone forces exactly the zero defect floor. Walls 14.4, 14.6.

## 4. Standalone route candidates and PW-B

Each candidate has an exact receiver or diagnostic; none has a pre-divisor producer. "Zero-indexed" means the object is built from the unknown Ξ divisor. On `XiDivisorSupport`, the HJ residual, SEC seam, CDC confluence, BSH mate gain, IRK noninvertibility and W1C Clifford energy are each equivalent to `Re ρ = 1/2`, with exact depth laws; the depth supremum is `Δ` (S:TheZeroIndexedRoutesMeasureOneSide). Their common missing input is source forcing.

| Candidate | Established [L] | (a) Just work | (b) Open |
|---|---|---|---|
| **APF** paired Fredholm | Fredholm index; cycle-trace Fourier reconstruction; `XiC(orientation)=0` iff all trace coefficients vanish. | Finite coefficients (J8). | **B-C:** zero-independent exhaustion forcing the coefficients to vanish. |
| **BSH** mate curvature | Framed curvature reads `n^{2Re s−1}`; Calderón–Witt Gamma–Green mate curvature vanishes iff `Re = 1/2`. | Fibre diagnostics (J7). | **B-C:** a prime−Gamma section built before the divisor and a mate identity coupling it to `Ξ(s)=0`. |
| **CDC** constitutive dagger | Calibrated confluence iff `Re s = 1/2`; individual defects vanish while total exchange work tends to `1/8`. | Finite accounting (J7). | **B-C:** one source potential descending on all closed error fibres. |
| **DR** dyadic Ξ roots | Zero-free cusp roots; finite marked monodromy images. | Known zero-free atlases (J7). | **B-RH:** global root compatibility on the strict-right domain. |
| **EGC** pole-safe contour | Inner mass-subtracted cancellation; complete correction has a Gamma floor `(m+1)·corr → −ε²/2`. | Inner contour theorem (J7). | **B-C/B-RH:** exterior expanding-contour covariance sign. |
| **EWJ** Euler/Wold jets | Finite-depth jets; compact-quotient character; transverse compression gaps. | Finite jets (J8). | **B-C:** zero-independent admission and norm exhaustion. |
| **FEL** theta likelihood | Exact KL and adaptive reveal accounting; unconditional BSY zero sum. | Finite histories (J7). | **B-C/B-RH:** cofinal source contrast balance. |
| **HJ** Hurwitz reflection | Prime-2 residual `2^{ρ−2} − 2^{−ρ̄−1}` vanishes iff `Re ρ = 1/2`; all-divisor vanishing equals HCF's two grid signs; a pre-divisor signed reservoir matrix exists and reverses under reflection (R:XiPreDivisorReflectionDefectStabilization). | Parity transports (J7). | **B-C:** the global stabilization (one bulk port weighted by `|ξ(s)|²`) that would force the residual; it is specified, not constructed. |
| **IRK** rotation-algebra trace | Completed Ξ-jet relation invertible off line, not on line; trace equals boundary winding. | Finite words (J8). | **B-C:** global arithmetic Poisson/projective lift with the original source defect. |
| **MSC** Möbius–Sonin | Unweighted critical logarithmic `L²` squarefree source; evaluation columns in `L²` on `Re s > 1/2`. | Column identities (J7). | **B-C:** source-faithful transport to nonnegative Sonin/Weil energy. |
| **PCS** singular co-shift | Explicit singular ground; shift/co-shift incompatible with invertible dilation. | Shift-plus-defect identities (J7). | **B-C:** wall-class annihilation preserving the forward mode. |
| **PTR** photonic source | Finite lossless stacks real-rooted; RH iff Ξ is a locally uniform limit (converse built from zeros); continuum Poisson port has unit Calkin gap. | Finite stacks (J8). | **B-C:** pre-divisor nonlocal prime-faithful port overcoming the unit gap. |
| **RFHM** support grade | Full-support/phase admission at unbounded Mellin grade; reversible sewing inverse-covariant. | Creation theorem (J7). | **B-C:** a source law breaking inverse covariance. |
| **SC** Stokes/Witt–Krein | Chamber-constant fibres; wall-singular polarization; rigged Krein wall-regular completion excluded. | Ghost transport (J7). | **B-C:** cross-fibre indefinite index surviving the wall. |
| **SEC** adjacent seam | Essential norm = seam charge; time-one Fock boundedness on the divisor iff RH. | Finite jets (J8). | **B-C:** exact compactness from a pre-divisor source. |
| **W1C** centered Lee–Yang | Centered ferromagnetic limit `Ξ/Ξ(0)` implies RH; prime-pivot walls form divisibility chains; prime-Ising subtree product law. | Finite graphs (J8). | **B-C:** arithmetic couplings with the centered critical limit. |
| **WBF** source certificates | Abstract genealogy Gram/determinant/completion theorems; no arithmetic content. | Instantiate once a stream exists (J7). | **B-C:** an arithmetic certificate stream with faithful Ξ/Weil landing. |

### PW-B — Hawking–BM cusp forcing (inside PM)

- **Established [L].** Weak retarded realization, two-response action identities and weighted native cusp energy admission at every positive damping; all constructions are indexed by `XiZeroCopy`. The Eisenstein value at `i` factors through `ζ(s)L(s,χ₋₄)`, so it does not isolate ζ.
- **(a) Just work.** Fixed-damping identities (J7).
- **(b) B-C.** A pre-divisor formulation, a complete-energy ceiling as damping vanishes, and the action-to-optical/all-divisor landing.

## 5. Supporting programmes: established frontier and remaining tasks

Programmes are overlapping tool sets, not further RH routes. Task IDs match the review-2310 numbering; "solved" entries stay listed so that they are not reopened.

### 5.1 Arithmetic Positivity Theory (APT)

Established [L]: limiting critical prime kernel negative definite on every finite pattern; fixed-support finite-scale negativity; negativity on linear-width windows `N ≤ m+1 ≤ (1+δ)N` with all harmonics and prime tails; complete-form positivity on high dyadic blocks, polynomial windows `[M, LM]`, `L ≤ M^δ`, eighth-power-separated lacunary unions and dense two-band families under high-energy dominance; ring majorant `log L + O(1)`; low/high Schur bound `A_high E_high − K_low E_low`. Working source: explicit kernel shape (minimum at `1/2`, couplings `I₀/(4π²k²) + O(k⁻⁴)`) and quantitative grid-tent transfer to every odd `C²` receiver.

| ID | Task | Status |
|---|---|---|
| APT-1 | Low scales and densely adjacent blocks without high-energy dominance. | **B-C**, open. |
| APT-2 | Growing-support range on which the actual prime channel stays negative. | Linear-width windows **solved** [L]; windows of growing relative width open (**B-C**). |
| APT-3 | Sharp cost of window width and nonlacunary unions. | Partial bounds; sharp law open (**B-C**). |
| APT-4 | Complete-family transfer with controlled norm loss. | Tents approximate every odd receiver [L], but positivity transfers only from positive sources; **B-RH** at all-test positivity. |
| APT-5 | Quantitative depth/height detection of grids. | **B-C**, open. |
| APT-6 | New admitted sources and source-faithful operator realization. | **B-C**, open. |
| APT-7 | Exact kernel extrema and shape. | Proved [S]; integration blocked by a duplicate public declaration (J2). |
| APT-8 | Single-height prime-phase saving beyond `log log T`. | **B-C**, open. |

### 5.2 BiScale Uncertainty

Established [L]: packet/band/spline receivers; multiplicity ceiling; prime-power node criticality and deletion prices; recovery stability `3(Σφ(q))ε^{1/6}`. Working source: cutoff-independent normalized stability `9ε^{1/3}`, stratum constants `3Σ_{q∈S}φ(q)`, linear dyadic-tower constant, windowed and single-window lag recovery with explicit cutoff cost (B:StratifiedObservationRecoveryAndBoundedRelationSynthesis).

| ID | Task | Status |
|---|---|---|
| BS-1 | Critical band `C(1+L)` / universal packet bound. | **B-RH**. |
| BS-2 | Raw band constant. | Solved under RH (B:CramerLimitLaw). |
| BS-3 | Two-tower and prime-power blind optima. | Enclosures only; **B-C**. |
| BS-4 | Sharper recovery constants, windowed observations. | **Solved** [L]. |
| BS-5 | Bounded completion cost for arithmetic observation families. | [S] (B:ProducerCompletionAndPrimeClockKernelSynthesis): on the pole-free hyperplane of the factorial–Müntz family the completed source has zero divisor mass and zero Weil energy, so the ramp part inherits the archimedean coercivity `((A/2) log M − C)·Σ‖d_n a_n‖²`; every far negative polar packet has a nonnegative coherent completion at bounded archimedean energy. Both are paid by the archimedean gain; completion for sources without it **B-C**. |
| BS-6 | Finite-prime certificate reaching the band receiver. | **B-RH**. |
| BS-7 | Test `E(U) = W(U)` from finite data. | **B-C**; equality also encodes simplicity. |

### 5.3 Trans-Horizon Incidence Mechanics (THIM)

Established [L]: global prefix-defect sign at large horizons; response-level damping commutation; complete half-damped classifications for constant-sign, residue-flip (`φ(q) < 4|S∩units|`), subgroup, finite-frequency and phase-shifted prime patterns; sub-half oscillating patterns admitted only at zero amplitude; logarithmic moments are a complete receiver invariant while all translated periodic moments are not; double-pole repair laws; Buchstab band signs through band 10 and nonconcavity of the cofinal profile. The conservation and dissipation laws split into three exact classes: Beurling-universal multiplicative laws, sign-blind parity-orbit laws, and `ℤ`-lattice laws driven by the Bézout relations `gcd(n,n+1) = 1`, `pa − qb = 1` (T:CompleteSignedTransHorizonEnergyAndTransferSelectivity). Class I holds on every Beurling system and class II cannot tell a row from its parity twin; only class III uses the additive successor structure of `ℤ` that Beurling systems lack. The paid class is a union of critical-Wiener-monoid orbits and reads pole orders through logarithmic pole moments.

| ID | Task | Status |
|---|---|---|
| THIM-1 | Signed pronic primitive energy at cofinally small damping. | **B-RH**. |
| THIM-2 | Signed moment hierarchy to a quantitative receiver bound. | Information side solved; quantitative bound **B-C**. |
| THIM-3 | Cross-lobe terms for arbitrary odd sources. | **B-RH** at full odd positivity. |
| THIM-4 | Low-horizon/Buchstab/concavity classification. | Largely solved; all-band asymptotics **B-C**. |
| THIM-5 | Schedule and parity-transformation classification. | Largely solved (p-adic injectivity iff every slot observed); general parity **B-C**. |
| THIM-6 | Endpoint laws for other kernels. | Extended to sub-half partial-pole and double-pole laws; general sources **B-C**. |
| THIM-7 | Remaining multiplicative spectra. | Half-damped classification complete for the stated classes; sub-half general patterns **B-C**. |
| THIM-8 | Index formula for the paid class. | Orbit and pole-moment structure proved; a non-perturbative formula computing the class of the Möbius weight from arithmetic counts **B-C**. |

### 5.4 Bézout–Valuation Incidence (BVI)

Established [L]: energy = compensated interior bracket `+ O_ε(1)`; strict contraction iff bounded energy; fixed-modulus cancellation; centered-prime `30/17` range; balanced bounds with arbitrarily small leading coefficient; VK band; no universal `O(N)` observation horizon, while `Φ(N)` samples always recover; sandwich constant of order `N²`; radical-state normal form reduces a global defect bound to finitely many tests per horizon.

| ID | Task | Status |
|---|---|---|
| BV-1 | Compensated interior contraction at cofinal damping. | **B-RH**. |
| BV-2 | Growing-modulus dual norm with all tails. | Balanced leading term solved; tails **B-C**. |
| BV-3 | Dual rows with vanishing readout defect and energy. | **B-RH**. |
| BV-4 | Chain structure to signed pronic estimate. | Solved for `η ≥ 1/2`; below half **B-RH** at cofinal damping. |
| BV-5 | Sharp observation horizon and conditioning. | Superlinearity proved; sharp order **B-C**. |
| BV-6 | General signed prime packet and complementary lags. | **B-C**. |

### 5.5 Arithmetic Criticality Theory (ACT programme)

| ID | Task | Status |
|---|---|---|
| AC-1 | Fixed-shift variation for every profile. | **B-RH**. |
| AC-2 | Signed gauge with global nodal-remainder control. | Conditional endpoint signs only; **B-C**. |
| AC-3 | Coercivity after removing the radical. | Uniform coercivity against the original graph norm is false even on compact primitive tests; a quotient-norm law remains **B-C**. |
| AC-4 | Larger full/even windows. | Margins through `29/100` (full), mean-zero through `(log 2+1/50)/2`; larger radii **B-C**. |
| AC-5 | Averaged versus pointwise shift law. | Averaged inequality only under RH; **B-C**. |
| AC-6 | Ground crossing excluded by a decaying floor. | **B-RH**. |
| AC-7 | Capacity-ratio rates and Harnack propagation. | Ratio tends to 1 on plateau truncations; **B-C**. |
| AC-8 | From the frustration count to the ground energy at aperture `A`. | The ground energy is bounded above by the frustration mass; a lower bound from the count (samples reach twice `π(⅔e^{2A})`) **B-C**. |

### 5.6 Arithmetic Incidence Positivity (AIP programme)

| ID | Task | Status |
|---|---|---|
| AI-1 | One shared all-scale budget. | **B-RH**. |
| AI-2 | Adverse sign-changing profiles; optimal nested allocation. | Lattice balance, prime-triangle index 2, edge-tent obstruction proved; general **B-C**. |
| AI-3 | Integrated atom-versus-density bounds. | Log-concave gauge law solved; general weighted **B-C**. |
| AI-4 | Axis/self-energy extension of the odd lattice calibration. | **Solved** [L]. |
| AI-5 | Normalized cross-window interactions. | Inter-window bounds proved; summable all-scale allocation **B-C**. |
| AI-6 | Sign of the prime-minus-two-pole Chebyshev pairing. | Spectral form exact; sign **B-RH**. |

### 5.7 Arithmetic Continuation and Critical Energy (ACCE)

| ID | Task | Status |
|---|---|---|
| CE-1 | Signed relative-loss integral at cofinal damping. | **B-RH**. |
| CE-2 | Actual tangent covariance with all terms. | **B-C**. |
| CE-3 | One-sided inversion-pairing estimates. | Exact single-damping equivalence proved; estimate **B-C**/**B-RH**. |
| CE-4 | Convexity / no interior bump. | **B-C**. |
| CE-5 | Transported floor with compulsory decay. | Transport framework solved [L] (C:VanishingApertureFloorAndGradedTransport): ceiling-compatible relative and additive steps, ceiling-renormalized monotone functional, graded negative-floor transport to `Δ ≤ σ`. The step estimate itself is **B-RH**; its graded form at a rate below `1/2` is quasi-RH. |
| CE-6 | Compensated mass floor. | **Resolved** [L]: equivalent to the ground floor; rate equality iff no depth clustering. |

### 5.8 Square Root Threshold, SSIC and the DCI pincer

| ID | Task | Status |
|---|---|---|
| SR-1 | Actual lag sign / subexponential floor. | **B-RH**. |
| SR-2 | Discrete grid top/visibility/tail. | Requires `ZerosApproachLine`; **B-C**. |
| SR-3 | Unrestricted mass-floor converse. | **Resolved to a sharp dichotomy** (§2.5); remaining arithmetic input is the cluster exclusion of Wall 1.11. |
| SR-4 | Control beyond polynomial length/height. | **B-C**. |
| SR-5 | Prime-height/Gamma coupling gain. | Kronecker peaks force negativity or exponential height escape; **B-C**. |
| SI-1–SI-6 | Resolution limits of readings; parity collapses; rate readings; hiding after full constraints; growing-density policies; numerical ledger unit. | The programme's seven listed problems are resolved [L]: sign-blind Type-II and rank-two readout Gram readings have resolution limit exactly `θ = 2` (they certify nothing below the balanced scale; Q:TheExactFloorOfThePronicGramReading); band recipe, fatality classification of parity collapses, rate reading, counterexample design, growing-density policies and the incidence-ledger unit (Q-modules of the same names). Reading trichotomy (O:TheTrichotomyOfReadings). Remaining: readings of the actual ζ source that add the missing arithmetic information (**B-C**). |
| DCI | Remaining obstruction after the pincer. | Collapsed clusters at doubly exponential height (Wall 1.11); **B-C**. |

### 5.9 Arithmetic Compensation Theory (ACCC)

| ID | Task | Status |
|---|---|---|
| ACCC-1 | Relative to absolute signed control. | **B-C**/**B-RH**. |
| ACCC-2 | Comparable arithmetic corrector. | Bézout corrector constructed (`1 + dual residual`, factor 3); its loss budget is the RH receiver (**B-RH**). |
| ACCC-3 | Adverse moving-horizon profiles. | Sharpened to admission-or-escape; exclusion **B-C**. |
| ACCC-4 | Transfer with doubly exponential decay. | **B-RH**. |
| ACCC-5 | Compensated prime–polar exponent; balanced rows. | Balanced leading term solved; exponent improvement is quasi-RH (**B-C**). |

### 5.10 Signed Arithmetic Energy Incidence (SAEI) and Arithmetic Orientation Theory (AOT)

SAEI established [L]: holonomy criterion; frustrated-cycle threshold `2t cos(π/k) ≤ 1`; packed-path certificates for three/four-node arithmetic models; Kron reduction and aligned-overlap monotonicity; sharp Paley–Wiener companion price `A³h/(3π)` iff `Ah ≤ π`; chain bounds of §2.6. AOT established [L]: width functor; trichotomy of readings; aperture transport; Wiener algebra (units iff no Bohr-polydisk zero, local factor `δ₁ − aδ_p` a unit iff `|a| < √p`); repairing-ideal codimension counts obstruction points; frustration index (lattice ledger balanced, prime triangle `ν = 2`, dense replicas give index `≥ 2M` without a negative continuum form); continuum single-tower Cholesky.

| ID | Task | Status |
|---|---|---|
| SAEI-1 | Continuum supersolution and packed paths with pole/Gamma terms. | **B-C**, **B-RH** at full positivity. |
| SAEI-2 | Adverse profiles uniformly in aperture. | **B-C**. |
| SAEI-3 | Companion interpolation for actual ζ. | Model prices sharp; actual companion supply **B-C**. |
| SAEI-4 | Sub-half first-column estimate. | **B-RH**. |
| SAEI-5 | Generator domain and projections. | No Riesz basis (Bessel only); remaining need **B-C**. |
| SAEI-6 | Joint capacity of multi-tower profiles. | Exact on the smooth-number simplex with equal weights; strictly below the sum of single capacities on every non-box support; exact value with the actual unequal weights **B-C**. |
| AOT-1 | Joint all-prime tower budget (single towers are paid). | **B-RH** at full allocation. |
| AOT-2 | A repair leaving the Wiener unit class for actual μ below `Δ`. | **B-C**; nonempty-hull classification at or below `Δ` open. |

### 5.11 ACS internals and Trans-Threshold Pair Correlation (TTPC)

| ID | Task | Status |
|---|---|---|
| ACS-1 | RR-compatible arithmetic effectivity at all apertures. | **B-RH**; equivalently the arithmetic Hasse–Weil bound on Lefschetz numbers [S]. |
| ACS-OP5 | Effectivity from the λ-ring. | **Resolved negatively** [S]: Hecke/Adams stability forces the zero defect floor instead of producing it. |
| ACS-2 | Coupled data excluding the golden Beurling datum. | Purity ⇔ bounded traces ⇔ Hasse–Weil remainder in curve models; arithmetic forcing law **B-C**. |
| ACS-3 | Source bound for the detection aperture. | Quantitative detection under isolation/margin premises; unconditional **B-C**. |
| SCG-1 | Sign-changing gauge paying the full form. | **B-RH**. |
| TTPC-1 | Coalescent prime-pair surplus `≤ (1/18 + o(1))N`. | **B-C** (gives a `3/4` proportion, not RH). |
| TTPC-2 | Remaining five end-form terms and coherent weighted error. | **B-C**. |

## 6. Evidence and verification limits

**Coverage.** The six named reports supplied the inventory (31 live routes, 17 candidates, PW-B, 44 named failed mechanisms, 19 retired labels). The frontier map was read twice: at checkpoint `8f6c98f1a` and again after a concurrent rewrite at checkpoint `e108313a9`. The killed-routes catalogue was read in its header, mechanism and endpoint sections, and through its full change set since the previous review's checkpoint `7f877d94d`. Corpus research used 118 saved search queries, one or more per route, candidate, programme and wall face, plus exact-name lookups for every declaration cited here; the saved results, digests and the working log are in [`logs/review-2410/`](../../../logs/review-2410/). Lean files added between the two review checkpoints (269 committed, plus later additions) are listed in [`new-lean-files.txt`](../../../logs/review-2410/new-lean-files.txt); their module documentation and key statements were read, together with older capstones surfaced by the searches.

**Statements read directly.** Among others: `exists_aperture_quotient_lower_bound`, `mem_apertureGraphCompletion_iff_supported`, `exists_linearWindow_criticalPrimeEnergy_le`, `eventually_fullEnergy_latticeTrain_nonneg`, `tendsto_calibratedSignedJumpEnergy_latticeBumpProfile_netAtom`, `hodgeDefectAt_zeta_lt_top`, `horizonFreq`, `re_W_zeta_nonneg_of_lowGrid`, `lowBlindTests_effectivity`, `exists_centeredOperator_l2_le_uniform`, `guthMaynardLargeValuesBound_holds`, `riemannHypothesis_iff_forall_ne_zero_longSawtoothTailGapTheta_lt_one`, `longSawtoothTailGapTheta_lt_one_vk_and_box`, `zeta_coalescent_certificate`, `continuumTower_reflection_cholesky`, `gradedIncidenceAllocation_half_seventyFive`, `riemannHypothesis_iff_cofinal_bezoutCorrected_loss`, `moebius_reverse_inclusion_and_index_tfae`, `castelnuovoSeveriMetrologyAndWidthDictionary_tfae`, `eventually_re_heatHankel_pos_of_polarGroundEnergy`, `exists_halfPlane_lt_half_iff_exists_jasBudgetProductPositive`, `lefschetzEnvelopeCone_riemannRoch_tfae`, `lefschetzEnvelopeCone`, the theorem list and documentation of `CompensatedWidthFloorAndGroundEnergyRate`, `OffLineClusterWeilUnbounded`, `XiPreDivisorReflectionDefectStabilization`, `TheTrichotomyOfReadings`, `TransportInApertureAndTheCeilingLyapunovIdentity`, `TheWidthFunctor`, and the new Suzuki `L²`, CHMD sharp-cut, Gaussian-tail and λ-ring modules. A text scan of every listed new file and of the later additions finds no `sorry`, `admit`, `axiom` declaration or `native_decide`.

**Compilation.** None. No build, leaf check or axiom audit was run for this review, so integration status is reported from the source tree: "[L]" means integrated and inspected, not freshly kernel-checked. Some integrated modules (for example `ArithmeticDampingCenteredSpectrum`, `TheLinearWindowOfTheCriticalPrimeChannel`) currently have no olean in the build directory.

**Concurrency.** Other agents committed and edited during the review (commits `e108313a9` and `37fa6a3db`, a frontier-map rewrite, edits to the λ-ring, Suzuki `L²`, CHMD and grid-tent modules). Wiring status is reported as of `37fa6a3db`; statements are reported as read, and later edits may change details.

**Interpretation.** A receiver or equivalence does not supply its input; a model counterexample excludes only its class; a conditional theorem keeps its premise. RH's status follows the [Clay problem statement](https://www.claymath.org/millennium/riemann-hypothesis/). B-C items are open in the corpus; worldwide novelty is not claimed.
