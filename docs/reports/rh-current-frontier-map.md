# RH proof-route frontier

**Status:** RH open. **31 live routes; 17 standalone candidates; PW-B candidate sub-branch.** BVI is supporting infrastructure, not a route.

**Corpus checkpoint:** `1da80a29b330873d6d868ad4b2997e7ca59180df`. Checkpoint covers committed changes; working-source additions retain [S] unless integrated.

**Evidence:** [L] integrated Lean source, not a fresh kernel audit; [S] unintegrated/working/unfinished source, not certified closure; [P] paper only. Conditional statements retain their premises; unfinished proofs are explicit. A proved RH receiver does not establish its arithmetic input.

**Classification:** Live = source-defined observable + proved RH-sufficient receiver + explicit open estimate. Candidate = incomplete independent source mechanism or source-to-RH landing; a zero-indexed RH equivalence alone is insufficient. Supporting framework = tools feeding routes. A killed mechanism need not kill its parent route.

## Find a route

| Family | Live routes | Route candidates | Supporting frameworks |
|---|---|---|---|
| Arithmetic incidence / crossing | [AIP](#aip) | — | — |
| Prime explicit formula / signed energy | [WL](#wl), [RW](#rw), [FU](#fu), [RP](#rp), [PA](#pa), [LI](#li), [JAS](#jas), [CTF](#ctf), [EWU](#ewu), [OWU](#owu), [PBM](#pbm), [RB](#rb), [ACT](#act) | [APF](#apf), [EGC](#egc), [EWJ](#ewj), [FEL](#fel) | [BVI](#bvi) → CTF |
| Möbius cancellation | [MC](#mc) | [MSC](#msc) | [BVI](#bvi), [SignedSuccessorArithmetic](#ssa), [ADR](#adr) |
| Theta sign / heat / moments | [TT](#tt), [LA](#la), [TH](#th), [HCF](#hcf) | [HJ](#hj) | [ALDG](#aldg) → LA |
| Zero visibility / localization | [SRT](#srt) | — | [AOG](#aog) |
| Causal hyperbolic–modular duality | [CHMD](#chmd) | — | — |
| Geometry / index / arithmetic rigidity | [TG](#tg), [HF](#hf), [GTA](#gta), [ACS](#acs) | [DR](#dr), [IRK](#irk) | [AOG](#aog) → ACS, HF |
| Newton dynamics | [XN](#xn) | — | — |
| Renewal / singular comparison | [RN](#rn) | — | — |
| Ward / collision | [WD](#wd) | — | [ALDG](#aldg) |
| Suzuki / boundary limits | [SZ](#sz) | [SEC](#sec) | — |
| Physical realization | [PM](#pm) (FZZ-P) | [PTR](#ptr), [W1C](#w1c), [PW-B](#pw-b) | [BVI](#bvi), [ADR](#adr), [SignedSuccessorArithmetic](#ssa) |
| Singular source completion | — | [BSH](#bsh), [CDC](#cdc), [PCS](#pcs), [RFHM](#rfhm), [SC](#sc), [WBF](#wbf) | — |
| Deterministic zeta recurrence | [BAG](#bag) | — | — |

[Dead mechanisms](rh-killed-routes.md) · [Shared frontier](#shared-frontier) · [Supporting frameworks](#supporting-research-frameworks)


## Shared frontier

| Question | Established [L] | Open boundary |
|---|---|---|
| Full signed positivity | Full Weil floor ≥`‖f‖₂²/5000` through radius `3/10`; odd floor ≥`‖f‖₂²/1000` through `181/500`; smooth primitive floor ≥`‖f‖₂²/1000` through `(log2+1/50)/2`. | All apertures. The overlapping-prime strip estimate at `23/40` leaves the pole unpaid; it is not full positivity. |
| Graded floors | Odd allocation deficit `75e^r‖f‖₂²`; full/even/odd Sobolev floor `−Ce^(r−κr^α)(‖f‖₂²+‖f′‖₂²)`, every `0<α<3/5`, without moment restrictions. | Source-derived aperture-uniform H¹ floor, or every positive exponential rate. Current leading rate remains `1/2`. |
| Ground energy / RR | Small-aperture positive floors; Gaussian upper ceiling; exact aperture-jump and relative-step RH criteria; bounded-gap graded-floor transfer. Restricted low-grid-blind RR+ampleness. | Actual source step/leakage bound, not transport algebra. No uniform positive gap at unbounded aperture; vanishing floors survive conditionally. |
| Completed domains | RW/SZ sign transfer; CHMD supported maximal graph = completed real aperture core, including boundary support and nodal truncations. SZ common shifts under bounded envelopes. | Actual source sign. No aperture-uniform coercivity, derivative/Weil isomorphism or global quotient-surjectivity conclusion. |
| Damping / approximation | Half-damping admission, compact tails and endpoint norm continuity; exact signed-energy and residual identities. | Admission cofinally near zero or approximation error→0. Relative decay, linear readout and scalar work do not bound complete energy. |
| Zero-width dictionary | RH ⇔ zero width=0 ⇔ full/even/odd Hodge defect vanishes ⇔ cofinal damped-μ admission ⇔ vanishing Báez–Duarte residual. Full/odd H¹ floors and pointwise critical-deficit energy have exact rate sets `[width,∞)`, endpoint attained. RH iff critical energy bounded iff coprime cross-work bounded below iff cumulative critical energy is O(1+T). | Source-derived rate zero. Equivalent endpoints do not identify finite tests, norms or rates; no unrestricted L²-only floor converse follows. |

Sources: D:ThreeTenthsSharpGaugeWeilPositivity; I:SchurLendingOddWindowThreeHundredSixtyTwoThousandths; I:OverlappingPrimeStripsTwentyThreeFortieths; G:AllApertureSourceRiemannRochAndCoercivityLaws; G:AllParityCriticalDeficitAndEndpointSobolevLaws; O:TheWidthDictionary; O:TheWidthFunctor; M:TheCompensatedRemainderOfTheFullLedger; B:WeilLagCriticalDeficitEndpointAndLimitLaw.

## Live routes

<a id="wl"></a>
### WL — Weil lag function

- **Path:** Exact prime data → one-sided lag/deficit bound, or subexponential critical-deficit energy → RH.
- **Proved [L]:** Exact prime-lag/Abel identities; one universal compact spline gives an RH-equivalent one-sided prime-sum bound. Translated pairing is a finite prime sum with full polar correction. Multiplicity defect detects nonsimple critical zeros, but its finite-cutoff convergence assumes packet boundedness.
- **Packet/energy receivers [L]:** D²−1/4 cancels both polar exponentials; stationary packet=pure lag convolution+decaying polar/trivial-zero remainder. Spline and autocorrelation-spline eventual upper bounds each characterize RH. Critical energy E satisfies `2E(T)+∫₀ᵀE≤4∫₀ᵀ(normalizedLogError)²`. RH iff E bounded iff coprime cross-work bounded below iff `∫₀ᵀE=O(1+T)`.
- **Exact endpoints [L]:** Incoming deficit=`Re Σ_zero copies e^(T(ρ−1/2))/ρ²+O((1+T)e^(−T/2))`. Pointwise E and coprime-work rate sets are `[width,∞)`, with no slack/polynomial loss. For `0≤σ<1/2`, width≤σ iff incoming=`O(e^(σT))` iff deficit primitive has an upper `O(e^((1/2+σ)T))` bound iff lag has a one-sided `O(e^(σL))` bound. Two distinct primes suffice on mixed integer lags `L=klog p+llog q≥0`, not separate progressions.
- **Mean law [L, conditional on RH]:** `C₄=Σ_distinctρ mρ²/|ρ|⁴` is finite and positive unconditionally; under RH, `T⁻¹∫₀ᵀE→C₄` and mean signed-work density→C₄/2. C₄ is the infimum of valid linear cumulative-energy slopes; every slope>C₄ works, attainment at C₄ unproved. No source bound follows from this conditional limit.
- **Arithmetic coordinates [L]:** `|E+coprimeCrossWork|≤49/4`. RH iff centered off-diagonal work has an upper `O(1+T²)` bound, equivalently an upper `O(1+T)` bound; centered Euler curvature admits the analogous cubic/linear equivalence. Quadratic chronological-work upper bound suffices. Every-positive-rate lower bounds on coprime cross-work iff RH.
- **Arithmetic saving [L]:** For every `0<a<3/5`, `E(T), −coprimeCrossWork(T)≤Cexp(T−κT^a)` and `|incoming(T)|≤Cexp(T/2−κT^a)`. No polynomial or zero-rate bound.
- **Filtered deficit [S]:** `Γ⁻¹∫_[Γ,2Γ]|∫ incoming(t)ψ(t)cos(γt)dt|dγ≤CαΓ^(−1/2)N(ψ)` for real C² ψ supported in [0,2A], `0≤A≤αlogΓ`, `0≤α<2/3`, Γ sufficiently large; `N=‖ψ‖∞+‖ψ‖₁+‖ψ″‖₁`. Spectral analogue has Γ^(−4/3). Deep-shell weighted count at depth≥θ has decay exponent `(4/3−2α)θ/8`, `0<θ<1/2`; three-shell count is subpower. Frequency averages do not give pointwise deficit, sign at zero ordinates or bounded critical energy. E: B:ZeroDensityFilteredCriticalDeficitLaw.
- **Explicit inputs [L]:** Every aperture a>0 has a nonzero C² spline supported in [−a,a], with explicit mass/derivative bounds, exact Fourier dilation, fourth-order Fourier decay and integrable Gamma pairing. No polar blindness or Weil sign follows. E: B:ExplicitApertureSplineInputs.
- **Open / obstacle:** Prove actual E bounded, coprime cross-work bounded below, lag/spline sign, or the weaker sufficient signed-work/rate targets above. PNT savings retain positive exponential growth; exact endpoint and mean laws do not control adverse arithmetic correlation.
- **Sources:** B:CubicSplineUniversalProbe; B:SplineProbeFiniteShiftBounds; B:EffectiveTranslatedPairingAndMultiplicityDefect; I:LagChebyshevAbelSummation; B:WeilLagPacketCancellationAndPositivity; B:WeilLagAndDeficitEnergyZeroWidthLaw; B:WeilLagCriticalDeficitEndpointAndLimitLaw.

<a id="rw"></a>
### RW — Restricted Weil ground energy

- **Path:** Complete prime−Gamma−polar form → nonnegative constrained ground energy at every aperture → RH.
- **Proved [L]:** Odd/primitive positivity and constrained ground-energy receivers; exact prime–Gamma–polar form; fixed-aperture completion/sign transfer. Eventual grid-tent nonnegativity for every seed at radius R implies window positivity, Hodge index and μ(R)≥0. Small-aperture positive floors and derivative-controlled all-aperture negative floors; see shared frontier.
- **H¹ endpoint [L]:** Full/odd Sobolev floors characterize width at the exact exponent; aperture-uniform H¹ floor iff RH. Pure L² endpoint transfer requires a fixed second-gauge/mass bound on the test class; no unrestricted L² converse. E: G:AllParityCriticalDeficitAndEndpointSobolevLaws.
- **Sonin boundary [L]:** Cutoff-1 domination fails on large-support real odd tests with zero mean and both polar moments zero. Arbitrarily large negative subspaces survive any finite list of continuous moment constraints. At each cutoff Λ>1, sufficiently separated finite packets of a sufficiently narrow profile satisfy domination uniformly in packet coefficients; one pole-free test can fail at 1 and satisfy it at Λ. Neither full-Weil negativity nor RW retirement. E: A:SpectralRealisationAndOperatorConstraints.
- **Compensation [L]:** On smooth compact sources, absolutely summable paired energies give Q=E₊−E₋; E₋≤E₊+B‖u‖² iff μ(A)≥−B, with optimal B=−μ(A). Every-positive-rate compensated floors iff RH; a rate σ floor gives width≤σ, lag floors and damping admission for ε>σ. Converse above zero width still needs locally bounded off-line depth mass.
- **Transport [L]:** On monotone cofinal apertures, RH iff total nonnegative jumps sum to μ(A₀), equivalently no partial jump sum exceeds μ(A₀). From the positive small-aperture seed, nonnegative relative step factors suffice; positive factors exclude finite contact. Bounded-gap discrete rate-σ floors extend to continuous apertures with factor exp(2σΔ). Ceiling-renormalized energy is bounded above; its monotonicity and bounded weighted leakage are unproved inputs.
- **Shell flux [L]:** Ground-energy drop equals nonnegative shifted relaxation energy; shell flux vanishes on the smaller domain and equals `(μ(b)−μ(a))·groundOverlap` on the larger ground state. Flat step iff extended smaller ground remains a ground state. Flux-ratio formula needs nonzero overlap; generic CCM-family identity, not arithmetic flux control.
- **Literal flow [L]:** Full-form translation invariance, finite eigenspace dimension and independence of translates exclude a nonzero smaller-support eigenvector at larger aperture. Hence every shell flux is nonzero and μ is strictly decreasing. RH iff μ(A)>0 at every finite aperture; otherwise a unique zero separates positive and negative energy. Near-top visibility at lag V with width w bounds that crossing by V/2+w, retaining amplitude/slack/horizon premises. No lower bound preventing crossing.
- **Prime-shell decomposition [L]:** Freeze prime powers at N=⌊e^(2a)⌋. The a→b energy drop is a nonnegative frozen-flow relaxation plus an arithmetic jump bracketed by shell correlations of the frozen/literal ground states. Shell terms read only the opposite boundary collars. A nonnegative-factor relative law iff RH; every nonzero one-node weight perturbation fails it. No positive exponential-in-aperture relative floor survives the doubly exponential ceiling. Graded relaxation bounds imply width≤σ conditionally; no arithmetic collar bound.
- **Open / obstacle:** Produce source-derived relative step bounds or bounded cumulative leakage at every positive rate, paying complete prime/polar energy and low modes. Telescoping and floor-transfer receivers do not produce these bounds. Density-free L² width-to-floor converse remains open; lag-grid receivers additionally retain nonaliasing/attainment premises.
- **Sources:** R:WeilMarkovOddPositivity; R:WeilMarkovPrimitiveHyperplane; R:PaperRestrictedWeilGroundThreshold; S:GroundEnergyAbscissaAndLagGridAttainmentBridge; C:CompensatedWidthFloorAndGroundEnergyRate; C:VanishingApertureFloorAndGradedTransport; A:QuantitativeGridTentDetection; C:TheApertureFlowIsAShellFlux; C:TheApertureFlowNeverStalls; C:ThePrimeShellBetaFunction.

<a id="fu"></a>
### FU — CCM-FU signed prime scheduling

- **Path:** Signed Möbius/prime scheduling → completed Abel moment A(M)/M bounded above → RH.
- **Proved [L]:** One-sided completed-Abel receiver; actual terminal primes p>√N realize graph sources with vanishing diagonal cost and full signed off-diagonal energy. Cutoff-wise decreasing prime-exhaustive histories; isolated critical prime channel is uniformly negative on growing fixed-relative-width windows. Exact clock kernels retain center, lag and cutoff, with operator decomposition, Cauchy–Schwarz bounds and fixed-cutoff center decay at ±∞. Off-diagonal sign remains a premise, not a consequence of realization.
- **Open / obstacle:** Control the complete history: initial seed, inter-cutoff drift, earlier action, covariance and endpoint terms. Isolated prime-channel gain and small clock diagonal cost do not bound completed Abel action.
- **Sources:** R:CCM/CCMFUSuzukiMobiusDivisorOneSided; R:MobiusDivisorPaidPrimeExhaustion; R:MobiusDivisorPrimeGraphClockRealization; A:TheLinearWindowOfTheCriticalPrimeChannel; B:PrimeGraphClockOffDiagonalSynthesisAndStationaryEnergyProducer; B:PrimeGraphClockCorrelationKernels; B:ProducerCompletionAndPrimeClockKernelSynthesis.

<a id="rp"></a>
### RP — Route-P / SP-E history floor

- **Path:** Literal matched−quantile prime history → eventual linear defect floor → RH.
- **Proved [L]:** Exact linear-floor criterion; signed hyperbola, centroid and square-debt identities; low-LCM payment. Native first clock jet has bounded noncompact synthesis and strong, not operator-norm, differentiation.
- **Open / obstacle:** Produce the complete-history floor with high-LCM pairs, moving core and singular-domain transport controlled jointly. Positive damping-shell traces do not provide that floor.
- **Sources:** R:SPEQuantileRieszRoutePLinearFloorCriterion; R:RoutePLcmPairPayment; R:PaperAbelRoutePOrder; R:BurnolBaseFirstJetAdmission.

<a id="pa"></a>
### PA — Prime–archimedean source passivity

- **Path:** Continued exact prime−archimedean trace → high-frequency passivity, subexponential Bernstein mismatch, or signed compact moment completion → RH.
- **Proved [L]:** Exact source/trace recovery; RH-equivalent current, Bernstein-mismatch and signed compact-moment receivers. Every fixed Hausdorff order is positive at sufficiently large shifts; finite order blocks have common thresholds. Positive saddle bands retain a signed complement.
- **Open / obstacle:** Prove high-frequency current sign, arbitrarily thin exponential mismatch bounds, or positivity at all remaining shifts across unbounded orders. Finite-order thresholds, tomography and passive deletion do not establish the missing orientation.
- **Sources:** R:PrimeArchEndpointFrequencyAccretivity; R:SoninCoupledBernsteinMismatchRH; R:PrimeArchHausdorffFixedOrderLargeShiftPositivity; R:PrimeArchSignedCompactCompletionCollapse.

<a id="mc"></a>
### MC — Möbius cancellation at half power

- **Path:** Signed Möbius source → half-power cancellation/subpower energy or square-sampled Chebyshev bound → RH. Alternate receiver: non-admission of every oscillating smooth-power probe below half damping.
- **Proved [L]:** Half-power cancellation/energy receivers; signed bilinear decompositions and actual fixed-modulus/window cancellation. Oscillating-probe non-admission is an alternate receiver; short-modulus, zero-frequency and stated Vinogradov–Korobov/collar ranges are controlled. BVI supplies prime-negative bounds above any fixed positive damping floor within its horizon-dependent band.
- **Prime-root cancellation [L]:** Vinogradov decomposition, Type-I and dyadic Type-II assembly give `|Σₙ≤N μ(n)ζⁿ|≤2U+UWp+(⌊log₂N⌋+1)√B`, `1≤U<p`, with `Wp≤p(1+log p)` and `B=2(1+H_N³)(N²/p+N²/U+N²Wp/(Up)+NWp)`. Explicit finite estimate; no all-horizon half-power receiver bound.
- **Composite orders [L]:** Type-II and log-weighted Type-I bounds allow any primitive-root order r>0; log Type-I retains U<r. Composite double Type-I retains resonances `r∣d₁d₂`, with bound `UF[UN/r+(U+r)(1+log r)]`; assembled μ (U≥1) and Λ (1≤U<r) estimates retain this cost. Root-order splitting pays small-order major arcs separately. E: V:MinorArcSumsAtCompositeRootsOfUnity; V:TheDualNormAtCompositeModuli.
- **Mean-to-energy transfer [S]:** BVI converts a supplied summatory power saving into a smaller positive receiver-growth exponent. Mean zero removes the leading `T^(1−2ε)` coefficient, not all growth; no global half-power cancellation or admission follows.
- **Full-row inversion [S]:** For every modulus d>0, the absolutely convergent Möbius kernel row satisfies `Σₙ≥1 μ(n)ℓ_d(n)=2Ψ_d(1)−(6/π²)m_d=(d−1)(d−3)/4−(6/π²)m_d`, `ℓ_d=(BernoulliKernel_d−m_d)/n²+cubicKernel_d/n³`. No moving-modulus tail, window cancellation or half-power bound follows. E: V:TheMoebiusRowInvertsTheCrossScaleKernel.
- **Prime below-diagonal cancellation [L]:** For `Q^δ≤p≤Q^(1−δ)`, `0<δ<1`, actual μ-window kernel statistic is at most `23(1+log(2Q))³(p²/Q)Q^(−δ/4)`, eventually `(p²/Q)Q^(−δ/8)`. Centered cross-scale form against any bounded small-prime row is at most `[23(1+log(2Q))³Q^(−δ/4)+6Q^(−2δ)]Σp/Q`. Centered prime row `(Λ−1)1_(Q,2Q]` has kernel bound `24(1+log(2Q))⁴(p²/Q)Q^(−δ/4)` and corresponding summed dual-norm bound. No RH-strength estimate.
- **All-modulus cross-scale law [L]:** For Q≥2, δ>0, N≥2Q and every `Q^δ≤d≤Q^(1−δ)`, both actual window rows μ and Λ−1 satisfy `|kernelStatisticAll(N,c′,d)|≤11L⁴(d²/Q)Q^(−δ/32)`, L=1+log(2Q). For finite S in this range, summed dual norm≤`11L⁴Q^(−δ/32)Σ_(d∈S)d/Q`; mean-corrected bilinear remainder against any |c|≤1 supported on S is ≤`[11L⁴Q^(−δ/32)+6LQ^(−2δ)]Σ_(d∈S)d/Q`. Composite major arcs retained; no full-energy bound. E: V:TheDualNormAtCompositeModuli.
- **Diagonal reduction [L/S]:** Abel/harmonic kernel bound from actual window partial sums plus a `1/J` tail [L]. For every K≥1, `Q≤Kd`, `d≤2Q`, N≥2Q, exponential window saving transfers to `CK(d²/Q)exp(−c√log Q/2)`, C independent of K; centered-prime PNT specialization [L]. μ specialization claims `exp(−√log Q/24)` but its window-sum identity has a summation-scope defect [S]. Combining moving K with minor arcs claims `C(d²/Q)e^(−c√log Q)` for every `Q^δ≤d≤2Q`, δ>0 [S]: μ branch and combined theorem inherit that defect. Independent prime estimates survive; no full-range bilinear/energy saving. E: V:TheDualNormAtCompositeModuli; [BVI source gaps](#bvi).
- **Open / obstacle:** Bound principal counterterm and high-product remainder jointly across diagonal/moving scales at RH strength. Alternatively exclude every oscillating probe below half damping by an actual quadratic gap. Below-diagonal savings, relative forcing decay and admission-equivalent recurrences do not establish that global bound.
- **Sources:** R:MobiusHilbertFormEquivalence; R:MobiusSquareResidueShortBilinear; T:OscillatingProbeSourceEstimatesEnergyGapAndCollarLimitations; V:ParityPairAndSelectivitySynthesis; V:MinorArcMoebiusSumsAtPrimeRootsOfUnity; V:TheMeanValueIsTheLeadingCoefficientOfTheReceiver; V:TheDualNormIsMinorArcBelowTheDiagonal; V:TheDiagonalDualNormIsArchimedean; V:TheCentredPrimeRowIsMinorArcBelowTheDiagonal.

<a id="tt"></a>
### TT — Theta-tail and heat–Cassini currents

- **Path:** Theta source → directed signed covariance/Wold decay or odd Weil-form sign → RH.
- **Proved [L]:** Exact theta seam/tail, Wold and odd/primitive Weil receivers; sharp Wold boundedness threshold t<1/2; Φ-Doob/reflected-prime identities. Restricted current signs and simple-critical transform uniqueness are available.
- **Open / obstacle:** Prove signed nonlocal covariance or full odd/primitive positivity at every rapidity and test scale. Translation-averaged depth blindness and restricted local signs do not orient the full form.
- **Sources:** R:XiHeatCassiniWoldNaturalSquareEnergySubhalf; R:PaperWoldDirectedCovarianceRH; R:WeilMarkovOddPositivity; R:WeilMarkovPrimitiveHyperplane.

<a id="la"></a>
### LA — Line anchor

- **Path:** Literal theta source → all-height Laguerre/Hadamard or Jensen sign → real-rooted Ξ → RH.
- **Proved [L]:** Exact log-derivative, heat-slice and coefficient-inertia receivers; fixed-degree Jensen–Hermite limits. Actual-ξ compensated tails converge on fixed discs and, at t=exp(u⁴), R=u³, on radius-Mu discs: C→∞, BC²→0. At heat κ/C, 0<κ<1/2, tail/Gaussian-reference→1 uniformly on bounded real intervals. Zero width bounds heat-real-rootedness time; corpus Newman constant is the nonnegative-time truncation/rescaling.
- **Exact finite head [L]:** Head is nonnegative on the real axis, with positive scalar and every central-zero factor retained. Exact complementary tail has nonnegative Taylor coefficients for R≥0, R²≥1/2. Head coefficient positivity transfers losslessly to the full slice; at any such fixed R, all-height head coefficient positivity iff RH. No Gaussian-error premise. Heat refinements: WD.
- **Divisor coordinates [L]:** For R≥0, actual ξ finite head equals a positive scalar times the local divisor polynomial at x²; even coefficients match, odd coefficients vanish, central multiplicities remain. Disjoint/split divisor copies multiply exactly; transitions retain the full signed convolution. No actual coefficient-sign or repairing-factor supply theorem; [source](../../formal/GaloisForLFunctions/ArithmeticLocalDivisorGeometry/SourceLocalFactors.lean).
- **Divisor geometry [L]:** Retained horizontal head is monic, even, nonnegative of degree 2N, N=retained zero-copy count. A retained off-line zero at its own ordinate forces N≥2 and a positive root at its depth δ. Coefficient positivity after heat λ/2, λ>0, implies `δ²≤λh_N²`, `h_N=maxRoot(He_(2N−1))`; central multiplicities retained. No coefficient-sign producer; [source](../../formal/GaloisForLFunctions/ArithmeticLocalDivisorGeometry/SourceDivisorGeometry.lean).
- **Heat/cumulant tools [S]:** Exact Mehler finite-head bracket and Riemann–von Mangoldt quadratic/fourth tail asymptotics: [WD](#wd). Pointwise heated-slice bounds are not all-order coefficient sign.
- **Local divisor repair [L]:** Pair `P(Y)=Y²+2(u²−δ²)Y+(u²+δ²)²` is real-axis nonnegative after Y=x², but coefficient-positive iff δ²≤u²; some Y+c, c≥0, repairs it iff δ²≤3u². At u=0, δ≠0, no nonzero polynomial multiplier repairs P. Positive scalar/central monomial factors and positive rescaling preserve the cone. Exact geometric cost: `(Y+u²+δ²)^nP` is coefficient-positive iff δ²≤(2m+1)u² for n=2m, or δ²≤(2m+3)u² for n=2m+1, including u=δ=0. Local models, not actual-ξ factor supply; [ALDG](#aldg).
- **Cancellation boundary [L]:** Universal coefficient-cone preservation/reflection by multiplication holds exactly for positive monomials. Every nonmonomial coefficient-positive Q admits a degree≤2deg Q witness P>0 on [0,∞) with a negative coefficient but PQ coefficient-positive. Bound sharp: `Q=1+Y^D` reflects below degree 2D; `P=Y^(2D)−Y^D+1` defeats it at degree 2D. No source-specific reverse shell cancellation; [source](../../formal/GaloisForLFunctions/ArithmeticLocalDivisorGeometry/UniversalReflectors.lean).
- **Open / obstacle:** Prove all-height/all-degree finite-head coefficient positivity, or its critical-heat counterpart. Real-axis nonnegativity is closed; coefficient sign, including near-double off-line pairs, is not.
- **Sources:** R:XiLogDerivReCriterion; R:XiJensenHermiteLimit; R:XiSliceGaussianTailLimit; R:XiSliceDenseGaussianTail; R:XiSliceGaussianTailHeat; R:XiSliceGaussianFiniteHeadPositivity; R:DeBruijnNewmanConstant; S:LagRateBoundsTheDeBruijnNewmanHeatTime.

<a id="tg"></a>
### TG — Topological sub-unit gate

- **Path:** Pre-divisor Euler/Gaussian source → positive-residual cubic transgression and integer trace<1 → RH.
- **Proved [L]:** Boundary winding/index and source-sensitive cubic transgression identities; exact topological/central-gap receivers. Literal Gaussian integer weights n^(−σ)e^(−yn²), σ≥0,y>0, have nonpositive coprime divisibility covariance and finite-product divisibility bounds.
- **Open / obstacle:** Construct the matrix-complete identity E_base=E_residual+Tr T_D with E_residual≥0 and integer trace<1 on every disc, or prove the zero-rate central-gap bound. Coprime indicator covariance does not control arbitrary signed/Euler-inverted combinations or the complete prime−Gamma−polar residual.
- **Sources:** R:FormationAnchoredCubicSpecialization; R:RestrictedProjectionIndexOperatorNormCriterion; R:GaussianCentralGapExplicitCriterion; R:GaussianIntegerLogConcavity; R:GaussianDivisibilityCorrelation.

<a id="hf"></a>
### HF — Positive Hodge form on arithmetic cohomology

- **Path:** Arithmetic cohomology/full-positive weight → RH; alternate prime-window discrepancy ceiling `≤e^(L/2)+O(L)` → WL's one-sided deficit primitive → RH.
- **Proved [L]:** Prime-blind/odd positivity receivers; actual-ζ finite negative index and positive low-grid-blind subspaces. Finite cohomological packets, trace identities and spectral interpolation. Actual-ζ zero-side scaling surface equals its prime–Gamma–pole surface. Smooth even-polar/primitive prime-blind tests have S/L>45 when the second moment is finite.
- **Receiver synthesis [L]:** Complex prime-blind, all-integer zero-pole blind, prime-power zero-pole blind and even pole-free prime-blind positivity are each RH-equivalent. RH iff every deleted-prime-power symbol lies in [−Λ(m)/√m,0); strict negativity alone is unconditional, the lower bound is not.
- **Orbit segments [L]:** A pole-blind test supported in [−a,a], low-grid-blind at aperture a+T/2, has positive translate span on [0,T] and sharp Hasse–Weil bound for |t|≤T. No fixed nonzero compact test is low-grid-blind at every aperture; local positivity does not exhaust a generic orbit.
- **Index boundary [L]:** Hodge defect `D=sup_a hodgeDefectAt(ζ,a)` counts distinct right zeros. Finite D iff finite off-line divisor iff uniformly bounded positive-time heat counts/collision masses iff uniformly bounded horizontal window charges iff all sufficiently high zeros are critical. `2·#{distinct right zeros ρ: 0≤Imρ<T}≤horizontalCollisionCharge(T)` and `D≤sup_T horizontalCollisionCharge(T)`. Finite D is even; RH iff D<2. Finiteness gives Θ<1 and short-window Möbius/prime power savings, not elimination of finite exceptions. No source charge ceiling; multiplicity-sensitive identity: WD.
- **Family restriction [S]:** Scale-stable subspace index counts distinct jointly seen right zeros; positivity iff joint off-line blindness. Finite index targets have single-member orbit witnesses, not an arithmetic index ceiling; [SRT family law](#srt). E: J:TheOrientationOfScaleStableFamilies.
- **Arithmetic base [S]:** Theta h⁰ on Spec ℤ satisfies exact Riemann–Roch and recovers completed ζ by Mellin transform; only base/pole-plane RR, not scaling-surface RR: [ACS](#acs). Damped orbit energy and quantitative curve witnesses: [SRT](#srt).
- **Open / obstacle:** Produce nonnegative complete Weil energy on unrestricted blind/odd/primitive tests, paying low modes and the signed Λ prime−polar term; alternatively derive D<2 independently from the source. No bound on D is supplied by its count identities. High spectral ratio and auxiliary Gram lower bounds do not sign the ground minimum. A global cohomological realization must retain the actual cup/trace/Ξ pairing.
- **Sources:** R:WeilPositivityPrimeBlindDuality; R:MarkovOddSectorFarkasAndOneSidedPBAP; R:MarkovTwoCellTelescopingAndFortyFiveRatioPBAP; G:SourceRiemannRochAwayFromTheLowFrequencyDivisor; B:NodeCriticalityPhaseSensitivityAndCalibrationSynthesis; J:TheScalingDatumOfAConfiguration; J:TheArchimedeanPlaceOrientsOrbitSegments; J:TheIndexExit.

<a id="chmd"></a>
### CHMD — Causal Hyperbolic–Modular Duality

- **Path:** Exact Weil source → causal prime-wave, Chebyshev-discrepancy derivative pairing, or Möbius-rest one-sided bound, or theta-Doob odd-sector half-bound → RH.
- **Proved [L]:** Exact source prime-wave and Möbius-wave receivers; theta-Doob graph, signed quotient, stationary resolvent and nodal identities. RH iff complete odd energy is nonnegative / no odd bound state exceeds the half-threshold. Completed real aperture core equals supported maximal graph; nodal parts preserve it. Sharp half-line/interval restrictions preserve the full graph uniformly in cut location and land in exact aperture cores.
- **Localization [L]:** Expanding symmetric windows converge in graph norm, commute with nodal truncation, and recover full signed energy, nodal interaction and primitive oneL defect. Sharp half-line restriction preserves the arithmetic generator domain; A(P_cu)=P_cAu+K_cu, K_c skew-adjoint and uniformly bounded in c, retaining Gamma and every prime-power term.
- **Open / obstacle:** Prove the complete signed wave's one-sided bound or odd Doob/nodal inequality. Pay reflected-prime interaction and primitive oneL defect. Exact localization, bounded commutator and defect convergence supply no sign.
- **Sources:** R:CHMDStage22PrimeWaveGrowthLawAndTwoPointSumCriterion; R:CHMDChebyshevDiscrepancyDerivativeTransportLaw; R:CHMDOddSectorCriterion; R:CHMDSupportedApertureDomain; R:CHMDSharpSpatialCut; R:CHMDSharpWindowNodalConvergence; R:CHMDSharpGeneratorDomain.

<a id="th"></a>
### TH — Theta moment positivity

- **Path:** Exact theta/prime−Gamma moments → all-degree Hankel/Bezoutian positivity → RH.
- **Proved [L]:** Low-order theta/Hankel/Stein signs; all-rank strict positivity for nonzero nonnegative coefficient vectors on one small positive-time interval. Stable-polynomial and finite-rank positive regions.
- **Open / obstacle:** Prove all-degree Hankel/Bezoutian positivity for arbitrary signed coefficients at one common positive heat time, or the equivalent full phase/current sign. Orthant positivity is insufficient.
- **Sources:** R:ThetaCuspSteinCertificates; R:XiHeatHankelFormOrthantPositivity; R:XiHeatStableTestPositivity; R:XiGaussianHeatTraceCompleteMonotonicity.

<a id="rn"></a>
### RN — Theta renewal and singular comparison

- **Path:** Literal theta renewal/connection source → divisor-faithful winding or directed boundary-work sign → RH.
- **Proved [L]:** Native Green/BV solvers, multiplicity-exact packets and fixed-Gaussian realization. Compact cone-positive renewal operator has exact regularized determinant and resonance multiplicities; unregularized native synthesis has a topology obstruction.
- **Open / obstacle:** Prove mixed prime+Gamma≥pole with all cusp/seam terms and directed boundary-current sign. Cone positivity does not imply real spectrum; global source-faithful completion needs appropriate topology/regularization.
- **Sources:** R:PaperThetaNativeResolvent; R:ThetaRenewalPositiveFredholm; R:ThetaRenewalFredholmSpectrum; R:PaperThetaUnregularizedExtensionObstruction.

<a id="wd"></a>
### WD — Ward orientation and horizontal collision

- **Path:** Directed source current → global negative-cross control or collision charge<2 → RH.
- **Proved [L]:** Exact Ward/collision receivers and integrable nonnegative cap, vanishing iff RH. Actual-ξ tail has C=A−D, 0≤D≤B/2; for R≥4, exp(Cx²−Bx⁴)≤tail(x)≤exp(Cx²). Full unnormalized slice=head·tail with nonzero head scalar and exact x² factors for central zero copies; compensated error≤|head(x)|Bx⁴ needs no XiC(t)≠0. At λ>0, 2Cλ<1, actual-tail heat is integrable and lies below its Gaussian reference with explicit fourth-moment error. Dense scaled-heat limit: LA.
- **Finite-head heat [L]:** Exact polynomial head/tail split; tail heated-cone sign for R²+r²+6s≥1/2. Head heat-cone positivity transfers to full-slice positivity, including central zeros by joint continuity. All-order heat positivity at λ≥localWidth²/3; λ=0 when (|t|+1/2)²≤431/2. Classical/VK zero-free profiles improve the high-height threshold but do not make it tend to zero. A κ/log t head-coefficient bound gives a narrower zero strip conditionally.
- **Mehler bracket [S]:** For real P, λ>0, `σ=1−2aλ>0`, heat at λ/2 of `Pe^(ax²)` equals `σ^(−1/2)e^(ax²/σ)(heat_(λ/(2σ))P)(x/σ)`. Actual ξ head P at R≥4 retains central factors; with tail quadratic a and fourth mass B, `Mehler(P)−BMehler(X⁴P)≤heated slice≤Mehler(P)`. Pointwise bracket, not coefficient/derivative sign. E: R:XiSliceMehlerAndRVMCountingCumulants.
- **Counting cumulants [S]:** First two normalized-head cumulants are reciprocal-zero sums; exact head/tail splitting. For large t and `8≤R≤t/8`, tail mass and real quadratic term each equal `log(t/(2π))/(πR)+O(log t/R²+log t/t)`; fourth term equals `log(t/(2π))/(3πR³)+O(log t/R⁴+log t/(t²R))`. No subconvexity input. Multi-pair thresholds 16/57 and 4/11 have no declarations in this source. E: R:XiSliceMehlerAndRVMCountingCumulants.
- **Collision accounting [L]:** At a real zero of order k, backward nonreal multiplicity is k−k%2. Collision times after each t>0 are finite; nonreal count equals their total collision mass. RH iff every positive-time collision has mass zero; no collision-exclusion estimate.
- **Index bridge [L]:** For finite `D=sup_a hodgeDefectAt(ζ,a)`, total collision mass after sufficiently small t>0 equals `2(D+E)`, `E=Σ_right(mρ−1)≥0`. Infinite D forces that mass→∞ as t↓0. Uniform boundedness detects finite exceptions, not their absence; HF gives the finiteness dictionary and D<2 receiver.
- **Critical heat [L]:** Collision/heat counts even; interval count drop=sum of collision masses. Positive corpus Newman constant is the last positive collision; finite off-line divisor iff finite positive collision set. WD threshold≤width²/3; Newman constant≤width²/2, distinct thresholds. RH iff retained-head coefficients are nonnegative at every height and every positive heat, for any fixed R²≥1/2. Verification-height reduction retains its actual-zero verification premise.
- **Small-time ceiling [L/S]:** Counts, remaining and instantaneous collision mass `≤CεR(t)log(2+3R(t))`, `R(t)=max(Xε,2πe^((c+ε)/t))+1`, `0<t≤1/8`: c=3/2 [L], c=27/40 [S]. The latter uses the interior Lindelöf envelope and Gaussian comparison; every zero beyond the corresponding height is real and simple. Bounds diverge as t↓0; no uniform index bound, collision exclusion or t=0 theorem. E: R:KiKimLeeInteriorLindelofHorizon.
- **Central masking model [L]:** For `e^(sD²)[X^(2m)(X²−a)²]`, all real a, nonnegative-time coefficient positivity iff `s≥max(a,0)τ_m`; τ_m strictly decreases, `1/(8m+10)≤τ_m≤1/(8m+5)`, `8mτ_m→1`. For a>0, index `⌊m/2⌋` gives the radical threshold; unique even contact degree `m+2+(m mod 2)`, constant coefficient positive. Top coefficient costs O(a/m²), full cone O(a/m). Hermite normalization `λ^j(2j)!`, λ=2s>0; all Gaussian moments nonnegative iff `λ≥2b²τ_m`. No actual-ξ cofactor control; [ALDG](#aldg).
- **Root/strip receiver [L]:** Nonzero polynomial P with positive root δ fails the heat coefficient cone when `4λ deg P≤δ²`, λ≥0, heat time λ/2. Normalized radius head `P_t=expand₂(sliceTruncPoly(t,H_R))` fails the shifted cone when `8λ|H_R|≤(δ−σ)²`, 0≤σ<δ≤R. For `1/2≤R≤1`, coefficient positivity at some `0≤λ≤δ₀²/(320log(180|t|))` at every `|t|≥73/5` implies width≤δ₀≥0; no log(1/δ₀) loss. Positivity remains a premise, not an improved strip theorem.
- **Sharp root barrier [L]:** At λ>0, coefficient-positive heat at λ/2 bounds every stationary point of a degree-N≥2 polynomial by `√λ·maxRoot(He_(N−1))`. For real-axis-nonnegative degree-2d P, d≥2, each positive root obeys `δ≤√λh_d`, `h_d=maxRoot(He_(2d−1))`. Equality forces a positive multiple of `He_(2d)(X/√λ)−He_(2d)(h_d)`. This extremizer is nonnegative, has heat cone exactly `s≥λ/2`, and at first heat only its leading and positive constant coefficients remain. Its roots ±√λh_d are exactly double; in monic normalization its residual cofactor is monic, even and strictly positive. Sonin minimum and `h_d²/(2d)→4` proved. [Barrier](../../formal/GaloisForLFunctions/ArithmeticLocalDivisorGeometry/HermiteHeatRootBarrier.lean); [factorization](../../formal/GaloisForLFunctions/ArithmeticLocalDivisorGeometry/HermiteExtremizerFactorization.lean); [edge limit](../../formal/GaloisForLFunctions/ArithmeticLocalDivisorGeometry/HermiteEdgeAsymptotics.lean).
- **Optimal heat [L]:** Every nonzero even nonnegative polynomial with a positive root has an attained first heat τ>0 and cone [τ,∞). For degree 2m+4, root √a, a>0, minimal first heat is `a/(2h_(m+2)²)`, attained by the scaled Hermite extremizer. Every constant below 4 fails the universal degree bound; central masking/optimal heat ratio→2. No actual-ξ sign input. [First heat](../../formal/GaloisForLFunctions/ArithmeticLocalDivisorGeometry/EvenPolynomialHeatCone.lean); [optimum](../../formal/GaloisForLFunctions/ArithmeticLocalDivisorGeometry/HermiteOptimalHeat.lean).
- **Arithmetic head/width [L]:** Exact Cesàro prime formula for the first normalized-head coefficient retains finite-head twist, explicit-formula remainder and compensated infinite tail; requires Ξ(t)≠0, cutoff Y>1. Raw head=Ξ(t)²P_t for R≥0 only off central zeros. For σ≥0, R≥1/2, width≤σ iff every shifted P_t has nonnegative coefficients, equivalently at every positive heat. No arithmetic coefficient bound.
- **Euler–Stieltjes cap [L]:** For `0<τ≤366/25`, θ≥0, `0≤2R_θ(τ)≤E(τ)−C(τ)`, where R_θ is right-of-level Stieltjes mass, C the critical-line divisor contribution, `E=8π Im(ξ′/ξ)(101/100+iτ)` has an absolutely convergent Euler expansion. R_θ decreases with θ; a.e. global cap obeys the same bound. C≤E, with equality at one such τ iff RH. For every σ≥0, cap vanishing above transverse σ iff width≤σ. No independent source saturation bound.
- **Open / obstacle:** Force cap/collision mass to vanish, prove Euler–Stieltjes saturation independently of the zero divisor, or supply all-height finite-head coefficient positivity at arbitrarily small heat. Exact arithmetic formulas, root detection and tail transfer do not orient the signed coefficients.
- **Sources:** R:XiWardCapGlobalIntegrability; R:XiWardGlobalCapRightZeroSum; R:XiWardGlobalCapAndFiniteHeadArithmetic; R:XiSliceGaussianTailCompensation; R:XiSliceGaussianTailWindowBounds; R:XiSliceGaussianTailRealBounds; R:XiSliceGaussianTailHeat; R:XiSliceGaussianFiniteHeadPositivity; R:XiSliceHeatFiniteHeadReduction; R:DeBruijnCollisionJumpLaw; J:TheIndexExit; R:DeBruijnCollisionMassAndCriticalHeat.

<a id="li"></a>
### LI — Paired Li and prime–Gamma balances

- **Path:** Literal prime−Gamma history → signed lower floor → Li positivity → RH.
- **Proved [L]:** Exact paired Li/source histories. Reciprocal-depth rate law: RH iff actual-clock lower floors hold at every positive exponential rate; unconditional reciprocal depth≤1/431. This rate is not raw zero width.
- **Open / obstacle:** Prove the actual subexponential lower floor, or the stronger finite lower bound for the literal primitive, retaining first-crossing and outside correlations.
- **Sources:** R:LiEvenCrossActualClockGrowthLaw; R:LiSignAlongSquares; R:PaperLiNegativeOperator.

<a id="sz"></a>
### SZ — Suzuki screw and shifted-kernel limits

- **Path:** Complete signed boundary pairing → screw nonnegativity or shifted-Ξ confinement → RH.
- **Proved [L]:** Every compact real L² source has full extended first variation J+γ₀‖f‖₂²−2 fullPairing(C_f), retaining every prime/polar term; only J can be infinite. Primary cusps converge uniformly in translation; the literal arithmetic pairing has an exact common finite prime head, and positive-tail normalization avoids ∞−∞. J=∞ forces strict literal small-shift deficit. No finite-energy or smoothness premise. The actual high-dyadic compact critical family has strict first-order literal deficit, with a shift neighbourhood depending on the source. Screw/RW sign transfer remains established.
- **Proved [L], moving primary:** Strong L² source convergence and positive shifts tending to zero satisfy the compensated-energy Fatou lower bound. Infinite limiting energy forces divergence, with no compact support or approximation-rate premise. This covers the nonnegative primary term.
- **Common shift [L]:** Explicit first-variation error→0 under common correlation cutoff, mass and increment-slope envelopes. High dyadic blocks, bounded block horizons and polynomial-width lacunary families have common smoothing/shift thresholds independent of coefficients and all finer smoothing. Thresholds still depend on scale/truncation; correlation cutoff grows as `2log V`. At fixed normalized increment bound, common strict deficit holds on radius-3/10 tests and odd radius-181/500 tests, with slopes `mass/10000` and `mass/2000`; no large-scale subsidy.
- **Receiver dictionary [L]:** For each compact C² test, eventual Suzuki deficit slope≥μ−δ for every δ>0 iff full Weil energy≥μ. All-test asymptotic non-overshoot iff RH; every-positive-rate odd deficit floors iff RH. These equivalences do not produce their sign inputs. Untruncated critical-source correlation at integer dilation r is O(r^(−3/2)); not the complete infinite-head first variation. E: A:CommonShiftForTheSuzukiDeficit.
- **Joint compact-window limit [L]:** Strong-L²/positive-shift Gamma-liminf and constant-source recovery retain complete Gamma, finite prime head, pole and infinite Lévy energy; a.e. common support suffices. No rate coupling needed. Positive limiting energy transfers to eventual literal deficit. Compact L²-continuous families with a supplied common Weil floor have one common shift, without C²/increment bounds. The floor remains an input; no global sign producer. E: R:Suzuki/SuzukiCriticalMovingWindowDeficit.
- **Noncompact extension [S]:** For L² f with `|C_f(t)|≤Ke^(−βt)` at every real t≥0, β>1/2: absolute pole/source integrals, infinite-prime Fubini and full extended first variation. Bound `0≤shiftedCoeff(ω,n)/ω≤2n^ωlog n` supplies a summable majorant for `0<ω≤1/2`, ω<β−1/2. Strong-L² moving sources with common K,β satisfy full signed Gamma-liminf; no aperture/shift rate coupling. Positive limiting Weil floor remains an input. E: R:Suzuki/SuzukiCriticalMovingAperture.
- **Growing-aperture transfer [S]:** Compact f_j→g in L², correlation cutoffs A_j→∞, target correlation decay β>1/2 and `e^(2A_j)‖f_j−g‖₂→0` give full signed Gamma-liminf and inherit any supplied target floor; approximants need no common decay envelope. No actual-family rate bound produced.
- **Collared source [S]:** Actual finite-family correlations satisfy `|C_g(t)|≤K(S,b)e^(−3t/2)` for every real t≥0, uniformly over sharp V≥1 and smooth V>0 truncations. Real-lag integration by parts retains the moving boundary. Sharp-truncation limits give `4∫₀∞C_g(t)cosh(t/2)dt=2R_cE_c`, complete infinite-prime energy and extended first variation; no absolute two-variable polar Fubini claim. Smooth truncation L² error≤`√(UΣb²/V)` and full prime energies converge. E: R:Suzuki/SuzukiCriticalCollaredFirstVariation.
- **Unbounded truncations [S]:** Each fixed sufficiently high dyadic block, polynomial-width window or finite lacunary union has one ω₀>0 for strict literal deficit of both the untruncated collared source and every V≥criticalTruncationThreshold, uniformly in coefficients. Deficit slope≥`(s/8)log M·Σb²`, s=min of the two positive archimedean slopes. ω₀ still depends on the scale family; no common threshold over all growing supports or RH-completeness. E: R:Suzuki/SuzukiCriticalCollaredFirstVariation.
- **Open / obstacle:** Prove complete first-variation sign on an RH-complete family, paying low/mixed modes. Finite high-scale collared families have noncompact decay/polar identification and truncation-uniform shifts in source; extending their positivity to the full receiver cone remains open.
- **Sources:** R:Suzuki/SuzukiCriticalFirstVariation; R:Suzuki/SuzukiCriticalL2PrimaryVariation; R:Suzuki/SuzukiCriticalPolePointwise; R:Suzuki/SuzukiCriticalL2Pole; R:Suzuki/SuzukiCriticalL2Arithmetic; R:Suzuki/SuzukiCriticalL2WeilNormalization; R:Suzuki/SuzukiCriticalL2FirstVariation; R:Suzuki/SuzukiCriticalLiteralFamilyContraction; R:Suzuki/SuzukiCriticalMovingPrimaryEnergy; R:Suzuki/SuzukiCriticalMovingWindowDeficit; [compact-L² certificate](../drafts/pipeline/3-formalized/sz-critical-source-extended-energy-domain-2026-10-24.md); [literal-family certificate](../drafts/pipeline/3-formalized/sz-critical-family-literal-source-deficit-2026-10-24.md); [primary-energy certificate](../drafts/pipeline/3-formalized/sz-critical-moving-primary-energy-2026-10-24.md); [joint-limit certificate](../drafts/pipeline/3-formalized/sz-critical-moving-source-liminf-2026-10-24.md); [noncompact paper](../drafts/pipeline/2-fully-proven/sz-collared-source-infinite-head-2026-10-24.md).

<a id="pm"></a>
### PM — Physical-model Haar approximation (FZZ-P)

- **Path:** FZZ alternating Nyman–Beurling source → global dyadic Haar approximation, equivalently cofinal signed-damping admission at 0 → RH. PW-B is a [candidate sub-branch](#pw-b).
- **Proved [L]:** FZZ-P Haar approximation and cofinal small-damping admission are RH-equivalent. Exact complete-energy, signed log-loss and drift/deviation/forcing/flux admission identities. Half-damping sharp/Riesz residue synthesis, compact tails and endpoint norm continuity; relative compensation decays without an absolute-energy bound.
- **Reduction [L]:** Complete energy=(1−α)²·sector energy+transverse energy; α→1 and relative transverse energy→0 for 0<ε<1/2. For compatible dyadic depth mε>1, contractive actual-prefix recurrence with bounded forcing iff admission. Square-cutoff error contracts for 1/4<β<ε; the compensated-head recurrence assumes ε>1/2, and the VK-band prefix bound retains geometric shell error. No small-damping producer.
- **Observation [L]:** O_q(v)(n)=v(n)−v(⌊n/q⌋), q≥2, is injective with the root value retained; same-root pronic distances satisfy horizon-uniform two-sided bounds. Origin shift k has sharp energy cost (k+1)(k+2)/2; reverse recovery retains the lost head. Actual-source observation boundedness iff damping admission; majorant observations diverge for 0<ε≤1/2, parity-twin observations grow logarithmically uniformly above each ε₀>0. Actual-source control remains in the horizon-dependent VK band. Full-cell stability, not finite-moment recovery or a small-damping producer.
- **Euler boundary [L]:** Removing finitely many primes preserves damped-μ admission, paid ideal and obstruction hull for ε>0. Local Euler factors are critical Wiener units; μ's full inverse product is a Wiener unit for ε>1/2, outside that algebra for ε≤1/2. Infinite signed cancellation remains essential.
- **Prime-support boundary [L]:** Exact signed hypercube energy equals pronic energy. Prime blocks give growth ≳y^(1−2ε)/log²y for both μ and its all-positive parity twin, 0≤ε<1/2; all bounded weights have uniform budgets above 1/2. Endpoint ε=1/2 open; no full-receiver divergence.
- **Spectral boundary [L]:** For 0≤σ<1 and nonnegative integrable w with positive mass on (0,∞), `∫w(τ)∏_(p∈S)|1−p^(−σ+iτ)|²dτ` is unbounded over finite prime sets S. Canonical arithmetic landing: exact Mellin/divisor-product identity and positive spectral mass give unbounded hypercube dilation energy over squarefree P, every Ramanujan modulus r>1, `−1/2≤ε<1/2`. No continuity premise; ε=1/2 and full size-cutoff receiver control remain open.
- **Mean-value boundary [S]:** For bounded pattern s with Cesàro mean L and 0<ε<1/2, its own-mean-centered damped receiver satisfies `E_T(s)/T^(1−2ε)→ΓεL²`, `Γε=[ζ(1−ε)/(1−ε)]²/(1−2ε)>0`. Nonzero mean excludes admission; mean zero gives only `o(T^(1−2ε))`. No actual small-damping bound.
- **Actual parity separation [S]:** At every fixed 0<ε<1/2, actual μ energy is `o(T^(1−2ε))`, its Ramanujan-isometric positive twin has energy `≥cεT^(1−2ε)`, and their energy ratio→0. Global in T, not restricted to the VK band. First-pronic-moment/prime-power-coefficient matching still misses this separation. No boundedness or admission conclusion.
- **Defect normalization [L]:** Forcing energy F→∞ and Eμ/F→0, `0<ε<1/2`; finite pronic L¹ forcing mass `Mε=Re(−ζ′(1+ε)/ζ(1+ε))`. Translation-b word displacement energy≤b² and signed work≤bMε; fixed-word normalized effects vanish on escape. Absolute forcing tail beyond H≤`Kε(H+1)^−ε`, word-work tail≤`bKε(H+1)^−ε`, uniformly in final horizon. Moving b still needs bH^−ε control; no receiver-energy bound. [Tail](../../formal/GaloisForLFunctions/ArithmeticDefectRigidity/BoundedWordErrorsHaveAnAbsoluteHorizonTail.lean).
- **Moving cofactor window [L]:** Source cutoff `J(T)=⌊log(F(T)/Eμ(T))⌋→∞`; signed cofactor tail beyond J retains complete forcing with relative squared error≤`(1+log(F/Eμ))²/(F/Eμ)→0`. No fixed-cutoff limit exchange or admission premise; forcing normalization still loses receiver scale. [Source](../../formal/GaloisForLFunctions/ArithmeticDefectRigidity/ForcingEscapesAMovingCofactorWindow.lean).
- **Power-subtracted cofactor [L]:** For 0<ε<1/2, actual forcing `fε(n)=cεn^(1−ε)+rε(n)`, cε>0, has bounded pronic L² remainder. For `C̃=C−cεn^(1−ε)`, receiver+C̃=rε. Total variation `Σ_(n≤T)|Aε(n)²+Aε(n)C̃(n)|/[n(n+1)]≤Bε√Eμ(T)`. On escape, variation/Eμ→0, cofactor pairing/Eμ→−1 and residual²/Eμ→0. Excluding antipodal escape remains open; [ADR](#adr).
- **Intrinsic pole subtraction [L]:** Actual receiver Aε has absolute Mellin trace `ℓε(Aε)=Σ_n Aε(n)mellinCell(1−ε,n)/(1−ε)=cε`, without admission. On rows v(0)=0 with summable trace, `C̃ε(v)=Cε(v)−ℓε(v)n^(1−ε)` is linear; its actual-source image also belongs to the trace domain. Fixed floor dilation `v(⌊n/j⌋)` preserves that domain and scales absolute/signed trace by `j^(−(1−ε))`; damped cofactor trace multiplier=1/j, finite packets=sum of these harmonic weights. Full-operator boundedness/domain invariance and coercivity remain open. [Linear map](../../formal/GaloisForLFunctions/ArithmeticDefectRigidity/ThePoleTraceDefinesALinearCofactorRenormalization.lean); [fixed-cofactor trace](../../formal/GaloisForLFunctions/ArithmeticDefectRigidity/FixedCofactorsHaveAHarmonicBoundaryTrace.lean).
- **Diffuse escape [L]:** Energy quantiles obey `rE(T)≤E(q_T(r))≤rE(T)+1`; interval error≤1. Signed cofactor work on quantile interval [r,s] has `|W+(s−r)E(T)|≤2Bε√E(T)+1`. Every moving cell multiplier |φ_T(n)|≤1 retains antipodal density with error≤Bε√E(T), hence normalized error→0 on escape. No concentration premise; no infinite-cofactor exchange or escape exclusion. [Quantiles](../../formal/GaloisForLFunctions/ArithmeticDefectRigidity/EnergyQuantilesRetainDiffuseEscape.lean); [signed pairing](../../formal/GaloisForLFunctions/ArithmeticDefectRigidity/EnergyQuantilesPreserveTheSignedCofactorPairing.lean); [moving localization](../../formal/GaloisForLFunctions/ArithmeticDefectRigidity/MovingLocalizationsRetainTheSignedDensity.lean).
- **Dilation commutator [L]:** For floor dilation D_p, `C̃ε(D_pv)−D_p(C̃εv)=ℓε(v)[⌊n/p⌋^(1−ε)−p^(−(1−ε))n^(1−ε)]`. Pointwise/pronic norm≤|ℓε(v)| uniformly in p and horizon. Actual commutator energy≤cε²; normalized energy→0 on escape even for arbitrary moving p(T). Not boundedness/coercivity of C̃ε; [source](../../formal/GaloisForLFunctions/ArithmeticDefectRigidity/CofactorRenormalizationHasABoundedDilationCommutator.lean).
- **Exact row reconstruction [L]:** On the zero-origin trace domain, `v=floorTransform(μ·n^(−ε),Rε(v))+ℓε(v)Hε`, Rε=Id+C̃ε, `Hε=floorTransform(μ·n^(−ε),n^(1−ε))`. Thus (residual,trace) is injective; residual kernel lies in the Hε line. Actual source: `Aε=floorTransform(μ·n^(−ε),rε)+cεHε`. No bounded inverse, admission of Hε or nonzero kernel asserted; [source](../../formal/GaloisForLFunctions/ArithmeticDefectRigidity/TheResidualAndPoleTraceDetermineTheRow.lean).
- **Common covariance [L]:** Receiver-normalized fixed-cofactor Gram entries have one common subsequential limit K, retaining `K(1,1)=1`, symmetry, `|K(j,k)|≤1/√(jk)` and finite-packet positivity. Simultaneous integer dilation p contracts every packet quadratic form by at most 1/p. No admission/concentration premise. Infinite cofactor sums and the moving forcing boundary cannot yet be passed through this limit. [Source](../../formal/GaloisForLFunctions/ArithmeticDefectRigidity/CountableCofactorCovariancesHaveACommonLimit.lean).
- **Gram coordinate [L]:** With cofactor energy G and forcing/cofactor pairing Q, `F+G−2Q=Eμ` exactly. Gram determinant `FG−Q²=EμF−〈receiver,forcing〉²` lies in [0,EμF], hence determinant/F²→0. This normalized collapse erases receiver scale; signed distance/Eμ=1 retains it, without an absolute bound. [Source](../../formal/GaloisForLFunctions/ArithmeticDefectRigidity/TheReceiverIsTheGramTangent.lean).
- **Natural cutoff [L]:** For d≤N and prime core p, the dilation primitive on n≤N is `pAε(⌊n/p⌋)−Aε(n)+αε(p⌊n/p⌋−n)`, with Aε the centered damped-μ prefix and αε its divisor mean. Uniform head pronic norm iff admission at ε>0. Uniform complete natural-form bound implies admission; converse for the n>N tail is absent. Bounds throughout (a,b), 0≤a<b, imply zero abscissa≤1/2+a. No bound is produced.
- **Size-cutoff spectral form [L]:** Finite signed μ form `Rε(D)=∫W_r(ξ)|Σ_(d≤D)μ(d)d^(−1/2−ε)e^(2πiξlog d)|²dξ≥0`. Uniform bound `Rε(D)≤ζ(1/2+ε)²Φ_r(1)` for ε>1/2. No bound for 0<ε≤1/2, RH-equivalence or complete-tail identification for this observable; [source](../../formal/GaloisForLFunctions/SignedSuccessorArithmetic/TheSizeTruncatedHypercubeForm.lean).
- **Open / obstacle:** Prove global L² Haar approximation or horizon-uniform complete signed-energy budget at arbitrarily small ε>0. Exact residual/trace inversion needs quantitative coercivity; infinite-cofactor limits must retain the moving boundary. Bounded commutators and localized antipodal laws do not exclude escape. Absolute majorants fail at/below half damping; separate termwise savings do not prove admission.
- **Sources:** R:FermiNymanHaarApproximationEquivalence; C:ObstructingTermsAndRegimeClassification; C:ComplementarySectorPropagationAndAffineContraction; C:SignedObservationStabilityAndOriginSelectivity; V:ParityPairAndSelectivitySynthesis; J:EulerFactorsAndPayment; V:TheHypercubeDirichletFormDivergesBelowHalfDamping; V:TheMeanValueIsTheLeadingCoefficientOfTheReceiver; V:TheNaturalCutoffDilationFormIsTheReceiver; V:TheParityPairAtTheLeadingExponent.
- **Spectral sources:** [TheSpectralHypercubeFormIsUnbounded](../../formal/GaloisForLFunctions/SignedSuccessorArithmetic/TheSpectralHypercubeFormIsUnbounded.lean); [TheHypercubeDirichletFormIsUnbounded](../../formal/GaloisForLFunctions/SignedSuccessorArithmetic/TheHypercubeDirichletFormIsUnbounded.lean).

<a id="jas"></a>
### JAS — Joint ancestry

- **Path:** Arithmetic prime-product Weil form → level-one positivity on sufficiently large-prime tests → RH; or square-shell arithmetic Riesz sums → finite-power-window subpower bound → RH.
- **Proved [L]:** Level-one prime-product, torus-density and finite-power square-shell criteria are RH-equivalent. Literal Gamma–theta source is admitted at all finite supports/phases/grades. Unconditional positivity reaches a growing logarithmic prime budget, not the receiver's level-one power budget.
- **Open / obstacle:** Prove sign at the y^(1/2) level-one budget, all-amplitude damped-shell positivity, or every-exponent subpower Riesz bounds on m<k≤m+m/log(m+1). Source admission does not close the budget gap.
- **Sources:** R:JointAncestryLevelOneCapstones; R:JointAncestrySquareShellFinitePowerCriterion; R:JointAncestryEndpointBudgetProducer; R:GammaThetaFullSupportSource.

<a id="ctf"></a>
### CTF — Chronological tail and Báez–Duarte approximation

- **Path:** Bounded chronological Bose/Möbius rows (or finite Báez–Duarte dilates) → vanishing L² error → RH.
- **Proved [L]:** Chronological/Báez–Duarte approximation and dual sampling criteria. Residual=(1−Λ-readout)²+centered pronic energy. Literal −μ_N aligns the readout; Rayleigh/cofactor identities and κ/log N lower floors are exact. Half-damped residue convergence does not imply undamped error decay.
- **Open / obstacle:** Construct bounded rows with total approximation error→0, or prove the arithmetic dual sampling bound. Bound centered energy, not just linear readout or Selberg diagonal; moving cutoffs and small damping remain coupled.
- **Sources:** R:ChronologicalRiemannEquivalence; R:ChronologicalDualSamplingCriterion; V:VonMangoldtReadoutFormOfTheBaezDuarteCriterion; V:TheDualProblemRayleighQuotientAndCofactorCuspLaws.

<a id="hcf"></a>
### HCF — Gaussian heat trace / critical feature variance

- **Path:** Exact arch−prime heat trace → one-sided vertical growth or all-degree positivity on two prime-log source grids after polar cancellation → RH.
- **Proved [L]:** Exact centered Gaussian explicit formula; fixed-rank signs; heat/vertical/Hankel receivers with multiplicity-exact inertia. All-degree positivity of both literal prime–archimedean grids with spacings log2,log3 on their polar hyperplanes is RH-equivalent; one grid admits aliases.
- **Open / obstacle:** Prove both actual source-grid signs at every degree, or the one-sided vertical/prime-chirp bound. Finite ranks, offsets of one step, and entropy identities do not settle all heights. Arbitrary-zero polynomial-aperture detection is formalized via SRT, not source positivity; its alternative centered-heat derivation remains [P].
- **Sources:** R:XiCenteredHeatBounds; R:XiGaussianHeatRouteCapstone; R:XiGaussianHeatTwoPrimeSourceSampling; R:HeatGridAliasingBoundary.

<a id="xn"></a>
### XN — Xi Newton invariant discs

- **Path:** Xi first-jet source → line-centered Newton self-map discs covering every zero → RH.
- **Proved [L]:** Line-centered Newton-disc coverage/self-map criterion; exact nonnegative Laplacian of interior margin. Fixed-disc polynomial pole repair preserves reflection and first root jets, not self-mapping.
- **Open / obstacle:** Construct discs covering every zero with nonnegative margin throughout. Boundary positivity alone does not pay the interior curvature Green potential; global scalar damping has only the trivial repair.
- **Sources:** R:XiNewtonSchwarzPickCriticalLine; R:XiNewtonDiscSourceMargin; R:XiNewtonDiscCurvature; R:XiNewtonScalarDamping.

<a id="bag"></a>
### BAG — Deterministic zeta self-return

- **Path:** Fixed-base ζ strong recurrence on all compact right-strip sets, local recurrence at every strip point, or cutoff-uniform positive Haar mass of target-ζ head twists → RH.
- **Proved [L]:** Fixed-base strong/local recurrence and cutoff-uniform positive Haar-mass receivers. Weak recurrence ladders collapse to RH; source/finite-head approximation and return diagnostics retain target-zero exceptions.
- **Open / obstacle:** Prove recurrence on a neighborhood of every right-strip point, equivalently the qualifying Haar/return bound at every tolerance. Universality for zero-free targets, conull recurrence and cofactor returns do not remove possible actual-zero exceptions.
- **Sources:** R:ZetaStrongRecurrenceReceiver; R:ZetaWeakRecurrenceLadderCollapse; R:PaperZetaReturnSpectralCriterion.

<a id="ewu"></a>
### EWU — Even pole-weight uniqueness

- **Path:** Actual even blind minimum nonnegative at every aperture → even positivity → λ=Λ → RH.
- **Proved [L]:** Even-polar/full-positive weight rigidity; blind minima attained, antitone in aperture, nonnegative at every aperture iff RH. Literal full Weil positivity for sufficiently high dyadic/polynomial windows and separated lacunary unions; dense two-band estimates retain high-energy dominance. Low/high bounds retain −K_low E_low.
- **Receiver transfer [L]:** Grid-tent energy/mass approximation covers every odd C² receiver with norm-control (α,β)=(1,0). Complex tests split into two real patterns with error≤C(R,Mg,Kg,L)/(6(n+1)); unmodulated odd lag tests need one pattern. Eventual tent nonnegativity for every seed at fixed R implies window positivity/Hodge/μ(R)≥0. Constant/every-positive-rate tent floors iff RH; current floors remain −78e^r mass or −((8+ε)e^r+C)mass. No zero-rate floor or density of the positive high-scale family.
- **Restricted completion [L]:** Pole-free factorial combinations have exact ramp/tail Weil-energy equality and zero completed-source divisor-sampling mass. The limiting full tail span has logarithmic coercivity above a fixed scale, including arbitrary finite high-scale supports. This restricted pole-free family is not proved RH-complete.
- **Beyond-dyadic source [L]:** q-adic sign-flip/drift-free and higher-order harmonic families; inverse-square envelope, tail<1, window/mass bounds, low-band Mellin exclusion and logarithmic Lévy coercivity. Uniform prime/polar channel bounds yield positive complete energy for nonzero sufficiently high dyadic blocks, uniformly above a fixed truncation threshold. Exact compact full-Weil/zero-form receiver retains Lipschitz phase-combination premise; no RH-completeness.
- **Quantitative realizations [L/S]:** Explicit polynomial window exponent `L≤M^(1/10²¹)` and scale thresholds instantiate existing positivity [L]. Each fixed high dyadic/polynomial/lacunary family has one Suzuki shift threshold for all coefficients, all V≥criticalTruncationThreshold and its untruncated collared source [S]: [SZ](#sz). No common threshold over unbounded scale families or full low/mixed-scale sign. E: O:ConcreteReceiverScales; A:CommonShiftForTheSuzukiDeficit; R:Suzuki/SuzukiCriticalCollaredFirstVariation.
- **Cell kernels [L]:** Harmonic charge/Poisson-window decomposition; nonnegative charges give R(t)≥A(2)/144. For q≥3, q-adic sign-flip charge A(2)=2log2>0, not a total-kernel sign. For every divisor scale d≥3, a nonzero perturbation of the dyadic multiplier is admissible with tail≤4/5 and R(t)≤−1/14000 on [0,1]. Generalized asymptotic-prime-energy identification remains absent; kernel sign is not full low/mixed-scale Weil positivity.
- **Selectivity boundary [L]:** Uniform high polynomial-window positivity holds for every |w|≤CΛ, including Liouville-twisted, prime-power-deleted and primes-only weights. At fixed truncation V it holds for every weight once the scale threshold may depend on V. Wide windows detect every nonzero shifted-pair weight; restricted high-scale positivity alone cannot identify Λ or establish full positivity with ζ's fixed Gamma/pole part.
- **Full-cone selection [L]:** Narrow pair tests recover every weight coordinate m≥2, with factorial-tent approximation. Every nonzero single-coordinate perturbation Λ+δδ_m fails full-cone positivity, both signs, including composite m; positive perturbations have eventual negative truncated-kernel witnesses. Without growth assumptions, positivity on the nonpositive-correlation cone iff RH and U≥Λ; on the nonnegative-correlation cone iff RH and L≤Λ. Their intersection is full positivity. Source identification is closed; Λ's cone membership remains RH, not a sign producer.
- **Open / obstacle:** Prove actual even blind minimum≥0 at every aperture. Pay low modes and mixed scales on an RH-complete cone; positivity of restricted high-scale families does not transfer through arbitrary tent approximation or polar-nonclosed limits.
- **Sources:** R:EvenSectorPoleWeightUniqueness; R:EvenSectorBlindVariationalAttainment; A:CompactCriticalPolynomialWindowAndTemperednessBridge; A:DenseScaleWindowsAndMultiWindowPositivity; A:FromTheCriticalFamilyToTheReceiver; A:QuantitativeGridTentDetection; A:FactorialRampSmoothingAndGramMargin; A:FactorialTailSpanWeilCoercivity; A:AdmissibleStencilsAndCellKernelsBeyondDyadic; A:WideWindowSelectivityAndBeurlingInfrastructure; A:SourceSelectionInTheFullWeilCone.

<a id="gta"></a>
### GTA — Transverse Schur charge

- **Path:** Actual theta-stage positive quartic Schur charge → rank-uniform transverse decay → RH.
- **Proved [L]:** Uniform late theta-stage quartic Schur decay is RH-equivalent. Finite truncations converge strongly without RH; positive charge and compact/ideal diagnostics are available.
- **Open / obstacle:** Prove rank-uniform transverse-energy decay from the arithmetic source, independent of zero data. Strong finite-prefix convergence is insufficient.
- **Sources:** R:Hedenmalm/HedenmalmThetaSchurQuarticSpectralDecayEquivalence; R:PaperThetaSchurModeCharge; R:PaperThetaSchurCompactGap.

<a id="owu"></a>
### OWU — Odd Weil-weight uniqueness

- **Path:** Actual Λ odd Weil positivity, or odd-positive arithmetic weight plus all-scale dilation-ray sign → RH.
- **Proved [L]:** Actual-Λ odd positivity and odd-polar-hyperplane criteria. On odd sinh-neutral tests the pole term vanishes; the complete signed archimedean−prime form remains. Exact blind dual/ground structure, local odd positivity and prime-incidence reductions.
- **Open / obstacle:** Prove all-aperture odd sinh-neutral positivity, or full reflected-prime/polar payment on unrestricted odd tests. An alternative odd-positive weight also needs all-scale dilation-ray sign. Local collar absorption leaves diagonal/polar terms unpaid.
- **Sources:** B:OddSectorPolarHyperplaneAndPoleWeightSynthesis; R:WeilOddConeMinorantRigidity; R:WeilDilationRayCriterion; R:OddSectorBlindVariationalAttainment.

<a id="pbm"></a>
### PBM — Regularized prime/log-ζ abscissa

- **Path:** Fixed pole-regularized prime or log-ζ coefficients → Dirichlet series convergence at every real `σ>1/2` → RH.
- **Proved [L]:** RH iff either fixed regularized series Σ(1_ℙ(n)−1/log n)n^(−σ) or Σ((Λ(n)−1)/log n)n^(−σ) converges for every real σ>1/2. Prime-gap continuation is available at weaker exponents. This route uses abscissa cancellation, not DR's monodromy.
- **Open / obstacle:** Prove cancellation of those actual coefficients to the critical abscissa. Regularization and compact-ideal comparison do not supply it; the prime-gap alternative additionally needs an exponent≤1/2 and zero-freeness.
- **Sources:** R:RegularizedLogZetaAbscissa; R:PaperPrimeRegularizedIdeal; R:PrimeGapDirichletContinuation.

<a id="rb"></a>
### RB — Robin/Nicolas divisor-sum criterion

- **Path:** Extremal divisor sums/primorial Mertens product → eventual Robin/Nicolas inequality → RH.
- **Proved [L]:** Exact eventual Robin/Nicolas criteria; Robin reduction to colossally abundant integers. Fixed k-free/exponent-defect margins; any large Robin counterexample must contain a growing lcm core and have small moving valuation defect.
- **Open / obstacle:** Prove the inequality on increasingly prime-saturated extremal integers/primorials at square-root remainder scale. Necessary divisibility and defect conditions are not a contradiction.
- **Sources:** R:RobinCriterionRiemann; R:NicolasInequalityRiemannConverse; R:RobinColossallyAbundantReduction; B:RobinMovingValuationDefect.

<a id="srt"></a>
### SRT — Prime-side one-parameter lag localization

- **Path:** Fix one generic width `0<w<log 2/2`; actual prime–archimedean sign on unmodulated difference bumps `κ_w(t+v/2)−κ_w(t−v/2)` for all `v≥V` → RH.
- **Proved [L]:** One generic fixed-width continuous late-lag receiver and exact lag-rate/zero-width law. Explicit visibility, excluded-depth and conditional doubly logarithmic horizons; restricted model/grid laws retain their density, attainment and nonaliasing premises. Ordinary arithmetic floor has rate 1/2 with subexponential saving.
- **Tent detection [L]:** Negative lag witnesses transfer to finite-scale tents and smooth detectors at seed radius V/2+w. Eventual tent sign at R implies depth<1/R below exp(R/(10⁵A(log R)²))−306, R≥e⁶, for a corpus constant A≥1. Sharper near-top/attained-top transfers retain their amplitude, local-count, separation and horizon premises; reverse height-to-floor transfer retains polar constraints and off-line density control. No source sign or uniform witness-resolution bound follows.
- **Orbit classification [L]:** For FE-symmetric tempered configurations, all-scale Hasse–Weil iff orbit Hodge iff off-line-pair blindness. A real smooth compact spectrally generic test exists for every configuration; one actual-ζ orbit therefore decides RH. Rate-σ orbit bound iff blindness above depth σ; for generic ζ tests iff zero width≤σ. No attained-global-top premise.
- **Orbit refinements [L]:** Eventual boundedness implies sharp all-scale Hasse–Weil. Translate-Gram negative index counts distinct seen right zeros; orbit-surface positive index is one plus that count. Neither gives a source-derived bound.
- **Damped orbit [S]:** `E_x(ε)=sup_(t≥0)e^(−εt)|c_x(t)|` decreases in ε. For FE-symmetric tempered configurations, ε≥0, finiteness iff blindness above depth ε; orientation iff E_x(ε)<∞ for every ε>0, with no common bound as ε↓0. Generic actual-ζ orbit specializes this to RH. Correspondence damping is a convolution automorphism with Rosati ε↔−ε; damped two-scale correctors cancel the pole, not the primitive-trace sign problem. No source bound. E: J:CorrectorsInTheDampingParameter.
- **Scale-stable families [S]:** On FE-symmetric tempered configurations, Weil positivity on a real C² compact-test subspace closed under every translation iff joint off-line blindness. Each off-line pair has one common spectral endpoint where all members vanish. Finite Gram-index supremum counts distinct jointly seen right zeros; every finite lower target is witnessed by translates of one member, not necessarily one member for all targets. Orbit spans combine visibility from different seeds. Actual-ζ full-form specialization supplied; no independent positivity/index bound or maximal-subspace classification. E: J:TheOrientationOfScaleStableFamilies; also HF/ACS.
- **Model selectivity [L]:** A nonempty pure-curve shifted pair q^±aβ_i, 0≤a≤1/2, retains symmetry and has generic-orbit rate set [a,∞). For nonempty finite symmetric clusters with 0<d(k)≤δ≤1/2, r≥0, `4r≤L` and `r·TV(d)·sinh(2δr)≤1`, fixed-resolution windowed forms are nonnegative at every test aperture, yet generic orbits fail Hasse–Weil orientation. Actual ζ is not identified with these models; [source](../../formal/GaloisForLFunctions/ArithmeticOrientationGeometry/TheShiftedPairAndTheClusterModels.lean).
- **Curve windows [S]:** For finite curve spectrum of size N, source support length<log q gives `c_f(νlog q)=log q·‖f‖² trace_ν`. Turán bound detects every |β|>1 in every sufficiently late N-consecutive-power window, for every nonzero such source; golden datum needs two consecutive powers of 5. Model visibility, not actual-ζ finite-spectrum or uniform-horizon control. E: J:QuantitativeReadingsOnCurveOrbits.
- **Single-height source bounds [L]:** For C² f supported in [−a,a], a≥0, `B_f=4(‖f‖₁+‖f″‖₁)`, polar energy≤`2e^aB_f²/(1+2π|ξ|)^4`. Full Weil positivity follows from supplied `Re Π_f(ξ)≤ce^(θa)‖f‖₂²`, `log(1+π|ξ|/4)≥12+ce^(θa)`, and both `B_f²/[8(1+π|ξ|)]` and the polar bound ≤‖f‖₂². Without a prime-saving premise, horizon `log(1+π|ξ|/4)≥Cε+(4+ε)e^a+2` suffices with the same two error budgets. At an off-line zero, phase saving plus signal>local-background bounds force a distinct nearby off-line companion, not a contradiction. E: A:SingleHeightPhaseSelectiveApertureAndPowerSaving.
- **Phase exceptions [L]:** Under `2r e^(2a)≤1`, C² window η supported in [−r,r], weighted measure of `|Re Π_f(ξ+ξ₀)|>ce^(θa)‖f‖₂²` is ≤`‖η‖₂²·4a(2a+C)/(c²e^(2θa))`, c>0, C absolute; weight `|FTη(−2πξ)|²`. Finite-prime phases recur syndetically. No uniformly eventual power saving exists, even for a bounded-C² endpoint-pair family; under RH its phase-recurrence gaps must grow doubly exponentially in a. No particular zero ordinate is forced outside the exception set. E: A:SingleHeightPhaseSelectiveApertureAndPowerSaving.
- **Detector [L]:** An off-line zero of depth δ and ordinate γ has a C∞ compact negative Weil witness at aperture ≤Cδ⁻²(4+|γ|)². The degree-38 corollary is also formalized; both retain the complete Weil form.
- **Open / obstacle:** Prove actual-Λ late-lag lower bounds at every positive exponential slack, source-derived orbit rate zero, or sufficient horizon containment. Generic-test existence is closed; visibility/index/rate identities do not force orientation.
- **Sources:** S:OneParameterLagFamilyDecidesTheCriticalLine; S:ZetaLagFamilyVinogradovKorobovEnvelope; G:DoublyLogarithmicVisibilityAndExcludedDepthLaw; A:QuantitativeGridTentDetection; J:TheOrientationOfACycle; J:TheOrientationRateIsTheDepthOfTheDeepestSeenZero; J:EventualHasseWeilIsHasseWeil; J:TheOrientationIndexOfACycle; S:SmoothWeilDetectorPolynomialAperture; [smooth detector](../drafts/pipeline/3-formalized/cluster-horizon-smooth-polynomial-detector.md).

<a id="act"></a>
### ACT — Arithmetic criticality / single-shift variation

- **Path:** Fix any `a>0`; actual theta-shift ground state `ω_a` and full prime collar → `D_a(u)≤2S_a(u)+V_a(u)` for every even compact `C²` profile `u` → odd Weil–Markov positivity → RH.
- **Proved [L]:** Exact single-shift theta-ground variation and all-aperture odd-form receiver. Full/odd small-window positivity, folded-source identities, signed moment cancellation and mean-zero floors. Ground-energy upper decay excludes a uniform positive gap at unbounded aperture.
- **Open / obstacle:** For one fixed a>0 prove D_a(u)≤2S_a(u)+V_a(u) for every even compact C² profile. Retain all reflected-prime terms, middle-region/signed-gauge remainder and admission. Current all-aperture mass loss remains exponential.
- **Sources:** D:ShortProfilePoleFreeVariationInequality; S:PolarGroundEnergyAndPoleFreeLagAbscissaBridge; D:RestrictedWeilGroundEnergyCriticalAtInfinity; D:SignChangingTwoMomentAndAtomPoleIntegralLaw.

<a id="aip"></a>
### AIP — Arithmetic incidence positivity

- **Path:** Actual prime incidence + canonical plateau gauge → all-aperture `GlobalIncidenceAllocation` → complete odd zero-form positivity ↔ RH.
- **Proved [L]:** Complete source identity: W=pool+crossing+ΣevenGain−ΣoddCost+remainder−pole. GlobalIncidenceAllocation iff RH; constant-mass or every-positive-rate mass/Sobolev deficits suffice. Exact tower squares, finite graph/frustration reductions, shared-strip payment and odd positivity through 181/500.
- **Open / obstacle:** Pay all prime and pole costs jointly on every odd compact C² test, retaining favorable even gains and signed remainder. Shared all-parity VK Sobolev floor still has leading rate 1/2; exact endpoint equivalences supply no zero-rate estimate. Individual tower/entry-strip budgets cannot reuse the same reserve globally.
- **Sources:** I:GlobalIncidenceAllocationCondition; I:ReflectedPrimePolarAllocation; I:GlobalSharedSurplusAllocation; S:TheIncidenceLedgerGradedByTheZeroWidth; M:TheCompensatedRemainderOfTheFullLedger.

<a id="acs"></a>
### ACS — Arithmetic Castelnuovo–Severi effectivity

- **Path:** Source-defined sections → all-aperture Riemann–Roch with ampleness → scaling Hodge index → RH.
- **Proved [L]:** Source-defined section cones and RR+ample→Hodge→RH receiver. Low-grid/pole-blind subsurfaces have RR+ampleness; local full/odd/primitive floors and finite-defect classifications. Actual-ζ smooth-window certificate leaves only the signed coalescent prime surplus; no unconditional 3/4 or RH consequence.
- **All-parity identity [L]:** For real compact C² F supported in [−A,A], `Q(F)=(γ₀−2)‖F‖₂²+Lévy(F)+4horizonEnergy(F)+2∫₀^(2A)D(t)G²(C_F)(t)dt`, D=incoming critical deficit, G²=double gauge derivative. Horizon term≥0; `|G²(C_F)|≤‖F‖₂²/4+‖F′‖₂²`. No parity/moment premise or linear aperture loss. Full-source RR has VK Sobolev deficit `−Ce^(r−κr^α)`, every `0<α<3/5`.
- **Filtered forms [S]:** Exact cosine+sine Weil quadrature equals the complex-modulated form and its full critical-deficit decomposition, also on the scaling surface. Plancherel bounds each zero's depth-difference energy by `min(2π,8πA²δ²)e^(2A|δ|)‖F‖²`, δ=Reρ−1/2. Frequency integral over [Γ,2Γ] splits into finite local ordinates Γ/2≤|Imρ|≤4Γ plus remote error `≤32e^A W²·reciprocalSquareWeightTotal/Γ`, W=‖F‖₁+‖F″‖₁. Averaged subpower coercivity, bad-frequency measure and logarithmic-aperture strict positivity have no declarations in this source; [WL](#wl)'s filter estimate alone is not that closure. E: G:ZeroDensityFilteredWeilPositivityAndCoercivity.
- **Arithmetic h⁰ [S]:** `h⁰(d)=log Σ_(n∈ℤ)exp(−πn²e^(−2d))` satisfies `h⁰(d)−h⁰(−d)=d`, is positive/strictly increasing, tends to 0 as d→−∞ and has h⁰(d)−d→0 as d→∞. Completed ζ is its theta Mellin transform for Re s>1. On a,b>0, `h⁰(log a)+h⁰(log b)` has pole-plane RR difference `log(D²/2)`, D=aH+bV. Base/pole-plane identity only; no section law in full test directions or Hodge sign. E: J:TheThetaH0OfSpecZ.
- **Exact endpoint [L]:** For σ≥0, width≤σ iff full/odd H¹ defect floor `−Ce^(2σr)`, equivalently graded Sobolev RR on all full/odd test subspaces. Rate sets=`[width,∞)`; aperture-uniform H¹ floor iff RH and self-improves to sign zero. Pure L² transfer only for test classes with fixed second-gauge/mass bound; no source-derived uniform H¹ floor.
- **Finite models [L]:** On finite P-smooth supports, prime incidence splits by valuation fibres and |form|≤(Σ_p E_p)Σc², E_p=2log p/(√p−1). Two-prime box positivity iff κ≥E_p+E_q; 1–3-prime resonator remainder is negative for nonzero coefficient mass. Cross-collar positivity needs a bound premise; pole compensation needs c≥0 and pole weight≥max(S)/4. No full actual-ζ form identification.
- **Hecke/RR [L]:** RR on an ample half-space alone is nonselective; RR plus fibre-scaling invariance at one scale>1 on a nonnegative-degree cone forces Hodge. Finite Rosati RR iff spectral unitarity; exact Lefschetz/coboundary identity and cyclic Hecke–Lefschetz defect bridge. For the Hecke-stable envelope cone: RH ⇔ Hodge ⇔ RR ⇔ surface RR(0,0) ⇔ equality with the positive cone. Ampleness/Bézout are consequences, not standalone converses.
- **Proportion transfers [L]:** Distinct critical-line count N₀* obeys 2N_right+N₀*≤N without simplicity; dyadic proportions transfer to cumulative counts and off-line moments. Source gives eventual offLineMoment(V)≤0.066V without a surplus premise. Coalescent budget β yields proportion 29/36−β; β≤1/18 gives 3/4 and moment≤0.057V conditionally. Actual β bound remains open; model/mixing thresholds are not actual-ζ estimates.
- **Tower scope [L]:** Single-prime Gram entries are two-sided Laurent moments. Well-founded visible outer eigenvalues give finite-window negative-index lower bounds; failure of upper-level well-foundedness forces unbounded ordinates. Abstract weighted Wolff data hide infinitely many outer eigenvalues behind positive scalar-identity Toeplitz matrices; no realization by an actual ζ test. Two distinct primes' mixed shift orbit recovers full right-zero count for tempered configurations with a spectrally generic test; not two separate progressions or an arithmetic positivity theorem.
- **Orbit sections [L]:** On a fibre-compatible orbit surface, RR for an ample nonnegative-degree cone iff it contains the open positive cone and orbit Hodge holds; on configurations the latter is off-line-pair blindness. No independent arithmetic section construction.
- **Family sections [S]:** For a scale-stable real compact C² family on an FE-symmetric tempered configuration, RR for a supplied ample nonnegative-degree section set iff open-positive-cone inclusion plus joint off-line blindness. Finite family index counts jointly seen right zeros: SRT. No constructed arithmetic sections, maximality theorem or source index ceiling. E: J:TheOrientationOfScaleStableFamilies.
- **Prime reduction [L]:** Sub-Nyquist separation isolates prime 2; small shifts leave odd-prime even differences. Proper-prime-power error is `O(T^(2/3+η)log T)=O(T^(−1/3+η)N(T,2T))`, hence o(N) for 0<η<1/3, not absolute o(1). Full and prime-only coalescent budget hypotheses are equivalent. Parity-halved all-shift sieve retains explicit window, level and remainder costs.
- **Signed model [L]:** Ramanujan cancellation retains a negative half-diagonal, endpoint and divisor-second-moment errors. Actual prime-pair/model discrepancy remains uncontrolled. Narrow-strip gain algebra assumes a quadratic surplus budget, not an actual ζ estimate.
- **Open / obstacle:** Prove aperture-uniform H¹ floor, original-source RR with ampleness, or independent RR on a Hecke-stable nonnegative-degree cone. Pay low-frequency/mixed sectors or establish an arithmetic section law. Quantitative branch: bound actual signed prime-pair/model discrepancy or coalescent surplus β. Endpoint attainment does not lower the source's positive exponential rate; a fixed positive global gap is impossible.
- **Sources:** O:AnEffectivityFromSectionsThatDoesNotReadTheForm; G:SourceRiemannRochAwayFromTheLowFrequencyDivisor; G:AllApertureSourceRiemannRochAndCoercivityLaws; G:AllParityCriticalDeficitAndEndpointSobolevLaws; P:SmoothWeightedCertificateAtFourThirds; G:CrossTowerCollarAndFiniteEulerLatticePositivity; G:LambdaRingEffectivityAndHeckeLefschetzRigidity; G:CoalescentSurplusAndTransThresholdProportionLaws; G:OnePrimeAgainstTwoAndWolffTowerObstruction; J:SectionsOnTheOrbitOfACycle; P:CoalescentPrimeReductionAndParitySieve; P:RamanujanDirichletCoalescentTransfer.

## Route candidates

Promotion gap = missing independent source mechanism/landing, not merely an unproved final estimate.

<a id="apf"></a>
### APF — Arithmetic paired Fredholm

- **Path:** Prime source → divisor exhaustion → Fourier-trace vanishing → RH.
- **Proved [L]:** Fredholm index and actual cycle-trace Fourier reconstruction.
- **Promotion gap:** Construct zero-independent divisor exhaustion/vanishing of all trace coefficients. Reconstructing the off-line coefficients does not force them to vanish.
- **Sources:** R:PaperZetaCycleFourierReconstruction; R:PaperPrimeFredholmReconstruction.

<a id="bsh"></a>
### BSH — Arithmetic mate curvature

- **Path:** Literal prime−Gamma section → mate identity → orientation.
- **Proved [L]:** Framed curvature and compact-ideal diagnostics distinguish radial fibres; finite cutoffs are trace-blind.
- **Promotion gap:** Construct a pre-divisor arithmetic section and mate identity coupling s to Ξ(s)=0 without assuming neutral radial character.
- **Sources:** R:Deninger/DeningerOneSidedFramedMateCurvatureTransgression; R:PaperDeningerFramedCurvature.

<a id="cdc"></a>
### CDC — Constitutive dagger

- **Path:** Arithmetic presentation → neutral grade → source law.
- **Proved [L]:** Calibrated dagger confluence iff Re s=1/2; exact entropy/exchange-defect identities.
- **Promotion gap:** Construct one source-defined potential descending on all closed error fibres and forcing confluence at actual Ξ zeros. Parameter-wise classification is not source forcing.
- **Sources:** R:ConstitutiveDaggerConfluence; R:PaperCompletionInformationCost.

<a id="dr"></a>
### DR — Dyadic Xi roots

- **Path:** Global compatible dyadic roots on strict-right domain → zero-free Ξ → RH.
- **Proved [L]:** Zero-free cusp roots, finite monodromy/Kummer data and capped atlas; critical regularized-series convergence is RH-equivalent.
- **Promotion gap:** Prove source-driven global continuation with compatible roots on the full strict-right domain. Finite covers and local roots do not control global monodromy.
- **Sources:** R:XiSymmetricLittlewoodZeroFreeCuspDyadicRoots; R:XiTiltPuncturedMonodromy; R:RegularizedLogZetaAbscissa.

<a id="egc"></a>
### EGC — Pole-safe contour

- **Path:** Shifted contour source → enclosed-pole cancellation plus outer source covariance/sign → RH.
- **Proved [L]:** Complete copy correction and enclosed-pole cancellation; exterior tail small on centered shifts. Prime-2 arithmetic-ray sign and nonzero Gamma baseline are explicit.
- **Promotion gap:** Prove outer expanding-contour covariance/sign excluding off-line copies. Inner cancellation is unconditional for all zeros; raw source decay cannot beat its Gamma floor.
- **Sources:** R:PaperEGCCompleteCorrection; R:PaperEGCEnclosedPoleCancellation; R:PaperEGCSourceRayBaseline.

<a id="ewj"></a>
### EWJ — Euler/Wold jets

- **Path:** Faithful third jets → exhaustive source budget → RH receiver.
- **Proved [L]:** Exact finite-depth jets and compact-quotient character; fixed-history observations miss transverse gaps.
- **Promotion gap:** Provide zero-independent source admission and norm exhaustion into the RH receiver; finite-jet feasibility does not supply either.
- **Sources:** R:PaperEulerWoldDepthHistory; R:PaperEulerWoldCompactCharacter.

<a id="fel"></a>
### FEL — Theta likelihood

- **Path:** Predeclared likelihood history → zero/prime contrast balance → RH.
- **Proved [L]:** Exact probability/KL and adaptive-history entropy accounting. BSY integral equals a convergent off-line zero sum.
- **Promotion gap:** Derive cofinal zero-to-contrast balance from a predeclared arithmetic source. Adaptive accounting and the zero-indexed scalar identity do not select the line.
- **Sources:** R:PaperThetaObservationHistory; R:PaperCircleAdaptiveHistory; R:BalazardSaiasYorZeroSum.

<a id="hj"></a>
### HJ — Hurwitz reflection

- **Path:** Rational source fibres → reflection residual zero → RH.
- **Proved [L]:** Exact two-seed residual equals SEC's first-prime charge and vanishes iff Reρ=1/2. Parity/heat orientation transports the obstruction; all-divisor vanishing equals HCF's two-grid sign.
- **Promotion gap:** Construct pre-divisor arithmetic forcing of residual vanishing or even-witness sign at actual Ξ zeros. Zero-indexed vectors and parity transport leave source positivity open.
- **Sources:** R:PrimeTailSeedHurwitzReflection; R:XiHurwitzFunctionalEquationEvenWitness; R:XiSignedHeatOrientationConvergence.

<a id="irk"></a>
### IRK — Rotation-algebra trace

- **Path:** Arithmetic boundary defect → K₀/Chern landing → integral orientation.
- **Proved [L]:** Finite trace/winding laws; completed Xi-jet relation invertible off-line, no left inverse on-line. Logarithmic trace equals boundary winding.
- **Promotion gap:** Construct an arithmetic Poisson/projective lift with integral analytic count and the correct source defect. Completed-relation classification does not provide orientation.
- **Sources:** R:PrimeRotationXiRelativeKTwo; R:PrimeRotationCanonicalTraceIntegrality; R:PrimeRotationXiCompletedResolution.

<a id="msc"></a>
### MSC — Möbius−Sonin transport

- **Path:** Fixed squarefree arithmetic Hilbert source preserving strict-right divisor/conormal → Sonin energy sign → RH.
- **Proved [L]:** Fixed squarefree density/discrepancy Hilbert source preserves strict-right divisor multiplicities and conormal. Full critical logarithmic discrepancy lies in L² with admitted evaluation columns.
- **Promotion gap:** Build a source-faithful bridge from squarefree Hilbert observation to nonnegative Sonin/Weil energy or another RH-closing sign. Divisor preservation and L² admission alone are insufficient.
- **Sources:** R:SquarefreeDiscrepancyHilbertTransport; R:Hedenmalm/HedenmalmSquarefreeSummatoryConormalTransport; B:SquarefreeUnweightedHilbertSource.

<a id="pcs"></a>
### PCS — Singular co-shift

- **Path:** Singular ground → wall-class annihilation preserving forward mode → RH.
- **Proved [L]:** Explicit singular/wall ground; finite-prime projections converge strongly but retain norm/ideal gaps. Native shift/co-shift cannot be identified with invertible chronological dilation.
- **Promotion gap:** Produce source-natural wall-class annihilation preserving the forward mode. Any CTF bridge must retain the nonzero shift defect, not identify full carriers.
- **Sources:** R:PaperPrimeCoShiftCalkin; R:PaperPrimeCoShiftCofinalGap; R:PCSChronologicalDilationCarrierObstruction.

<a id="ptr"></a>
### PTR — Photonic source

- **Path:** Prime-faithful lossless port/stack → real-rooted transfer limit Ξ → RH.
- **Proved [L]:** Finite lossless stacks are real-rooted; their locally uniform Ξ-limit is RH-equivalent. Existing converse inserts unknown Ξ zeros into stack parameters. Continuum Poisson port has unit norm/Calkin gap at every positive depth. Explicit three-slab positive-impedance entire/even real-rooted stack [O:ConcreteFiniteSourceCertificates]; no Ξ limit.
- **Promotion gap:** Construct a nonlocal prime-faithful pre-divisor port preserving exact Ξ, or an independent zero-loss theorem overcoming the continuum gap.
- **Sources:** R:PhotonicLosslessProductPortRH; R:PaperPoissonNativeSource; R:PaperPoissonCompletionGap.

<a id="rfhm"></a>
### RFHM — Support grade

- **Path:** Phase/depth/compound-faithful source → broken inverse covariance → wall law.
- **Proved [L]:** Completed Gamma–theta source admits all finite supports, phases and Mellin grades; forward creation and strong cutoff exhaustion. Reversible sewing remains inverse-covariant.
- **Promotion gap:** Supply a source-defined non-inverse-covariant phase/depth/compound law with arithmetic wall orientation. Forward completion alone does not break the symmetry.
- **Sources:** R:GammaThetaFullSupportSource; R:GammaThetaFullSupportCreation; R:PaperRFHMSurvivalInformation.

<a id="sc"></a>
### SC — Stokes/Witt−Krein

- **Path:** Cross-fibre indefinite invariant → source orientation.
- **Proved [L]:** Chamber-constant rigged fibres, common-null-set Fourier reconstruction and finite Witt/Selberg coordinates; canonical polarization is wall-singular.
- **Promotion gap:** Construct a source-fixed cross-fibre indefinite restriction/index selecting the critical wall. Coordinate transport supplies no orientation.
- **Sources:** R:PaperKreinWallFourierCompletion; V:WittSelbergReceiverCoordinates.

<a id="sec"></a>
### SEC — Adjacent prime seam

- **Path:** Exact eventual compactness or time-one factorial-Fock jet boundedness → zero seam jump → RH.
- **Proved [L]:** Essential norm equals seam jump; exact vanishing iff Reρ=1/2. Time-one factorial-Fock boundedness on XiDivisorSupport is RH-equivalent; asymptotic prime-seam smallness is nonselective.
- **Promotion gap:** Prove exact eventual compactness or Fock boundedness from a pre-divisor arithmetic source at actual Ξ zeros.
- **Sources:** R:XiPrimeSeamAdjacentEssentialNormNoGo; R:PaperPrimeSeamIdealTrace; R:TimeOneGammaJetFockRHCriterion.

<a id="w1c"></a>
### W1C — Clifford–Dirac / centred Lee–Yang

- **Path:** Arithmetic operator/domain or centred ferromagnetic producer → real-rooted Ξ → RH.
- **Proved [L]:** Finite ferromagnetic Lee–Yang theorem and Ising-limit→RH receiver. Bare Clifford operator and finite/local Euler ports have no-go boundaries; prime interaction/field-density constraints are explicit.
- **Promotion gap:** Construct source-defined couplings with centered slow-field law converging to Riemann's measure, or a faithful arithmetic scattering denominator; critical interaction density must be produced.
- **Sources:** R:WeightOneCliffordSpectralNoGo; R:LeeYangIsingGraphDatum; R:IsingLawConvergenceRH; R:HermitianPencilEulerFactorObstruction.

<a id="wbf"></a>
### WBF — Source certificates

- **Path:** Arithmetic certificate stream → uniform-depth positive completion → Ξ landing.
- **Proved [L]:** Abstract scalar genealogy Gram/Fredholm recovery, relative determinants and strong-prefix versus infinite-Calkin separation; no arithmetic coupling in these results.
- **Promotion gap:** Define an arithmetic certificate stream and source-faithful depth-uniform completion landing on Ξ/Weil positivity. Abstract bounded scalar completion is not yet an RH route.
- **Sources:** H:PaperGenealogyFredholmRecovery; H:PaperGenealogyDeterminantGauge; H:PaperCriticalGenealogyCompletion.

<a id="pw-b"></a>
### PW-B — Physical cusp forcing (PM sub-branch)

- **Path:** Physical cusp → positive-damping action/response → zero-damping exclusion → RH.
- **Proved [L]:** Native two-response action, positive-damping admission and principal/forced response limits.
- **Promotion gap:** Pre-divisor source formulation removing XiZeroCopy indexing; small-damping complete-energy ceiling and action→optical magnitude→ordered cap→all-divisor extinction transfer.
- **Sources:** R:ThetaCusp/ThetaCuspHawkingBMPWNativeTwoResponseAction; R:ThetaCusp/ThetaCuspHawkingBMPrincipalSmallDamping; R:ThetaCusp/ThetaCuspHawkingBMForcedSmallDamping.

## Supporting research frameworks

<a id="bvi"></a>
### BVI — Bézout–valuation incidence

- **Role:** Arithmetic incidence/reciprocity, successor and pronic-energy estimates for PM, MC, CTF; no independent proof route.
- **Proved [L]:** Exact Λ readout and centered pronic residual; literal μ complete-period primitive energy grows linearly. Fixed-modulus cancellation, inverse/coprime reciprocity, short-window and balanced/unbalanced actual-row bounds retain explicit tails. Prime-negative multiplicative weights are bounded on the stated horizon-dependent VK band; prime-positive class diverges logarithmically. Equal period forms and selected Gram diagonals can have opposite Λ readouts.
- **Observation [L]:** All translated fifth/sixth moments with error 0≤ε≤1 recover Selberg coordinates up to reflection within 3ε^(1/6), independent of cutoff. Physical recovery costs Σ_active φ(q), ≤N on a dyadic tower; finite-window recovery retains boundary errors. Exact relation-Parseval law separates linear visible-mode response from cubic invisible-mode response. No actual Möbius/Λ sign estimate.
- **Cancellation/boundary [L/S]:** Prime-root/below-diagonal savings, composite μ/Λ assembly with resonant products, and every-modulus dual-norm/bilinear saving on `Q^δ≤d≤Q^(1−δ)` [L]: MC. Diagonal Abel/PNT bounds are uniform and linear in K [L]; extension to `Q^δ≤d≤2Q` for both rows inherits the unfinished μ window identity [S]. Prime-support hypercube energy diverges below half damping; natural size-cutoff head boundedness characterizes admission [L]: PM. Actual μ/twin energy ratio→0 globally at fixed 0<ε<1/2 [S], without admission.
- **Exact full row [S]:** Absolutely convergent Möbius inversion of Bernoulli/cubic cross-scale kernels gives the closed fixed-d formula in [MC](#mc); no uniform moving-modulus tail or window saving. E: V:TheMoebiusRowInvertsTheCrossScaleKernel.
- **Finite arithmetic tools [L]:** Type-I double-convolution bound `UFWp` for support lengths U,V<p and amplitudes F,1; Type-II short-factor bound scales linearly with arbitrary outer amplitude. Finite-field Kloosterman moments `Σ_a|K(a,b)|²=q(q−1)` and `Σ_(a≠0)|K(a,b)|²=q²−q−1` for b≠0 follow from character orthogonality. No growing incomplete-window or RH-strength balanced-receiver bound; [moment source](../../formal/GaloisForLFunctions/SignedSuccessorArithmetic/TheKloostermanSecondMomentIsACount.lean).
- **Mean/rate transfer [S]:** Bounded-pattern mean L fixes the leading receiver coefficient ΓεL²; finite Dirichlet kernels have L=K(1−ε), their pole value. Positive signing maximizes this coefficient among bounded patterns of the same amplitude with existing means. For |r|≤1 and `|Σₙ≤x r(n)|≤Cx^β`, 0≤β<1, `E_T(r)≤K(1+T^(1−2ε−γ))`, `γ=min(2(1−β)(1−ε)/(2−β),(1−2ε)/2)>0`, 0<ε<1/2. Remaining exponent is positive; no admission follows.
- **Source gaps:** Mean/rate file puts `−L*x` inside the summand in `hasMeanValue_of_rate` and `exists_abs_sqrt_patternReceiver_sub_le_of_rate`; parity file repeats this for raw μ² mean, so its exact Γε(6/π²)² coefficient is not established as written. Diagonal `sum_range_moebiusWindowRow` puts the second Mertens sum inside the first summand, not outside: its μ exponential corollary, combined μ/prime dichotomy and `exists_kernelStatisticAll_moebius_and_centredPrime_le_everyModulus` are not established as written. Independent centered-prime specialization, generic Abel reduction and mean-zero/μ-twin ratio statements retain their scopes.
- **Open / obstacle:** Complete signed receiver estimate across all growing moduli, horizons and small damping. Primitive/raw/centered energies are distinct; matching Gram diagonals is not matching full forms. PM's full-cell observation stability does not supply finite-moment-to-receiver stability.
- **Sources:** V:TheMoebiusPrimitiveEnergyGrowsLinearly; V:VonMangoldtReadoutFormOfTheBaezDuarteCriterion; V:DualNormOfTheActualRowsBeatsTheLargeSieve; V:SingleModulusReciprocityAndDyadicWindowIncidence; V:ParityPairAndSelectivitySynthesis; B:StratifiedObservationRecoveryAndBoundedRelationSynthesis; V:TheMeanValueIsTheLeadingCoefficientOfTheReceiver; V:TheNaturalCutoffDilationFormIsTheReceiver; V:TheParityPairAtTheLeadingExponent; V:TheDualNormIsMinorArcBelowTheDiagonal; V:TheDiagonalDualNormIsArchimedean; V:TheCentredPrimeRowIsMinorArcBelowTheDiagonal.

| Framework | Feeds | Established contribution / boundary |
|---|---|---|
| ArithmeticCompensationTheory (ACCC) | AIP, MC, RW, ACT, BVI | Exact compensated-source identities and Sobolev-rate dictionary; no source-derived zero-rate bound. |
| SignedArithmeticEnergyIncidence (SAEI) | AIP, MC, PM, CTF | Signed graph/frustration, prime-tower and receiver coordinates; local PSD/payment is not full continuum sign. |
| SignChangingScrewGauge (SCG) | AIP, ACT | Signed gauges, folded potentials and moment cancellation; middle-region/remainder sign remains. |
| ArithmeticOrientationTheory | HF, ACS, AIP, PM, MC | Source sections, orientation invariants and equivalent width/forcing dictionaries; no independent arithmetic orientation. |
| <a id="aog"></a>ArithmeticOrientationGeometry (AOG) [L/S] | ACS, HF, WD, SRT, PM, MC | Configuration/source equality, orbit rate/index laws, RH iff D<2, shifted-curve/cluster models and finite-Euler admission invariance [L]. Scale-stable family blindness/index/RR, damping-corrector laws, quantitative curve-window witnesses and theta h⁰ base/pole-plane RR [S]: SRT/ACS. No independent positivity, full-surface RR or index-bound producer. |
| <a id="adr"></a>ArithmeticDefectRigidity (ADR) [L] | PM, MC | Finite forcing L¹ mass, bounded power-subtracted L² remainder, pole trace, absolute word tails, quantile/moving-localization antipodal laws, bounded dilation commutator, residual/trace injectivity, common countable covariance limit and moving cofactor-window forcing law. Open: quantitative inverse/coercivity, full-operator domain and infinite-cofactor boundary control excluding escape. [PM](#pm); [umbrella](../../formal/GaloisForLFunctions/ArithmeticDefectRigidity.lean). |
| <a id="aldg"></a>ArithmeticLocalDivisorGeometry (ALDG) [L] | LA, WD | Local cones, sharp geometric repair, universal reflectors and actual ξ finite-head/signed-transition identification [L]: LA. Masked-pair heat ray/contact index, sharp Hermite root bound, equality rigidity, Sonin minimum, extremizer heat ray/double-root factorization, edge limit, attained first heat, fixed-depth optimum and masking ratio→2 [L]: WD. Actual-divisor Hermite receiver [L]. Open: actual repairing-factor/cofactor sign. [Source geometry](../../formal/GaloisForLFunctions/ArithmeticLocalDivisorGeometry/SourceDivisorGeometry.lean), [Source factors](../../formal/GaloisForLFunctions/ArithmeticLocalDivisorGeometry/SourceLocalFactors.lean), [threshold](../../formal/GaloisForLFunctions/ArithmeticLocalDivisorGeometry/MaskedPairHeatThreshold.lean), [barrier](../../formal/GaloisForLFunctions/ArithmeticLocalDivisorGeometry/HermiteHeatRootBarrier.lean). |
| Node/phase calibration synthesis [L] | HF, EWU, WL, PM | Four prime-blind RH receivers and deleted-node symbol intervals; twist-invariant window extrema versus phase-sensitive damped admission. Shifted prime weights are invisible on the prime-power-blind cone with ζ's Gamma/pole part held fixed—not a shifted-product explicit formula. Node 2 separates these weights; degree-two positivity iff shift=0 and RH. No unconditional critical producer. |
| <a id="ssa"></a>SignedSuccessorArithmetic | MC, PM, BVI | Multiplicative signs ↔ successor dilation cocycle; sharp adjacent logarithmic agreement coefficient 1/3, conductor-3 extremizers, prime-conductor bias −1/p with every-scale error `abs(C(N)+N/p)≤2p(log_p N+2)` [L]. Odd-shift coefficient 1/3; lag-2 optimum in [1/6,1/4], exact value open [L; shift source](../../formal/GaloisForLFunctions/SignedSuccessorArithmetic/TheFloorReadsTheParityOfTheShift.lean). Two-scale deficit `C(2N+1)−σ₁+C(N)+N=4·doubleAgreementCount`; global zero deficit forces exact 1/3 logarithmic agreement, but complete zero-defect classification remains open [L; source](../../formal/GaloisForLFunctions/SignedSuccessorArithmetic/TheTwoScaleDeficitIsQuantized.lean). Unit-complex successor correlation ≥`−(log M)/2−3`; cube-root values cannot differ at every adjacent pair on 1..9, but optimal complex coefficient remains between −1/2 and −1/3 [L; source](../../formal/GaloisForLFunctions/SignedSuccessorArithmetic/TheComplexSuccessorFloor.lean). Prime-subset divergence and size-cutoff spectral form: PM; finite-field moments: BVI. No actual μ/Liouville receiver estimate. |
| Concrete source certificates [L] | PA, LA, TH, HCF, HF, AIP, PM, PTR, EWU, BVI | Finite graph/index, horizon-5 radical, half-damping, Hausdorff/Jensen/theta/heat-rank, photonic and receiver-scale instances. Radius-1/5 nonzero positive spline, finite 1/10→1/5→3/10 floor chain, half-damping paid ideal, prime-2 heat, Suzuki variation and scale-4 Lefschetz instances. Not cofinal positivity, new exponents or independent routes. O:ConcreteFiniteSourceCertificates; O:ConcreteReceiverScales; O:ConcreteSourceDictionaries. |
| TransThresholdPairCorrelation | HF, ACS | Actual-ζ certificate N₀*≥(29/36−ε)N−coalescentSurplus; proper powers contribute o(N), so full/prime-only budgets are equivalent [L]. Signed Ramanujan model cancellation retains endpoint/divisor errors [L]. Budget thresholds: β<5/36 beats 2/3; β≤577/4500 beats HD(1); β≤1/18 reaches 3/4, not RH. Unsigned factor-two model gives 49/72; spectral factor-two model gives 3/4. Actual signed prime-pair/model discrepancy and surplus bound remain open. |
| ReflectiveDirichletPolynomialS2 | MC, BVI | Principal reflection, S₂ and dispersion transfers; no RH-strength balanced cancellation. |
| ReverseTwistedArcPoleCompression | RW, OWU | Pole-receiver reformulation; no independent sign producer. |
| Analytic large-value/zero-density tools | Shared, WL, ACS | Guth–Maynard large-value and 30/13 zero-density bounds [L]. All-length Heath–Brown pair-sum bound [L, R:Sieve/HeathBrownPairSumAllLengths]. Sharp S₂ middle exponent `2−1/k` and exact Proposition 12.1 for every integer k≥1 [L, R:Sieve/GuthMaynardSharpSTwo]. Uniform-away-from-line Ingham/GM envelope and logarithmic-window cosine-filter decay [S]: WL. Full-form quadrature/depth-difference bounds [S]: ACS; advertised averaged coercivity/strict positivity absent. No pointwise critical-energy bound or zero exclusion. |
| Gaussian / TP₂ tools [L] | TG, shared | Literal law P(n)∝n^(−σ)e^(−yn²), σ≥0,y>0: global scale log-concavity; P(ab divides n)≤P(a divides n)P(b divides n), with finite-product version. Coprime divisibility indicators have nonpositive covariance. No arbitrary signed/Euler-inverted correlation or transfer to complete Weil/pronic energy. |
| Producer/prime-clock synthesis [L] | EWU, HF, FU, CHMD | Pole-free ramp/tail completion and high-scale coercivity; exact center/lag/cutoff clock kernels, operator decomposition, Cauchy–Schwarz bounds and fixed-cutoff center decay. Actual p>√N realization has small diagonal cost; nonnegative off-diagonal sums are an explicit premise. No RH-complete positive cone or independent route. |
| Spectral-realization synthesis [L] | RW, EWU, PTR | Trace decay, coefficient-uniform finite-packet decoupling and cutoff-1/Λ>1 Sonin boundary: RW. Bundles existing determinant/operator-ideal restrictions and real-rooted ground-state receivers; growth/Poisson-balance inputs remain premises. No constructed Ξ operator or independent route. A:SpectralRealisationAndOperatorConstraints. |

Key sources: O:TheWidthDictionary; O:TheEffectivityConeFromSections; M:TheCompensatedRemainderOfTheFullLedger; P:SmoothWeightedCertificateAtFourThirds; G:CoalescentSurplusAndTransThresholdProportionLaws; J:ScalingDataAndWeilPlanes; J:TheCorrespondenceAlgebra; J:TheScalingDatumOfAConfiguration; J:TheOrientationOfACycle; J:TheSelectivityBatteryOfOrientation; J:CorrectorsAndTheLefschetzTrace; B:NodeCriticalityPhaseSensitivityAndCalibrationSynthesis; R:Sieve/GuthMaynardTheoremOneOne; R:Sieve/GuthMaynardHeathBrownStatement; R:ZetaZeroDensityThirtyThirteenths; H:LogConcaveIntegralComposition; R:GaussianIntegerLogConcavity; R:GaussianDivisibilityCorrelation; B:ProducerCompletionAndPrimeClockKernelSynthesis; [signed-successor sources](../../formal/GaloisForLFunctions/SignedSuccessorArithmetic.lean); [all-length and sharp S₂ certificate](../drafts/pipeline/3-formalized/heath-brown-all-length-dilation-closure.md).

## Dead mechanisms / scope boundaries

Full statements and positive survivors: [killed-routes ledger](rh-killed-routes.md).

| Mechanism | Boundary | Surviving target |
|---|---|---|
| Fixed positive all-aperture CCM/RR gap | Refuted; Gaussian upper ceiling tends to zero. | Nonnegative or suitable aperture-dependent floor. |
| Positive exponential relative floor [L] | Also contradicts the doubly exponential ceiling. | Faster-decaying positive factors or graded negative floors; arithmetic shell correlations retained. |
| Derivative completion = Weil completion | Refuted; Suzuki primitive is dense-range, not onto. | Fixed-aperture sign transfer and CHMD supported-domain identification. |
| Unit-cutoff Sonin domination from finitely many moment constraints [L] | Negative spaces of arbitrary finite dimension, even after mean/polar cancellation. | At Λ>1, narrow separated finite packets satisfy domination uniformly in coefficients; no full-Weil sign. |
| Finite blindness / local correlation matching ⇒ full positivity | Nonselective; polar moment and origin energy need not survive naive limits. | Full signed form with tail/origin control. |
| Discard favorable odd-fold terms; pay every prime from one reused strip budget | Scoped counterexamples. | Joint signed allocation retaining even gains, pole and remainder. |
| Absolute/HS bounds ⇒ sub-half-damping admission | Fails at/below the stated critical thresholds. | Signed covariance/reciprocal-source cancellation. |
| One heat grid or finitely many same-step offsets ⇒ RH | Abstract aliasing obstruction. | Both literal prime grids at all degrees. |
| Gaussian model heat positivity ⇒ actual ξ sign | Model nonselectivity; real-axis head sign is not coefficient sign. | Exact positive-tail transfer; actual all-height finite-head coefficient sign. |
| Finite Euler deletion ⇒ smaller damping threshold [L] | Paid ideal and obstruction hull unchanged. | Infinite signed cancellation beyond the absolute Wiener algebra. |
| Prime-support hypercube budget below half damping [L] | μ and parity twin diverge for 0≤ε<1/2; arithmetic spectral extension reaches −1/2≤ε<0. | Size-cutoff prime-core head boundedness iff actual receiver admission; bound remains open. |
| Nonzero-mean bounded pattern admitted below half damping [S] | Receiver has positive leading coefficient ΓεL². | Mean-zero leading term vanishes; bounded complete energy remains open. |
| Fixed-word/forcing normalization [L] | Fixed-word displacement and forcing work vanish relative to escaping receiver energy; forcing normalization loses receiver size. | Absolute word tails, pole subtraction, localized antipodal laws, common covariance limit and growing cofactor window retaining forcing. Absolute receiver bound open. |
| One real factor repairs every off-line pair [L] | Repair exists exactly for δ²≤3u². | Sharp geometric multiplicity thresholds [L]; actual divisor supply remains open. |
| Positive finite-shell cancellation [L] | Universal reversible multipliers are exactly positive monomials; nonmonomial witness degree 2deg Q is sharp. | Source-specific signed divisor information. |
| Extreme coefficient prices full masked-pair heat [L] | Top adverse coefficient costs O(a/m²), full cone asymptotic a/(8m); constant coefficient stays positive at contact. | Exact middle-order contact and full threshold; actual-ξ cofactor control open. |
| Successor 1/3 logarithmic agreement floor at every shift [L] | Conductor-4 twins have lag-2 coefficient≤1/4 despite perfect successor balance. | Odd-shift 1/3 floor; lag-2 optimum in [1/6,1/4]. |
| High-scale polynomial windows ⇒ full weight selectivity [L] | Same positivity for all Λ-dominated weights; fixed-V positivity for every weight. | Full-cone node recovery [L] identifies Λ but still requires RH-equivalent membership. |
| Finite prefixes / compact-ideal observations ⇒ global source orientation | Nonselective; norm/Calkin and growing-horizon gaps persist. | Source-faithful uniform completion plus an independent sign/vanishing law. |
| Finite-Euler two-prime box below κ=E_p+E_q [L] | Negative witnesses; sharp finite-model threshold. | Adequate diagonal budget; separate actual-Weil and cross-collar transfer. |

## Source locator

`K:Module` means `formal/GaloisForLFunctions/<directory>/Module.lean`. References select endpoint/frontier modules, not an exhaustive theorem catalogue.

| K | Directory | K | Directory |
|---|---|---|---|
| R | RHTower | H | HTGeometry |
| B | BiScaleUncertainty | V | BezoutValuationIncidence |
| T | TransHorizonIncidenceMechanics | A | arithmetic-positivity-theory |
| C | ArithmeticContinuationAndCriticalEnergy | I | ArithmeticIncidencePositivity |
| S | SquareRootThreshold | Q | ScaleSignedIncidenceCriticality |
| G | ArithmeticCastelnuovoSeveri | O | ArithmeticOrientationTheory |
| D | ArithmeticCriticalityTheory | M | ArithmeticCompensationTheory |
| P | TransThresholdPairCorrelation | J | ArithmeticOrientationGeometry |

Formalized arbitrary-zero detector: [polynomial-aperture detection](../drafts/pipeline/3-formalized/centered-heat-polynomial-aperture-detection.md). Its alternative centered-heat derivation remains paper-only.

## Alias lookup

BVI→[support](#bvi); C1→RW; CCM-FU→FU; CLG/TTF,K-RVM,S6F,TCD,UEB→TH; CSB,STC,U,MPLF,RHist,BPC,TQFQ,WS2,SQB→RN; D2,Q,RG,RG-ETA,TK→PA; E,EDQ,L,HDL,PSRC→MC; FZZ-P→PM; PW-B→[candidate](#pw-b); G,HC→WD; O→WL/RW (genus mechanism dead); P,SP-E→RP; SV2,RG-HF→SZ; T1,T2,Route T→TT; Route T successor/ULF sub-unit anchor→TG; Deninger→HF. [Retired labels](rh-killed-routes.md#retired-labels).
