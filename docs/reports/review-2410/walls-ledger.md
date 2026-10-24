# The walls ledger

**Status at 2026-10-24.** Three core problem families remain: **Wall 1, arithmetic estimates at the critical rate; Wall 3, information, norm and shared-resource transfer; Wall 14, faithful arithmetic realization and orientation.** None is removed. Several local walls are solved (fixed-aperture CHMD completion, the SZ critical passage, the mass-floor converse as an exact dichotomy, finite Hodge index, half-damping chain bounds), and four new faces are precise: the quasi-RH barrier at the start of Wall 1, collapsed off-line clusters, the finite low-frequency sector, and the arithmetic Hasse–Weil bound.

Companions: [complete report](hard-obstacles.md), [routine work and research programme](hard-obstacles-summary.md), [route unification](route-unification-ledger.md). Inventory: 31 live routes, 17 standalone candidates and PW-B.

## 1. How to read a wall

An **open estimate** is a missing arithmetic theorem. A **proved obstruction** excludes only its stated class and keeps a positive survivor. A **resolved local wall** has an exact positive theorem; a stronger transfer may remain open. A **candidate construction** has no completed producer. The three families organize research; they are not proved equivalent as construction problems.

## 2. Wall 1 — arithmetic estimates at the critical rate

Write `Δ = sup_ρ |Re ρ − 1/2|`.

### 2.1 The entry barrier

Every unconditional receiver estimate in the corpus has rate exactly `1/2` with a subexponential saving from the classical zero-free region: `e^{r−c√r}` (allocation, prime residual), `e^{L/2−κ√L}` and `e^{L/2−κL^a}`, `a < 3/5` (window ceiling, deficit), `exp(v/2−v^a)` (lag floor), `e^{−κV(T)/270}` (damping). For every `Δ`-reading receiver a bound at a fixed rate `σ < 1/2` gives `Θ ≤ 1/2 + σ < 1`. Proved instances: short-window Möbius or prime power saving ⇔ `Θ < 1` (V:ShortWindowMoebiusSavingIsTheQuasiRiemannHypothesis, V:ShortWindowPrimeSavingIsTheQuasiRiemannHypothesis); one Sobolev allocation rate below `1/2` ⇔ a fixed zero-free strip (M:TheCompensatedRemainderOfTheFullLedger); JAS level-one budget positivity for some `λ > 0` ⇔ quasi-RH (R:JointAncestryBudgetZeroFreeLaw). Powers of the deficit multiply its rate (S:AmplificationMultipliesTheZeroWidthExponent). The first step past Wall 1 is therefore quasi-RH in every such route.

### 2.2 Faces

| Face | Present wall | Resolved part / strongest survivor | Required new input |
|---|---|---|---|
| **1.1 Critical signed cancellation** | Prime/Möbius lag, packet, deficit, Mertens, regularized-series and divisor-sum estimates at every positive slack. | Explicit universal spline with finite-shift threshold `τ > 4`; exact cancellation identities; fixed-modulus Möbius cancellation; balanced rows with arbitrarily small leading coefficient; Guth–Maynard large values. | Signed cancellation beyond the classical zero-free region. |
| **1.2 Axis orientation** | Symmetry, nonnegative defects or integral counts do not force line support. | Ward cap, winding/index, Newton margin and Gaussian-tail receivers; `(Im z)² ≤ max(Δ²−2t,0)` for heat zeros. | All-height source sign or forced vanishing. |
| **1.3 Global Weil positivity** | At each aperture the obstruction is a finite low-frequency sector of doubly exponential dimension; no aperture-uniform payment. | Full window `3/10`; odd `181/500`; primitive `(log 2+1/50)/2`; finite defect at every aperture; positivity off the low grid; low-blind RR+ample+Hodge. | Pay the low sector and mixed terms uniformly in aperture. |
| **1.4 Arithmetic cone rigidity** | Uniqueness of the full-positive weight is not existence. | Cone `⊆ {Λ}`; admixtures and shifted pairs excluded; prime-power node criterion. | Positivity of `Λ` itself. |
| **1.5 Contrast equality** | Correct likelihood/Jensen accounting leaves a residual. | Exact BSY zero sum; adaptive reveal accounting. | Arithmetic equality of the cofinal contrast. |
| **1.6 Quantifiers** | Fixed rank, degree, order, history or aperture data do not meet the receiver. | All-rank orthant positivity; finite-order Hausdorff blocks; fixed-rank eventual coercivity; RW margin ⇒ heat-Hankel window at times `≤ K/n`. | Uniformity in the quantifier the receiver uses. |
| **1.7 Amplification** | Powers multiply the rate. | Exact exponent bookkeeping. | New correlation input. |
| **1.8 Critical pronic energy** | Bounded energy at cofinally small damping. | Admission above `Δ`; VK band; compensated diagonal and predecessor terms bounded; contraction ⇔ bounded energy. | Compensated interior estimate. |
| **1.9 Signed continuation** | Signed loss integral uniform in horizon. | Exact continuation/corrector equivalences; scalar work paid; core debt a ζ-log ratio; Bézout corrector comparable within 3. | Cross-covariance and flux control. |
| **1.10 Relative versus absolute compensation** | Relative errors vanish super-logarithmically while `P^{1−2ε}` remains. | Summable dyadic motion; two-scale rate `CTP^{−4β}`; admission-or-escape profile. | Absolute signed control; exclusion of horizon escape. |
| **1.11 Off-line multiplicity clusters** *(new)* | Mass-only floors and the equality of ground rate with `Δ` fail exactly when local depth mass is unbounded. | Compensated floor ≡ ground floor; rate equality ⇔ compensated floors above `Δ`; dichotomy with clustering; a rate excess needs collapsed clusters at heights `exp(e^{εA}/(40Δ²))`; count-only data cannot give a floor. | Arithmetic anti-collapse bound on off-line multiplicity in unit windows. |
| **1.12 Interior anti-alignment** *(new)* | MC's quadratic gap `θ(ε,t) < 1` between the proved collars. | Strict gap on the VK high-height collar and on bounded-height small-`ε` collars; planted Euler factors keep every collar. | Decorrelation or amplitude mismatch of the finite Euler–Maclaurin packet in the interior. |

Key evidence: [TheCompensatedRemainderOfTheFullLedger](../../../formal/GaloisForLFunctions/ArithmeticCompensationTheory/TheCompensatedRemainderOfTheFullLedger.lean), [TheHodgeIndexOfZetaHoldsAwayFromLowFrequencies](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/TheHodgeIndexOfZetaHoldsAwayFromLowFrequencies.lean), [TheHodgeDefectOfZetaIsFiniteAtEveryDegree](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/TheHodgeDefectOfZetaIsFiniteAtEveryDegree.lean), [CompensatedWidthFloorAndGroundEnergyRate](../../../formal/GaloisForLFunctions/ArithmeticContinuationAndCriticalEnergy/CompensatedWidthFloorAndGroundEnergyRate.lean), [OffLineClusterWeilUnbounded](../../../formal/GaloisForLFunctions/RHTower/OffLineClusterWeilUnbounded.lean), [MasterDCIPincerTheorem](../../../formal/GaloisForLFunctions/DilutionCrystallizationPincer/MasterDCIPincerTheorem.lean), [OscillatingProbeSourceEstimatesEnergyGapAndCollarLimitations](../../../formal/GaloisForLFunctions/TransHorizonIncidenceMechanics/OscillatingProbeSourceEstimatesEnergyGapAndCollarLimitations.lean).

### 2.3 The floor constraint

For `A ≥ 3`, `μ(A) ≤ K exp(11A/2 − πe^{2(A−2)})`; a positive floor `m₀e^{−B(A)}` needs `B(A) ≥ πe^{2(A−2)} − 11A/2 + log(m₀/K)`. The same ceiling binds graded `L²`-RR coefficients and fixed positive Hardy weights. Survivors: finite-aperture nonnegativity, floors decaying at the compulsory rate, graded negative floors. The ceiling tending to zero does not prove `μ(A) → 0`.

## 3. Wall 3 — what readings, norms and local budgets lose

Walls 1 and 3 meet at the square-root aperture `½ log T` at height `T`, where a test's prime horizon reaches `T` and its length reaches `√T`. Below it the Dirichlet mean value is exactly diagonal and sign readings are blind; above it `1`-separated height samples lose injectivity and admit hiding sections (O:TheNyquistBoundAtTheDiagonal). TTPC's barrier at prime cutoff `X = T` is the same threshold.

| Face | Proved limitation | Positive survivor | Open transfer |
|---|---|---|---|
| **3.1 Readings** | Sub-Nyquist sign readings are invisible to every orientation flip; magnitudes, Ramanujan amplitudes and all translated periodic moments miss admission; prime signs and real-axis means miss it too. | Trichotomy: depth certification needs Nyquist crossing, magnitudes, or mass/dilution/first-moment data (O:TheTrichotomyOfReadings). Logarithmic moments are a complete receiver invariant. | Realizable supra-Nyquist readings for actual ζ with priced error. |
| **3.2 Aperture/height escape** | Bounded-aperture positivity is compatible with depth `1/2`; finite radii admit non-positive mimics. | Cofinal positivity decides; explicit visibility; horizon-escape law. | Arithmetic horizon containment. |
| **3.3 Norm and cone transfer** | Derivative and Weil norms inequivalent; no uniform coercivity relative to the original graph norm. | RW/SZ sign transfer; CHMD completion = supported maximal graph with quotient lower bound at each aperture; sharp cuts in the full graph; expanding windows [S]. | Aperture-uniform constants; positive-family to complete-cone transfer. |
| **3.4 Shared signed resources** | Local payments reuse surplus; frustrated patterns can be PSD yet locally unpayable; fixed-width signed strip payment is false. | Holonomy criterion; integer-log lattice ledger balanced; frustration only on prime-sum edges; prime triangle index 2; signed Cheeger; packed paths in finite models; single-tower continuum Cholesky. | One shared budget in the continuum with Gamma and pole. |
| **3.5 Endpoint logarithms** | Pole cancellation alone does not pay half damping. | Partial-pole-sum logarithmic criterion; double-pole repair laws. | Endpoint control for new sources. |
| **3.6 Horizon and origin changes** | Generic below-half interchange fails; unbounded drift fails. | Interchange at/above half; sharp fixed-shift cost. | Actual moving-tail bounds. |
| **3.7 Damping topology** | Not Hilbert–Schmidt at `η ≤ 1/2`; no Riesz lower bound for residue modes; no bounded inverse. | Finite-support `ℓ²` bound on `[1/2,1)`; norm continuity at `1/2`; Bessel bound 48; real spectrum and coordinates; first column is the receiver. | Signed sub-half estimates. |
| **3.8 Multiplicity and index** | Packet `m²`, Weil `m`, index distinct count; curve finite index vs scaling defect. | Multiplicity ceiling; sector index laws; cyclic and one-prime tower detection. | Paid multiplicity assumptions in any transfer. |
| **3.9 Observation horizons** *(new)* | No universal `O(N)` arbitrary-phase observation horizon; sandwich constant of order `N²`. | `Φ(N)` samples always recover; stratified and dyadic constants; windowed recovery with explicit cost. | Sharp horizon and conditioning. |
| **3.10 Unit orbits and hulls** *(new)* | Invertible critical-Wiener filters preserve admitted and unadmitted classes; half-plane points do not exhaust the hull; pointwise nonvanishing is not invertibility. | Admission ⇔ empty Bohr hull ⇔ rank-zero quotient; units ⇔ no Bohr-polydisk zero; local factor `δ₁ − aδ_p` a unit iff `\|a\| < √p`. | A non-unit repair for actual μ below `Δ`. |
| **3.11 Coupled quantifiers in exact transfers** *(new)* | Proved bridges pair two parameters: Weil margin at aperture `A` controls heat degree `n` only at time `≤ K/n`, `K < A²/4`. | The bridge itself (R:XiGaussianHeatWindowFromWeilMargin). | Decoupling to one fixed time. |

Evidence: [TheTrichotomyOfReadings](../../../formal/GaloisForLFunctions/ArithmeticOrientationTheory/TheTrichotomyOfReadings.lean), [CHMDSupportedApertureDomain](../../../formal/GaloisForLFunctions/RHTower/CHMDSupportedApertureDomain.lean), [TheLatticeOddLedgerIsBalanced](../../../formal/GaloisForLFunctions/ArithmeticOrientationTheory/TheLatticeOddLedgerIsBalanced.lean), [TheChainIsBoundedAtHalfDamping](../../../formal/GaloisForLFunctions/SignedArithmeticEnergyIncidence/TheChainIsBoundedAtHalfDamping.lean), [UnitsOfTheWienerMonoidPreservePayment](../../../formal/GaloisForLFunctions/ArithmeticOrientationTheory/UnitsOfTheWienerMonoidPreservePayment.lean), [SuperlinearObservabilityHorizonAtArbitraryPhase](../../../formal/GaloisForLFunctions/BezoutValuationIncidence/SuperlinearObservabilityHorizonAtArbitraryPhase.lean).

## 4. Wall 14 — faithful arithmetic realization and orientation

| Face | Obstructed architecture | Positive survivor | Required construction |
|---|---|---|---|
| **14.1 Capacity, ideals and limits** | Fixed finite passive carriers, trace-class transport, fixed spectral gaps. | Growing carriers, `det₂`, gapless nonlocal ports, centered real-law limits. | Keep the source and divisor through a controlled limit. |
| **14.2 Algebra without orientation** | Finite-rank integral lattices, Witt integrality, FE symmetry, λ-ring and Adams identities as purity. | Exact ghost, index and radial-character identities. THIM's Bézout-selective laws (`gcd(n,n+1) = 1`, `pa − qb = 1`), the only class of its conservation laws that fails on Beurling systems and separates parity twins (T:CompleteSignedTransHorizonEnergyAndTransferSelectivity). | An independent orientation law. |
| **14.3 Diagnostic without producer** | Zero-indexed carriers and vanishing interfaces. | Exact depth laws on the divisor (S:TheZeroIndexedRoutesMeasureOneSide). | A source built first, with landing proved. |
| **14.4 Effectivity and the Hasse–Weil bound** | Positive graph cones, product cones, nonpositive grades, fixed Hardy weights; Hecke or Adams stability (RR then forces the defect floor). | Exact Lefschetz–adjunction identity on the scaling surface; Hecke–Lefschetz envelope cone with RR ⇔ RH [S]; Rosati cone RR ⇔ unitarity on curves; golden datum violates it. | The arithmetic Hasse–Weil bound `\|L(x,a) − ((a+1)/2)x·x\| ≤ √a·x·x` on every positive-cone cycle at every scale, from an independent geometric principle. |
| **14.5 Pre-divisor weld** *(new)* | Oriented pre-divisor data exist but no global identity forces them. | Signed prime/Gamma reservoir matrix defined at every spectral point and reversing under reflection (R:XiPreDivisorReflectionDefectStabilization). | The one-port stabilization identity at every spectral point. |
| **14.6 Section and count selectivity** *(new)* | Sign-coded sections read the sign; finite section counts and ranks are identical for `Λ` and a shifted pair. | Source-defined sections that do not read the form; Nyquist rank bounds. | An arithmetic section law with the right count and sign. |

Evidence: [LambdaRingEffectivityAndHeckeLefschetzRigidity](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/LambdaRingEffectivityAndHeckeLefschetzRigidity.lean), [TheEffectivityConeFromSections](../../../formal/GaloisForLFunctions/ArithmeticOrientationTheory/TheEffectivityConeFromSections.lean), [SectionCountRiemannRochAndPrimeBlindSelectivity](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/SectionCountRiemannRochAndPrimeBlindSelectivity.lean), [TheGoldenCurveIsABeurlingSystem](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/TheGoldenCurveIsABeurlingSystem.lean).

## 5. Changed, solved and new walls

| Previous formulation | Present disposition | Wall still present |
|---|---|---|
| Positive-width improvement treated as ordinary partial progress | Any fixed rate below `1/2` is quasi-RH in every `Δ`-reading route. | 1.1 entry barrier. |
| CHMD quotient lower bound and whole-quotient landing open | Solved at each fixed aperture; completion is the supported maximal graph. | Aperture-uniform constants, 3.3. |
| SZ cusp-preserving passage to `ω = 0` | Solved for compact `C²` [L] and compact `L²` [S]; limit is the Weil energy. | Sign, 1.3; growing support, 1.6. |
| Width-to-unrestricted mass floor open | Exact dichotomy with clustering; count-only data provably insufficient. | New face 1.11. |
| Finite negative index of ζ unknown | Finite at every aperture; Hodge index holds off an explicit low grid. | Uniform payment of the low sector, 1.3. |
| Effectivity hoped from λ-ring/Hecke structure | Stability forces the zero defect floor; envelope cone has RR ⇔ RH. | Hasse–Weil bound, 14.4. |
| Odd window `0.362` not yet in the lag family | Transferred. | All apertures, 1.3. |
| AIP axis/self-energy extension | Solved. | Shared budget, 3.4. |
| Prime channel negativity only on fixed supports | Linear-width windows. | Growing relative width. |
| Chain `ℓ²` bound only for `1/√2 < η < 1` | Uniform on `[1/2,1)`, Hilbert–Schmidt exactly above `1/2`. | Sub-half signed estimates, 1.8. |
| Receivers equivalent only as statements | Width functor: isomorphic objects. | Producers, all walls. |
| Readings classified case by case | Trichotomy theorem in model classes. | Actual-ζ readings, 3.1. |
| Residue-flip quarter law for special families | General `φ(q) < 4\|S ∩ units\|` at half damping. | Sub-half spectra. |
| Recurrence studied through universality | RH ⇔ strong recurrence on every compact set; locally ⇔ nonvanishing. | 1.2. |
| MC target only as global bilinear bound | Alternate exact target `θ(ε,t) < 1`; collars proved. | New face 1.12. |
| Heat positivity at fixed rank only | Bridge from Weil margins with a rank–time window. | New face 3.11. |
| Pre-divisor candidates purely zero-indexed | Pre-divisor reservoir data exist for HJ/SEC. | New face 14.5. |
| Effectivity through section counts | Counts nonselective; sign-coded cones read the sign. | New face 14.6. |
| Observation cost assumed polynomial | No universal `O(N)` horizon. | New face 3.9. |
| Filtering as a repair tool | Units preserve both classes; hull calculus exact. | New face 3.10. |

## 6. Scoped no-go register

"No-go" retires the stated mechanism, not a route. Full statements are in the [killed-routes catalogue](../rh-killed-routes.md#dead-mechanisms). Rows marked **legacy evidence** rest on catalogue identifiers rather than freshly inspected Lean.

### 6.1 The 44 named mechanisms

| Code | Excluded mechanism | Strongest retained statement |
|---|---|---|
| **WIP** | Witt integrality, positive integral Euler data and FE imply purity. | Golden Beurling counterexample; ghost reconstruction; Rosati cone RR ⇔ unitarity on curves. |
| **ODR** | Every unbounded origin drift preserves admission. | Sharp quadratic fixed-shift cost; drift preservation ⇔ bounded drift. |
| **LGP** | Lossless pairwise payment for every positive signed form. | Balanced holonomy; frustration index theory; packed nonlocal paths. |
| **WHL** | Pole cancellation alone pays half damping. | Partial-pole-sum logarithmic energy law. |
| **PAF** | Summable losses keep a fixed positive floor. | Doubly exponential compulsory decay; same ceiling for RR cones. |
| **ADJ** | Polynomial cross-prime majorant / nonnegative resonator remainder. | Hecke Cartesian incidence; normalized resolvent; negative resonator gap. |
| **HCT** | Below-half interchange and bounded backward transport. | Exact half threshold; bounded chain on `[1/2,1)`. |
| **AUT** | `L²` automorphic positivity locates ζ scattering poles. | Spectral sieve estimates; separate scattering law needed. |
| **LLM** | Mollified moments force every off-line zero away. | Near-line density and mean-square floors. |
| **GEN** | Fixed-part localization detects free orbits. | Support = fixed + twice-left count. |
| **UCF** | Averaged or reflection-even data pay the angular gate. | Angular quantization and Hermite detector. |
| **TEQ** | Theta equilibrium plus an unavailable maximum principle. | Equilibrium with attained maximum is a receiver. |
| **CAL** | Negative-time collisions or automatic backward monotonicity. | Positive-time multiple zeros refute RH. |
| **DSA** | Integral escape indicator vanishes automatically. | Pre-divisor transgression with a sub-unit bound would pay it. **Legacy evidence.** |
| **INT** | Finite-rank integral Frobenius lattice at nonreal zeros. | Finite-rank obstruction and torsion law. |
| **TWN** | Twin factorization supplies its own square root. | Root-tower receiver. |
| **NEV** | Termwise Nevanlinna sign proves the domain. | Exact source-sign receiver. |
| **ISG** | Balanced prime trees or fixed chains give a Ξ limit. | Centered ferromagnetic convergence suffices; prime-Ising subtree product law. |
| **SRP** | Full-positive weights at pole weight `β > 1`. | Pole weight forced to one. |
| **FPR** | A fixed finite passive realization is exact. | Growing passive carriers. |
| **DEF** | Deformation-stable estimates select ζ's line. | Need source-sensitive rigidity. |
| **CRT** | Finite-aperture or finite-prefix agreement gives full positivity. | Cofinal positivity decides; finite-radius mimicry theorem. |
| **TRC** | Trace-class transport realizes the source. | `det₂`/Hilbert–Schmidt carrier. |
| **APW** | Approximate or admixture weights. | `Λ` rigidity; admixtures excluded. |
| **JPR** | Automatic Jensen hyperbolicity at all degrees. | Explicit automatic regime. |
| **TOR** | Independent phases equal the ζ orbit law. | Deterministic phase-law target. **Legacy evidence.** |
| **REF** | Translation positivity gives reflection positivity. | Reflected sign retained. **Legacy evidence.** |
| **CPF** | One radial Carleman pole form dominates the source. | Signed rate measures. **Legacy evidence.** |
| **TMD** | A global formation primitive is free. | Formation receiver. **Legacy evidence.** |
| **TK** | Changing thermal ensemble removes the PA defect. | Exact PA receiver. **Legacy evidence.** |
| **BAG** | Finite Euler recurrence proves recurrence near zeros. | Local recurrence ⇔ nonvanishing; return threshold = distance to nonvanishing targets. |
| **SEL** | Selberg eigenvalue gaps locate scattering poles. | Arithmetic spectral gaps. |
| **R1** | Anchored weak chiral-loss passage gives a sub-unit defect. | Cubic = winding. |
| **R2** | Prime-2 renewal self-similarity forces zero winding. | Odd-winding counterexamples. |
| **R3** | Holomorphic two-prime quantum slack. | Quantization receivers. |
| **RAW** | Raw prime series converge to the critical line. | Pole-subtracted receiver. |
| **BD** | Even screw kernel stays Markov at cofinal apertures. | Boundary `2a ≤ log(plastic)`. |
| **PTR** | Local Maxwell collars admit prime conormals. | Lossless finite real-zero theorem; product-limit receiver. |
| **HFR** | Fixed-rank heat positivity decides RH. | Growing-window receiver. |
| **HUS** | Averaged Husimi positivity forces slice sign. | Uncertainty-priced identity. |
| **GAP** | Lossless realization with a fixed resonance-free gap. | Gapless handoff. |
| **CCP** | Even ground parity selects RH. | Finite-top ground law; isolated top quartet forces odd grounds. |
| **COS** | Finite local ports invert the cosine shift. | Nonlocal sech/Poisson map. |
| **POI** | Positive Poisson transport preserves real zeros. | Sharp two-tone threshold `\|β\|cosh(2c) ≤ \|α\|cosh c`. |

### 6.2 Route-class obstructions established at this checkpoint

| Excluded mechanism | Survivor / remaining target |
|---|---|
| Unit-cutoff Sonin domination without mean zero | Domination for mean-zero small-support tests. |
| Identification of derivative and Weil completions | Fixed-aperture sign transfer; CHMD supported domain. |
| Uniform positive restricted-Weil gap at unbounded aperture | Aperture-dependent floors. |
| Bounded certificate fusion as width control | Cofinal rate sampling; band reconstruction in models. |
| Magnitude-only / all-translated-moment receiver classification | Logarithmic moments; VK-band parity separation. |
| Complete-period quadratic data as signed control | Exact sign-orbit classification. |
| Weighted node rank as an RR selector | Hecke ampleness criterion on the whole open-positive cone. |
| Residue-flip repair below quarter density | General quarter law. |
| Prime signs or real-axis mean as admission selector | Oscillating-pattern phase diagram. |
| Independent pole/test product effectivity | Strict coupled cone, RR ⇔ AIP allocation. |
| Nonpositive-grade RR as ample effectivity | RR+ample ⇔ `c > 0` and the matching floor. |
| Fixed positive Hardy-weight RR | Aperture-dependent floors; Sobolev-rate dictionary. |
| Integer-horizon uniform coercivity | Support-localized `H¹` floor. |
| Sub-half oscillating prime patterns | Admitted only at zero amplitude. |
| Renormalized defect as a complete budget | Joint counterterm/remainder identity. |
| Pure-prime canonical paths; independent edge budgets | Frustration-index law; terminal reduction. |
| Fixed-width signed prime-band payment | Square-root-scale boundary band paid. |
| Uniformly bounded full-weight sampled frustration | Count/mass laws; balance below `0.3`. |
| Unsigned coalescent model as a `3/4` certificate | Signed sieve model meets the target at `Υ ≤ 2`. |
| Finite-aperture index as purity | Explicit detection under margins. |
| Higher matrix invariants beyond `2/3` | Slack conservation; `λ ≥ 3/4` survivors. |
| λ-ring/Adams algebra as purity selector | Hecke incidence identity; envelope cone. |
| Finite admitted-parameter sets plus zero-free collars | Energy-gap criterion. |
| Separate sawtooth/tail divergence as exclusion | `θ < 1` ⇔ non-admission. |
| Arbitrary second-row cancellation on prime-shift residues | Fixed arithmetic second row. |
| Nonvanishing-pole convolution repairing positive drift | Pole-vanishing criteria. |
| Parity-blind receiver classification | Fatality classification of parity collapses. |
| Invertible Wiener filtering as repair | Unit-orbit and hull invariance. |
| Sign-blind Riesz endpoint repair | Signed residue convergence at half damping. |
| Bare centering of `Λ − 1` at fixed modulus | Omitted-residue corrector. |
| Universal `O(N)` observability | `Φ(N)` recurrence recovery. |
| Bounded primitive energy below half damping | Linear growth law for literal μ. |
| Low-ratio coercivity as prime-blind closure | `S/L > 45` barrier. |
| Raw even polar-ground strip passage | Polar-quotient receiver; RH ⇔ full form ≥ 0 on real-rooted tests. |
| Unconditional even-ground selection | Isolated top quartet forces odd grounds. |
| Ordinary cyclic normal-regulator landing | Relative/negative cyclic realizations open. |
| Faster-than-theta divisor-preserving tails | Full-divisor exponent `b = 2` sharp. |
| Half-plane nonvanishing as Wiener invertibility; half-plane points as the whole hull | Bohr-polydisk criterion. |
| Uniform Riesz lower bound for residue modes | Bessel bound; signed convergence. |
| Undersampled companions as derivative payment | Sharp Nyquist price. |
| One admitted damping as finite-curve purity | Zero-chain equivalence. |
| Universal integrated polar domination for log-concave gauges | Exact exceptional sets `{2,3,4,5,7,11,13}`, `{2,3,4,5,7,11}`. |
| Scalar comb energy as charge determination | Signed amplitude completes the reading. |
| Sparse-node blindness as pole control | Line-design enclosures. |
| Finite two-prime Euler lattice positivity below the envelope | Sharp `κ ≥ E_p + E_q`. |
| Gaussian heat coefficient positivity as zero exclusion | Detection below threshold; moving-height tail convergence. |

### 6.3 Retired aliases

| Labels | Present home |
|---|---|
| A, C2/I, D1, N | PA and actual-source trace/moment receivers. |
| AF | Charged boundary separation. |
| AP, IW | Witt/scaling or cyclic clock classifications. |
| B, F, M | Singular carrier constructions. |
| FD2 | GTA's uniform Schur target. |
| G2, H | WD/orientation primitives. |
| HB | PM/PW-B retarded realization. |
| J | Residual jets and determinants. |
| K | TH/RN infinite operators. |
| R | CDC/JAS/WBF/TG wall classes. |
| RBH | PM nonseparated sources. |
| SNR | A source-defined aperture invariant. |

## 7. What would remove a core wall

- **Wall 1:** a source-derived bound inserted into an existing receiver with all tails and quantifiers. Its first instance would be a fixed zero-free strip.
- **Wall 3:** a new exact transfer or sharp classification on a stated class and norm; it proves RH only if the source satisfies the transferred estimate.
- **Wall 14:** an independently constructed carrier, effectivity or weld with faithful landing and the required sign; for ACS, the arithmetic Hasse–Weil bound.

Local progress counts at its actual scale: a larger window, a sharper collar, a new row range or a new reading classification is real progress without removing a family.
