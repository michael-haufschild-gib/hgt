# Research routes and their mathematical obstacles

Status: 29 October 2026, corpus checkpoint `3c5f89e3b2` plus working tree. **RH remains open.** The inventory is 31 live routes, 17 standalone candidates and the PW-B branch of PM. Every live route has an exact RH receiver; none has the arithmetic input that receiver needs.

Companions: [summary, open problems and next questions](obstacles-summary.md) · [walls ledger](walls-ledger.md) · [route unification](route-unification-ledger.md) · [frontier map](../rh-current-frontier-map.md) · [scoped obstructions](../rh-killed-routes.md).

## How to read this report

Evidence: corpus searches, then Lean statements, module docstrings and proof structure. No builds or kernel audits were run. **[L]** and **[S]** follow the [frontier map](../rh-current-frontier-map.md): integrated source at the checkpoint, or working source that is unintegrated or unfinished (HKT, the actual-ζ spectral laws of RAPT and the infinite-pattern laws of ACP are [S] there). **(inference)** marks a conclusion of this review, not a Lean theorem. Research record: [working log](../../../logs/review-2910-research-2026-10-29.md).

Obstacles fall into two classes.

- **A — Just work.** The ingredients exist: a finite computation with certified errors, an instantiation or composition of proved theorems, transport of a supplied bound between proved dictionaries, or formalization of a written proof. A-items can be large. They never promise that a desired sign is true.
- **B — Open mathematics.** A missing inequality, construction or uniformity, tagged by strength:
  - **[RH]** equivalent to RH;
  - **[RH+]** strictly stronger than RH (for example, also forcing simple zeros);
  - **[FS]** equivalent to finitely many off-line zeros, equivalently to RH above some height; implies the Lindelöf hypothesis and a fixed zero-free strip (§8);
  - **[LH]** at least as strong as the Lindelöf hypothesis;
  - **[≥QRH]** implies a fixed zero-free strip \(\Theta<1\);
  - **[open]** an intermediate problem with no known solution, possibly below RH strength.

A conditional receiver does not prove its input.

## The frontier in thirteen results

### 1. Selection is a theorem; the margin is classified and does not select ζ

- **Selection.** A bounded weight \(|\lambda|\le\Lambda\) is eventually positive on atomic families at some root iff RH holds and \(\lambda=\Lambda\) on \(n\ge2\); twin-blind positivity cannot reach an RH-complete family [L]. On one prime's towers, index zero of every tower kernel holds iff RH and \(\lambda=\Lambda\); every \(\lambda\ne\Lambda\) has, unconditionally, a generator with nonzero tower index [S]. [Selection](../../../formal/GaloisForLFunctions/SelectiveMultiscaleArithmeticPositivity/PositivityAtEveryRootSelectsTheVonMangoldtWeight.lean), [tower selection](../../../formal/GaloisForLFunctions/HeckeKreinToeplitz/IndexZeroSelectsTheVonMangoldtWeight.lean).
- **The margin.** On the harmonic hyperplane \(\sum x_n/\sqrt n=0\) the prime form has sharp gap \(2\log2\) [L]. A gauge with harmonic correlation \(c\) keeps gap \(\ge(2\log2)c^2\). Every prime pattern \(P\) has harmonic mean \(c_P=\prod_{p\in P}(p-1)/(p+1)\) [L]. [Sharp gap](../../../formal/GaloisForLFunctions/RenormalizedArithmeticPotentialTheory/TheSpectralGapOfThePrimeFormIsTwoLogTwo.lean), [Euler-product mean](../../../formal/GaloisForLFunctions/ArithmeticCountingPositivity/EveryPrimePatternHasItsEulerProductHarmonicMean.lean).
- **Classification of flips [L].** Finite flip sets have exact secular gaps; a single flip has gap \(2\log2\) iff \(p\ge11\); gaps decrease strictly under proper inclusion; prime-tail flips have gaps \(\ll(\log Q)^{-3}\); cofinite flips have harmonic correlation \(0\), hence gap \(0\), while converging pointwise to the untwisted sign. The maximal gap plus one exact dyadic probe at prime \(2\) selects the empty flip set, within finite flips. [Probe](../../../formal/GaloisForLFunctions/ArithmeticCountingPositivity/OneDyadicProbeSelectsTheFinitePrimeSource.lean), [cofinite](../../../formal/GaloisForLFunctions/ArithmeticCountingPositivity/CofinitePrimeFlipsHaveZeroGap.lean), [maximal flips](../../../formal/GaloisForLFunctions/ArithmeticCountingPositivity/LargePrimeFlipsAttainTheMaximalGap.lean).
- **Actual eigenlines for every pattern [S].** For every prime set \(P\), including zero-density sets, and every conductor \(m\), an actual prime-matrix eigenline converges to the adjunction energy \(E_m\) with squared constraint coordinate converging to the counted conductor coefficient. [Conductor coordinates](../../../formal/GaloisForLFunctions/ArithmeticCountingPositivity/EveryPrimePatternHasActualConductorCoordinates.lean).
- **The margin is the width of an index-one window [S].** The atomic form \(D\delta_1-P\) has window index \(0\), \(1\), \(\ge2\) as \(D\) crosses \(\log N-\gamma\) and \(\log N-\gamma-2\log2\). [Window](../../../formal/GaloisForLFunctions/HeckeKreinToeplitz/TheMarginIsTheWidthOfTheIndexOneWindow.lean).

The margin separates \(\zeta\) from parity twins (Liouville), not from single large-prime flips. Whatever selects \(\zeta\) must see the sign of every prime.

### 2. Index theory of the Weil kernel (Krein–Langer) [S]

The orbit kernel \(K_\zeta\) of the cubic spline on the Hecke lattice \(\mathbb Q_{>0}^\times\) has Gram matrices equal to prime-side Weil Grams. Its index is the number of distinct right zeros, which is even. [Lindelöf stratum](../../../formal/GaloisForLFunctions/HeckeKreinToeplitz/TheFiniteIndexStratumOfZetaIsLindelofDeep.lean), [index formula](../../../formal/GaloisForLFunctions/HeckeKreinToeplitz/HyperbolicPairsAndTheIndexFormula.lean).

| Law | Statement |
|---|---|
| Global law | \(\kappa(K_\zeta)=0\iff\psi(x)-x\le C\sqrt x\log^2x\) eventually; for curve data over \(\mathbb F_q\), \(\kappa=0\iff N_k\ge q^k+1-Cq^{k/2}\). [Global law](../../../formal/GaloisForLFunctions/HeckeKreinToeplitz/TheGlobalLawIsTheOneSidedSquareRootCount.lean) |
| Two primes | Two distinct primes carry the whole index: \(\kappa(K_\zeta|_{\langle p,q\rangle})=\#\)right zeros. |
| One prime | A tower sees the distinct outer eigenvalues \(p^{\rho-1/2}\); it sees every right zero in ordinate windows shorter than \(2\pi/\log p\), and loses at most a factor \(\lfloor H\log p/2\pi\rfloor+1\) in windows of height \(H\). [Nyquist](../../../formal/GaloisForLFunctions/HeckeKreinToeplitz/TheNyquistLawOfAPrimeTower.lean) |
| Blind primes | For \(\kappa\) right zeros at most \(\binom\kappa2\) primes are blind; positivity on infinitely many prime towers forces index zero for every positive kernel plus finitely many pairs. On \(\mathbb Z^2\), positivity on both axes does not imply positivity. [Locality](../../../formal/GaloisForLFunctions/HeckeKreinToeplitz/LocalityFailsButAlmostEveryPrimeDecides.lean), [blind primes](../../../formal/GaloisForLFunctions/HeckeKreinToeplitz/AllButFinitelyManyPrimesSeeTheWholeIndex.lean) |
| Golden calibration | The golden curve has index \(1\) on its own Frobenius tower and index \(\infty\) on the two-prime lattice. [Golden](../../../formal/GaloisForLFunctions/HeckeKreinToeplitz/TheGoldenCurveIsDecidedOnItsTowerButNotOnTheLattice.lean) |
| Price | \(m\) negative squares force \(\mathcal E_{\rm crit}\ge50m^2-3m/2\); \(\kappa\le\lfloor\sqrt{2\mathcal E_{\rm crit}/97}\rfloor\). [Index is energy](../../../formal/GaloisForLFunctions/HeckeKreinToeplitz/IndexIsEnergy.lean) |
| Heat | If \(\kappa<\infty\), the small-time collision mass equals \(2(\kappa+\sum(\text{mult}-1))\); if \(\kappa=\infty\) it tends to \(\infty\). [Heat collisions](../../../formal/GaloisForLFunctions/HeckeKreinToeplitz/HeatCollisionsCountTheIndex.lean) |
| Compression | Compressing by an auxiliary \(P=\sum p_\alpha\delta_{y_\alpha}\) never raises the index; it kills a separated pair iff \(\hat P\) vanishes at the character or its reflection. [Stepanov compressions](../../../formal/GaloisForLFunctions/HeckeKreinToeplitz/StepanovCompressionsAndTheAnnihilationLaw.lean) |
| Integer atoms | RH iff every Weil Gram of cubic-spline atoms at \(\log(i+1)\), \(i<N\), is positive semidefinite; some shrinking schedule carries the whole index. [Integer families](../../../formal/GaloisForLFunctions/HeckeKreinToeplitz/IntegerFamiliesCarryTheWholeIndex.lean) |

Consequence (inference): positivity, counting and index are one statement in three languages. Over \(\mathbb F_q\) the count is produced (Stepanov), over \(\mathbb Z\) it is the WL receiver.

### 3. One-prime tower positivity is RH at every generator size; it needs square-root precision

- RH iff the Weil form is positive on all \(p\)-towers for one fixed prime, also for pole-free \(C^2\) generators supported in \([-\varepsilon,\varepsilon]\) [L]. [One prime](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/OnePrimeSeesTheWholeDefectOfZeta.lean), [pole-free generators](../../../formal/GaloisForLFunctions/SelectiveMultiscaleArithmeticPositivity/TheDyadicSignOfAPoleFreeGeneratorIsRH.lean).
- **Precision rigidity [L].** \(\lambda\) and \(\lambda+\varepsilon n^{-\eta}\), \(0<\eta<\tfrac12\), are never both tower-positive along a nonnegative generator; \(\Lambda\) and the Liouville twin never both. [Rigidity](../../../formal/GaloisForLFunctions/SelectiveMultiscaleArithmeticPositivity/TheDyadicSignIsRigid.lean), [battery](../../../formal/GaloisForLFunctions/HeckeKreinToeplitz/TheSelectivityBatteryOnPrimeTowers.lean).

Consequence (inference): the deciding input must be parity-sensitive, square-root-precise and active at unbounded aperture. Interval statements about primes that survive relative error \(o(1)\) (Brun–Titchmarsh, short-interval prime number theorems, Guth–Maynard's \(x^{17/30+\varepsilon}\) asymptotics) cannot decide it.

### 4. Atomic receivers reach \((\log\log N)^{1+\varepsilon}\) overlap

RH iff \(W\ge0\) eventually on atomic families of width \((\log\log N)^\alpha/N\), every \(\alpha>1\) [L]; integer families at every fixed width carry the whole index [S]. The receiver stops at \(\alpha=1\): compactly supported profiles of Gevrey class \(\le1\) do not exist (quasi-analytic boundary). At every width, \(W\ge0\) on atomic tests iff the Markov form is nonnegative on the pole complement \(p=0\) and \(M+2a_0B\ge0\) on \(p=1\). [Denjoy–Carleman](../../../formal/GaloisForLFunctions/SpacingScaleHarmonicAnalysis/TheDenjoyCarlemanProfiles.lean), [gap and one scalar](../../../formal/GaloisForLFunctions/ArithmeticLorentzianGeometry/TheHodgeIndexIsAGapOnThePoleComplementAndOneScalar.lean).

### 5. Narrow positivity reaches a quarter of Robin–Euler; the separated regime has an actual spectral law

- Full positivity on window tests at widths \(\le K_\star\delta_N\), \(K_\star\approx0.108\) for plateau profiles (a quarter of the Robin–Euler ratio \(K_1\approx0.43\)); with absolute values on the pole term the method stays below about half of \(K_1\). [Quarter](../../../formal/GaloisForLFunctions/ArithmeticLorentzianGeometry/TheStabilityRegimeReachesAQuarterOfTheRobinEulerThreshold.lean).
- On the whole separated regime \(0<c<1\): the complete Weil matrix splits exactly at the spacing; Ramanujan trial energies are simple and proper [L]; each conductor has one simple actual complete-Weil eigenline converging to its Ramanujan line, with energy \(F_\varphi(c)+E_m-\gamma+\alpha\,1_{m=1}\) [S]. [Splitting](../../../formal/GaloisForLFunctions/RenormalizedArithmeticPotentialTheory/TheFullWeilMatrixSplitsAtTheSpacing.lean), [eigenlines](../../../formal/GaloisForLFunctions/RenormalizedArithmeticPotentialTheory/TheSimpleCompleteWeilEigenlinesConvergeToRamanujanLines.lean).
- Open: the bottom of the actual spectrum past \(K_1\) uniformly in conductor and energy, and the sign of the full form there.

### 6. The complete source: the finite-index chain ends at the first prime layer

- Complete logarithmic cells form a dyadic multiresolution \(C_{2a}+C_{2a+1}=T_{\log2}C_a\) [L]. Gamma pays all detail mass; balanced sections above one index carry a twin-blind floor [L]. Each individual complete Haar cell has original Weil energy \(\ge\tfrac1{10}\) of its mass, because no prime lag couples a cell to itself [S]. [Floor](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/HaarCellEffectivity.lean), [single cells](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/EveryHaarCellHasPositiveWeilEnergy.lean).
- **Uniform finite index, layer by layer.** Exponents \(k\ge3\); prime two; every finite prime set; the full even-power source with its pole together with odd powers \(k\ge3\): \(\operatorname{ind}(\Gamma-S_2-M_{\rm odd})\le A+1\) [L]. Beyond one head the full-polar nonfirst source retains \((1-\varepsilon)\Gamma+2\cosh^2-2\sinh^2\) [S]. [Squares and odd powers](../../../formal/GaloisForLFunctions/ArithmeticIndexDescent/SquaresAndOddHigherMixedPowersHaveUniformFiniteIndex.lean), [nonfirst reserve](../../../formal/GaloisForLFunctions/ArithmeticIndexDescent/TheFullNonfirstSourceRetainsAlmostAllGamma.lean).
- **What remains:** the first prime layer \(k=1\) over all primes (absolute constant \(\sum_p\log p/\sqrt p\) diverges), odd diagonals, finite heads, coarse error, poles and archimedean mass. Full prime–polar cancellation holds only with an \(e^R\) loss [S]. Uniform finite index of the complete form is [FS]. [Prime–polar](../../../formal/GaloisForLFunctions/ArithmeticIndexDescent/TheFullPrimePolarSourceCancelsInGammaNorm.lean).
- Cross-level couplings: pole rank two and removable, Gamma \(\pi4^{-(d-1)}\), touching levels uniform; the prime part is the Chebyshev sequence \(d\mapsto W(f,T_{d\log2}g)\), almost periodic under RH and never summable (inference). Its positivity is §3, which is RH.

### 7. Ordered entries are centered Chebyshev integrals

For \(\operatorname{supp}f<b<\operatorname{supp}g\) and every \(c\): \(W(f,g)=-\int_0^\infty(e^h-\psi(e^h)-c)\,q'_{f,g}(h)\,dh-\Gamma_{\rm tail}(f,g)\). The Gamma boundary operator has norm \(\pi/2\), no maximizer and no uniform relative reserve [S]. [Chebyshev identity](../../../formal/GaloisForLFunctions/ArithmeticIndexDescent/TheOrderedWeilSourceIsACenteredChebyshevDefect.lean).

### 8. Finite off-line support is RH above a height, and contains Lindelöf

- **TFAE [S]** for any two distinct primes: \(\kappa(K_\zeta)<\infty\); \(\kappa\) on the two-prime lattice \(<\infty\); finitely many off-line zeros; nonreal zero counts of \(H_t\) bounded for \(t>0\); all zeros above some height \(T_0\) critical. [TFAE](../../../formal/GaloisForLFunctions/HeckeKreinToeplitz/TheFiniteIndexStratumOfZetaIsLindelofDeep.lean).
- **Strata [L].** RH \(\Rightarrow\) finite support \(\Rightarrow\) zeros approach the line \(\iff\) LH \(\wedge\) (\(\cos(hD)\Xi\) has finitely many nonreal zeros, all \(h>0\)) \(\Rightarrow\) LH \(\wedge\) \(\Theta<1\). Backlund: LH iff off-line zeros are sparse (\(o(\log t)\) per unit window at fixed depth). [Depth](../../../formal/GaloisForLFunctions/RHTower/LindelofCosineFiniteDefectDepth.lean), [Backlund](../../../formal/GaloisForLFunctions/RHTower/LindelofOpenImpliesCriticalLine.lean).
- **Other exact receivers.** Finite \(\mathcal E_{\rm crit}\) and bounded source work; subtracted lag bounded on one side; bounded cosine defects [L/S].
- Consequence (inference): finite support with an effective \(T_0\) below the numerically verified height is RH. Finite support is RH-hard at large height, which is where every difficulty lives.

### 9. Heat flow

For \(0<t\le1/8\), zeros of \(H_t\) with \(|\operatorname{Re}z|\ge2\pi e^{(2/3+\varepsilon)/t}\) are real and simple [L]. Off-line zeros of depth \(\ge d\) in \([X,2X]\) number at most \(C\log X\cdot N(t)\) whenever \(t\log X\le cd^2\), constants uniform in \(d\) [L]. A polynomial bound \(N(t)\le At^{-a}\) would give polylogarithmic deep counts, not finiteness [L]. Localized energy evolution: local force, forward simplicity and pair-force bounds proved; the evolution estimate is unfinished [S]. [Horizon](../../../formal/GaloisForLFunctions/RHTower/KiKimLeeTwoThirdsHorizon.lean), [uniform depth](../../../formal/GaloisForLFunctions/RHTower/Heat/HeatUniformDepthZeroDensity.lean), [polynomial counts](../../../formal/GaloisForLFunctions/RHTower/DeepOffLineZerosAreCountedByTheHeatFlow.lean).

### 10. Critical-line census: two thirds, the exchange rates, and their prices

| Census statement | Value |
|---|---|
| Simple critical zeros | \(\ge HD(1)+10^{-8}\approx0.67250071\) [L] |
| Simple **or** critical zero copies | \(\ge0.8876\) [L] |
| Distinct ordinates carrying a critical zero | \(\ge4/5\) [L] |
| Zero copies within \(4/\log T\) of the line | \(\ge3/4\) [L] |

- **Bandwidth exchange [L].** Proportion \(2-\phi(\lambda)\); at \(\lambda=1+\delta\) the gain over \(2/3\) is \(\delta(2-(3E-4)\delta)/(3(1+\delta)^2)\). \(E(1/9)\le4\) gives exactly \(+1/30\), i.e. \(70\%\). [Narrow strip](../../../formal/GaloisForLFunctions/TransThresholdPairCorrelation/NarrowStripClosePairEnergyAndExchangeRate.lean).
- **Capacity law [L].** In the \(c=2\) rank–trace capacity \(2-\kappa\): \(3/4\iff\kappa\le5/4\) (hence \(70\%\iff\kappa\le13/10\), inference). At bandwidth \(4/3\) the diagonal, archimedean and pole constant is \(43/36=5/4-1/18\) unconditionally, the prime–pole cross term is \(O(T^{5/6}\log^2T)\), and a prime surplus \(\le N/18\) (`PrimeSurplusFourThirds`) gives \(75\%\) simple critical zeros. [Two routes to 3/4](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/BreakingTheCoalescenceBlindSpotAndThreeQuarters.lean).
- **Zero-side spectral slack [L].** \((H(\lambda)-\varepsilon)N+\text{zeroSideSlack}\le N_0^*\) for every \(\lambda<1\), \(H(\lambda)=2-1/\lambda-\lambda/3\). The grid-dimension ceiling \(\text{zeroSideSlack}\le(\lambda-H(\lambda)+\varepsilon)N\) makes the \(3/4\) hypothesis false for every \(\lambda<3/4\). For displaced off-line pairs at \(\kappa=4/3\), the slack reaches \(N/12\) iff the displacement parameter \(\eta\ge1/6\); an explicit non-coalesced configuration (\(s_1=179\), \(p=32\), \(\eta=1/16\)) has slack below \(N/12\) and proportion \(179/243<3/4\). [Slack conservation](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/SpectralSlackConservationAndTheHyperbolicDisplacementThreshold.lean).
- **Price.** Beyond bandwidth one the prime side is a signed sum over coalescent prime pairs whose Poisson term cancels only against the exact Hardy–Littlewood term [L]; one-sided sieves give nothing, two-sided asymptotics are parity problems (inference). Value moments are depth-blind [L]; the shallow Cauchy energy is \(O(N)\) with a majorant that counts all zeros [L]. [Coalescent anatomy](../../../formal/GaloisForLFunctions/TransThresholdPairCorrelation/CoalescentSieveAnatomyAndModelCalibration.lean).

### 11. Quasi-RH: translation and density complete, production absent

- Fixed-strip dictionaries are exact: escaped Möbius rates, Hecke-defect caps, theta-prefix growth, uniform Vaughan power savings, the Möbius-divisor Abel moment and its quotient head, Suzuki finite-contact residuals [L]; balanced-regime short-window Möbius or prime power savings \(\iff\Theta<1\) [L]; the strip \([1/4,3/4]\) iff the normalized Chebyshev Cesàro mean-square energy is \(\ll N^{3/2+\varepsilon}\) [L]. [Abscissa laws](../../../formal/GaloisForLFunctions/RHTower/QuasiRHQuotientHeadAndFiniteContactAbscissaLaw.lean), [short windows](../../../formal/GaloisForLFunctions/ReflectiveDirichletPolynomialS2/ShortWindowDispersionAtSeventeenThirtieths.lean), [Cesàro](../../../formal/GaloisForLFunctions/RHTower/QuasiRHNormalizedChebyshevCesaroAndMertensActionAbscissaLaw.lean).
- **Density inputs [L].** Guth–Maynard Theorem 1.1 is proved: \(N(\sigma,T)\ll T^{(30/13)(1-\sigma)+\varepsilon}\) on \([1/2,5/6]\); the density hypothesis on \(\sigma\ge5/6\); primes in \((x,x+x^{17/30+\varepsilon}]\) with the asymptotic; almost all intervals of length \(x^{\theta}\), \(\theta>2/15\). Vinogradov–Korobov zero-free region. A density envelope never drops below \(1\), so no density bound forces a zero-free region. [Guth–Maynard](../../../formal/GaloisForLFunctions/RHTower/Sieve/GuthMaynardTheoremOneOne.lean), [corollaries](../../../formal/GaloisForLFunctions/RHTower/GuthMaynardCorollariesUnconditional.lean), [envelope](../../../formal/GaloisForLFunctions/RHTower/DensityEnvelopeNoGo.lean).
- The Chen–Gupta–Li intake (279 modules) has detector and density components and no zero-free capstone [E].

### 12. Over finite fields the local-to-global step is a count

Trickle-down on every Frobenius ladder \(\iff\) one-sided square-root count; hyperelliptic curves pass by Stepanov's count; the golden fake fails [L]. Over \(\mathbb Z\), \(1-T_p^N\) annihilates a zero symbol iff the zero is critical and on a height lattice [L]. Hyperbolicity of the atomic Gram holds for every sign twin; the Metzler sign is selective [L]. [Count](../../../formal/GaloisForLFunctions/ArithmeticLorentzianGeometry/TheTrickleDownInequalityIsTheSquareRootCount.lean), [Stepanov mechanism](../../../formal/GaloisForLFunctions/ArithmeticCorrespondencePositivity/SparseAnnihilatorsAndTheStepanovMechanism.lean).

### 13. Number-field foundations

Hecke characters split into finite characters and real parities; Hecke ideal theta has finite Fourier dual, exponential tails, unit-domain Mellin continuation, reflection and residues; global units unfold with the exact radial logarithmic Jacobian [L]; logarithmic Gaussian integrals give the real and complex Gamma factors [S]. Missing: identification of the unfolded Mellin integrals with normalized Hecke \(L\)-series and the full functional equation. These are tools; they carry no selective sign. [Theta continuation](../../../formal/GaloisForLFunctions/HeckeLFunctions/HeckeThetaHasMellinContinuation.lean).

## Live routes

Each entry gives the current state, then **A** (just work) and **B** (open).

### WL — Weil lag / prime-error energy

**Current:** Bounded critical-deficit energy, coprime cross-work floors and a linear cumulative prime-error energy budget are each RH-equivalent; eventual \(\psi(x)-x\le C\sqrt x\log^2x\) is RH-equivalent and is the HKT global law \(\kappa(K_\zeta)=0\) [S]. Abel-slope saturation at the archimedean genus is RH plus simple zeros. The prime error is the separated off-diagonal of the complete form (§7) and the unpaid cross-level coupling (§6). The tensor square \((\psi(x)-x)^2\) returns the mean-square receiver with abscissa \(2\Theta\) (inference).

**A:** Certified fixed truncations with archimedean and high-zero tails; lag/count/energy dictionaries with constants; tabulate \(d\mapsto W(f,T_{d\log2}g)\).

**B:** The one-sided prime-error or cross-work bound **[RH]**; subtracted lag **[FS]**; genus saturation **[RH+]**. [Receiver](../../../formal/GaloisForLFunctions/BiScaleUncertainty/WeilLagCriticalDeficitEndpointAndLimitLaw.lean).

### RW — Restricted Weil ground energy

**Current:** RH iff the ground minimum is positive at every finite aperture; the minimum strictly decreases with an exact shell decomposition; finite-aperture Gårding allows a nonzero index; positive floors must decay doubly exponentially; Gamma boundary norm \(\pi/2\) without uniform relative reserve [S].

**A:** Certified finite-aperture variational bounds and shell ledgers; the Gamma square reserve in the shell flux.

**B:** Cumulative aperture relaxation bounded by the initial energy, paying low modes, prime collars and polar terms **[RH]**. [Aperture flow](../../../formal/GaloisForLFunctions/ArithmeticContinuationAndCriticalEnergy/TheApertureFlowNeverStalls.lean).

### FU — Signed prime scheduling

**Current:** An eventual upper bound on the normalized completed Abel moment is RH-equivalent; narrow translated prime channels have a useful sign, wide-window channels can be positive [S].

**A:** Seed, drift, earlier-history, cross-block and endpoint ledgers for fixed schedules.

**B:** The joint signed total over a prime-exhaustive schedule **[RH]**. [Receiver](../../../formal/GaloisForLFunctions/RHTower/CCM/CCMFUSuzukiMobiusDivisorOneSided.lean).

### RP — Matched-quantile history floor

**Current:** RH iff an eventual floor \(-B(K+2)\); unconditionally the history drops below \(-\delta(K+2)\) cofinally, so no sublinear floor exists. Low-LCM payment and signed identities. [Floor](../../../formal/GaloisForLFunctions/RHTower/SPEQuantileRieszRoutePLinearFloorCriterion.lean), [escape](../../../formal/GaloisForLFunctions/RHTower/SPEQuantileRieszRoutePLinearHistoryEscape.lean).

**A:** Fixed histories; low-LCM instantiation; the escape constant \(\delta\) on computed ranges.

**B:** A linear floor paying high-LCM pairs, moving core and singular-domain transport together **[RH]**.

### PA — Prime–archimedean passivity

**Current:** Current-sign, Bernstein-mismatch and signed compact-moment receivers; each fixed moment order is positive after a large shift; first-atom moments by quadrature leave one analytic tail estimate. [High-order moments](../../../formal/GaloisForLFunctions/RHTower/PrimeArchThetaFirstAtomHighOrderMomentBounds.lean).

**A:** The remaining analytic tail; further atoms; explicit thresholds for finite order blocks.

**B:** All-order/all-shift sign, high-frequency accretivity, or an every-positive-rate mismatch bound **[RH]**.

### MC — Möbius cancellation

**Current:** Every strict half-power cancellation bound and subpower Hilbert energy are RH-equivalent; fixed strips have complete dictionaries (§11); Vinogradov–Korobov gives no fixed power saving; a linear Mertens budget forces RH and simple zeros. Inputs available: Guth–Maynard density and short-interval primes at \(x^{17/30+\varepsilon}\) [L], both at relative precision \(o(1)\).

**A:** Fixed-modulus and below-diagonal estimates; rate normalizations; translate any supplied strip bound through every dictionary.

**B:** Every strict half-power **[RH]**; the linear Mertens budget **[RH+]**; any fixed one-sided power saving, including a short-window power saving in the balanced regime **[≥QRH]**. [Hilbert criterion](../../../formal/GaloisForLFunctions/RHTower/MobiusHilbertFormEquivalence.lean).

### TT — Theta tails and directed covariance

**Current:** Seam, Wold and odd-Weil receivers with the sub-half range explicit; restricted current signs; continuum light-cone positivity.

**A:** Fixed directed-covariance and reflected-prime terms; continuum and short-support identities.

**B:** Signed nonlocal covariance at every rapidity and scale, or complete odd/primitive positivity **[RH]**. [Wold receiver](../../../formal/GaloisForLFunctions/RHTower/PaperWoldDirectedCovarianceRH.lean).

### LA — Line anchor / Jensen and heat signs

**Current:** Finite-head/heat receivers and positive complementary tails; ordinary \(\xi\) coefficients Turán [L] and Lorentzian [S]; Jensen–Laguerre on \(s\ge0\); local cofactor \(\xi=P\cdot g\) with \(\deg P=O(\log T)\); reality horizon \(2\pi e^{(2/3+\varepsilon)/t}\) [L].

**A:** Certified finite heads and low degrees; coefficient conventions; heat-tail errors with the local cofactor.

**B:** All-height/all-degree head signs, including low orders and near-double configurations **[RH]**; uniform heat count **[FS]**. [Finite-head reduction](../../../formal/GaloisForLFunctions/RHTower/XiSliceHeatFiniteHeadReduction.lean).

### TG — Integer trace below one

**Current:** Winding, cubic transgression and central-gap receivers; Gaussian coprime-divisibility covariance signs on indicators.

**A:** Finite projection/transgression data with residual and trace kept apart.

**B:** A matrix-complete decomposition with nonnegative residual and integer trace below one on every disc, or a zero-rate central-gap bound **[RH]**. [Index estimate](../../../formal/GaloisForLFunctions/RHTower/RestrictedProjectionIndexOperatorNormCriterion.lean).

### HF — Arithmetic Hodge positivity

**Current:** Full Hodge/Weil sign, zero Hecke defect and small source work are exact receivers. The complete source has the multiresolution, a twin-blind floor, single-cell floors [S] and uniform finite index on every layer except \(k=1\) (§6). Index equals right-zero count and is priced by \(\mathcal E_{\rm crit}\) (§2). The margin is classified and does not select \(\zeta\) (§1).

**A:** Complete-cell Grams in multiresolution coordinates; explicit head sizes; first-layer constants \(C_P\) along growing prime sets.

**B:**
- Complete residual sign, complete-cell index zero, or a work ceiling at an RH threshold **[RH]**.
- Uniform finite index, finite \(\mathcal E_{\rm crit}\) **[FS]**.
- Selective positivity in the separated regime beyond Robin–Euler **[open]** (Q1).

[Index capture](../../../formal/GaloisForLFunctions/ArithmeticIndexDescent/TheCompleteCellsCaptureEveryFiniteIndex.lean), [work threshold](../../../formal/GaloisForLFunctions/ArithmeticIndexDescent/TheSourceWorkHasAClosedQuantumThreshold.lean).

### CHMD — Causal hyperbolic–modular duality

**Current:** Wave/Doob receivers; completed aperture core; residual radical equals Weil radical; ordered entries are Chebyshev integrals; finite generator orbits approximate cell sources in \(L^2\) but are not compact.

**A:** Domain/cutoff theorems on fixed sources; signed residual with the primitive defect; bounded-window transport.

**B:** The complete one-sided wave bound or odd Doob/nodal inequality **[RH]**. [Odd criterion](../../../formal/GaloisForLFunctions/RHTower/CHMDOddSectorCriterion.lean).

### TH — Theta moment positivity

**Current:** All ranks strictly positive on nonnegative coefficient vectors at one common small time; fixed-rank stable regions.

**A:** Finite signed blocks with explicit degree/time dependence.

**B:** Signed vectors at every degree under one common time **[RH]**. [Orthant theorem](../../../formal/GaloisForLFunctions/RHTower/XiHeatHankelFormOrthantPositivity.lean).

### RN — Renewal and singular comparison

**Current:** Theta renewal solvers, a compact cone-positive operator, exact determinant resonances.

**A:** Finite packet/resolvent data in the admitted topology with cusp/seam terms.

**B:** Directed boundary-work orientation, or mixed prime-plus-Gamma versus pole **[RH]**; cone positivity does not give real spectrum. [Exact spectrum](../../../formal/GaloisForLFunctions/RHTower/ThetaRenewalFredholmSpectrum.lean).

### WD — Ward caps and collision

**Current:** A nonnegative integrated cap vanishes iff RH; Hermite heat-repair costs; shallow Cauchy energy \(O(N)\) at depth \(1/\log T\) [L]; uniform-depth heat counting and the \(2/3\) reality horizon [L] (§9). Finite support iff bounded heat counts; small-time collision mass is \(2\times\)(index plus multiplicity excess) [S].

**A:** Cap/head data on compact regions; explicit \(N(t)\) bounds on compact time ranges; shallow-energy constants; the localized energy evolution estimate.

**B:** Cap extinction or all-height coefficient sign as \(t\downarrow0\) **[RH]**; uniform nonreal count **[FS]**; uniform high count **[LH]**. [Ward receiver](../../../formal/GaloisForLFunctions/RHTower/XiWardGlobalCapAndFiniteHeadArithmetic.lean).

### LI — Paired Li balances

**Current:** Every-positive-rate floors for the prime–Gamma clock are RH-equivalent; RH is primitive nonpositivity of the Cayley–Li Toeplitz ladder, whose couplings do not decay [S].

**A:** Fixed paired histories; finite Cayley ladders.

**B:** A subexponential floor for the literal primitive, or an arithmetic proof of the ladder sign **[RH]**. [Cayley ladder](../../../formal/GaloisForLFunctions/ArithmeticLorentzianGeometry/RHIsReflectionPositivityOfTheCayleyLadder.lean).

### SZ — Suzuki first variation

**Current:** Compact-\(L^2\) first variation equals the full Weil form; RH iff nonnegativity on factorial and grid tent families with all terms retained [S].

**A:** Moving-aperture limits on specified tent families.

**B:** The sign on the tent families **[RH]**. [RH-complete transfer](../../../formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiCriticalRHCompleteFamilyTransfer.lean).

### PM — Haar approximation / damped admission

**Current:** Global Haar approximation, cofinal signed-damping admission and positive gauge mass for every escape state are exact receivers; record-minimum limits still permit zero gauge mass. [Record minima](../../../formal/GaloisForLFunctions/ArithmeticDefectRigidity/RecordMinimaForceInfiniteCofactorLimits.lean).

**A:** Fixed compact cofactor Grams; energy-transfer formulas with effective pole orders.

**B:** Positive gauge mass for every escape state or a complete-energy bound as damping \(\to0\) **[RH]**; exterior tightness **[open]**. [Haar receiver](../../../formal/GaloisForLFunctions/RHTower/FermiNymanHaarApproximationEquivalence.lean).

### JAS — Joint ancestry

**Current:** Level-one prime-product positivity and finite-power square-shell bounds are receivers; unconditional signs reach a logarithmic prime budget.

**A:** Support/grade formulas; budget gaps on chosen shells.

**B:** The half-power prime budget or all-amplitude shell control **[RH]**. [Capstones](../../../formal/GaloisForLFunctions/RHTower/JointAncestryLevelOneCapstones.lean).

### CTF — Chronological / Báez–Duarte approximation

**Current:** Residual \(=(1-\Lambda\text{-readout})^2+\)centered pronic energy; vanishing error is RH-equivalent.

**A:** Optimized finite rows with both components reported.

**B:** Bounded rows with complete error \(\to0\), or the dual-sampling bound **[RH]**. [Readout criterion](../../../formal/GaloisForLFunctions/BezoutValuationIncidence/VonMangoldtReadoutFormOfTheBaezDuarteCriterion.lean).

### HCF — Gaussian heat trace and two-grid signs

**Current:** Exact archimedean-minus-prime Gaussian traces; positivity on both literal \(\log2/\log3\) grids with polar cancellation is RH-equivalent; one grid aliases. In HKT language: one prime tower hides exactly the aliasing classes, two prime lattices carry the whole index [S]. [Two grids](../../../formal/GaloisForLFunctions/HeckeKreinToeplitz/OneGridHidesTwoGridsDecide.lean).

**A:** Finite degrees/heights on both grids with explicit errors.

**B:** Both grid signs at all degrees and heights **[RH]**. [Two-grid receiver](../../../formal/GaloisForLFunctions/RHTower/XiGaussianHeatTwoPrimeSourceSampling.lean).

### XN — Newton invariant discs

**Current:** Line-centred self-map discs covering all zeros give RH; exact curvature formula for the interior margin.

**A:** Certified discs and curvature integrals.

**B:** A covering family with nonnegative interior margin **[RH]**. [Disc criterion](../../../formal/GaloisForLFunctions/RHTower/XiNewtonSchwarzPickCriticalLine.lean).

### BAG — Deterministic self-return

**Current:** Actual-\(\zeta\) recurrence through the right strip, or positive Haar mass, is an RH receiver.

**A:** Finite-head return estimates on zero-free compact targets.

**B:** Recurrence at every right-strip point and tolerance **[RH]**. [Return receiver](../../../formal/GaloisForLFunctions/RHTower/ZetaStrongRecurrenceReceiver.lean).

### EWU — Even pole-weight uniqueness

**Current:** Attained even blind minima give an all-aperture criterion; positivity in high windows and locally through radius \(181/500\); RH iff for every aperture some real weights make \(\zeta\)'s full Weil functional nonnegative up to that aperture [L].

**A:** Certified finite even blind problems; finite-level feasibility.

**B:** Nonnegative blind minima at every aperture **[RH]**. [Existence form](../../../formal/GaloisForLFunctions/RHTower/WeilPositivityFiniteLevelExistenceDecidesRH.lean).

### GTA — Transverse Schur charge

**Current:** Rank-uniform decay of the quartic Schur charge is RH-equivalent.

**A:** Finite-rank charges.

**B:** Rank-uniform transverse decay **[RH]**. [Decay equivalence](../../../formal/GaloisForLFunctions/RHTower/Hedenmalm/HedenmalmThetaSchurQuarticSpectralDecayEquivalence.lean).

### OWU — Odd Weil-weight uniqueness

**Current:** Odd/pole-hyperplane and dilation-ray criteria; smooth odd witnesses separate \(\Lambda\) from Liouville and the first-prime flip at radii \(181/500\) and \(23/40\). These are finite-aperture separations that persist under small \(n^{-\eta}\) perturbations, so they cannot decide (§3).

**A:** Collar accounting with signed autocorrelations and both pole corrections.

**B:** The all-aperture odd sign **[RH]**; conductor/forcing incompatibility **[open]**. [Dilation criterion](../../../formal/GaloisForLFunctions/RHTower/WeilDilationRayCriterion.lean).

### PBM — Pole-regularized prime series

**Current:** Convergence of pole-subtracted coefficients at every real \(\sigma>1/2\) is RH-equivalent.

**A:** Regularized partial sums in controlled half-planes.

**B:** Critical-abscissa cancellation **[RH]**; any fixed abscissa \(<1\) **[≥QRH]**. [Criterion](../../../formal/GaloisForLFunctions/RHTower/RegularizedLogZetaAbscissa.lean).

### RB — Robin / Nicolas extremizers

**Current:** Eventual criteria; reduction to colossally abundant integers; valuation-defect margins.

**A:** Certified finite extremal ranges.

**B:** The moving remainder on prime-saturated extremizers **[RH]**. [CA reduction](../../../formal/GaloisForLFunctions/RHTower/RobinColossallyAbundantReduction.lean).

### SRT — Lag localization and atomic visibility

**Current:** Every-width lag bounds; atomic receivers at \((\log\log N)^\alpha/N\), \(\alpha>1\) [L]; integer atoms at fixed width carry the whole index [S]; one-prime tower positivity of every small pole-free generator is RH [L]; tower Nyquist law [S].

**A:** Fixed-width detectors; atomic Grams between \(K_\star\) and the first excitation with Markov, full and pole-hyperplane forms apart.

**B:** Late-lag bound, all-generator tower bound, or full sign at unbounded overlap **[RH]**; full sign at a fixed separated ratio beyond Robin–Euler **[open]** (Q1); an explicit shrinking full-index schedule **[open]**. [Lag receiver](../../../formal/GaloisForLFunctions/SquareRootThreshold/EveryWidthDecidesTheCriticalLine.lean).

### ACT — One-shift arithmetic criticality

**Current:** One fixed theta shift with a full all-profile variation inequality gives odd positivity and RH; short collars are absorbed with support-dependent shifts.

**A:** Signed moment ledgers for prescribed profiles and shifts.

**B:** One shift paying every support and profile **[RH]**. [Short-profile scope](../../../formal/GaloisForLFunctions/ArithmeticCriticalityTheory/ShortProfilePoleFreeVariationInequality.lean).

### AIP — Arithmetic incidence allocation

**Current:** Global joint allocation is the odd sign. The route shares the complete-cell transfer, the atomic receiver, the finite-index chain, selection and margin, the gap/scalar reduction and the separated-regime eigenlines (§§1, 4–6).

**A:** Complete incidence matrices in multiresolution coordinates; touching-level costs against the margin.

**B:** Signed allocation on source-complete cells **[RH]**; the selective separated-regime step **[open]** (Q1). [Allocation criterion](../../../formal/GaloisForLFunctions/ArithmeticIncidencePositivity/GlobalIncidenceAllocationCondition.lean).

### ACS — Arithmetic effectivity and the census

**Current:** Source RR, effectivity, Rosati-height and chirality receivers; complete-cell realization and index capture; the one-prime tower law; single-cell floors [S]. The census module carries the rank–trace exchange rates, the \(\kappa\le5/4\) capacity law and the slack conservation calculus (§10).

**A:** Fixed source families in complete cells; projection and finite-sieve data; the slack calculus at \(\lambda\in[3/4,1)\).

**B:** Full-source quadratic RI with degree-zero subquadratic growth, a Rosati-height lower bound, or complete-cell index zero **[RH]**; uniform finite index **[FS]**; a census input beyond \(2/3\): prime surplus \(\le N/18\) at bandwidth \(4/3\), or zero-side slack \(\ge N/12\) **[open]**. [Effectivity receiver](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/ExactArithmeticSourceEffectivity.lean).

## Route candidates and promotion obstacles

A candidate lacks an independent source construction or its landing. Every promotion gap is **[open]** and becomes **[RH]** once it is the final sign. A sufficient hypothesis must fail for the battery: the Liouville twin, single-prime flips with the maximal margin, \(\Lambda+\varepsilon n^{-\eta}\), the golden curve and over-regular Beurling systems.

| Candidate | Established mechanism | A — Just work | B — Promotion gap |
|---|---|---|---|
| **APF** Arithmetic paired Fredholm | Cycle traces have arithmetic Fourier reconstruction. | Fixed cycles and mixtures with truncation control. | Zero-independent divisor exhaustion and trace vanishing. [Source](../../../formal/GaloisForLFunctions/RHTower/PaperZetaCycleFourierReconstruction.lean) |
| **BSH** Arithmetic mate curvature | Framed curvature vanishes at critical half-density. | Finite curvature/cocycle identities. | A pre-divisor section and mate identity forcing the vanishing. [Source](../../../formal/GaloisForLFunctions/RHTower/Deninger/DeningerOneSidedFramedMateCurvatureTransgression.lean) |
| **CDC** Constitutive dagger | Calibrated confluent potentials exist exactly on the line. | Finite repair/exchange defects. | One arithmetic potential descending on every fibre. [Source](../../../formal/GaloisForLFunctions/RHTower/ConstitutiveDaggerConfluence.lean) |
| **DR** Dyadic roots | Dyadic levels reach the Littlewood zero-free cusp. | Roots on known zero-free charts. | Compatible extension to the whole strict-right domain. [Source](../../../formal/GaloisForLFunctions/RHTower/XiSymmetricLittlewoodZeroFreeCuspDyadicRoots.lean) |
| **EGC** Pole-safe contour | Complete copy correction; nonzero Gamma baseline. | Corrected contours. | Outer-contour orientation excluding off-line copies. [Source](../../../formal/GaloisForLFunctions/RHTower/PaperEGCSourceRayBaseline.lean) |
| **EWJ** Euler/Wold jets | Three-channel histories converge; compact quotient character. | Fixed jets. | Source admission and norm exhaustion across depth. [Source](../../../formal/GaloisForLFunctions/RHTower/PaperEulerWoldDepthHistory.lean) |
| **FEL** Theta likelihood | Entropy bookkeeping; convergent BSY zero sum. | Predeclared finite histories. | Cofinal balance from arithmetic, independent of zeros. [Source](../../../formal/GaloisForLFunctions/RHTower/BalazardSaiasYorZeroSum.lean) |
| **HJ** Hurwitz reflection | Two-seed residual equals SEC charge; HCF bridge. | Convergent fibres. | Pre-divisor forcing of residual vanishing. [Source](../../../formal/GaloisForLFunctions/RHTower/PrimeTailSeedHurwitzReflection.lean) |
| **IRK** Rotation-algebra trace | Completed Xi-jet relation invertible exactly off the line. | Finite jet inverses. | Charged arithmetic Poisson lift with integral count. [Source](../../../formal/GaloisForLFunctions/RHTower/PrimeRotationXiCompletedResolution.lean) |
| **MSC** Möbius–Sonin transport | Squarefree Hilbert source recovers moments. | Evaluation jets. | Source-faithful nonnegative Sonin/Weil energy. [Source](../../../formal/GaloisForLFunctions/RHTower/SquarefreeDiscrepancyHilbertTransport.lean) |
| **PCS** Singular prime co-shift | Shift-plus-defect decomposition; strong finite-prime convergence. | Retained defect and cutoff errors. | Wall annihilation retaining the forward mode. [Source](../../../formal/GaloisForLFunctions/RHTower/PCSChronologicalDilationCarrierObstruction.lean) |
| **PTR** Photonic realization | Lossless products real-rooted; Xi-limit criterion; gapless realization law. | Finite stacks. | Prime-faithful nonlocal port built without Xi zeros. [Source](../../../formal/GaloisForLFunctions/RHTower/PhotonicLosslessProductPortRH.lean) |
| **RFHM** Support/grade forcing | Full support/phase/grade admission. | Coherent defects. | A source law sensitive to phase/depth orientation. [Source](../../../formal/GaloisForLFunctions/RHTower/PaperRFHMSurvivalInformation.lean) |
| **SC** Stokes/Witt–Krein | Rigged chambers; finite-index = positive minus finite rank [S]. | Finite cross-fibre coordinates. | A cross-fibre index selecting the wall; a finite index would only reach [FS]. [Source](../../../formal/GaloisForLFunctions/RHTower/PaperKreinWallFourierCompletion.lean) |
| **SEC** Adjacent prime seam | Seam-charge/essential-norm and Fock criteria. | Finite jets and seam charges. | All-order Fock boundedness or eventual compactness. [Source](../../../formal/GaloisForLFunctions/RHTower/TimeOneGammaJetFockRHCriterion.lean) |
| **W1C** Clifford–Dirac / Lee–Yang | Ferromagnetic Ising limits to Riemann's law force RH. | Finite couplings. | Source-defined centred couplings; a Bohr-torus Lee–Yang lift is the natural landing. [Source](../../../formal/GaloisForLFunctions/RHTower/IsingLawConvergenceRH.lean) |
| **WBF** Source certificates | Abstract genealogy Gram and Fredholm recovery. | Certificate streams. | Arithmetic stream with uniform-depth landing. [Source](../../../formal/GaloisForLFunctions/HTGeometry/PaperCriticalGenealogyCompletion.lean) |
| **PW-B** PM cusp branch | Native two-response action with cutoff-independent limit. | Positive-damping actions. | Remove zero indexing; ceiling→optical→cap→extinction chain. [Source](../../../formal/GaloisForLFunctions/RHTower/ThetaCusp/ThetaCuspHawkingBMPWNativeTwoResponseAction.lean) |

## Supporting programmes

| Programme | Contribution | Unresolved input |
|---|---|---|
| HKT | Index theory of \(K_\zeta\): global law, two-prime and Nyquist laws, blind primes, golden calibration, index–energy price, heat collisions, compressions [S] | An index ceiling from local data (arithmetic Krein–Langer theorem) |
| SMAP | Selection; margin; multiresolution; level couplings; Gårding; tower sign is RH; precision rigidity | Selective positivity where overlap begins; the signed cross-level coupling |
| ACP | Gap classification for finite, prime-tail, cofinite and sparse flips; harmonic means; actual conductor coordinates for every pattern [S] | A selector beyond finite flips; infinite-pattern greatest gaps |
| AID, SAHT, ACS cells | Finite-index chain; Chebyshev identity; Gamma reserve; canonical energy; single-cell floors [S] | \(k=1\) layer [FS]; residual sign; upper bound on \(\mathcal E_{\rm crit}\) |
| RAPT | Sharp gap; adjunction spectrum; separated-regime splitting, trial energies and actual eigenlines [S] | Bottom spectrum past Robin–Euler uniformly; growing conductors |
| SSHA, ALG | Atomic receivers; quarter-Robin–Euler positivity; gap/scalar reduction; count-based local-to-global over \(\mathbb F_q\) | Full sign beyond Robin–Euler; local-to-global over \(\mathbb Z\) |
| Census (Zeta23, IGP, TTPC, ACS) | \(2/3\), \(HD(1)\), \(0.8876\); bandwidth and capacity exchange rates; slack calculus | A two-sided trans-threshold pair estimate or displacement-sensitive slack |
| SCP | Shallow Cauchy energy \(O(N)\) | A displacement-sensitive constant |
| RHTower heat/depth | Strata; \(2/3\) horizon; uniform-depth counts; local cofactor | Near-axis count; any vanishing mechanism |
| Density and short intervals (RHTower Sieve, RDPS2) | Guth–Maynard Theorem 1.1, \(30/13\), \(17/30\); DH \(\sigma\ge5/6\); VK region; balanced-window QRH dictionary | Any fixed power saving |
| BVI, ACG, CP, ADR | Readout/pronic decompositions; escape classification; gauge-mass criterion; Stepanov mechanism | Visibility of every escape state; actual cancellation |
| HLF, HTGeometry number fields | Hecke theta continuation, unit unfolding, Gamma factors [L/S] | Identification with Hecke \(L\)-series; uniform estimates |

## External mathematical status

RH is unsolved ([Clay](https://www.claymath.org/millennium/Riemann-Hypothesis/)). External proofs below are not validated by this review.

- **Alpöge–Furman two-thirds theorem.** External formalized package `Zeta23`; §10 builds on it.
- **Guth–Maynard large values theorem.** Published result; formalized unconditionally in the corpus (`guthMaynardLargeValuesBound_holds`).
- **Quasi-RH manuscript (Chen–Gupta–Li).** Claims Dirichlet zero-freeness for \(\operatorname{Re}s>7/8\) [E]; intake has no capstone; the Proposition 4.6 envelope has floor \(288\) against the collision quantum \(2\), which blocks an RH endpoint, not the \(7/8\) claim.
- **Ordinary-correlation manuscript.** Claims fixed-form Liouville two-point bounds \(X/(\log X)^c\): no power saving, no uniformity in growing shifts [E].
- **Context.** Lorentzian polynomials; de Bruijn–Newman \(\Lambda\le0.2\); Ki–Kim–Lee; Bourgain's density hypothesis for \(\sigma\ge25/32\); Montgomery's pair correlation on \(|\alpha|\le1\) under RH. None supplies zero exclusion.
