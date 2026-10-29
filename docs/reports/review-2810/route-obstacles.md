# Research routes and their mathematical obstacles

**RH remains open.** The inventory is 31 live routes, 17 standalone candidates and the PW-B branch of PM. Every live route has an exact RH receiver; none has the arithmetic input that receiver needs.

Companions: [summary, open problems and next questions](obstacles-summary.md) · [walls ledger](walls-ledger.md) · [route unification](route-unification-ledger.md) · [frontier map](../rh-current-frontier-map.md) · [scoped obstructions](../rh-killed-routes.md).

## How to read this report

Evidence comes from corpus searches followed by reading Lean statements, module docstrings and proof structure. Source inspection supports the corpus-wide inventory; **[K]** marks individually kernel-checked results. No full or umbrella builds. **[L]**, **[S]** and **[K]** follow the [frontier map](../rh-current-frontier-map.md): integrated source, working or unfinished source, and individual Lean checks with standard transitive axioms, respectively. **(inference)** marks a conclusion drawn here from proved statements; it is not a Lean theorem. Research record: [working log](../../../logs/review-2810-v3-research-2026-10-28.md).

Obstacles fall into two classes.

- **A — Just work.** The ingredients exist: a finite computation with certified error terms, an instantiation of a proved theorem, transport of a supplied bound between proved dictionaries, or formalization of a written proof. A-items can be large. They never promise that a desired sign is true.
- **B — Open mathematics.** A missing inequality, construction or uniformity. Strength tags:
  - **[RH]** equivalent to RH;
  - **[RH+]** strictly stronger than RH, for example also forcing simple zeros;
  - **[FS]** equivalent to finitely many zeros off the critical line. This implies the Lindelöf hypothesis and a fixed zero-free strip (§9);
  - **[≥QRH]** implies a fixed zero-free strip \(\Theta<1\), the quasi-Riemann hypothesis, which is unproved apart from a pending external claim;
  - **[open]** an intermediate problem with no solution in the corpus or the literature consulted, possibly solvable below RH strength.

A conditional receiver does not prove its input. A false proposed estimate belongs in neither class.

## The frontier in twelve results

### 1. Selection is a theorem; the margin is measured but not selective at its maximum

- **Selection.** A bounded weight \(|\lambda|\le\Lambda\) is eventually positive on atomic families at some root iff RH holds and \(\lambda=\Lambda\) on \(n\ge2\). Twin-blind positivity cannot reach an RH-complete family [L]. [Selection](../../../formal/GaloisForLFunctions/SelectiveMultiscaleArithmeticPositivity/PositivityAtEveryRootSelectsTheVonMangoldtWeight.lean).
- **The margin.** The multiplicative walk has Poincaré constant \(2\log2\). On the harmonic hyperplane \(\sum x_n/\sqrt n=0\), the prime form satisfies \(P_N\le(\log N-\gamma-2\log2+\varepsilon)|x|^2\), and the conductor-two excitation shows \(2\log2\) is optimal. The Liouville twin has gap \(0\); every sign gauge has gap at most \(2\log2\) [L]. [Sharp gap](../../../formal/GaloisForLFunctions/RenormalizedArithmeticPotentialTheory/TheSpectralGapOfThePrimeFormIsTwoLogTwo.lean), [margin](../../../formal/GaloisForLFunctions/SelectiveMultiscaleArithmeticPositivity/TheSelectiveMarginIsTwoLogTwo.lean), [first excitation](../../../formal/GaloisForLFunctions/SelectiveMultiscaleArithmeticPositivity/TheConductorTwoIsTheFirstExcitation.lean).
- **What pays the margin.** For a gauge \(\omega\) put \(c_N=\sum\omega(n)/n\,/\sum1/n\). Gauging keeps at least \(c_N^2\) of the harmonic variance, so the gap is at least \((2\log2)c_N^2\), uniformly over all gauges [L]. A single-prime parity flip \(\omega_p(n)=(-1)^{v_p(n)}\) has \(c_N\to(p-1)/(p+1)\) by an exact fibre count [L]. [Harmonic correlation](../../../formal/GaloisForLFunctions/ArithmeticCountingPositivity/HarmonicCorrelationPaysThePrimeGap.lean), [parity pairing](../../../formal/GaloisForLFunctions/ArithmeticCountingPositivity/PrimeParityPairing.lean).
- **The margin does not select \(\zeta\).** Every submaximal gap is attained by a completely multiplicative, polar-matched twin with a negative complete Weil test [L]. For every prime \(p\ge11\) the flip \(\omega_p\) attains the maximal gap \(2\log2\) exactly, has Weil coefficients of the same size as \(\Lambda\), and still fails complete Weil positivity [S]. [Near-maximal](../../../formal/GaloisForLFunctions/ArithmeticCountingPositivity/NearMaximalGapsDoNotForceWeilPositivity.lean), [maximal](../../../formal/GaloisForLFunctions/ArithmeticCountingPositivity/LargePrimeFlipsAttainTheMaximalGap.lean).
- **Where it acts.** On atomic tests the pole hyperplane is the harmonic hyperplane. Below the spacing a twin differs from \(\zeta\) only in the prime form. The sharp selective Gårding inequality turns the gap into a reserve \(c_0(2\log2-\eta)\) at narrow widths [L]. [Harmonic hyperplane](../../../formal/GaloisForLFunctions/SelectiveMultiscaleArithmeticPositivity/ThePoleHyperplaneIsTheHarmonicHyperplane.lean), [Gårding](../../../formal/GaloisForLFunctions/SelectiveMultiscaleArithmeticPositivity/TheSelectiveGardingInequality.lean).

So the margin separates \(\zeta\) from parity-type twins such as Liouville, not from sparse multiplicative flips. Whatever selects \(\zeta\) must see the sign of every prime.

### 2. One-prime tower positivity is RH at every generator size, and it needs square-root precision

- **Tower law.** On the tower \(g(\cdot-k\log p)\) of one prime, the supremum over generators and windows of the number of negative squares of Weil's form equals the number of distinct outer eigenvalues \(p^{\rho-1/2}\). RH is equivalent to positivity on all \(p\)-towers for one fixed prime [L]. [One prime](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/OnePrimeSeesTheWholeDefectOfZeta.lean).
- **Generator size buys nothing.** For every prime and every \(\varepsilon>0\), RH holds iff \(\Lambda\) is positive along the \(p\)-tower of every pole-free \(C^2\) generator supported in \([-\varepsilon,\varepsilon]\) [S]. The Toeplitz positivity of one prime's tower has no intermediate content at any overlap. [Pole-free generators](../../../formal/GaloisForLFunctions/SelectiveMultiscaleArithmeticPositivity/TheDyadicSignOfAPoleFreeGeneratorIsRH.lean).
- **Precision.** \(\lambda\) and \(\lambda+\varepsilon n^{-\eta}\), \(0<\eta<\tfrac12\), are never both tower-positive along a nonnegative generator, although their sums over every interval \((a,b]\) differ by at most \(\varepsilon(b-a)a^{-\eta}\). \(\Lambda\) and its Liouville twin are never both tower-positive [S]. [Rigidity](../../../formal/GaloisForLFunctions/SelectiveMultiscaleArithmeticPositivity/TheDyadicSignIsRigid.lean).

Consequence (inference): an input that decides the sign must be parity-sensitive (Liouville) and square-root-precise (every \(n^{-\eta}\), \(\eta<\tfrac12\)). Statements about primes in intervals that survive a relative error \(o(1)\), including Brun–Titchmarsh and every short-interval prime number theorem, cannot decide it. Finite-aperture inequalities move continuously with \(\varepsilon\), so the deciding input must also act at unbounded aperture.

### 3. Atomic receivers reach \((\log\log N)^{1+\varepsilon}\) overlap

- RH holds iff \(W\ge0\) eventually on atomic families of width \((\log\log N)^\alpha/N\), for every \(\alpha>1\) (Denjoy–Carleman profiles of class \(1+1/r\)); also for \(\alpha>2\) with an explicit Gevrey-2 profile [L]. [Denjoy–Carleman](../../../formal/GaloisForLFunctions/SpacingScaleHarmonicAnalysis/TheDenjoyCarlemanProfiles.lean), [Gevrey](../../../formal/GaloisForLFunctions/SpacingScaleHarmonicAnalysis/TheGevreyProfile.lean).
- **Profile-class boundary [S].** Nonzero smooth compactly supported Gevrey profiles exist exactly at order \(s>1\). This blocks the stated Gevrey-window construction at \(\alpha=1\); it does not prove that every possible endpoint or bounded-overlap receiver fails. [Exact class boundary](../../../formal/GaloisForLFunctions/HeckeKreinToeplitz/TheReceiversEndAtTheQuasiAnalyticBoundary.lean).
- Under overlap growth the Markov form is negative unconditionally, and RH is Markov nonnegativity on the pole hyperplane [L]. [Pole](../../../formal/GaloisForLFunctions/SpacingScaleHarmonicAnalysis/ThePoleIsTheOnlyNegativeSquareBeyondTheThreshold.lean).
- **At every width,** \(W\ge0\) on atomic tests iff \(M\ge0\) on the pole complement \(p=0\) and \(M+2a_0B\ge0\) on the affine hyperplane \(p=1\). Beyond the Robin–Euler threshold the Markov form has exactly one negative direction, the pole vector. [Gap and one scalar](../../../formal/GaloisForLFunctions/ArithmeticLorentzianGeometry/TheHodgeIndexIsAGapOnThePoleComplementAndOneScalar.lean).

### 4. A smooth plateau gives full positivity at every fixed separated width

- Eventually \(W\ge0\) on every window test \(\sum_nG_n(\cdot-\log n)\) with arbitrary \(C^2\) shapes at widths \(w\le K_\star\delta_N\): \(K_\star\approx0.108\) of the spacing for plateau profiles (a quarter of the Robin–Euler ratio \(\approx0.43\)), \(\approx0.072\) for every profile. With absolute values on the pole term the method stays below about half the threshold. [Quarter](../../../formal/GaloisForLFunctions/ArithmeticLorentzianGeometry/TheStabilityRegimeReachesAQuarterOfTheRobinEulerThreshold.lean).
- **Arithmetic modes.** For the Ramanujan profile of conductor \(m\ge2\) at width \(K/N\), \(0<K<\tfrac14\): \(W(f_N)/\|f_N\|^2\to\log(K_m/K)\), \(K_m=m\,e^{d(m)}e^{\beta(\varphi)/\|\varphi\|^2}/(2\pi)\), with \(d(m)=\sum_{p\mid m}\log p/(p-1)\). The pole sits at the Robin–Euler ratio \(K_1\) and the first excitation at \(4K_1\) [S]. [Mode energies](../../../formal/GaloisForLFunctions/RenormalizedArithmeticPotentialTheory/TheWeilEnergiesOfTheArithmeticModes.lean).
- **The whole separated regime \(0<c<1\).** The complete matrix splits into self-energy, the literal prime kernel, the archimedean cross integral and both pole products [L]. Every bounded spectral window is exhausted, with multiplicity, by the arithmetic adjunction energies [S]. For each \(b<2-\log(2\pi)\), one smooth plateau has every complete-Weil eigenvalue at least \(b\), eventually at each fixed \(c\in(0,1)\) [S]. Taking \(b>0\) gives positivity of the whole matrix. The plateau can retain arbitrarily near unit square mass; the horizon depends on \(c\). This proves a sign where the Markov form can be negative, while touching, overlap and RH-complete exhaustion remain open. [Splitting](../../../formal/GaloisForLFunctions/RenormalizedArithmeticPotentialTheory/TheFullWeilMatrixSplitsAtTheSpacing.lean), [complete spectral counts](../../../formal/GaloisForLFunctions/RenormalizedArithmeticPotentialTheory/TheBoundedCompleteWeilSpectrumIsTheAdjunctionSpectrum.lean), [plateau positivity](../../../formal/GaloisForLFunctions/CriticalArithmeticCorrelationTheory/SmoothPlateausMakeTheSeparatedCompleteWeilMatrixPositive.lean), [shape and charge limits](../../../formal/GaloisForLFunctions/CriticalArithmeticCorrelationTheory/ThePlateauShapeAndChargeHaveTheirIndicatorLimits.lean).

### 5. The prime form has a known bottom spectrum

Below \(\log N-\gamma\), the spectrum of \(P_N\) within distance \(T\) comes only from integers with \(\log m+d(m)<T\). Actual spectral counts equal adjunction counts, and each adjunction energy \(E_m=\gamma+\log m+d(m)\) carries eventually one eigenline converging to its Ramanujan line [S]. Fixed conductor packets are realized; growing-conductor control is open. [Top spectrum](../../../formal/GaloisForLFunctions/RenormalizedArithmeticPotentialTheory/TheTopSpectrumOfThePrimeFormIsExhaustedByTheIntegers.lean), [counts](../../../formal/GaloisForLFunctions/RenormalizedArithmeticPotentialTheory/TheBoundedPrimeSpectrumIsTheAdjunctionSpectrum.lean).

### 6. The complete source: the finite-index chain ends at the first prime layer

- Complete logarithmic cells recover every mixed Weil entry and form a dyadic multiresolution, \(C_{2a}+C_{2a+1}=T_{\log2}C_a\); prime two acts as the unilateral shift on every generator chain [L]. [Multiresolution](../../../formal/GaloisForLFunctions/SelectiveMultiscaleArithmeticPositivity/TheCompleteSourceIsADyadicMultiresolution.lean), [level matrix](../../../formal/GaloisForLFunctions/SignedArithmeticHodgeTheory/ArithmeticTranslationsHaveAnExactDyadicLevelMatrix.lean).
- Gamma pays all logarithmic detail mass, a mean graph on pair averages and all dyadic parent variances. Balanced sections above one index carry a full-form floor uniformly in the horizon, for every twist \(|\omega|\le1\), Liouville included [L]. [Floor](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/HaarCellEffectivity.lean), [twin-blind](../../../formal/GaloisForLFunctions/SelectiveMultiscaleArithmeticPositivity/TheHaarFloorIsTwinBlind.lean).
- **Signed Haar Gamma cross terms [L].** For the actual one-level Haar section \(h=\sum_a d_a h_a\), the full diagonal error satisfies \(\left|\Gamma(h)-\sum_a d_a^2\Gamma(h_a)\right|\le16e^{1/2}\|h\|_2^2\), including low indices. Mean cancellation and disjoint target rectangles pay each boundary remainder once. All three exact files passed direct Lean checks. This supplies an ordinary-mass error; paying it jointly with the exact diagonal, arithmetic potential and poles is separate. It is not an upper Gamma bound for the all-level generator projection. [Boundary cost](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/TheHaarGammaCrossTermsCostOnlyMass.lean).
- **Uniform finite index, layer by layer [L].** Gamma minus each of the following has negative dimension bounded independently of horizon and family:
  - the all-prime mixed block with exponents \(k\ge3\);
  - the whole signed prime-two Euler mixed source;
  - every fixed finite prime set;
  - **the entire even-power source with its pole, together with the odd mixed powers \(k\ge3\)**: \(\operatorname{ind}(\Gamma-S_2-M_{\rm odd})\le A+1\). The literal square-prime pole is half the squared mean, and the square boundary keeps a fixed Gamma share because the completed \(\xi\) field grows logarithmically on the zero-free edge.

  [Squares and odd powers](../../../formal/GaloisForLFunctions/ArithmeticIndexDescent/SquaresAndOddHigherMixedPowersHaveUniformFiniteIndex.lean), [square source](../../../formal/GaloisForLFunctions/ArithmeticIndexDescent/TheSquarePrimeSourceRetainsGammaEnergy.lean), [edge field](../../../formal/GaloisForLFunctions/ArithmeticIndexDescent/TheXiEdgeFieldHasLogarithmicGrowth.lean), [k≥3](../../../formal/GaloisForLFunctions/ArithmeticIndexDescent/AllHigherPrimePowerMixedFormsHaveUniformFiniteIndex.lean), [prime two](../../../formal/GaloisForLFunctions/ArithmeticIndexDescent/TheGammaMeanGraphPaysThePrimeTwoMixedBlock.lean).
- **What remains:** the first prime layer \(k=1\) over all primes, where the absolute constant \(\sum_p\log p/\sqrt p\) diverges; odd-power diagonal blocks; finite detail heads; the coarse error; the actual poles and archimedean mass. Uniform finite index of the complete form is equivalent to finite off-line support, so the last layer carries an [FS] statement, at least as hard as the Lindelöf hypothesis (§9).
- **All real lags and fixed finite Euler families [K].** For the original finite cell source, retain root and all labels \(a<A\) at every dyadic level. Every real-lag correlation has head error at most \(96\Gamma(f)/(1+\log A)\). For a fixed finite prime set \(P\), the complete critical Euler correlation error is at most \(96C_P\Gamma(f)/(1+\log A)\), where \(C_P=\sum_{p\in P}2\log p/(\sqrt p-1)\). Absolute convergence includes every prime power. One \(A>\exp(96C_P/\delta)\) works for every profile and horizon. Odd-prime commutation is unnecessary; original Gamma pays both projected probes. The complete-power constants are not summable over all primes; the higher-power sector has the separate finite budget below. [all-lag bound](../../../formal/GaloisForLFunctions/SignedArithmeticHodgeTheory/EveryTranslationHasAnAllLevelGammaTailBound.lean), [complete finite Euler families](../../../formal/GaloisForLFunctions/SignedArithmeticHodgeTheory/FiniteEulerFactorsHaveAllLevelGeneratorApproximation.lean).

- **All primes, exponents \(k\ge3\) [K].** Put \(H=\sum_{p,k\ge3}2\log p/p^{k/2}<\infty\), with \(p\) prime. For \(C_t(f)=\int f(x)f(x+t)\,dx\) and \(Q_A=U(1-P_A)U^*\), the sum of absolute coefficientwise changes is
  \[
  \sum_{p,k\ge3}\frac{2\log p}{p^{k/2}}
    |C_{k\log p}(f)-C_{k\log p}(f-Q_Af)|
  \le\frac{96H\Gamma(f)}{1+\log A}.
  \]
  The complete correlation is absolutely convergent on whole-line \(L^2\), with its directed finite-sum limit and original-source integral identity. One \(A>\exp(96H/\delta)\) pays the complete source and every finite selection by \(\delta\Gamma(f)\), uniformly in all finite cell profiles and horizons. Every generator orbit remains. General BV profiles retain their noncell component. [All-prime higher-power theorem](../../../formal/GaloisForLFunctions/SignedArithmeticHodgeTheory/AllHigherPrimePowersHaveAllLevelGeneratorApproximation.lean).
- **Actual stopping averages and complete even-power error [K].** The whole-orbit cutoff is exactly averaging over logarithmic stopping blocks, with weights $\ell_m/\ell_a$ summing to one. A finite original source has an actual finite real compact BV head $h=P_Af$ and tail $t=f-h$, with $\int h=\int f$, $\int t=0$, $\int ht=0$ and $\int t^2\le32\Gamma(f)/(1+\log A)$. Both square-source centering corrections cancel in the mixed difference. For every $\varepsilon>0$, one $C_\varepsilon$ before all source families, horizons and cutoffs gives
  \[
  |S_{\rm even}(f)-S_{\rm even}(h)|
  \le\varepsilon(\Gamma(h)+\Gamma(t))
    +C_\varepsilon\frac{32\Gamma(f)}{1+\log A}.
  \]
  Here `squarePrimeSource` is the complete **even-power** source; its exponents at least four also belong to the higher-power sector. Uniform payment of $\Gamma(h)+\Gamma(t)$ by original $\Gamma(f)$ remains an analytic target. Ordinary mean preservation does not preserve the two exponential Weil moments. [Exact block averages](../../../formal/GaloisForLFunctions/SignedArithmeticHodgeTheory/GeneratorCutoffsAreLogarithmicBlockAverages.lean), [literal BV identities](../../../formal/GaloisForLFunctions/SignedArithmeticHodgeTheory/ActualGeneratorHeadsPreserveTheSourceMean.lean), [full even-power error](../../../formal/GaloisForLFunctions/SignedArithmeticHodgeTheory/TheSquareSourceHeadErrorHasOnlyAGammaStabilityCost.lean).
- **Exact method boundary [K].** The literal coefficient tail beginning at exponent \(r+1\) is summable iff \(r\ge2\). The prime and square masses \(\sum_p2\log p/\sqrt p\), \(\sum_p2\log p/p\) both diverge. This rejects absolute coefficient payment for those two layers; it does not assert divergence of actual compact-source correlations. The full even-power head error above isolates the remaining projected-Gamma cost. Uniformly paying that cost, the first-prime source and both exponential Weil moments remains separate from coefficient summation. [Coefficient classification](../../../formal/GaloisForLFunctions/SignedArithmeticHodgeTheory/CriticalEulerCoefficientMassStartsAtCubes.lean).
- Finitely many full generator orbits approximate cell sources in \(L^2\), but one Haar generator has an infinite orthogonal orbit of fixed Gamma energy: approximation is not compactness [L]. [Orbits](../../../formal/GaloisForLFunctions/SignedArithmeticHodgeTheory/FiniteGeneratorOrbitsApproximateThePhysicalCellSource.lean), [noncompact](../../../formal/GaloisForLFunctions/SignedArithmeticHodgeTheory/CompactDetailsDoNotMakeTranslationOrbitsCompact.lean).

### 7. Cross-level couplings: three paid, one is the one-prime Toeplitz problem

| Part between levels \(j<k\), \(d=k-j\) | Law | Status |
|---|---|---|
| Pole | \(2A(f)B(f)\cosh(d\log2/2)\): rank two, hyperbolic, vanishes on \(\sum_jc_j2^{-j/2}=0\) | Removed by one linear condition |
| Gamma tail | \(\le\pi4^{-(d-1)}(\|f\|^2+\|g\|^2)\) | Summable |
| Touching levels | \(\le C_\ell(\|f\|^2+\|g\|^2)\), uniform under translation | Bounded |
| Prime comb | \(-\int(e^h-\psi(e^h)-c)\,q'(h)\,dh\) | Open |

[Pole](../../../formal/GaloisForLFunctions/SelectiveMultiscaleArithmeticPositivity/ThePoleCouplesTheLevelsHyperbolically.lean), [separated](../../../formal/GaloisForLFunctions/SelectiveMultiscaleArithmeticPositivity/SeparatedLevelsCoupleThroughTheChebyshevError.lean), [touching](../../../formal/GaloisForLFunctions/SelectiveMultiscaleArithmeticPositivity/TouchingLevelsCoupleUniformly.lean).

The prime part is the open coupling. By the explicit formula, \(d\mapsto W(f,T_{d\log2}g)\) is a sum over zeros of \(2^{d(\rho-1/2)}\): almost periodic with positive mean square under RH, exponential otherwise, never summable (inference). Positivity of the generator-orbit form is the one-prime tower positivity of §2, which is RH at every generator size [S]. The proved finite-generator approximation controls L², fixed finite Euler families and the all-prime exponent≥3 sector. Upgrading it to the complete Weil form remains necessary; the retained-orbit sign does not follow from the approximation.

### 8. Ordered entries are centered Chebyshev integrals

For real tests \(f\) left of \(b\), \(g\) right of \(b\), and every \(c\):
\[
W(f,g)=-\int_0^\infty\big(e^h-\psi(e^h)-c\big)\,q'_{f,g}(h)\,dh-\Gamma_{\rm tail}(f,g),\qquad q_{f,g}(h)=e^{-h/2}\!\int f(u)g(u+h)\,du .
\]
The Gamma tail is a localized mass minus a nonnegative square reserve. The Gamma boundary operator has norm \(\pi/2\), attained by no nonzero input, with no uniform relative reserve [S]. [Chebyshev identity](../../../formal/GaloisForLFunctions/ArithmeticIndexDescent/TheOrderedWeilSourceIsACenteredChebyshevDefect.lean), [square reserve](../../../formal/GaloisForLFunctions/ArithmeticIndexDescent/TheOrderedWeilSourceRetainsItsGammaSquareReserve.lean).

### 9. Finite off-line support implies the Lindelöf hypothesis and a zero-free strip

- **Strata [L].** Say the zeros *approach the line* if for every \(h>0\) only finitely many zeros have \(\tfrac12-\operatorname{Re}\rho>h\) or \(\operatorname{Re}\rho-\tfrac12>h\). Then:
  \[
  \text{RH}\ \Rightarrow\ \text{finite off-line support}\ \Rightarrow\ \text{zeros approach the line}\ \Longleftrightarrow\ \text{LH}\wedge\big(\cos(hD)\Xi\text{ has finitely many nonreal zeros }\forall h>0\big)\ \Rightarrow\ \text{LH}\wedge\Theta<1 .
  \]
  The step to LH is Backlund's criterion. [Depth and Lindelöf](../../../formal/GaloisForLFunctions/RHTower/LindelofCosineFiniteDefectDepth.lean).
- **Heat flow.** \(\Xi\) has finitely many nonreal zeros iff the nonreal zero counts of \(H_t\) are bounded as \(t\downarrow0\) [S]. Split at height \(h\): the high collisions are bounded uniformly in \(t\) at every height iff the zeros approach the line. What the flow adds beyond depth counting of \(\Xi\) is the near-axis count alone [S]. For \(0<t\le1/8\), zeros of \(H_t\) with \(|\operatorname{Re}z|\ge2\pi e^{(27/40+\varepsilon)/t}\) are real and simple [S]. [Heat count](../../../formal/GaloisForLFunctions/RHTower/DeBruijnNonrealCountRightLimit.lean), [high collisions](../../../formal/GaloisForLFunctions/RHTower/DeBruijnHighCollisionsReadTheDepth.lean), [horizon](../../../formal/GaloisForLFunctions/RHTower/KiKimLeeInteriorLindelofHorizon.lean).
- **Other receivers of finite support.** \(\mathcal E_{\rm crit}<\infty\), bounded source work, bounded complete-cell index ([AID](../../../formal/GaloisForLFunctions/ArithmeticIndexDescent/TheCriticalSourceRateHasACanonicalEnergy.lean)); prime lag minus finitely many exponentials bounded on one side ([lag](../../../formal/GaloisForLFunctions/RHTower/FiniteOffLineConverse.lean)); bounded cosine defects ([cosine](../../../formal/GaloisForLFunctions/RHTower/XiCosineShiftBoundedDefectFiniteOffLine.lean)). The RH threshold is \(\mathcal E_{\rm crit}\le Q_*=1294047/2000\); index \(k\) costs \(\mathcal E_{\rm crit}\ge\max\{(Q_*/2)k,50k^2-3k/2\}\) [S]. Finite support forces \(\Theta<1\) also through the index exit ([index exit](../../../formal/GaloisForLFunctions/ArithmeticOrientationGeometry/TheIndexExit.lean)).
- **Krein–Langer structure [S].** On a group, a positive-definite kernel plus \(\kappa\) hyperbolic character pairs has negative index at most \(\kappa\), with equality when one element separates the pairs; a positive part never pays a pair; bounded index passes to pointwise kernel limits, not to \(L^2\) limits of tests. [Index formula](../../../formal/GaloisForLFunctions/HeckeKreinToeplitz/HyperbolicPairsAndTheIndexFormula.lean), [closure](../../../formal/GaloisForLFunctions/HeckeKreinToeplitz/BoundedIndexIsClosedUnderPointwiseLimits.lean). With the tower law of §2, finite support is equivalent to bounded tower index at two primes with incommensurable logarithms (inference: one prime aliases zeros on a lattice of ordinates, a second removes the aliasing).

### 10. Critical-line census: two thirds, the exchange rate, and its price

The corpus imports the external, formalized Alpöge–Furman theorem (Lean package `Zeta23`). Its mechanism is a Sylvester-inertia rank–trace inequality: the explicit-formula Gram is a positive part from critical zeros plus an indefinite part from off-line pairs; its Frobenius norm is computed from primes through pair correlation.

| Census statement | Value |
|---|---|
| Simple critical zeros | \(\ge2/3\); \(\ge HD(1)=0.6725007\ldots\) with the Montgomery–Taylor window; \(+10^{-8}\) from Gabor pinching |
| Simple **or** critical zero copies | \(\ge1-(1-HD(1))/(3/2+\sqrt2)=0.8876\ldots\) |
| Off-line zero copies | \(\le1-HD(1)\) |
| Distinct ordinates carrying a critical zero | \(\ge4/5\) |
| Zero copies within \(4/\log T\) of the line | \(\ge3/4\) |

[Two thirds](../../../formal/GaloisForLFunctions/RHTower/Zeta23SimpleCriticalDensity.lean), [simple or critical](../../../formal/GaloisForLFunctions/RHTower/Zeta23SimpleOrCriticalOptimal.lean), [Gabor](../../../formal/GaloisForLFunctions/IncommensurableGaborPinching/CriticalLineZeroProportion.lean), [ordinates](../../../formal/GaloisForLFunctions/RHTower/Zeta23CriticalOrdinateCensus.lean).

- **Exchange rate [L].** The certified proportion is \(2-\phi(\lambda)\), where at bandwidth \(\lambda\) the normalized Frobenius form factor is \(\phi=2/\lambda-2/(3\lambda^2)+(2/\lambda^2)\int_1^\lambda(\lambda-\alpha)F(\alpha)\,d\alpha\). At \(\lambda=1+\delta\), with the Cesàro pair energy \(E(\delta)=(2/\delta^2)\int_1^{1+\delta}(1+\delta-\alpha)F\), the gain over \(2/3\) is \(\delta(2-(3E-4)\delta)/(3(1+\delta)^2)\). A bound \(E\le B\) yields a gain \(1/(3(3B-2))\). [Narrow strip](../../../formal/GaloisForLFunctions/TransThresholdPairCorrelation/NarrowStripClosePairEnergyAndExchangeRate.lean), [form factor](../../../formal/GaloisForLFunctions/TransThresholdPairCorrelation/FormFactorThresholdAndShiftInequality.lean).
- **Three quarters** follows from one prime-side mean-value inequality at bandwidth \(4/3\) (`FrobeniusFourThirds`: twice the GUE value on \((1,4/3]\)), and then the zeros are also simple [L]. [Reduction](../../../formal/GaloisForLFunctions/RHTower/ZetaThreeQuartersReduction.lean).
- **Price.** Beyond \(\alpha=1\) the prime side is a signed sum over prime pairs in the coalescent band. Its Poisson main term integrates to zero against the dyadic kernel only with the exact Hardy–Littlewood main term [L]. One-sided sieve bounds therefore control nothing, and two-sided pair asymptotics meet the parity barrier (inference). [Coalescent anatomy](../../../formal/GaloisForLFunctions/TransThresholdPairCorrelation/CoalescentSieveAnatomyAndModelCalibration.lean).
- **Value moments are depth-blind [L].** An equal-valued reflected pair has every holomorphic value moment of two critical zeros, so mollified moments certify simple zeros of either kind. [Mimicry](../../../formal/GaloisForLFunctions/RHTower/ValueMomentsCannotSeparateReflectedPairs.lean).
- **Shallow Cauchy energy [L].** For strict-right zeros in \([T,2T]\) at depth \(\le h\), the shifted Cauchy energy obeys \(hE_h\le C\max(\kappa_2,2h\log T)\,T\log T\), \(0<h\le1/64\); at \(h=1/\log T\) this is \(O(N(T,2T))\), with squared-multiplicity and close-pair bounds and a joint shallow/deep budget. The majorant is the Lorentzian pair sum over all zeros of the window, so its constant cannot separate critical from off-line zeros (inference). [Bound](../../../formal/GaloisForLFunctions/ShallowCauchyPrimeEnergy/ShallowCauchyEnergyBound.lean), [implications](../../../formal/GaloisForLFunctions/ShallowCauchyPrimeEnergy/ShallowCauchyImplications.lean).

### 11. Quasi-RH: translation complete, production absent

- Fixed-strip dictionaries are exact: \(\Theta\le1-\theta\) in escaped Möbius rates, Hecke-defect caps and integer-theta growth; \(\Theta<1\) iff a uniform Vaughan power saving; \(\Theta=\tfrac12+\inf\{\)one-sided exponents\(\}\) for the Möbius-divisor Abel moment, its quotient head at any power cutoff and finite-contact Suzuki residuals [L]. [Abscissa laws](../../../formal/GaloisForLFunctions/RHTower/QuasiRHQuotientHeadAndFiniteContactAbscissaLaw.lean), [Vaughan](../../../formal/GaloisForLFunctions/BezoutValuationIncidence/UniformVaughanPowerBoundsAreFixedStrips.lean).
- Density inputs: \(N(\sigma,T)\ll T^{(8/3+\varepsilon)(1-\sigma)}\) boxes [L]; the density hypothesis on \(\sigma\ge5/6\) [L]; the Guth–Maynard box count is reduced to the \(S_2/S_3\) propositions of its large-values theorem. A density envelope can never decide vanishing: it never drops below \(1\) [L]. [8/3](../../../formal/GaloisForLFunctions/RHTower/ZetaZeroDensityEightThirds.lean), [DH](../../../formal/GaloisForLFunctions/RHTower/ZetaZeroDensityHypothesisFiveSixths.lean), [GM box](../../../formal/GaloisForLFunctions/RHTower/ZetaZeroDensityGuthMaynardBox.lean), [envelope](../../../formal/GaloisForLFunctions/RHTower/DensityEnvelopeNoGo.lean).
- The Chen–Gupta–Li intake (279 modules) has its zero detector and density components but no zero-free capstone (External status).

### 12. Over finite fields the local-to-global step is a count

- For curve data with nonnegative counts, trickle-down on every Frobenius ladder is equivalent to the one-sided square-root count \(N_k\ge q^k+1-Cq^{k/2}\); hyperelliptic curves pass by Stepanov's count, with no surface and no positivity input; the golden fake fails [L]. The local Lorentzian input at one prime is local RH [L]. [Count](../../../formal/GaloisForLFunctions/ArithmeticLorentzianGeometry/TheTrickleDownInequalityIsTheSquareRootCount.lean), [hyperelliptic RH](../../../formal/GaloisForLFunctions/RHTower/HyperellipticRiemannHypothesis.lean), [local factor](../../../formal/GaloisForLFunctions/ArithmeticLorentzianGeometry/TheLocalFactorTricklesDownByRamanujan.lean).
- Over \(\mathbb Z\), \(1-T_p^N\) annihilates a zero symbol iff the zero is critical and on a height lattice; sparse polynomials vanish to bounded order in characteristic zero [L]. [Stepanov mechanism](../../../formal/GaloisForLFunctions/ArithmeticCorrespondencePositivity/SparseAnnihilatorsAndTheStepanovMechanism.lean).
- Hyperbolicity of the atomic Gram holds for every completely multiplicative sign twin; the Metzler sign holds below the spacing for \(\zeta\) and fails in every gauge for any twin flipping a prime [L]. [Blind/selective](../../../formal/GaloisForLFunctions/ArithmeticLorentzianGeometry/HyperbolicityIsBlindTheSignIsNot.lean).

## Live routes

Each entry gives the current state, then A (just work) and B (open). Full source lists are in the [frontier map](../rh-current-frontier-map.md#live-routes).

### WL — Weil lag / prime-error energy

**Current:** Bounded critical-deficit energy, a lower bound on coprime cross-work and a linear cumulative prime-error energy budget are each equivalent to RH; eventual \(\psi(x)-x\le C\sqrt x\log^2x\) is equivalent to RH; Abel-slope saturation at the archimedean genus is RH plus simple zeros. The prime error is the separated off-diagonal of the complete form (§8) and the only unpaid cross-level coupling (§7). The pointwise square \((\psi(x)-x)^2\) is the "tensor square" of the prime error: its Mellin transform has singularities at \(\rho+\rho'\) and abscissa \(2\Theta\) (inference), so tensor-power amplification returns this route's mean-square receiver.

**A:** Evaluate fixed truncations with certified archimedean and high-zero tails; transport lag/count/energy dictionaries with constants; tabulate \(d\mapsto W(f,T_{d\log2}g)\) for the cell-1 generator.

**B:** The actual one-sided prime-error or cross-work bound **[RH]**; subtracted lag **[FS]**; genus saturation **[RH+]**, not an admissible RH premise. [Receiver](../../../formal/GaloisForLFunctions/BiScaleUncertainty/WeilLagCriticalDeficitEndpointAndLimitLaw.lean).

### RW — Restricted Weil ground energy

**Current:** RH iff the ground minimum is positive at every finite aperture. The minimum strictly decreases with an exact shell decomposition; finite-aperture Gårding allows a nonzero negative index; positive floors must decay doubly exponentially. Gamma boundary: norm \(\pi/2\), exact square reserve, no uniform relative reserve [S].

**A:** Certified finite-aperture variational bounds and shell ledgers; instantiate the Gamma square reserve in the shell flux.

**B:** Cumulative aperture relaxation bounded by the initial energy, paying low modes, prime collars and polar terms **[RH]**. Frozen finite-prime families become negative. [Aperture flow](../../../formal/GaloisForLFunctions/ArithmeticContinuationAndCriticalEnergy/TheApertureFlowNeverStalls.lean).

### FU — Signed prime scheduling

**Current:** An eventual upper bound on the normalized completed Abel moment is equivalent to RH. Narrow translated prime channels have a useful sign; wide-window channels can be positive [S].

**A:** Assemble seed, drift, earlier-history, cross-block and endpoint terms for a fixed schedule with existing clock kernels.

**B:** The joint signed total over a prime-exhaustive schedule **[RH]**. [Receiver](../../../formal/GaloisForLFunctions/RHTower/CCM/CCMFUSuzukiMobiusDivisorOneSided.lean).

### RP — Matched-quantile history floor

**Current:** RH is equivalent to an eventual floor \(-B(K+2)\) for the normalized history. Unconditionally the history drops below \(-\delta(K+2)\) cofinally for some \(\delta>0\), so no sublinear floor or sublinear correction exists; the route sits exactly at linear scale. Low-LCM payment and exact signed identities exist. [Floor](../../../formal/GaloisForLFunctions/RHTower/SPEQuantileRieszRoutePLinearFloorCriterion.lean), [escape](../../../formal/GaloisForLFunctions/RHTower/SPEQuantileRieszRoutePLinearHistoryEscape.lean).

**A:** Expand fixed histories, instantiate low-LCM estimates, measure the cofinal linear escape constant \(\delta\) on computed ranges.

**B:** A linear floor with high-LCM pairs, moving core and singular-domain transport controlled together **[RH]**.

### PA — Prime–archimedean passivity

**Current:** Exact current-sign, Bernstein-mismatch and signed compact-moment receivers; every fixed moment order is positive after a large enough shift. First-atom moment bounds come from high-order quadrature with exact rational integrals, leaving one uniform analytic tail estimate. [High-order moments](../../../formal/GaloisForLFunctions/RHTower/PrimeArchThetaFirstAtomHighOrderMomentBounds.lean).

**A:** Prove the remaining analytic tail estimate; extend quadrature to further atoms; explicit thresholds for finite order blocks.

**B:** An all-order/all-shift sign, high-frequency accretivity or an every-positive-rate mismatch bound **[RH]**. [Signed completion](../../../formal/GaloisForLFunctions/RHTower/PrimeArchSignedCompactCompletionCollapse.lean).

### MC — Möbius cancellation

**Current:** Every strict half-power cancellation bound and subpower Hilbert energy are RH-equivalent; fixed strips have complete dictionaries (§11); Vinogradov–Korobov gives no fixed power saving; a linear Mertens budget forces RH and simple zeros. [Abscissa laws](../../../formal/GaloisForLFunctions/RHTower/QuasiRHQuotientHeadAndFiniteContactAbscissaLaw.lean).

**A:** Specialize fixed-modulus and below-diagonal estimates; unify rate normalizations; translate any supplied strip bound through all dictionaries; finish the Chen–Gupta–Li and Guth–Maynard \(S_2/S_3\) intake.

**B:** Every strict half-power for the moving source **[RH]**; the linear Mertens budget **[RH+]**; any fixed one-sided power saving **[≥QRH]**. [Hilbert criterion](../../../formal/GaloisForLFunctions/RHTower/MobiusHilbertFormEquivalence.lean).

### TT — Theta tails and directed covariance

**Current:** Exact seam, Wold and odd-Weil receivers with the sub-half range explicit; restricted current signs; continuum light-cone positivity.

**A:** Evaluate fixed directed-covariance and reflected-prime terms; apply continuum and short-support identities with endpoints.

**B:** Signed nonlocal covariance at every rapidity and scale, or complete odd/primitive positivity **[RH]**. [Wold receiver](../../../formal/GaloisForLFunctions/RHTower/PaperWoldDirectedCovarianceRH.lean).

### LA — Line anchor / Jensen and heat signs

**Current:** Finite-head/heat receivers and positive complementary tails; ordinary \(\xi\) coefficients are Turán and Lorentzian; the Jensen family satisfies Laguerre on \(s\ge0\). Generic finite-product closure cannot admit Ramanujan local factors. Near an ordinate, \(\xi=P\cdot g\) with \(\deg P=O(\log T)\) and \(g'/g=O(\log T)\) on a fixed disc, and Gaussian averages of locally tame functions stay close to the function [S]. [Cofactor](../../../formal/GaloisForLFunctions/RHTower/XiZeroFreeCofactorNearAnOrdinate.lean).

**A:** Certify selected finite heads and low degrees; translate coefficient conventions; apply heat-tail errors with the local cofactor bounds.

**B:** All-height/all-degree head signs, especially low orders and near-double configurations **[RH]**. [Finite-head reduction](../../../formal/GaloisForLFunctions/RHTower/XiSliceHeatFiniteHeadReduction.lean).

### TG — Integer trace below one

**Current:** Winding, cubic transgression and central-gap receivers; Gaussian coprime-divisibility covariance has a sign on indicators.

**A:** Finite projection/transgression data, residual and trace kept separate.

**B:** A matrix-complete decomposition with nonnegative residual and integer trace below one on every disc, or a zero-rate central-gap bound **[RH]**. [Index estimate](../../../formal/GaloisForLFunctions/RHTower/RestrictedProjectionIndexOperatorNormCriterion.lean).

### HF — Arithmetic Hodge positivity

**Current:** Full Hodge/Weil sign, zero Hecke defect and small enough source work are exact receivers. The complete source is a multiresolution with Gamma-paid details and a twin-blind high-detail floor; every prime layer except \(k=1\) has uniform finite index (§6); every fixed finite Euler family and all primes with exponents≥3 have all-level generator approximation [K]; the complete even-power head error has only its explicit projected-Gamma cost plus paid tail mass (§6) [K]; cross-level prime couplings are the one-prime Toeplitz problem (§7); canonical critical energy has exact finiteness and RH thresholds (§9); the margin \(2\log2\) is sharp but does not select \(\zeta\) at its maximum (§1).

**A:** Finite complete-cell Grams in multiresolution coordinates; explicit detail-head sizes for the finite-index bounds; source-kernel cost transport; distinct-index and multiplicity energies kept apart.

**B:**
- Complete residual nonnegativity, complete-cell index zero, or an arithmetic upper bound on work at an RH threshold **[RH]**.
- Uniform finite index of the complete form, or finite \(\mathcal E_{\rm crit}\) **[FS]**.
- Complete-form transfer through touching and into overlap **[open]** (Q1); fixed separated plateau positivity has a source proof [S].

[Index capture](../../../formal/GaloisForLFunctions/ArithmeticIndexDescent/TheCompleteCellsCaptureEveryFiniteIndex.lean), [work threshold](../../../formal/GaloisForLFunctions/ArithmeticIndexDescent/TheSourceWorkHasAClosedQuantumThreshold.lean).

### CHMD — Causal hyperbolic–modular duality

**Current:** Wave/Doob receivers; the supported maximal graph equals the completed aperture core; the bounded carrier projection has residual radical equal to the Weil radical. Translation keeps \(W\) and escapes every exponential graph bound. Ordered entries are Chebyshev integrals; finite generator orbits approximate cell sources in \(L^2\), every fixed finite Euler correlation family and the all-prime higher-power sector [K], but are not compact. Their cutoff is actual mean-preserving stopping-cell averaging; the full even-power head error retains an explicit head-plus-tail Gamma cost [K].

**A:** Domain/cutoff theorems on fixed sources; the signed residual with the primitive defect; bounded-window scale transport.

**B:** The complete one-sided wave bound or odd Doob/nodal inequality **[RH]**. [Odd criterion](../../../formal/GaloisForLFunctions/RHTower/CHMDOddSectorCriterion.lean).

### TH — Theta moment positivity

**Current:** All ranks are strictly positive on nonzero nonnegative coefficient vectors at one common small time; fixed-rank stable regions are known.

**A:** Finite signed blocks with explicit degree/time dependence.

**B:** Positivity for signed vectors at every degree under one common time **[RH]**. [Orthant theorem](../../../formal/GaloisForLFunctions/RHTower/XiHeatHankelFormOrthantPositivity.lean).

### RN — Renewal and singular comparison

**Current:** Theta renewal solvers, a compact cone-positive operator, exact determinant resonances and multiplicity bookkeeping.

**A:** Finite packet/resolvent data in the admitted topology with cusp/seam terms.

**B:** Directed boundary-work orientation, or mixed prime-plus-Gamma versus pole **[RH]**. Cone positivity does not imply real spectrum. [Exact spectrum](../../../formal/GaloisForLFunctions/RHTower/ThetaRenewalFredholmSpectrum.lean).

### WD — Ward caps and collision

**Current:** A nonnegative integrated cap vanishes iff RH; sharp Hermite heat-repair costs; shifted shallow Cauchy energy \(O(N)\) at depth \(1/\log T\) [L] (§10). Heat flow: finite support iff bounded nonreal counts as \(t\downarrow0\); high collisions are bounded uniformly iff the zeros approach the line, so the flow's own content is the near-axis count [S] (§9).

**A:** Cap/head data on compact regions; explicit nonreal-count bounds for \(H_t\) on compact time ranges; explicit constants in the shallow-energy bound.

**B:** Cap extinction or the all-height coefficient sign as heat tends to zero **[RH]**. A uniform nonreal count **[FS]**; a uniform high count is equivalent to LH plus finiteness for every cosine shift. [Ward receiver](../../../formal/GaloisForLFunctions/RHTower/XiWardGlobalCapAndFiniteHeadArithmetic.lean).

### LI — Paired Li balances

**Current:** Every-positive-rate lower floors for the prime–Gamma clock are RH-equivalent; RH is primitive nonpositivity of the Cayley–Li Toeplitz ladder, whose couplings do not decay [S].

**A:** Fixed paired histories, first-crossing and outside-correlation terms; finite Cayley ladders.

**B:** A subexponential floor for the literal primitive, or an arithmetic proof of the ladder sign **[RH]**. [Clock growth](../../../formal/GaloisForLFunctions/RHTower/LiEvenCrossActualClockGrowthLaw.lean), [Cayley ladder](../../../formal/GaloisForLFunctions/ArithmeticLorentzianGeometry/RHIsReflectionPositivityOfTheCayleyLadder.lean).

### SZ — Suzuki first variation

**Current:** The compact-\(L^2\) first variation equals the full Weil form. RH is equivalent to nonnegativity of the complete first variation on factorial and grid tent families, with exact limits retaining all Lévy, Gamma, prime-power and polar terms [S]. [RH-complete transfer](../../../formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiCriticalRHCompleteFamilyTransfer.lean).

**A:** Apply moving-aperture limits to specified tent families with low and mixed terms visible.

**B:** First-variation sign on the tent families **[RH]**.

### PM — Haar approximation / damped admission

**Current:** Global Haar approximation, cofinal signed-damping admission and positive gauge mass for every escape state are exact receivers. Record-minimum limits have \(K_L(p,p)\ge p^{2\varepsilon-2}\), which still permits zero gauge mass; a zero-cofactor limit forces a continuum of limits. [Record minima](../../../formal/GaloisForLFunctions/ArithmeticDefectRigidity/RecordMinimaForceInfiniteCofactorLimits.lean).

**A:** Fixed compact cofactor Grams; energy-transfer/residue formulas with effective pole orders.

**B:** Positive gauge mass for every escape state, or a complete-energy bound as damping tends to zero **[RH]**; exterior tightness and exclusion of infinite-height escape **[open]**. [Haar receiver](../../../formal/GaloisForLFunctions/RHTower/FermiNymanHaarApproximationEquivalence.lean).

### JAS — Joint ancestry

**Current:** Level-one prime-product positivity and finite-power square-shell bounds are exact receivers; unconditional signs reach a logarithmic prime budget; RH is the dressed-PSD condition at \(\sigma=1\) together with any quasi-RH.

**A:** Finite support/grade formulas; budget gaps on chosen shells.

**B:** The half-power prime budget or all-amplitude shell control **[RH]**. [Level-one capstones](../../../formal/GaloisForLFunctions/RHTower/JointAncestryLevelOneCapstones.lean).

### CTF — Chronological / Báez–Duarte approximation

**Current:** The residual is \((1-\Lambda\text{-readout})^2\) plus centered pronic energy; vanishing global error is RH-equivalent.

**A:** Optimize/certify finite rows; report both components with moving-tail errors.

**B:** Bounded rows with complete error tending to zero, or the dual-sampling bound **[RH]**. [Readout criterion](../../../formal/GaloisForLFunctions/BezoutValuationIncidence/VonMangoldtReadoutFormOfTheBaezDuarteCriterion.lean).

### HCF — Gaussian heat trace and two-grid signs

**Current:** Exact archimedean-minus-prime Gaussian traces; positivity on both literal \(\log2/\log3\) grids with polar cancellation is RH-equivalent; one grid aliases a nonreal pair to a positive atom.

**A:** Finite degrees/heights on both grids with explicit errors.

**B:** Both grid signs at all degrees and heights, or the one-sided vertical-growth bound **[RH]**. [Two grids](../../../formal/GaloisForLFunctions/RHTower/XiGaussianHeatTwoPrimeSourceSampling.lean).

### XN — Newton invariant discs

**Current:** Line-centred self-map discs covering all zeros give RH; the interior margin has an exact curvature formula.

**A:** Certify specified discs and curvature integrals.

**B:** A covering family with nonnegative interior margin **[RH]**. [Disc criterion](../../../formal/GaloisForLFunctions/RHTower/XiNewtonSchwarzPickCriticalLine.lean).

### BAG — Deterministic self-return

**Current:** Actual-\(\zeta\) recurrence throughout the right strip, or the positive-Haar-mass condition, is an RH receiver.

**A:** Finite-head return/error estimates on zero-free compact targets.

**B:** Recurrence at every right-strip point and tolerance, including possible target-zero neighbourhoods **[RH]**. [Return receiver](../../../formal/GaloisForLFunctions/RHTower/ZetaStrongRecurrenceReceiver.lean).

### EWU — Even pole-weight uniqueness

**Current:** Attained even blind minima give an exact all-aperture criterion; full positivity holds in high-scale windows, sparse unions and locally through radius \(181/500\). The criterion is the dual of a prime-free existence theorem: RH holds iff for every aperture some real weights, of any sign and growth, make the full Weil functional of \(\zeta\)'s archimedean datum nonnegative up to that aperture [L]. [Blind minima](../../../formal/GaloisForLFunctions/RHTower/EvenSectorBlindVariationalAttainment.lean), [finite-level existence](../../../formal/GaloisForLFunctions/RHTower/WeilPositivityFiniteLevelExistenceDecidesRH.lean).

**A:** Certify finite even blind problems; compute finite-level feasibility at increasing apertures.

**B:** Nonnegative blind minima at every aperture, paying low and mixed modes **[RH]**.

### GTA — Transverse Schur charge

**Current:** Rank-uniform decay of the positive quartic Schur charge is RH-equivalent.

**A:** Finite-rank charges with explicit rank dependence.

**B:** Arithmetic transverse-energy decay uniform in rank **[RH]**. [Decay equivalence](../../../formal/GaloisForLFunctions/RHTower/Hedenmalm/HedenmalmThetaSchurQuarticSpectralDecayEquivalence.lean).

### OWU — Odd Weil-weight uniqueness

**Current:** Exact odd/pole-hyperplane and dilation-ray criteria. Smooth odd witnesses at radius \(181/500\) separate \(\Lambda\) from Liouville and the first-prime flip; at radius \(23/40\) one witness has \(W_\Lambda>\|F\|^2/25\) and \(W_{\rm Liouville}<-\tfrac3{10}\|F\|^2\). These are finite-aperture separations; they persist under small \(n^{-\eta}\) perturbations (§2), so they cannot decide the sign.

**A:** Extend certified collar accounting with signed autocorrelations and both pole corrections.

**B:** The all-aperture actual-\(\Lambda\) odd sign **[RH]**; the conductor/forcing incompatibility **[open]**. [Dilation criterion](../../../formal/GaloisForLFunctions/RHTower/WeilDilationRayCriterion.lean).

### PBM — Pole-regularized prime series

**Current:** Convergence of the pole-subtracted coefficients at every real abscissa above \(1/2\) is an exact RH criterion.

**A:** Regularized partial sums and tails in controlled half-planes.

**B:** Critical-abscissa cancellation **[RH]**; any fixed abscissa below \(1\) **[≥QRH]**. [Regularized criterion](../../../formal/GaloisForLFunctions/RHTower/RegularizedLogZetaAbscissa.lean).

### RB — Robin / Nicolas extremizers

**Current:** Eventual criteria, reduction to colossally abundant integers, fixed valuation-defect margins.

**A:** Enumerate and certify finite extremal ranges.

**B:** The moving remainder on increasingly prime-saturated extremizers **[RH]**. [CA reduction](../../../formal/GaloisForLFunctions/RHTower/RobinColossallyAbundantReduction.lean).

### SRT — Lag localization and atomic visibility

**Current:** Every-width lag bounds and atomic receivers at widths \((\log\log N)^\alpha/N\), \(\alpha>1\) (§3); eventual full matrix positivity for one smooth plateau at every fixed \(0<c<1\) [S] (§4); for any prime and \(\varepsilon>0\), positivity on all towers of every pole-free generator supported in \([-\varepsilon,\varepsilon]\) is RH [S] (§2).

**A:** Instantiate fixed-width detectors; compute atomic Grams between \(K_\star\) and the first excitation, keeping Markov, full and pole-hyperplane forms apart.

**B:**
- An actual late-lag bound, an all-generator tower bound, or full sign at unbounded overlap **[RH]**.
- Touching/overlap transfer of the complete-matrix floor, with width and horizon controlled together **[open]** (Q1).
- An \(\alpha=1\) or bounded-overlap receiver by another synthesis **[open]**. The Gevrey-class obstruction applies to the stated construction, not every possible endpoint receiver.

[Lag receiver](../../../formal/GaloisForLFunctions/SquareRootThreshold/EveryWidthDecidesTheCriticalLine.lean).

### ACT — One-shift arithmetic criticality

**Current:** For one fixed theta shift, a full all-profile variation inequality gives odd Weil positivity and RH; short collars are absorbed with support-dependent shifts.

**A:** The signed moment ledger for a prescribed profile/shift.

**B:** One shift paying every support and profile **[RH]**. [Short-profile scope](../../../formal/GaloisForLFunctions/ArithmeticCriticalityTheory/ShortProfilePoleFreeVariationInequality.lean).

### AIP — Arithmetic incidence allocation

**Current:** Global joint allocation is exactly the odd sign. The route has complete-cell transfer and the \((\log\log N)^{1+\varepsilon}\) receiver; the finite-index chain; \(\Lambda\)-selection and the margin; the reduction "atomic sign iff Markov sign on \(p=0\) plus one affine scalar"; eventual full separated matrix positivity for a smooth plateau [S] (§4). The beyond-spacing Metzler gauge is obstructed.

**A:** Complete incidence matrices in multiresolution coordinates with every successor, Gamma and polar term; touching-level costs against the available margin.

**B:** Signed allocation on source-complete cells or an RH-complete family **[RH]**; touching/overlap transfer with every mixed charge retained **[open]** (Q1). [Allocation criterion](../../../formal/GaloisForLFunctions/ArithmeticIncidencePositivity/GlobalIncidenceAllocationCondition.lean).

### ACS — Arithmetic effectivity

**Current:** Source RR, effectivity, Rosati-height and chirality receivers coexist with complete-cell realization and index capture. Weighted coarse Gamma recovery and logarithmic detail payment share one horizon-independent error; the square-plus-odd layers have uniform finite index (§6). On every signed Haar section, rooted divisor squares give D≥log(2)·mass/12 and both original poles leave D+P≥D/8≥mass/144, including the whole head. The full one-level Haar Gamma cross-error is at most \(16e^{1/2}\) times mass [L]. The actual divisor reserve now has the exact complete valuation identity D+T=½Σ occupation+R at q_p=1/p, with T,R≥0, original-domain membership and full summability proved [L]. T is the explicit Euler-minus-outgoing diagonal cost. Joint payment of T, the Gamma error, exact arithmetic diagonal and central mass remains open; neither the mass bound nor the nonnegative added cost supplies that payment. One prime tower sees every outer eigenvalue (§2).

**A:** Transport fixed source families into complete smooth cells; compute projection and finite-sieve data.

**B:** Full-source quadratic RI with degree-zero subquadratic growth, a Rosati-height lower bound, or complete-cell index zero **[RH]**; uniform finite index **[FS]**. [Effectivity receiver](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/ExactArithmeticSourceEffectivity.lean).

## Route candidates and promotion obstacles

A candidate lacks an independent source construction or its landing. Every promotion gap is **[open]** and becomes **[RH]** once it is the final sign. A sufficient hypothesis must fail for the selectivity battery: the Liouville twin, single-prime flips with the maximal margin, and the perturbations \(\Lambda+\varepsilon n^{-\eta}\) (§§1–2).

| Candidate | Established mechanism | A — Just work | B — Promotion gap |
|---|---|---|---|
| **APF — Arithmetic paired Fredholm** | Actual cycle traces have arithmetic Fourier reconstruction. | Fixed cycles, flows and finite mixtures with truncation control. | Zero-independent divisor exhaustion and trace vanishing. [Source](../../../formal/GaloisForLFunctions/RHTower/PaperZetaCycleFourierReconstruction.lean). |
| **BSH — Arithmetic mate curvature** | Framed composition curvature vanishes exactly at critical half-density. | Finite curvature/cocycle identities and calibration. | A pre-divisor section and actual mate identity forcing the vanishing. [Source](../../../formal/GaloisForLFunctions/RHTower/Deninger/DeningerOneSidedFramedMateCurvatureTransgression.lean). |
| **CDC — Constitutive dagger** | Calibrated confluent potentials exist exactly on the critical line. | Finite repair/exchange defects. | One arithmetic potential descending on every fibre before divisor restriction. [Source](../../../formal/GaloisForLFunctions/RHTower/ConstitutiveDaggerConfluence.lean). |
| **DR — Dyadic roots** | Dyadic levels extend to the Littlewood zero-free cusp. | Glue roots on known zero-free charts. | Compatible extension to the whole strict-right domain. [Source](../../../formal/GaloisForLFunctions/RHTower/XiSymmetricLittlewoodZeroFreeCuspDyadicRoots.lean). |
| **EGC — Pole-safe contour** | Complete copy correction; nonzero Gamma baseline. | Corrected contours; baseline separation. | Outer-contour orientation excluding off-line copies. [Source](../../../formal/GaloisForLFunctions/RHTower/PaperEGCSourceRayBaseline.lean). |
| **EWJ — Euler/Wold jets** | Three-channel histories converge; compact quotient character. | Fixed jets and quotient characters. | Source admission and norm exhaustion across depth. [Source](../../../formal/GaloisForLFunctions/RHTower/PaperEulerWoldDepthHistory.lean). |
| **FEL — Theta likelihood** | Entropy bookkeeping; convergent BSY zero-sum identity. | Predeclared finite histories and contrasts. | Cofinal balance from arithmetic, independently of zeros. [Source](../../../formal/GaloisForLFunctions/RHTower/BalazardSaiasYorZeroSum.lean). |
| **HJ — Hurwitz reflection** | Two-seed residual equals SEC charge; HCF two-grid bridge. | Convergent fibres; coordinate translation. | Pre-divisor forcing of residual vanishing. [Source](../../../formal/GaloisForLFunctions/RHTower/PrimeTailSeedHurwitzReflection.lean). |
| **IRK — Rotation-algebra trace** | Completed Xi-jet relation invertible exactly off the line. | Finite jet inverses and traces. | Charged arithmetic Poisson lift with integral analytic count. [Source](../../../formal/GaloisForLFunctions/RHTower/PrimeRotationXiCompletedResolution.lean). |
| **MSC — Möbius–Sonin transport** | Squarefree-discrepancy Hilbert source recovers moments; divisor transport. | Evaluation jets and readouts. | Source-faithful nonnegative Sonin/Weil energy. [Source](../../../formal/GaloisForLFunctions/RHTower/SquarefreeDiscrepancyHilbertTransport.lean). |
| **PCS — Singular prime co-shift** | Exact shift-plus-defect decomposition; strong finite-prime convergence. | Retained defect and cutoff errors. | Wall annihilation retaining the forward mode. [Source](../../../formal/GaloisForLFunctions/RHTower/PCSChronologicalDilationCarrierObstruction.lean). |
| **PTR — Photonic realization** | Lossless products real-rooted; Xi-limit criterion. | Finite stacks and transfer functions. | Prime-faithful nonlocal port built without Xi zeros. [Source](../../../formal/GaloisForLFunctions/RHTower/PhotonicLosslessProductPortRH.lean). |
| **RFHM — Support/grade forcing** | Full support/phase/grade admission; norm law. | Coherent defects and grade observables. | A source law sensitive to arithmetic phase/depth orientation. [Source](../../../formal/GaloisForLFunctions/RHTower/PaperRFHMSurvivalInformation.lean). |
| **SC — Stokes/Witt–Krein** | Rigged chambers; a.e. Fourier reconstruction. | Finite cross-fibre coordinates. | Arithmetic cross-fibre index selecting the wall; a finite index would land in the [FS] stratum. [Source](../../../formal/GaloisForLFunctions/RHTower/PaperKreinWallFourierCompletion.lean). |
| **SEC — Adjacent prime seam** | Seam-charge/essential-norm and factorial-Fock criteria. | Finite jets and seam charges. | All-order Fock boundedness or eventual compactness. [Source](../../../formal/GaloisForLFunctions/RHTower/TimeOneGammaJetFockRHCriterion.lean). |
| **W1C — Clifford–Dirac / Lee–Yang** | Ferromagnetic Ising limits to Riemann's law force RH. | Finite couplings and density constraints. | Source-defined centred couplings or a faithful scattering operator. [Source](../../../formal/GaloisForLFunctions/RHTower/IsingLawConvergenceRH.lean). |
| **WBF — Source certificates** | Abstract genealogy Gram and relative Fredholm recovery. | Certificate streams and determinants. | Arithmetic stream with uniform-depth landing on Xi/Weil data. [Source](../../../formal/GaloisForLFunctions/HTGeometry/PaperCriticalGenealogyCompletion.lean). |
| **PW-B — PM cusp branch** | Native two-response action with cutoff-independent limit. | Admitted positive-damping actions. | Remove zero indexing; prove the ceiling→optical→cap→extinction chain. [Source](../../../formal/GaloisForLFunctions/RHTower/ThetaCusp/ThetaCuspHawkingBMPWNativeTwoResponseAction.lean). |

## Supporting programmes

| Programme | Contribution | Unresolved input |
|---|---|---|
| SMAP | Selection theorem; margins \(2\log2\)/\(0\); multiresolution and level couplings; selective Gårding; one-prime tower sign is RH at every generator size [S]; precision rigidity [S] | Selective positivity where overlap begins; the signed cross-level prime coupling |
| ACP (counting positivity) | Gap \(\ge(2\log2)c_N^2\); parity fibre counts; submaximal [L] and maximal [S] gaps attained by failing multiplicative twins | A selective input beyond the gap |
| AID, SAHT, ACS cells | Actual mean-preserving stopping averages and complete even-power head error with explicit projected-Gamma cost [K]; square-plus-odd and \(k\ge3\) finite index; Chebyshev identity; Gamma reserve; canonical critical energy; all-level L², fixed Euler and all-prime higher-power approximation [K]; one-prime tower law | \(k=1\) layer ([FS]); residual sign; upper bound on \(\mathcal E_{\rm crit}\) |
| RAPT, CACT | Sharp gap; exact bounded complete spectrum [S]; smooth-plateau positivity of the whole matrix at each fixed \(c<1\) [S] | Touching/overlap and growing-conductor control; RH-complete exhaustion |
| SSHA, ALG | Atomic receivers to \((\log\log N)^{1+\varepsilon}\); narrow arbitrary-shape positivity; gap/scalar reduction; Metzler selectivity; count-based local-to-global over \(\mathbb F_q\) | Full sign on overlapping/RH-complete families; local-to-global over \(\mathbb Z\) |
| HKT | Krein–Langer index formula on groups; index closed under pointwise limits [S] | An arithmetic positive part and an index ceiling for \(\zeta\)'s kernel |
| SCP | Shallow Cauchy energy \(O(N)\) at depth \(1/\log T\); squared multiplicities; joint shallow/deep budget | A displacement-sensitive constant |
| Zeta23 (external), IGP, TTPC | \(2/3\), \(HD(1)\), \(0.8876\) simple-or-critical; exchange rate; \(3/4\) reduction; coalescent anatomy | A two-sided trans-threshold pair estimate |
| RHTower depth/heat | Finite support \(\Rightarrow\) zeros approach the line \(\Rightarrow\) LH \(\wedge\) QRH; heat high/near-axis split; reality horizon; local \(\xi\) cofactor | Near-axis count; any vanishing mechanism |
| BVI, ArithmeticCompensation, SignedSuccessor | Readout/pronic decompositions; escaped VK decay; strip dictionaries | Any fixed power saving |
| ACP (correspondence), ADR, ACG | Escape classification, gauge-mass criterion, prime-error/genus laws, Stepanov mechanism, elliptic Mertens budget = strict Hasse | Visibility of every escape state; actual cancellation |
| AES, CDG, PL, RBG, BGG, AIT | Field/virial laws, theta-prefix detectors, collided polarization, renormalization survival, positive-deformation rigidity, torsion intersection | Upper sign or cap on the computed defect |
| APD, MPG, SBWF, AE, ArtinMertens, HLF | Positive-measure rigidity, boundary capacity, finite-field calibration, Frobenius densities, Hecke \(L\)-series past \(\operatorname{Re}s=1\) [S] | An independent arithmetic positivity input |

## External mathematical status

RH is listed as unsolved by [Clay](https://www.claymath.org/millennium/Riemann-Hypothesis/). Proofs below are not validated by this review.

- **Alpöge–Furman two-thirds theorem.** An external, formalized package (`Zeta23`, pinned in the Lake manifest) proving that at least \(2/3\), and with the Montgomery–Taylor window \(HD(1)=0.6725\ldots\), of zeros are simple and on the critical line. The corpus builds §10 on it. Its standing in the literature is not assessed here.
- **Quasi-RH manuscript.** A September 2026 [manuscript](https://github.com/openai/math/blob/main/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf) claims Dirichlet zero-freeness for \(\operatorname{Re}s>7/8\). The corpus intake (`RHTower/ChenGuptaLi*`, 279 modules) covers the zero detector, Lemmas 3.3, 4.1, 4.2, 4.5, 6.2, Propositions 4.6 and 5.1, and the exponent consolidation to \((qT)^{7(1-\sigma)/3}\). It has no zero-free capstone; the continuation/contour step is not formalized. The Proposition 4.6 envelope has floor \(288\) against the collision quantum \(2\), which blocks an RH endpoint, not the \(7/8\) claim. [Collision no-go](../../../formal/GaloisForLFunctions/RHTower/ChenGuptaLiHorizontalCollisionNoGo.lean).
- **Ordinary-correlation manuscript.** A September 2026 [manuscript](https://github.com/openai/math/blob/main/preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/final.pdf) claims fixed-form Liouville two-point bounds \(X/(\log X)^c\): neither a power saving nor uniform in growing shifts.
- **Published results used as context.** [Lorentzian polynomials](https://arxiv.org/abs/1902.03719); the de Bruijn–Newman bound \(\Lambda\le0.2\); Ki–Kim–Lee finiteness of nonreal zeros of \(H_t\) for \(t>0\); Bourgain's density hypothesis for \(\sigma\ge25/32\); Montgomery's pair correlation on \(|\alpha|\le1\) under RH. None supplies zero exclusion.
