# Research routes and their mathematical obstacles

Status: 28 October 2026, corpus commit `389e3f1d10`. **RH remains open.** The inventory is 31 live routes, 17 standalone candidates and the PW-B branch of PM. Every live route has an exact RH receiver; none has the arithmetic input that receiver needs.

Companions: [summary, open problems and next questions](obstacles-summary.md) · [walls ledger](walls-ledger.md) · [route unification](route-unification-ledger.md) · [frontier map](../rh-current-frontier-map.md) · [scoped obstructions](../rh-killed-routes.md).

## How to read this report

Evidence comes from corpus searches followed by inspection of Lean statements, module docstrings and proof structure. No builds or kernel audits were run. **[S]** marks working source as in the [frontier map](../rh-current-frontier-map.md) (unintegrated, unfinished, or first committed on 28 October 2026). **(inference)** marks a conclusion drawn by this review from proved statements; it is not a Lean theorem. Research record: [working log](../../../logs/review-2810-v2-research-2026-10-28.md).

Obstacles are split into two classes:

- **A — Just work.** The ingredients exist: a finite computation with certified error terms, an instantiation of a proved theorem, transport of a supplied bound between proved dictionaries, or formalization of a written proof. A-items can be large. They never promise that a desired sign is true.
- **B — Open mathematics.** A missing inequality, construction or uniformity. Tags:
  - **[RH]** equivalent to RH;
  - **[RH+]** strictly stronger than RH, for example also forcing simple zeros;
  - **[≥QRH]** implies a fixed zero-free strip \(\Theta<1\), so it is at least as hard as the quasi-Riemann hypothesis, which is unproved in the literature apart from a pending external claim;
  - **[open]** an intermediate problem with no solution in the corpus or the literature consulted, possibly solvable without RH-strength input.

A conditional receiver does not prove its input. A false proposed estimate belongs in neither class.

## The frontier in ten results

### 1. Selectivity is now a theorem, and its size is known

The SMAP programme turns the old "twin-blindness" observation into Lean statements.

- **Selection.** A bounded weight \(|\lambda|\le\Lambda\) is eventually positive on atomic families at some root iff RH holds and \(\lambda=\Lambda\) on \(n\ge2\). No family of bounded weights containing a weight other than \(\Lambda\) is uniformly atomic-positive at a root. [Selection](../../../formal/GaloisForLFunctions/SelectiveMultiscaleArithmeticPositivity/PositivityAtEveryRootSelectsTheVonMangoldtWeight.lean).
- **The margin is exactly \(2\log2\).** The multiplicative walk has Poincaré constant \(2\log2\): \((2\log2-\varepsilon)\operatorname{Var}_{1/n}(\sqrt n\,x)\le D_N(x)\) eventually, so \(P_N\le(\log N-\gamma-2\log2+\varepsilon)|x|^2\) on the harmonic hyperplane \(\sum x_n/\sqrt n=0\). The proof is complete; the module docstring still carries an obsolete work-in-progress line. The conductor-two excitation shows \(2\log2\) is optimal. The Liouville twin has optimal gap \(0\), and every sign gauge \(\omega^2=1\) has gap at most \(2\log2\). [Sharp gap](../../../formal/GaloisForLFunctions/RenormalizedArithmeticPotentialTheory/TheSpectralGapOfThePrimeFormIsTwoLogTwo.lean), [selective margin](../../../formal/GaloisForLFunctions/SelectiveMultiscaleArithmeticPositivity/TheSelectiveMarginIsTwoLogTwo.lean), [first excitation](../../../formal/GaloisForLFunctions/SelectiveMultiscaleArithmeticPositivity/TheConductorTwoIsTheFirstExcitation.lean).
- **What the margin reads.** With \(S_N=\sum_{n\le N}\omega(n)/n\) and \(H_N=\sum_{n\le N}1/n\): \(S_N^2=o(\log N)\) kills every positive gap, while \(S_N/H_N\to1\) keeps \(2\log2\). Every finite coefficient flip of \(1\) keeps the full margin, so the maximal margin does not single out \(\zeta\). [No correlation](../../../formal/GaloisForLFunctions/SelectiveMultiscaleArithmeticPositivity/AMarginNeedsHarmonicCorrelation.lean), [full correlation](../../../formal/GaloisForLFunctions/SelectiveMultiscaleArithmeticPositivity/FullCorrelationKeepsTheMargin.lean).
- **Where it acts.** On atomic tests the pole hyperplane \(A(f)=0\) is the harmonic hyperplane. Below the spacing, a sign twin differs from \(\zeta\) only in the prime form: the archimedean diagonal and both pole moments cancel exactly. At narrow widths on that hyperplane, \(W\ge(\varphi_0+c_0G)\|f\|^2\), and the Liouville twin lies below \(\zeta\) by a margin uniform in \(N\). The sharp selective Gårding inequality holds with reserve \(c_0(2\log2-\eta)\). [Harmonic hyperplane](../../../formal/GaloisForLFunctions/SelectiveMultiscaleArithmeticPositivity/ThePoleHyperplaneIsTheHarmonicHyperplane.lean), [separation](../../../formal/GaloisForLFunctions/SelectiveMultiscaleArithmeticPositivity/ThePoleHyperplaneSeparatesTheFullWeilForms.lean), [Gårding](../../../formal/GaloisForLFunctions/SelectiveMultiscaleArithmeticPositivity/TheSelectiveGardingInequality.lean).

So the selective input is identified and measured: a gap of exactly \(2\log2\) on a discrete hyperplane, proved at narrow widths. Turning it into positivity where overlap begins is the open step.

### 2. Atomic receivers reach \((\log\log N)^{1+\varepsilon}\) overlap

- RH holds iff \(W\ge0\) eventually on atomic families of width \((\log\log N)^\alpha/N\), for every \(\alpha>1\) (Denjoy–Carleman profiles of class \(1+1/r\)), and for \(\alpha>2\) with an explicit Gevrey-2 profile. Smooth profiles give widths \((\log N)^\alpha/N\), \(\alpha>0\). [Denjoy–Carleman](../../../formal/GaloisForLFunctions/SpacingScaleHarmonicAnalysis/TheDenjoyCarlemanProfiles.lean), [Gevrey profile](../../../formal/GaloisForLFunctions/SpacingScaleHarmonicAnalysis/TheGevreyProfile.lean).
- **The receiver stops at \(\alpha=1\) (inference).** A window \((\log\log N)^{s}\) needs a compactly supported profile of Gevrey class \(s\). Class \(s=1\) is quasi-analytic, so the Denjoy–Carleman theorem excludes compact support there. The \(\alpha=1\) gap is a boundary of this synthesis method, not a missing computation.
- Under overlap growth the Markov form is negative unconditionally. RH is equivalent to Markov nonnegativity on the pole hyperplane. [Pole](../../../formal/GaloisForLFunctions/SpacingScaleHarmonicAnalysis/ThePoleIsTheOnlyNegativeSquareBeyondTheThreshold.lean).
- **At every width,** \(W\ge0\) on atomic tests iff \(M\ge0\) on the pole complement \(p=0\) and \(M+2a_0B\ge0\) on the affine hyperplane \(p=1\). Beyond the Robin–Euler threshold the Markov form has exactly one negative direction, the pole vector [S]. [Gap and one scalar](../../../formal/GaloisForLFunctions/ArithmeticLorentzianGeometry/TheHodgeIndexIsAGapOnThePoleComplementAndOneScalar.lean).

### 3. Narrow positivity reaches a quarter of the Robin–Euler threshold

- Eventually \(W\ge0\) on every window test \(\sum_nG_n(\cdot-\log n)\) with arbitrary \(C^2\) shapes \(G_n\) at widths \(w\le K_\star\delta_N\), \(\delta_N=\log(1+1/N)\). With PNT-sharpened Hardy weights and a halved cross penalty, \(K_\star\approx0.108\) of the spacing for plateau profiles: a quarter of the Robin–Euler threshold \(\approx0.43\). For arbitrary profiles \(K_\star\approx0.072\) [S]. The method keeps absolute values on the pole term, which holds it below about half the threshold even with optimal constants. [Quarter](../../../formal/GaloisForLFunctions/ArithmeticLorentzianGeometry/TheStabilityRegimeReachesAQuarterOfTheRobinEulerThreshold.lean), [every test near the logarithms](../../../formal/GaloisForLFunctions/ArithmeticLorentzianGeometry/WeilsFormIsPositiveOnEveryTestNearTheLogarithms.lean).
- **Arithmetic modes at the spacing scale.** For the Ramanujan profile of conductor \(m\ge2\) at width \(K/N\), \(0<K<1/4\):
  \[
  \frac{W(f_N)}{\|f_N\|^2}\to\log\frac{K_m}{K},\qquad K_m=\frac{m\,e^{d(m)}e^{\beta(\varphi)/\|\varphi\|^2}}{2\pi},
  \]
  where \(d(m)=\sum_{p\mid m}\log p/(p-1)\) is the tame different. \(K_m\) is the Robin–Euler ratio \(K_1=e^{\beta(\varphi)/\|\varphi\|^2}/(2\pi)\) of the pole multiplied by \(m\,e^{d(m)}\); for the first excitation \(m=2\) the factor is \(4\). The law is proved below a quarter of the spacing only [S]. [Mode energies](../../../formal/GaloisForLFunctions/RenormalizedArithmeticPotentialTheory/TheWeilEnergiesOfTheArithmeticModes.lean).

### 4. The prime form has a known bottom spectrum

Below \(\log N-\gamma\), the spectrum of \(P_N\) within distance \(T\) comes only from integers with \(\log m+d(m)<T\). Actual spectral counts equal adjunction counts, and each adjunction energy \(E_m=\gamma+\log m+d(m)\) carries eventually one actual eigenline converging to its Ramanujan line [S]. Fixed finite conductor packets are realized; growing-conductor control is open. [Top spectrum](../../../formal/GaloisForLFunctions/RenormalizedArithmeticPotentialTheory/TheTopSpectrumOfThePrimeFormIsExhaustedByTheIntegers.lean), [counts](../../../formal/GaloisForLFunctions/RenormalizedArithmeticPotentialTheory/TheBoundedPrimeSpectrumIsTheAdjunctionSpectrum.lean), [eigenlines](../../../formal/GaloisForLFunctions/RenormalizedArithmeticPotentialTheory/TheSimplePrimeEigenlinesConvergeToRamanujanLines.lean).

### 5. The complete source: the finite-index chain stops at the first prime layer

- Complete logarithmic cells recover every mixed Weil entry. They form a dyadic multiresolution: \(C_{2a}+C_{2a+1}=T_{\log2}C_a\), and every twisted Weil pairing is level-Toeplitz. In dyadic coordinates prime two acts as the unilateral shift on every generator chain. [Multiresolution](../../../formal/GaloisForLFunctions/SelectiveMultiscaleArithmeticPositivity/TheCompleteSourceIsADyadicMultiresolution.lean), [level matrix](../../../formal/GaloisForLFunctions/SignedArithmeticHodgeTheory/ArithmeticTranslationsHaveAnExactDyadicLevelMatrix.lean).
- Gamma pays all logarithmic detail mass, a mean graph on pair averages and all dyadic parent variances at once. Balanced sections above one index carry a full-form floor uniformly in the horizon. That floor holds for every twist \(|\omega|\le1\), Liouville included. [Floor](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/HaarCellEffectivity.lean), [twin-blind](../../../formal/GaloisForLFunctions/SelectiveMultiscaleArithmeticPositivity/TheHaarFloorIsTwinBlind.lean).
- **Uniform finite index, layer by layer [S].** Gamma minus each of the following has negative dimension bounded by one fixed detail head, independent of horizon and family:
  - the all-prime mixed block with exponents \(k\ge3\), whose tail constant \(4\sum_p\sum_{k\ge3}\log p/p^{k/2}\) is finite;
  - the whole signed prime-two Euler mixed source, paid through the Gamma mean graph;
  - every fixed finite prime set \(P\), with constant \(C_P=\sum_P4\log p/(\sqrt p-1)\).

  The regular even-power boundary symbol lies below Gamma by at least \(\gamma_E\). [k≥3](../../../formal/GaloisForLFunctions/ArithmeticIndexDescent/AllHigherPrimePowerMixedFormsHaveUniformFiniteIndex.lean), [prime two](../../../formal/GaloisForLFunctions/ArithmeticIndexDescent/TheGammaMeanGraphPaysThePrimeTwoMixedBlock.lean), [square boundary](../../../formal/GaloisForLFunctions/ArithmeticIndexDescent/TheSquarePrimeBoundaryHasAGammaGap.lean).
- **What remains:** the first prime layer \(k=1\) over all primes, where \(C_P\) diverges like \(\sum_p\log p/\sqrt p\); the square layer with its pole restored; the pure coarse source; and the poles. The poles have rank two and cost at most one negative direction. The divergence of \(C_P\) is the exact point where absolute, twin-blind payment ends.
- Finitely many full generator orbits approximate every finite cell source in \(L^2\) (error \(\le32\Gamma(f)/(1+\log A)\)). A single Haar generator has an infinite orthogonal orbit of fixed Gamma energy, so this is not compactness [S]. [Orbits](../../../formal/GaloisForLFunctions/SignedArithmeticHodgeTheory/FiniteGeneratorOrbitsApproximateThePhysicalCellSource.lean), [noncompact](../../../formal/GaloisForLFunctions/SignedArithmeticHodgeTheory/CompactDetailsDoNotMakeTranslationOrbitsCompact.lean).

### 6. Cross-level couplings: three paid, one structural

Between copies of one generator at dyadic levels \(j<k\), \(d=k-j\):

| Part | Law | Status |
|---|---|---|
| Pole | \(2A(f)B(f)\cosh(d\log2/2)\): rank two, hyperbolic, vanishes on \(\sum_jc_j2^{-j/2}=0\) | Removed by one linear condition |
| Gamma tail | \(\le\pi e^{-2\,\mathrm{gap}}(\|f\|^2+\|g\|^2)\), i.e. \(\pi4^{-(d-1)}\) | Summable |
| Touching levels | \(\le C_\ell(\|f\|^2+\|g\|^2)\), uniform under translation | Bounded |
| Prime comb / Chebyshev error | \(-\int(e^h-\psi(e^h)-c)\,q'(h)\,dh\) | Open |

[Pole](../../../formal/GaloisForLFunctions/SelectiveMultiscaleArithmeticPositivity/ThePoleCouplesTheLevelsHyperbolically.lean), [separated](../../../formal/GaloisForLFunctions/SelectiveMultiscaleArithmeticPositivity/SeparatedLevelsCoupleThroughTheChebyshevError.lean), [touching](../../../formal/GaloisForLFunctions/SelectiveMultiscaleArithmeticPositivity/TouchingLevelsCoupleUniformly.lean), [renormalization calculus](../../../formal/GaloisForLFunctions/SelectiveMultiscaleArithmeticPositivity/ALevelIsPaidByItsReserve.lean).

**The open part is never a summable cost (inference).** By the explicit formula, \(d\mapsto W(f,T_{d\log2}g)\) is \(\sum_\rho\hat f(\rho)\overline{\hat g(1-\bar\rho)}\,2^{d(\rho-1/2)}\) up to normalization.

- Under RH this sequence is almost periodic in \(d\) with positive Bohr mean square for generic \(f,g\). It is bounded and does not decay.
- Off RH it grows exponentially.

So the renormalization calculus (summable couplings keep a margin) can pay Gamma, touching and pole terms but never the prime part between generator orbits. Positivity of the generator-orbit form is positivity of a matrix Toeplitz sequence. By Herglotz's theorem that is positivity of the zero measure pushed to the circle by \(\gamma\mapsto\gamma\log2\): a one-prime RH-type statement. The same lattice phenomenon appears in [the Stepanov mechanism](../../../formal/GaloisForLFunctions/ArithmeticCorrespondencePositivity/SparseAnnihilatorsAndTheStepanovMechanism.lean): \(1-T_p^N\) kills a zero symbol iff the zero is critical and on a height lattice. Reducing the complete source to finitely many orbits therefore relocates the difficulty without lowering it.

### 7. Ordered entries are centered Chebyshev integrals

For real tests \(f\) left of \(b\) and \(g\) right of \(b\), and every \(c\):
\[
W(f,g)=-\int_0^\infty\big(e^h-\psi(e^h)-c\big)\,q'_{f,g}(h)\,dh-\Gamma_{\rm tail}(f,g),\qquad q_{f,g}(h)=e^{-h/2}\!\int f(u)g(u+h)\,du.
\]
The Gamma tail is a localized mass minus a nonnegative square reserve. The Gamma boundary operator has norm \(\pi/2\), attained by no nonzero input, with no uniform relative reserve [S]. [Chebyshev identity](../../../formal/GaloisForLFunctions/ArithmeticIndexDescent/TheOrderedWeilSourceIsACenteredChebyshevDefect.lean), [square reserve](../../../formal/GaloisForLFunctions/ArithmeticIndexDescent/TheOrderedWeilSourceRetainsItsGammaSquareReserve.lean).

### 8. Finite off-line support has exact receivers and costs at least a strip

| Receiver of finite off-line support | Source |
|---|---|
| \(\mathcal E_{\rm crit}<\infty\), bounded work, \(\Delta\mathcal W\to0\) or eventually \(\le39/50\), bounded spline index | [AID](../../../formal/GaloisForLFunctions/ArithmeticIndexDescent/TheCriticalSourceRateHasACanonicalEnergy.lean) |
| Prime lag minus finitely many exponentials bounded on one side | [lag](../../../formal/GaloisForLFunctions/RHTower/FiniteOffLineConverse.lean) |
| Uniformly bounded cosine defects | [cosine](../../../formal/GaloisForLFunctions/RHTower/XiCosineShiftBoundedDefectFiniteOffLine.lean) |
| Uniformly bounded nonreal zero counts of the heat-flowed \(H_t\), \(t>0\) | [heat count](../../../formal/GaloisForLFunctions/RHTower/DeBruijnNonrealCountRightLimit.lean) |

The RH threshold is \(\mathcal E_{\rm crit}\le Q_*=1294047/2000\), and a finite index \(k\) costs \(\mathcal E_{\rm crit}\ge\max\{(Q_*/2)k,50k^2-3k/2\}\) [S].

- Finite off-line support forces a zero abscissa \(\Theta<1\). [Index exit](../../../formal/GaloisForLFunctions/ArithmeticOrientationGeometry/TheIndexExit.lean).
- For \(0<t\le1/8\), every zero of \(H_t\) with \(|\operatorname{Re}z|\ge2\pi e^{(27/40+\varepsilon)/t}\) is real and simple [S]. [Reality horizon](../../../formal/GaloisForLFunctions/RHTower/KiKimLeeInteriorLindelofHorizon.lean).

### 9. Critical-line census: two thirds, imported and extended

The corpus imports the external, formalized Alpöge–Furman theorem (Lean package `Zeta23`, pinned in the Lake manifest). Its mechanism is a Sylvester-inertia **rank–trace inequality**:

- the explicit-formula Gram splits as a positive part from critical zeros plus an indefinite part from off-line pairs with bounded positive index;
- its Frobenius norm is computed from primes through Montgomery's pair correlation on \(|\alpha|\le1\).

| Census statement | Value |
|---|---|
| Simple critical zeros, all zeros counted with multiplicity | \(\ge2/3\); \(\ge HD(1)=0.6725007\ldots\) with the Montgomery–Taylor window |
| Off-line zero copies | \(\le1-HD(1)\) |
| IGP slack (MT kernel vanishes only on two narrow intervals, so short triples cannot be orthogonal) | \(HD(1)+10^{-8}\) |
| Distinct ordinates carrying a critical zero | \(\ge4/5\) |
| Zero copies within \(4/\log T\) of the line | \(\ge3/4\) |

Mollified value moments cannot raise these numbers: an equal-valued reflected pair has every value moment of two critical zeros, so they certify simple zeros of either kind, not critical ones ([mimicry](../../../formal/GaloisForLFunctions/RHTower/ValueMomentsCannotSeparateReflectedPairs.lean)).

[Two thirds](../../../formal/GaloisForLFunctions/RHTower/Zeta23SimpleCriticalDensity.lean), [off-line copies](../../../formal/GaloisForLFunctions/RHTower/Zeta23OffLineMultipleExclusionMontgomeryTaylor.lean), [IGP](../../../formal/GaloisForLFunctions/IncommensurableGaborPinching/CriticalLineZeroProportion.lean), [ordinates](../../../formal/GaloisForLFunctions/RHTower/Zeta23CriticalOrdinateCensus.lean), [near line](../../../formal/GaloisForLFunctions/RHTower/Zeta23SimpleOffLineNearLine.lean).

### 10. Over finite fields the local-to-global step is a count

- For curve data with nonnegative counts, weighted trickle-down on every Frobenius ladder is equivalent to the one-sided square-root count \(N_k\ge q^k+1-Cq^{k/2}\). Hyperelliptic curves pass it by Stepanov's count, and the golden fake fails it.
- The local Lorentzian input at one prime is exactly RH for the local factor; for genus one, depth one is the Ramanujan bound. "The whole content of the Hodge index over \(\mathbb Z\)" is the local-to-global step.
- Hyperbolicity of the atomic Gram holds for every completely multiplicative sign twin, so it is blind. The Metzler sign holds below the spacing for \(\zeta\) and fails in every gauge for any twin that flips a prime.
- RH is reflection positivity of the Cayley–Li ladder, whose couplings never decay [S].

[Count](../../../formal/GaloisForLFunctions/ArithmeticLorentzianGeometry/TheTrickleDownInequalityIsTheSquareRootCount.lean), [local factor](../../../formal/GaloisForLFunctions/ArithmeticLorentzianGeometry/TheLocalFactorTricklesDownByRamanujan.lean), [hyperelliptic RH](../../../formal/GaloisForLFunctions/RHTower/HyperellipticRiemannHypothesis.lean), [blind/selective](../../../formal/GaloisForLFunctions/ArithmeticLorentzianGeometry/HyperbolicityIsBlindTheSignIsNot.lean), [Cayley ladder](../../../formal/GaloisForLFunctions/ArithmeticLorentzianGeometry/RHIsReflectionPositivityOfTheCayleyLadder.lean).

## Live routes

Each entry lists the current state, then A (just work) and B (open). The [frontier map](../rh-current-frontier-map.md#live-routes) has full source lists.

### WL — Weil lag / prime-error energy

**Current:** Bounded critical deficit energy, a lower bound on coprime cross-work and a linear cumulative prime-error energy budget are each equivalent to RH. Eventual \(\psi(x)-x\le C\sqrt x\log^2x\) is equivalent to RH. Abel-slope saturation at the archimedean genus is equivalent to RH plus simple zeros. The prime error is literally the separated off-diagonal of the complete form (§7) and the only unpaid cross-level coupling (§6).

**A:** Evaluate fixed truncations with certified archimedean and high-zero tails; transport lag/count/energy dictionaries with constants; tabulate \(d\mapsto W(f,T_{d\log2}g)\) for the cell-1 generator to exhibit its almost-periodic profile.

**B:** The actual one-sided prime-error or cross-work bound **[RH]**; finitely-many-exponential version **[≥QRH]**; genus saturation **[RH+]**, not usable as an RH premise. [Receiver](../../../formal/GaloisForLFunctions/BiScaleUncertainty/WeilLagCriticalDeficitEndpointAndLimitLaw.lean).

### RW — Restricted Weil ground energy

**Current:** RH iff the ground minimum is positive at every finite aperture. The minimum strictly decreases with an exact shell decomposition, and finite-aperture Gårding allows a nonzero negative index. Positive floors must decay doubly exponentially. Gamma boundary: norm \(\pi/2\), exact square reserve, no uniform relative reserve [S].

**A:** Certified finite-aperture variational bounds and shell/error ledgers; instantiate the Gamma square reserve in the shell flux.

**B:** Cumulative aperture relaxation bounded by the initial energy, paying low modes, prime collars and polar terms **[RH]**. Frozen finite-prime families become negative, so telescoping supplies nothing. [Aperture flow](../../../formal/GaloisForLFunctions/ArithmeticContinuationAndCriticalEnergy/TheApertureFlowNeverStalls.lean).

### FU — Signed prime scheduling

**Current:** An eventual upper bound on the normalized completed Abel moment is equivalent to RH. Narrow translated prime channels have a useful sign; universal nonpositivity fails on dyadic windows.

**A:** Assemble seed, drift, earlier-history, cross-block and endpoint terms for a fixed schedule with existing clock kernels.

**B:** The joint signed total over a prime-exhaustive schedule **[RH]**. [Receiver](../../../formal/GaloisForLFunctions/RHTower/CCM/CCMFUSuzukiMobiusDivisorOneSided.lean).

### RP — Matched–quantile history floor

**Current:** An eventual linear defect floor is RH-equivalent; low-LCM payment and exact signed history identities exist.

**A:** Expand fixed histories, instantiate low-LCM estimates, expose the high-LCM/moving-core remainder.

**B:** The complete floor with high-LCM pairs, moving core and singular-domain transport controlled together **[RH]**. [Receiver](../../../formal/GaloisForLFunctions/RHTower/SPEQuantileRieszRoutePLinearFloorCriterion.lean).

### PA — Prime–archimedean passivity

**Current:** Exact current-sign, Bernstein-mismatch and signed compact-moment receivers. Every fixed moment order is positive after a large enough shift. First-atom moment bounds now come from high-order quadrature with exact rational integrals, leaving one uniform analytic tail estimate. [High-order moments](../../../formal/GaloisForLFunctions/RHTower/PrimeArchThetaFirstAtomHighOrderMomentBounds.lean).

**A:** Prove the remaining analytic tail estimate for the first atom; extend quadrature to further atoms; compute explicit thresholds for finite order blocks.

**B:** An all-order/all-shift sign, high-frequency accretivity or an every-positive-rate mismatch bound **[RH]**. [Signed completion](../../../formal/GaloisForLFunctions/RHTower/PrimeArchSignedCompactCompletionCollapse.lean).

### MC — Möbius cancellation

**Current:** Every strict half-power cancellation bound and subpower Hilbert energy are RH-equivalent. Fixed strips have complete dictionaries:

- \(\Theta\le1-\theta\) is equivalent to escaped-endpoint rates, the all-test Hecke-defect strip cap and integer-theta reading growth;
- \(\Theta<1\) is equivalent to a uniform Vaughan power saving.

Moreover \(\Theta=\tfrac12+\inf\{\)one-sided exponents\(\}\) for the Möbius-divisor square-root Abel moment, for its quotient head at any power cutoff \(M^\theta\), and for finite-contact Suzuki residuals. Vinogradov–Korobov decay gives no fixed power saving. A linear Mertens budget forces RH and simple zeros. [Abscissa laws](../../../formal/GaloisForLFunctions/RHTower/QuasiRHQuotientHeadAndFiniteContactAbscissaLaw.lean), [Vaughan](../../../formal/GaloisForLFunctions/BezoutValuationIncidence/UniformVaughanPowerBoundsAreFixedStrips.lean).

**A:** Specialize fixed-modulus and below-diagonal estimates; unify rate normalizations; translate any supplied strip bound through all dictionaries; finish the CGL intake (see External status).

**B:**

- Every strict half-power for the moving source, or exclusion of every subcritical oscillating probe **[RH]**.
- The linear Mertens budget **[RH+]**.
- Any fixed one-sided power saving in any dictionary **[≥QRH]**.

[Hilbert criterion](../../../formal/GaloisForLFunctions/RHTower/MobiusHilbertFormEquivalence.lean).

### TT — Theta tails and directed covariance

**Current:** Exact seam, Wold and odd-Weil receivers with the sub-half range explicit; restricted current signs; continuum light-cone positivity.

**A:** Evaluate fixed directed-covariance and reflected-prime terms; apply continuum and short-support identities with endpoints.

**B:** Signed nonlocal covariance at every rapidity and scale, or complete odd/primitive positivity **[RH]**. [Wold receiver](../../../formal/GaloisForLFunctions/RHTower/PaperWoldDirectedCovarianceRH.lean).

### LA — Line anchor / Jensen and heat signs

**Current:** Finite-head/heat receivers and positive complementary tails. Ordinary Xi coefficients are Turán and Lorentzian, and the Jensen family satisfies Laguerre on \(s\ge0\). Generic finite-product closure is exact in scope; Ramanujan local factors cannot enter it.

**A:** Certify selected finite heads and low degrees; translate coefficient conventions; apply heat-tail errors.

**B:** All-height/all-degree head signs, especially low orders and near-double configurations **[RH]**. [Finite-head reduction](../../../formal/GaloisForLFunctions/RHTower/XiSliceHeatFiniteHeadReduction.lean).

### TG — Integer trace below one

**Current:** Winding, cubic transgression and central-gap receivers. Gaussian coprime-divisibility covariance has a sign on indicators.

**A:** Finite projection/transgression data, residual and trace kept separate.

**B:** A matrix-complete decomposition with nonnegative residual and integer trace below one on every disc, or a zero-rate central-gap bound **[RH]**. [Index estimate](../../../formal/GaloisForLFunctions/RHTower/RestrictedProjectionIndexOperatorNormCriterion.lean).

### HF — Arithmetic Hodge positivity

**Current:** Full Hodge/Weil sign, zero Hecke defect and small enough source work are exact receivers. The complete source is a multiresolution with Gamma-paid details, a twin-blind high-detail floor and uniform finite index for every prime layer except \(k=1\) (§5). Its cross-level prime couplings are Chebyshev sequences (§6). Canonical critical energy has exact finiteness and RH thresholds (§8). The selective margin \(2\log2\) is sharp (§1).

**A:**

- Finite complete-cell Grams in multiresolution coordinates.
- Explicit detail-head sizes for the finite-index bounds.
- Restore the pole in the square-layer Gamma gap.
- Source-kernel cost transport.
- Distinct-index and multiplicity energies kept apart.

**B:**

- Complete residual nonnegativity, complete-cell index zero, or an arithmetic upper bound on work at an RH threshold **[RH]**.
- Uniform finite index of the complete form, or finite \(\mathcal E_{\rm crit}\) **[≥QRH]**: each gives finite off-line support.
- Selective positivity beyond the Robin–Euler point at fixed overlap **[open]**.

[Index capture](../../../formal/GaloisForLFunctions/ArithmeticIndexDescent/TheCompleteCellsCaptureEveryFiniteIndex.lean), [work threshold](../../../formal/GaloisForLFunctions/ArithmeticIndexDescent/TheSourceWorkHasAClosedQuantumThreshold.lean).

### CHMD — Causal hyperbolic–modular duality

**Current:** Wave/Doob receivers; the supported maximal graph equals the completed aperture core. The bounded carrier projection has residual radical equal to the Weil radical, with infinitely many theta states. Translation keeps \(W\) and escapes every exponential graph bound. Ordered entries are Chebyshev integrals; finite generator orbits approximate cell sources in \(L^2\) but are not compact [S].

**A:** Domain/cutoff theorems on fixed sources; the signed residual with the primitive defect; bounded-window scale transport.

**B:** The complete one-sided wave bound or odd Doob/nodal inequality **[RH]**. [Odd criterion](../../../formal/GaloisForLFunctions/RHTower/CHMDOddSectorCriterion.lean).

### TH — Theta moment positivity

**Current:** All ranks are strictly positive on nonzero nonnegative coefficient vectors over a common small positive time; fixed-rank stable regions are known.

**A:** Finite signed blocks with explicit degree/time dependence.

**B:** Positivity for signed vectors at every degree under one common time **[RH]**. [Orthant theorem](../../../formal/GaloisForLFunctions/RHTower/XiHeatHankelFormOrthantPositivity.lean).

### RN — Renewal and singular comparison

**Current:** Theta renewal solvers, a compact cone-positive operator, exact determinant resonances and multiplicity bookkeeping.

**A:** Finite packet/resolvent data in the admitted topology with cusp/seam terms.

**B:** Directed boundary-work orientation, or mixed prime-plus-Gamma versus pole **[RH]**. Cone positivity does not imply real spectrum. [Exact spectrum](../../../formal/GaloisForLFunctions/RHTower/ThetaRenewalFredholmSpectrum.lean).

### WD — Ward caps and collision

**Current:** A nonnegative integrated cap vanishes iff RH; finite-head/tail laws and sharp model heat-repair costs are formalized. Heat flow: zeros of \(H_t\) beyond \(2\pi e^{(27/40+\varepsilon)/t}\) are real and simple for \(0<t\le1/8\), and \(\Xi\) has finitely many nonreal zeros iff the nonreal counts of \(H_t\) are bounded as \(t\downarrow0\) [S]. [Horizon](../../../formal/GaloisForLFunctions/RHTower/KiKimLeeInteriorLindelofHorizon.lean).

**A:** Cap/head data on fixed compact regions; explicit nonreal-count bounds for \(H_t\) on compact time ranges.

**B:** Cap extinction, Euler–Stieltjes saturation or the all-height coefficient sign as heat tends to zero **[RH]**. A reality horizon uniform as \(t\downarrow0\) up to bounded count **[≥QRH]**. [Ward receiver](../../../formal/GaloisForLFunctions/RHTower/XiWardGlobalCapAndFiniteHeadArithmetic.lean).

### LI — Paired Li balances

**Current:** Every-positive-rate lower floors for the prime–Gamma clock are RH-equivalent; the unconditional reciprocal-depth rate \(\le1/431\) is not zero width. RH is primitive nonpositivity of the Cayley–Li Toeplitz ladder, equivalently entrywise nonnegativity. Its couplings do not decay, so the decaying-ladder no-go does not apply [S].

**A:** Fixed paired histories, first-crossing and outside-correlation terms; finite Cayley ladders.

**B:** A subexponential lower floor for the literal primitive, or an arithmetic proof of the Cayley-ladder sign **[RH]**. [Clock growth](../../../formal/GaloisForLFunctions/RHTower/LiEvenCrossActualClockGrowthLaw.lean).

### SZ — Suzuki first variation

**Current:** The compact-\(L^2\) first variation equals the full Weil form. RH is equivalent to nonnegativity of the complete Suzuki first variation on the RH-complete families of factorial tent patterns and grid tent patterns, with exact real-valued limits retaining all Lévy, Gamma, prime-power and polar terms [S]. [RH-complete transfer](../../../formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiCriticalRHCompleteFamilyTransfer.lean).

**A:** Apply moving-aperture limits to specified tent families with low and mixed terms visible.

**B:** First-variation sign on the tent families **[RH]**. [Full first variation](../../../formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiCriticalL2FirstVariation.lean).

### PM — Haar approximation / damped admission

**Current:** Global Haar approximation, cofinal signed-damping admission and positive gauge mass \(\inf_dd\,K_L(d,d)\) for every escape state are exact receivers. Record-minimum limits have \(K_L(p,p)\ge p^{2\varepsilon-2}\), which still permits zero gauge mass; a zero-cofactor limit forces a continuum of limits. Compact maximal-visible-order laws classify residue concentration. [Record minima](../../../formal/GaloisForLFunctions/ArithmeticDefectRigidity/RecordMinimaForceInfiniteCofactorLimits.lean).

**A:** Fixed compact cofactor Grams; energy-transfer/residue formulas with effective pole orders.

**B:** Positive gauge mass for every escape state, or a complete-energy bound as damping tends to zero **[RH]**. Exterior tightness and exclusion of infinite-height escape **[open]**. [Haar receiver](../../../formal/GaloisForLFunctions/RHTower/FermiNymanHaarApproximationEquivalence.lean).

### JAS — Joint ancestry

**Current:** Level-one prime-product positivity and finite-power square-shell bounds are exact receivers; unconditional signs reach a logarithmic prime budget.

**A:** Finite support/grade formulas; budget gaps on chosen shells.

**B:** The half-power prime budget or all-amplitude/every-exponent shell control **[RH]**. [Level-one capstones](../../../formal/GaloisForLFunctions/RHTower/JointAncestryLevelOneCapstones.lean).

### CTF — Chronological / Báez–Duarte approximation

**Current:** The residual is \((1-\Lambda\text{-readout})^2\) plus centered pronic energy; vanishing global error is RH-equivalent.

**A:** Optimize/certify finite rows; report both components with moving-tail errors.

**B:** Bounded rows with complete error tending to zero, or the dual-sampling bound **[RH]**. [Readout criterion](../../../formal/GaloisForLFunctions/BezoutValuationIncidence/VonMangoldtReadoutFormOfTheBaezDuarteCriterion.lean).

### HCF — Gaussian heat trace and two-grid signs

**Current:** Exact archimedean-minus-prime Gaussian traces; positivity on both literal \(\log2/\log3\) grids with polar cancellation is RH-equivalent; one grid can alias a nonreal pair to a positive atom.

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

**Current:** Attained even blind minima give an exact all-aperture criterion. Full positivity holds in high-scale windows, sparse unions and locally through radius \(181/500\), where the floor holds for every weight with \(w(2)=\log2\).

**A:** Certify finite even blind problems.

**B:** Nonnegative minima at every aperture, paying low and mixed modes **[RH]**. [Variational receiver](../../../formal/GaloisForLFunctions/RHTower/EvenSectorBlindVariationalAttainment.lean).

### GTA — Transverse Schur charge

**Current:** Rank-uniform decay of the positive quartic Schur charge is RH-equivalent.

**A:** Finite-rank charges with explicit rank dependence.

**B:** Arithmetic transverse-energy decay uniform in rank **[RH]**. [Decay equivalence](../../../formal/GaloisForLFunctions/RHTower/Hedenmalm/HedenmalmThetaSchurQuarticSpectralDecayEquivalence.lean).

### OWU — Odd Weil-weight uniqueness

**Current:**

- Exact odd/pole-hyperplane and dilation-ray criteria.
- Smooth odd witnesses at radius \(181/500\) separate \(\Lambda\) from Liouville and the first-prime flip. At radius \(23/40\) one odd witness has \(W_\Lambda>\|F\|^2/25\) and \(W_{\rm Liouville}<-\tfrac3{10}\|F\|^2\).
- Small even differences satisfy \(\operatorname{Re}W(g-T_{\log2}g)\ge\|g-T_{\log2}g\|^2/1000\) and persist at every larger aperture.
- At radius \(2\log2\) the exact \(\Lambda\)/Liouville difference has seven signed autocorrelation terms.

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

**Current:** Every-width lag bounds, orbit/index laws and polynomial-aperture detection. The atomic receiver reaches widths \((\log\log N)^\alpha/N\), \(\alpha>1\), and full positivity holds at \(K_\star\delta_N\) (§§2–3). Canonical work separates finite support from RH (§8).

**A:** Instantiate fixed-width detectors at the new orders; compute atomic Grams between \(K_\star\) and \((\log\log N)^{1+\varepsilon}\), keeping Markov, full and pole-hyperplane forms apart.

**B:**

- An actual late-lag bound, zero-rate orbit estimate, or full sign at any unbounded overlap **[RH]**.
- Full sign at a fixed overlap beyond the Robin–Euler point **[open]**.
- An \(\alpha=1\) receiver: a quasi-analyticity boundary of the synthesis (inference), not a task.

[Lag receiver](../../../formal/GaloisForLFunctions/SquareRootThreshold/EveryWidthDecidesTheCriticalLine.lean).

### ACT — One-shift arithmetic criticality

**Current:** For one fixed theta shift, a full all-profile variation inequality gives odd Weil positivity and RH; short collars are absorbed with support-dependent shifts.

**A:** The signed moment ledger for a prescribed profile/shift.

**B:** One shift paying every support and profile **[RH]**. [Short-profile scope](../../../formal/GaloisForLFunctions/ArithmeticCriticalityTheory/ShortProfilePoleFreeVariationInequality.lean).

### AIP — Arithmetic incidence allocation

**Current:** Global joint allocation is exactly the odd sign. The route has:

- complete-cell transfer and the receiver at widths \((\log\log N)^\alpha/N\), \(\alpha>1\);
- the uniform finite-index chain;
- \(\Lambda\)-selection and the sharp margin \(2\log2\);
- the reduction "atomic sign iff Markov sign on \(p=0\) plus one affine scalar".

The beyond-spacing Metzler gauge is obstructed.

**A:** Complete incidence matrices in multiresolution coordinates with every successor, Gamma and polar term; touching-level costs against the available margin.

**B:**

- Signed allocation on source-complete cells or an RH-complete overlap family **[RH]**.
- The selective overlap step (pole-complement sign plus affine floor at a fixed overlap beyond the Robin–Euler point) **[open]**.

[Allocation criterion](../../../formal/GaloisForLFunctions/ArithmeticIncidencePositivity/GlobalIncidenceAllocationCondition.lean).

### ACS — Arithmetic effectivity

**Current:** Source RR, effectivity, Rosati-height and chirality receivers coexist with complete-cell realization and index capture. Weighted coarse Gamma recovery and logarithmic detail payment share one horizon-independent coarse-mass error. The \(k\ge3\) block has uniform finite index; the even-power boundary has a Gamma gap [S].

**A:** Transport fixed source families into complete smooth cells; compute projection and finite-sieve data.

**B:**

- Full-source quadratic RI with degree-zero subquadratic growth, a Rosati-height lower bound, or complete-cell index zero **[RH]**.
- Uniform finite index **[≥QRH]**.

[Effectivity receiver](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/ExactArithmeticSourceEffectivity.lean).

## Route candidates and promotion obstacles

A candidate lacks an independent source construction or its landing. Every promotion gap is **[open]** and becomes **[RH]** once it is the final sign. Any sufficient hypothesis must fail for the Liouville twin: by the SMAP selection theorem, a twin-blind input cannot reach an RH-complete family.

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
| **SC — Stokes/Witt–Krein** | Rigged chambers; a.e. Fourier reconstruction. | Finite cross-fibre coordinates. | Arithmetic cross-fibre index selecting the wall. [Source](../../../formal/GaloisForLFunctions/RHTower/PaperKreinWallFourierCompletion.lean). |
| **SEC — Adjacent prime seam** | Seam-charge/essential-norm and factorial-Fock criteria. | Finite jets and seam charges. | All-order Fock boundedness or eventual compactness. [Source](../../../formal/GaloisForLFunctions/RHTower/TimeOneGammaJetFockRHCriterion.lean). |
| **W1C — Clifford–Dirac / Lee–Yang** | Ferromagnetic Ising limits to Riemann's law force RH. | Finite couplings and density constraints. | Source-defined centred couplings or a faithful scattering operator. [Source](../../../formal/GaloisForLFunctions/RHTower/IsingLawConvergenceRH.lean). |
| **WBF — Source certificates** | Abstract genealogy Gram and relative Fredholm recovery. | Certificate streams and determinants. | Arithmetic stream with uniform-depth landing on Xi/Weil data. [Source](../../../formal/GaloisForLFunctions/HTGeometry/PaperCriticalGenealogyCompletion.lean). |
| **PW-B — PM cusp branch** | Native two-response action with cutoff-independent limit. | Admitted positive-damping actions. | Remove zero indexing; prove the ceiling→optical→cap→extinction chain. [Source](../../../formal/GaloisForLFunctions/RHTower/ThetaCusp/ThetaCuspHawkingBMPWNativeTwoResponseAction.lean). |

## Supporting programmes

| Programme | Contribution | Unresolved input |
|---|---|---|
| SMAP | Selection theorem; sharp margins \(2\log2\)/\(0\); harmonic-correlation criteria; multiresolution and level couplings; selective Gårding | Selective positivity where overlap begins; signed cross-level prime coupling |
| ACS complete cells, Haar | Mixed-entry transfer; Gamma payment of details and mean graph; twin-blind high-detail floor | Coarse and first-prime-layer payment |
| AID, SAHT | Uniform finite-index chain; Chebyshev identity; Gamma reserve; projection and radical; canonical critical energy; finite-orbit approximation | \(k=1\) layer; residual sign; upper bound on \(\mathcal E_{\rm crit}\) |
| SSHA, ALG | Atomic receivers to \((\log\log N)^{1+\varepsilon}\); quarter-Robin–Euler positivity; gap/scalar reduction; Metzler selectivity; count-based local-to-global over \(\mathbb F_q\) | Full sign beyond the Robin–Euler point; local-to-global over \(\mathbb Z\) |
| RAPT, AIT | Sharp gap; spectrum = adjunction energies; arithmetic-mode energies \(\log(K_m/K)\); finite parts incl. \(-L'/L(1,\chi)\); torsion bounds | Growing conductors; Gamma/pole coupling of the full spectrum |
| BVI, ArithmeticCompensation, SignedSuccessor | Readout/pronic decompositions; escaped VK decay; strip dictionaries | Any fixed power saving |
| ACP, ADR, ACG | Escape classification, gauge-mass criterion, prime-error/genus laws, Stepanov mechanism | Visibility of every escape state; actual cancellation |
| AES, CDG, PL, RBG | Field/energy laws, theta-prefix detectors, collided polarization | Upper sign or cap on the computed defect |
| APD, MPG, SBWF, AE, ArtinMertens | Positive-measure rigidity, boundary capacity, finite-field calibration (hyperelliptic RH by counting), Frobenius densities in Mertens form | An independent arithmetic positivity input |
| Zeta23 (external), TransThresholdPairCorrelation, IGP | Unconditional \(2/3\) and \(HD(1)\) simple-critical proportions; \(+10^{-8}\) slack; ordinate census | A displacement-sensitive source estimate at depth \(1/\log T\) |

## External mathematical status

RH is listed as unsolved by [Clay](https://www.claymath.org/millennium/Riemann-Hypothesis/). Proofs below are not validated by this review.

- **Alpöge–Furman two-thirds theorem.** An external, formalized package (`Zeta23`) proving unconditionally that at least \(2/3\), and with the Montgomery–Taylor window \(HD(1)=0.6725\ldots\), of zeros are simple and on the critical line, together with Dirichlet analogues. The corpus imports it as a Lake dependency and builds §9 on it. Its standing in the literature is not assessed here.
- **Quasi-RH manuscript.** A September 2026 [manuscript](https://github.com/openai/math/blob/main/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf) claims Dirichlet zero-freeness for \(\operatorname{Re}s>7/8\). The corpus intake (`RHTower/ChenGuptaLi*`, 279 modules) covers:
  - the zero detector;
  - Lemmas 3.3, 4.1, 4.2, 4.5 and 6.2;
  - Propositions 4.6 and 5.1;
  - the zero-density exponent consolidation to \((qT)^{7(1-\sigma)/3}\).

  It has no zero-free capstone, and its analytic anchor states that the continuation/contour step is not formalized. A corpus no-go shows the standard CGL packet cannot carry horizontal reflection charge: the Proposition 4.6 envelope has floor \(288\) against the collision quantum \(2\). That blocks an RH endpoint, not the \(7/8\) claim. [Collision no-go](../../../formal/GaloisForLFunctions/RHTower/ChenGuptaLiHorizontalCollisionNoGo.lean).
- **Ordinary-correlation manuscript.** A September 2026 [manuscript](https://github.com/openai/math/blob/main/preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/final.pdf) claims fixed-form Liouville two-point bounds \(X/(\log X)^c\). This is neither a power saving nor uniform in growing shifts.
- **Published results.** [Lorentzian polynomials](https://arxiv.org/abs/1902.03719), the de Bruijn–Newman bound \(\Lambda\le0.2\), Ki–Kim–Lee finiteness of nonreal zeros of \(H_t\) for \(t>0\), and Bui–Heath-Brown's \(19/27\) simple zeros under RH are separate inputs. None supplies all-degree real-rootedness or zero exclusion.
