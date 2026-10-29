# Research routes and their mathematical obstacles

Status: 29 October 2026, corpus checkpoint `7f191801a3` plus working tree. **RH remains open.** The inventory is 31 live routes, 17 standalone candidates and the PW-B branch of PM. Every live route has an exact RH receiver; none has the arithmetic input that receiver needs. The atomic frontier has moved: the complete Weil form of \(\zeta\) is now unconditionally positive past the Metzler threshold at fixed overlap, where the Liouville twin is negative. What separates this from RH is overlap growth, from a bounded ratio to \(c_N\asymp\log\log N\).

Companions: [summary, open problems and next questions](obstacles-summary.md) · [walls ledger](walls-ledger.md) · [route unification](route-unification-ledger.md) · [frontier map](../rh-current-frontier-map.md) · [scoped obstructions](../rh-killed-routes.md).

## How to read this report

Evidence comes from corpus searches, then Lean statements, module docstrings and proof structure. No builds or kernel audits were run. **[L]**, **[S]**, **[K]** follow the [frontier map](../rh-current-frontier-map.md): integrated source, working or unintegrated source, individually checked source. **[Lean]** marks a Lean statement read in this review whose integration status was not assessed. **[E]** is an external claim. **(inference)** marks a conclusion of this review, not a Lean theorem. Research record: [working log](../../../logs/review-2910b-research-2026-10-29.md).

Obstacles fall into two classes.

- **A — Just work.** The ingredients exist: a finite computation with certified errors, an instantiation or composition of proved theorems, transport of a supplied bound between proved dictionaries, formalization of a written proof, or integration of working source. A-items can be large. They never promise that a desired sign is true.
- **B — Open mathematics.** A missing inequality, construction or uniformity, tagged by strength:
  - **[RH]** equivalent to RH;
  - **[RH+]** strictly stronger than RH (for example, also forcing simple zeros);
  - **[FS]** equivalent to finitely many off-line zeros, equivalently to RH above some height; it implies the Lindelöf hypothesis and a fixed zero-free strip (§9);
  - **[LH]** at least as strong as the Lindelöf hypothesis;
  - **[≥QRH]** implies a fixed zero-free strip \(\Theta<1\);
  - **[open]** an intermediate problem with no known solution, possibly below RH strength.

A conditional receiver does not prove its input.

## The frontier in fourteen results

### 1. Selection is a theorem; the margin is classified and does not select \(\zeta\)

- **Selection [L].** A bounded weight \(|\lambda|\le\Lambda\) is eventually positive on atomic families of growing overlap iff RH holds and \(\lambda=\Lambda\) on \(n\ge2\); twin-blind positivity cannot reach an RH-complete family. On one prime's towers, index zero for every \(C^2\) generator holds iff RH and \(\lambda=\Lambda\) [S]. [Selection](../../../formal/GaloisForLFunctions/SelectiveMultiscaleArithmeticPositivity/PositivityAtEveryRootSelectsTheVonMangoldtWeight.lean), [tower selection](../../../formal/GaloisForLFunctions/HeckeKreinToeplitz/IndexZeroSelectsTheVonMangoldtWeight.lean).
- **The margin [L].** On the harmonic hyperplane \(\sum x_n/\sqrt n=0\) the prime form has sharp gap \(2\log2\); a single flip \(\omega_p\) has gap \(2\log2\) iff \(p\ge11\); finite flip sets have exact secular gaps that decrease under inclusion; prime-tail flips have gaps \(\ll(\log Q)^{-3}\); cofinite flips have gap \(0\). One exact dyadic probe at \(2\) selects the empty set within finite flips. Every flip fails full Weil positivity by cone uniqueness [Lean]. [Maximal flips](../../../formal/GaloisForLFunctions/ArithmeticCountingPositivity/LargePrimeFlipsAttainTheMaximalGap.lean), [cofinite](../../../formal/GaloisForLFunctions/ArithmeticCountingPositivity/CofinitePrimeFlipsHaveZeroGap.lean), [probe](../../../formal/GaloisForLFunctions/ArithmeticCountingPositivity/OneDyadicProbeSelectsTheFinitePrimeSource.lean), [flips not positive](../../../formal/GaloisForLFunctions/ArithmeticCountingPositivity/NearMaximalGapsDoNotForceWeilPositivity.lean).
- **Index form [S].** The atomic form \(D\delta_1-P\) has window index \(0\), \(1\), \(\ge2\) as \(D\) crosses \(\log N-\gamma\) and \(\log N-\gamma-2\log2\): the margin is the width of an index-one window. [Window](../../../formal/GaloisForLFunctions/HeckeKreinToeplitz/TheMarginIsTheWidthOfTheIndexOneWindow.lean).

The margin separates \(\zeta\) from the Liouville twin, not from single large-prime flips.

### 2. Complete positivity crosses the Metzler threshold, and the Liouville twin fails there

- **Positivity past \(c=1\) [L].** For the explicit plateau \(\varphi_0=\mathrm{plateau}(1/1000)\) and \(c_0=1+10^{-18}\), the complete Weil matrix (primes, Gamma, both poles) is eventually positive definite at every fixed overlap ratio \(c\in(0,c_0]\), including the exact logarithmic spacing and ratios where no unimodular gauge makes the Markov Gram Metzler. Mechanism: a reference-operator floor \(1/25\), prime-defect coercivity from the plateau's variance reserve, and an overlap perturbation \(O((wN)^2)\), leaving the floor \(1/120\) on \([1/2,c_0]\). [Trans-Metzler positivity](../../../formal/GaloisForLFunctions/TransMetzlerWeilPositivity/TransMetzlerPositivity.lean).
- **Other profiles.** One smooth plateau is eventually positive definite at every fixed \(c\in(0,1)\) [L]; near-unit plateaus have one horizon and eigenvalue floor \(b<2-\log2\pi\) uniformly for \(0<c\le1\) [S]. [Separated regime](../../../formal/GaloisForLFunctions/CriticalArithmeticCorrelationTheory/SmoothPlateausMakeTheSeparatedCompleteWeilMatrixPositive.lean), [through touching](../../../formal/GaloisForLFunctions/CriticalArithmeticCorrelationTheory/OneHorizonMakesTheCompleteWeilMatrixPositiveThroughTouching.lean).
- **The Liouville twin fails [S].** For every \(C^2\) profile with Robin–Euler ratio \(c_{\rm RE}(\varphi)=e^{\beta(\varphi)/\|\varphi\|_2^2}/2\pi<1\) and every \(c>c_{\rm RE}\), the twin's complete form has eventual negative atomic witnesses; for \(\varphi_0\) at every \(c\ge1/2\); for some plateau at every \(c>e/2\pi\). It is nonnegative at narrow ratios. [Twin selectivity](../../../formal/GaloisForLFunctions/TransMetzlerWeilPositivity/LiouvilleTwinSelectivity.lean).

Consequence (inference): on \([1/2,c_0]\) the complete form of \(\zeta\) is positive, its Liouville twin negative and the Markov form negative. A parity-selective input (the pole of \(\zeta\), absent from \(\zeta(2s)/\zeta(s)\)) pays the full form where the Markov form fails. This was the separated-regime question of the previous ledger. **Not tested:** whether single flips \(\omega_p\), \(p\ge11\), which keep the pole and the maximal margin, are also positive at fixed ratio; no corpus module evaluates flips on atomic complete forms.

### 3. The RH-complete receiver needs overlap growth; the gap is from \(c\le1+10^{-18}\) to \(c_N\asymp\log\log N\)

- **Super-Gevrey receiver [L].** One explicit Steklov–Denjoy–Carleman profile, \(C_c^\infty([-1,1])\) with \(\int|\varphi^{(q)}|\le A\,12^q q!(\log(q+3))^{2q}\), gives: for every \(\beta>2\), RH iff eventual positivity on all atomic families at overlap \(c_N=(\log\log N)(\log\log\log N)^\beta\), which is \(o((\log\log N)^{1+\varepsilon})\). [Super-Gevrey growth](../../../formal/GaloisForLFunctions/TransMetzlerWeilPositivity/SuperGevreyCriticalGrowth.lean).
- **The quasi-analytic edge [S].** Compact Gevrey profiles of order \(\le1\) vanish; earlier receivers used \((\log\log N)^\alpha\), \(\alpha>1\). The remaining edge is \(\beta\le2\) and \(c_N=O(\log\log N)\). [Quasi-analytic boundary](../../../formal/GaloisForLFunctions/HeckeKreinToeplitz/TheReceiversEndAtTheQuasiAnalyticBoundary.lean). Inference: weights \(q!(\log q)^{(1+\varepsilon)q}\) are still non-quasi-analytic and should give \(\beta>1\).
- **Zero side of fixed ratio [S].** Under RH every ratio is positive; finite off-line support bounds the atomic index by the number of right zeros uniformly in \(c\) and \(N\); a tempered configuration with one off-line pair and a constant-density on-line lattice is negative at every \(c>0\) on a two-atom test. Fixed-ratio positivity therefore cannot follow from temperedness and finite support: it must use \(\zeta\)'s zero density \(\frac{\log T}{2\pi}\). [Zero-side stratum](../../../formal/GaloisForLFunctions/TransMetzlerWeilPositivity/ZeroSideStratum.lean).
- **Integer atoms [S].** RH iff every Weil Gram of cubic-spline atoms at \(\log(i+1)\), \(i<N\), is positive semidefinite; some shrinking schedule carries the whole index. [Integer families](../../../formal/GaloisForLFunctions/HeckeKreinToeplitz/IntegerFamiliesCarryTheWholeIndex.lean).

Consequence (inference): positivity is proved at bounded overlap by a perturbative argument around touching; RH is positivity at overlap growing like \(\log\log N\). Bounded-overlap completeness (whether positivity at every fixed \(c\) implies RH) is unknown and probably false, since one off-line zero is swamped at fixed overlap.

### 4. Index theory of the Weil kernel (HKT, AKLT)

The orbit kernel \(K_\zeta\) of the cubic spline on \(\mathbb Q_{>0}^\times\) has Gram matrices equal to prime-side Weil Grams; its index is the number of distinct right zeros [S].

| Law | Statement |
|---|---|
| Global law [S] | \(\kappa(K_\zeta)=0\iff\psi(x)-x\le C\sqrt x\log^2x\) eventually; for curve data over \(\mathbb F_q\), \(\kappa=0\iff N_k\ge q^k+1-Cq^{k/2}\). [Global law](../../../formal/GaloisForLFunctions/HeckeKreinToeplitz/TheGlobalLawIsTheOneSidedSquareRootCount.lean) |
| Parity form [S] | RH iff the odd Liouville class alone has an upper count: \(O(t)=\sum_{\lambda(n)=-1}e^{-nt}/n\le\tfrac12(H(t)+Ct^{1/2-\varepsilon})\). [Parity form](../../../formal/GaloisForLFunctions/ArithmeticKreinLangerTheory/TheParityFormOfTheGlobalLaw.lean) |
| Two primes, Nyquist, blind primes [S] | Two primes carry the whole index; one tower sees every right zero in ordinate windows shorter than \(2\pi/\log p\); at most \(\binom\kappa2\) primes are blind; infinitely many positive towers force \(\kappa=0\) for positive-plus-finitely-many-pairs kernels. |
| Cyclic and fine towers [S] | Tempered orbit index equals the supremum over consecutive-ratio towers, and over a fine sequence \(\langle p^aq^b\rangle\) in any two-prime lattice, finite or infinite. [Fine towers](../../../formal/GaloisForLFunctions/ArithmeticKreinLangerTheory/FineTowersDecideEveryOrbitKernel.lean) |
| Locality is twin-blind [L] | Unitary twists (Liouville, finite flips, vertical shifts) translate the pair spectrum and preserve tower faithfulness; the tower Hasse principle holds for every twin. [Locality](../../../formal/GaloisForLFunctions/ArithmeticKreinLangerTheory/LocalityIsTwinBlind.lean) |
| Local constituents [S] | On \(\mathbb Z^S\), \(|S|\ge2\), axis-supported kernels have index \(0\) or \(\infty\). |
| Exceptional waves [L/S] | On finite index, the least number of exponential waves leaving a bounded remainder on a separating tower is \(\kappa\); small-time heat collision mass is \(2(\kappa+\sum(m_\rho-1))\). [Wave number](../../../formal/GaloisForLFunctions/ArithmeticKreinLangerTheory/TheCollisionMassIsTheWaveNumber.lean) |
| Index stability [S] | Pointwise limits of finite Hermitian kernels give an eventual lower bound; off the discriminant (weights to zero, collisions, unit-circle contact) the index is continuous. |
| Price [S] | \(m\) negative squares cost \(\mathcal E_{\rm crit}\ge50m^2-3m/2\). [Index is energy](../../../formal/GaloisForLFunctions/HeckeKreinToeplitz/IndexIsEnergy.lean) |
| Compressions [S] | Compression never raises the index; Euler compressors \(\delta_1-c\delta_p\), \(|c|\le p^{-1/2}\), are index-neutral on open-strip pairs; over \(\mathbb F_q\) the characteristic polynomial annihilates the trace kernel and certifies nothing. [Compressions are receivers](../../../formal/GaloisForLFunctions/ArithmeticKreinLangerTheory/CompressionsAreReceivers.lean) |
| Twist tower over \(\mathbb F_q\) [S] | The index is at most the genus; one quadratic twist does not complete the upper count (datum \(\pm2,\pm\tfrac12\)); upper counts on the quadratic twists of all \(2\)-power base changes are equivalent to unitarity. [Twist tower](../../../formal/GaloisForLFunctions/ArithmeticKreinLangerTheory/TheTwistTowerCompletesTheUpperCount.lean) |

Consequence (inference): positivity, counting and index are one statement in three languages, and the producer must act on the point side: a certificate that vanishes at the primes, not at the zeros, and bounds one parity class from above.

### 5. Square-root precision: the count and positivity have different stabilizers (ASRP)

- **The count [S/L].** Either one-sided bound \(\psi(x)-x=O(\sqrt x\log^2x)\) is RH; an upper count for a \(\Lambda\)-majorant or a lower count for a \(\Lambda\)-minorant suffices [L]. Its stabilizer among sign gauges is exactly the flip sets of square-root prime mass; torus gauges likewise [L]. [Gauge stabilizer](../../../formal/GaloisForLFunctions/ArithmeticOfSquareRootPrecision/TheGaugeStabilizerOfTheCount.lean).
- **Deciding-input theorem [S].** Any property \(S\) implying the count rejects the Liouville twin, never holds for both \(a\) and \(a+\varepsilon n^{-\eta}\) (\(\eta<\tfrac12\)), is not determined by finitely many coefficients, and two \(S\)-weights differ by a square-root-class sequence. [Deciding input](../../../formal/GaloisForLFunctions/ArithmeticOfSquareRootPrecision/TheDecidingInputTheorem.lean).
- **Tower positivity is precision-exact [S].** It implies the count and its stabilizer is trivial: \(\Lambda+1/n\) has the count iff RH and is never tower-positive. [Precision-exact](../../../formal/GaloisForLFunctions/ArithmeticOfSquareRootPrecision/TowerPositivityIsPrecisionExact.lean).
- **Integrality is exact; the certificate is missing [S/L].** \(\{\int_0^1P:P\in\mathbb Z[X],\deg P\le n\}=\mathrm{lcm}(1,\dots,n+1)^{-1}\mathbb Z\), with least positive value \(e^{-\psi(n+1)}\). Small auxiliaries (Siegel half) are the lower count, large values (Liouville half) the upper count; each half at square-root scale is RH; the integrality exponent is \(\Theta\); \(\Theta<1\) iff the Siegel half holds at a power \(\theta<1\) [S]. Sup-norm ceilings at precision \(\theta<1\) force vanishing at \(0,\tfrac12,1\), as a Stepanov auxiliary vanishes at rational points [L]. Integer Dirichlet polynomials see integrality only at \(s\in\mathbb Z\), never at a nontrivial zero [S]. [Integrality lattice](../../../formal/GaloisForLFunctions/ArithmeticOfSquareRootPrecision/TheIntegralityLatticeOfTheHorizon.lean), [integrality exponent](../../../formal/GaloisForLFunctions/ArithmeticOfSquareRootPrecision/TheIntegralityExponentIsTheZeroWidth.lean), [sup-norm ceilings](../../../formal/GaloisForLFunctions/ArithmeticOfSquareRootPrecision/SupNormCeilingsForceVanishingAtSmallRationals.lean).
- **Inversion [S].** Monotone errors bounded by \(B\) invert with \(|I_x(E)|\le3B\max_{k\le x}|M(k)|\); uniform monotone inversion at every exponent \(\tfrac12+\delta\) is RH, below \(\tfrac12\) impossible. The Stirling error of \(\psi(n)=I_n(\log\lfloor\cdot\rfloor!)\) splits into a smooth term \(F(t)=t\log t-t\), a monotone part inverted at Mertens precision, and a sawtooth \(-\log y\le h\le0\): all of Chebyshev's precision lives in \(I_n(F)\) and \(I_n(h)\). [Monotone inversion](../../../formal/GaloisForLFunctions/ArithmeticOfSquareRootPrecision/MonotoneErrorsInvertAtMertensPrecision.lean), [Stirling split](../../../formal/GaloisForLFunctions/ArithmeticOfSquareRootPrecision/TheStirlingErrorSplits.lean) (working tree).
- **Curves calibrate the exponent [S].** For curve data the precision exponent is \(\tfrac12+\max\log\|\beta_i\|/\log q\); Stepanov's hyperelliptic count attains \(\tfrac12\); the golden datum has \(N_k/5^k\to1\) and exponent \(>\tfrac12\). [Curves](../../../formal/GaloisForLFunctions/ArithmeticOfSquareRootPrecision/CurvesCalibrateThePrecisionExponent.lean).

Consequence (inference): at \(\Lambda\) the count and positivity are the same statement, but as properties of weights the count sees only the square-root class while positivity sees every coefficient. Over \(\mathbb Z\) integrality is not the bottleneck of an auxiliary-function method; the analytic certificate is.

### 6. One-prime towers: RH at every generator size; two primes separate phases

- RH iff the Weil form is positive on all \(p\)-towers for one fixed prime, also for pole-free \(C^2\) generators supported in \([-\varepsilon,\varepsilon]\) [L]. \(\lambda\) and \(\lambda+\varepsilon n^{-\eta}\), \(0<\eta<\tfrac12\), are never both tower-positive along a nonnegative generator; \(\Lambda\) and its Liouville twin never both [L]. [One prime](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/OnePrimeSeesTheWholeDefectOfZeta.lean), [rigidity](../../../formal/GaloisForLFunctions/SelectiveMultiscaleArithmeticPositivity/TheDyadicSignIsRigid.lean).
- **Two-prime phase separation [S].** For distinct primes \(p,q\): \(|e_p|\log q+|e_q|\log p\ge c\min(|\Delta|,(2+|\Delta|)^{-C})\) for every ordinate difference \(\Delta\) (Baker); one prime aliases at \(\Delta=2\pi/\log p\). [Two-prime towers](../../../formal/GaloisForLFunctions/ArithmeticOfSquareRootPrecision/TwoPrimeTowersSeeEveryOrdinateDifference.lean).

Consequence (inference): the deciding input must be parity-sensitive, square-root-precise, use at least two primes, and act at unbounded aperture.

### 7. The complete source: the finite-index chain ends at the first prime layer

- Complete logarithmic cells form a dyadic multiresolution; Gamma pays all detail mass; each Haar cell has Weil energy \(\ge\) mass\(/10\) [L]. Full Haar identity \(W+G=D_X+P+\sum V_X(a)u_a^2\) with \(G\ge0\), \(V_X\) signed [L]; literal prime edges retain a Gamma reserve and have negative full-Weil entries \(\le-\log(3/2)M_b/\sqrt m\) [S].
- Uniform finite index on every layer except the first: exponents \(k\ge3\), prime two, finite prime sets, the full even source with its pole [L/S]; all even prime powers have a uniform original-Gamma approximation by actual generator heads [K]. Beyond one head the nonfirst source retains \((1-\varepsilon)\Gamma\) [S]. [Even powers](../../../formal/GaloisForLFunctions/SignedArithmeticHodgeTheory/AllEvenPrimePowersHaveOriginalGammaApproximation.lean), [nonfirst reserve](../../../formal/GaloisForLFunctions/ArithmeticIndexDescent/TheFullNonfirstSourceRetainsAlmostAllGamma.lean).
- **Remaining:** the first prime layer \(k=1\) (absolute mass \(\sum_p\log p/\sqrt p\) diverges), odd diagonals, heads, coarse error, poles. Full prime–polar cancellation holds only with an \(e^R\) loss [S]. Uniform finite index of the complete form is [FS].

### 8. Ordered entries are centered Chebyshev integrals

For \(\operatorname{supp}f<b<\operatorname{supp}g\) and every \(c\): \(W(f,g)=-\int_0^\infty(e^h-\psi(e^h)-c)\,q'_{f,g}(h)\,dh-\Gamma_{\rm tail}(f,g)\). The Gamma boundary operator has norm \(\pi/2\), no maximizer and no uniform relative reserve [S]. Cross-level couplings \(d\mapsto W(f,T_{d\log2}g)\) are prime-error sequences, almost periodic under RH and never summable (inference). [Chebyshev identity](../../../formal/GaloisForLFunctions/ArithmeticIndexDescent/TheOrderedWeilSourceIsACenteredChebyshevDefect.lean).

### 9. Finite off-line support is RH above a height and contains Lindelöf

- **TFAE [S]:** \(\kappa(K_\zeta)<\infty\); finite index on a two-prime lattice; finitely many off-line zeros; bounded nonreal counts of \(H_t\); all zeros above some \(T_0\) critical. [TFAE](../../../formal/GaloisForLFunctions/HeckeKreinToeplitz/TheFiniteIndexStratumOfZetaIsLindelofDeep.lean).
- **Strata [L].** Finite support \(\Rightarrow\) zeros approach the line \(\iff\) LH \(\wedge\) (\(\cos(hD)\Xi\) has finitely many nonreal zeros, \(h>0\)) \(\Rightarrow\) LH \(\wedge\) \(\Theta<1\). LH iff off-line zeros are sparse (\(o(\log t)\) per unit window at fixed depth). Finite support iff the subtracted lag is bounded on one side. [Depth](../../../formal/GaloisForLFunctions/RHTower/LindelofCosineFiniteDefectDepth.lean), [subtracted lag](../../../formal/GaloisForLFunctions/RHTower/FiniteOffLineConverse.lean).
- **Inside the stratum.** Atomic index \(\le\#\)right zeros at every ratio [S]; wave number and collision mass (§4).

Consequence (inference): finite support with an effective \(T_0\) below the verified height is RH. It is RH-hard at large height, where every difficulty lives.

### 10. Heat flow

For \(0<t\le1/8\), zeros of \(H_t\) with \(|\operatorname{Re}z|\ge2\pi e^{(2/3+\varepsilon)/t}\) are real and simple [L]. Off-line zeros of depth \(\ge d\) in \([X,2X]\) number at most \(C\log X\cdot N(t)\) when \(t\log X\le cd^2\) [L]. A polynomial bound \(N(t)\le At^{-a}\) would give polylogarithmic deep counts, not finiteness [L]. Local forces, forward simplicity, pair-force and collision-continuous energy are proved; the localized energy evolution estimate is unfinished [S]. [Horizon](../../../formal/GaloisForLFunctions/RHTower/KiKimLeeTwoThirdsHorizon.lean), [uniform depth](../../../formal/GaloisForLFunctions/RHTower/Heat/HeatUniformDepthZeroDensity.lean), [localized evolution](../../../formal/GaloisForLFunctions/RHTower/Heat/HeatLocalizedEnergyEvolution.lean).

### 11. Critical-line census

| Census statement | Value |
|---|---|
| Simple critical zeros | \(\ge HD(1)+10^{-8}\approx0.67250071\) [L] |
| Simple or critical zero copies | \(\ge0.8876\) [L] |
| Distinct ordinates carrying a critical zero | \(\ge4/5\) [L] |
| Zero copies within \(4/\log T\) of the line | \(\ge3/4\) [L] |
| Dichotomy [Lean] | Eventually \(N_0\ge\tfrac34N\), or at least \((HD(1)-\tfrac12-\tfrac1A-\varepsilon)N\) simple off-line zeros lie within \(A/\log T\) of the line; off-line simple plus twice off-line multiple \(\le(\tfrac13+\varepsilon)N\). [Near line](../../../formal/GaloisForLFunctions/RHTower/Zeta23SimpleOffLineNearLine.lean), [multiple exclusion](../../../formal/GaloisForLFunctions/RHTower/Zeta23OffLineMultipleExclusion.lean) |

- **Bandwidth exchange [L].** At \(\lambda=1+\delta\) the gain over \(2/3\) is \(\delta(2-(3E-4)\delta)/(3(1+\delta)^2)\); \(E(1/9)\le4\) gives exactly \(70\%\). [Exchange rate](../../../formal/GaloisForLFunctions/TransThresholdPairCorrelation/NarrowStripClosePairEnergyAndExchangeRate.lean).
- **Capacity [L].** \(3/4\iff\kappa\le5/4\) in capacity \(2-\kappa\); at bandwidth \(4/3\) the diagonal, archimedean and pole constant is \(43/36\) unconditionally, and a prime surplus \(\le N/18\) gives \(75\%\). A positive-definite majorant from sub-threshold data bounds the trans-threshold integral by \(8/27\) against the \(1/9\) needed. [Two routes to 3/4](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/BreakingTheCoalescenceBlindSpotAndThreeQuarters.lean), [threshold](../../../formal/GaloisForLFunctions/TransThresholdPairCorrelation/FormFactorThresholdAndShiftInequality.lean).
- **Zero-side slack [L].** \((H(\lambda)-\varepsilon)N+\text{slack}\le N_0^*\), \(H(\lambda)=2-1/\lambda-\lambda/3\); the grid-dimension ceiling refutes the \(3/4\) hypothesis for \(\lambda<3/4\); displaced pairs at \(\kappa=4/3\) reach slack \(N/12\) iff \(\eta\ge1/6\). [Slack](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/SpectralSlackConservationAndTheHyperbolicDisplacementThreshold.lean).
- **Price.** Beyond bandwidth one the prime side is a signed sum over coalescent prime pairs [L]; value moments are depth-blind [L]; the shallow Cauchy energy is \(O(N)\) with a majorant counting all zeros [L].

### 12. Quasi-RH: translation and density complete, production absent

- **Dictionaries [L].** Escaped Möbius rates, Hecke-defect caps, theta-prefix growth, uniform Vaughan savings, Möbius-divisor Abel moment, Suzuki residuals; balanced short-window Möbius or prime power savings \(\iff\Theta<1\); the strip \([1/4,3/4]\) iff the normalized Chebyshev Cesàro mean-square energy is \(\ll N^{3/2+\varepsilon}\). Integrality adds one more: \(\Theta<1\) iff small integer-polynomial auxiliaries exist at a power precision \(\theta<1\) [S].
- **Inputs [L].** Guth–Maynard Theorem 1.1: \(N(\sigma,T)\ll T^{(30/13)(1-\sigma)+\varepsilon}\) on \([1/2,5/6]\); DH on \(\sigma\ge5/6\); primes in \((x,x+x^{17/30+\varepsilon}]\); almost all intervals \(x^\theta\), \(\theta>2/15\); Vinogradov–Korobov. A density envelope never drops below \(1\). [Guth–Maynard](../../../formal/GaloisForLFunctions/RHTower/Sieve/GuthMaynardTheoremOneOne.lean), [envelope](../../../formal/GaloisForLFunctions/RHTower/DensityEnvelopeNoGo.lean).
- **Chen–Gupta–Li [E].** 279 intake modules: detector, density (\(7/3\) envelope) and tail components; no zero-free capstone.

### 13. Over \(\mathbb F_q\) the local-to-global step is a produced count

Trickle-down on every Frobenius ladder iff the one-sided square-root count; hyperelliptic curves pass by Stepanov's count; the golden fake fails [L]. Over \(\mathbb Z\), \(1-T_p^N\) annihilates a zero symbol iff the zero is critical and on a height lattice [L]. Hyperbolicity of the atomic Gram holds for every sign twin; the Metzler sign is selective [L]. With §4: the twist tower over \(\mathbb F_q\) acts geometrically on base changes (a vertical shift \(s\mapsto s+i\pi/\log q^{2^j}\)); over \(\mathbb Z\) the Liouville twist acts on prime constituents and is not a vertical shift (inference). [Trickle-down count](../../../formal/GaloisForLFunctions/ArithmeticLorentzianGeometry/TheTrickleDownInequalityIsTheSquareRootCount.lean), [Stepanov mechanism](../../../formal/GaloisForLFunctions/ArithmeticCorrespondencePositivity/SparseAnnihilatorsAndTheStepanovMechanism.lean).

### 14. Number-field and loop-group foundations

- **Hecke [L/K].** Global continuation and nonvanishing on \(\operatorname{Re}s=1\) [L]; dual-class Mellin integrals, unit unfolding, inverse-class series identity and residue cancellation of completed numerators [K]. Missing: removable values, class recombination, normalized functional equation, uniform bounds. [Continuation](../../../formal/GaloisForLFunctions/HeckeLFunctions/HeckeLFunctionsHaveGlobalContinuation.lean).
- **Positive-genus calibration [K/L].** For the genus-one curve \(y^2=x^3-x\) over \(\mathbb F_3\) (zeta numerator roots of modulus \(1/\sqrt3\)): adeles, Haar, finite approximation, local shells; the affine \(A_1\) Gindikin–Karpelevich coefficients have genuine poles at the Frobenius zeros with full multiplicity, and these poles survive the complete regularized affine Weyl sum. [Coefficients](../../../formal/GaloisForLFunctions/HTGeometry/LoopEisenstein/AffineA1FiniteFieldCoefficients.lean), [Weyl poles](../../../formal/GaloisForLFunctions/HTGeometry/LoopEisenstein/AffineA1FiniteFieldWeylPoles.lean).
- **Real loop group [K/S].** Bruhat, rank-one lifts, vertex generation, Iwasawa \(G=BK\) [K]; \(K\cap B=M\) and a Borel-equivariant spherical function [S]. Missing: arithmetic quotient and measures, coset-sum convergence, constant-term identification, Maass–Selberg relations.

These are tools; they carry no selective sign. The calibration shows that zeros of a positive-genus zeta function enter the polar divisor of an affine Weyl sum (inference from the module statements).

## Live routes

Each entry gives the current state, then **A** (just work) and **B** (open).

### WL — Weil lag / prime-error energy

**Current:** Bounded critical-deficit energy, coprime cross-work and a linear prime-error energy budget are RH-equivalent; either one-sided \(\sqrt x\log^2x\) count is RH and equals \(\kappa(K_\zeta)=0\) [S]; a majorant upper or minorant lower count suffices [L]; the count's gauge stabilizer is the square-root class [L]. Abel-slope saturation at the archimedean genus is RH plus simple zeros. Monotone errors invert at Mertens precision; the Stirling error splits into smooth, monotone and sawtooth parts (§5). The prime error is the separated off-diagonal of the complete form and the unpaid cross-level coupling (§8).

**A:** Certified truncations with archimedean and high-zero tails; tabulate \(d\mapsto W(f,T_{d\log2}g)\); compute \(I_n(F)\) and \(I_n(h)\) on certified ranges to locate the square-root part; classify one-signed perturbations at \(\sigma_{\rm abs}=\tfrac12\).

**B:** The one-sided count, equivalently the odd-class upper count **[RH]**; signed inversion of the smooth term and the sawtooth at square-root precision **[RH]**; subtracted lag **[FS]**; genus saturation **[RH+]**. [Receiver](../../../formal/GaloisForLFunctions/BiScaleUncertainty/WeilLagCriticalDeficitEndpointAndLimitLaw.lean).

### RW — Restricted Weil ground energy

**Current:** RH iff the ground minimum is positive at every finite aperture; the minimum strictly decreases with an exact shell decomposition; finite-aperture Gårding allows a nonzero index; positive floors must decay doubly exponentially; Gamma boundary norm \(\pi/2\) without uniform relative reserve [S].

**A:** Certified finite-aperture variational bounds and shell ledgers; the Gamma square reserve in the shell flux.

**B:** Cumulative aperture relaxation bounded by the initial energy, paying low modes, prime collars and polar terms **[RH]**. [Aperture flow](../../../formal/GaloisForLFunctions/ArithmeticContinuationAndCriticalEnergy/TheApertureFlowNeverStalls.lean).

### FU — Signed prime scheduling

**Current:** An eventual upper bound on the normalized completed Abel moment is RH-equivalent; narrow translated prime channels have a useful sign [L], wide-window channels can be positive [S].

**A:** Seed, drift, earlier-history, cross-block and endpoint ledgers for fixed schedules.

**B:** The joint signed total over a prime-exhaustive schedule **[RH]**. [Receiver](../../../formal/GaloisForLFunctions/RHTower/CCM/CCMFUSuzukiMobiusDivisorOneSided.lean).

### RP — Matched-quantile history floor

**Current:** RH iff an eventual floor \(-B(K+2)\); unconditionally the history drops below \(-\delta(K+2)\) cofinally, so no sublinear floor exists [L]. Low-LCM payment and signed identities.

**A:** Fixed histories; low-LCM instantiation; the escape constant \(\delta\) on computed ranges.

**B:** A linear floor paying high-LCM pairs, moving core and singular-domain transport together **[RH]**. [Floor](../../../formal/GaloisForLFunctions/RHTower/SPEQuantileRieszRoutePLinearFloorCriterion.lean).

### PA — Prime–archimedean passivity

**Current:** Current-sign, Bernstein-mismatch and signed compact-moment receivers; each fixed Hausdorff order is positive after a large shift; first-atom moments leave one analytic tail estimate.

**A:** The remaining analytic tail; further atoms; explicit thresholds for finite order blocks.

**B:** All-order/all-shift sign, high-frequency accretivity, or an every-positive-rate mismatch bound **[RH]**. [High-order moments](../../../formal/GaloisForLFunctions/RHTower/PrimeArchThetaFirstAtomHighOrderMomentBounds.lean).

### MC — Möbius cancellation

**Current:** Every strict half-power cancellation bound and subpower Hilbert energy are RH-equivalent; fixed strips have complete dictionaries (§12); a linear Mertens budget forces RH and simple zeros; \(M=o(\sqrt x)\) is false. The battery is formal: \(\Lambda+\varepsilon n^{-\eta}\) satisfies PNT and every short-interval law beyond \(17/30\) and fails the count [S]; any count-implying property has the deciding-input properties [S]. Integrality halves give the count in auxiliary-polynomial form [S].

**A:** Fixed-modulus and below-diagonal estimates; rate normalizations; transport of any supplied strip bound through every dictionary.

**B:** Every strict half-power **[RH]**; the linear Mertens budget **[RH+]**; any fixed one-sided power saving, including balanced short windows or small auxiliaries at a power precision **[≥QRH]**. [Hilbert criterion](../../../formal/GaloisForLFunctions/RHTower/MobiusHilbertFormEquivalence.lean).

### TT — Theta tails and directed covariance

**Current:** Seam, Wold and odd-Weil receivers with the sub-half range explicit; restricted current signs; continuum light-cone positivity.

**A:** Fixed directed-covariance and reflected-prime terms; continuum and short-support identities.

**B:** Signed nonlocal covariance at every rapidity and scale, or complete odd/primitive positivity **[RH]**. [Wold receiver](../../../formal/GaloisForLFunctions/RHTower/PaperWoldDirectedCovarianceRH.lean).

### LA — Line anchor / Jensen and heat signs

**Current:** Finite-head/heat receivers and positive complementary tails; ordinary \(\xi\) coefficients Turán [L] and Lorentzian [S]; Jensen–Laguerre on \(s\ge0\); local cofactor \(\xi=P\cdot g\), \(\deg P=O(\log T)\); reality horizon \(2\pi e^{(2/3+\varepsilon)/t}\) [L].

**A:** Certified finite heads and low degrees; coefficient conventions; heat-tail errors with the local cofactor.

**B:** All-height/all-degree head signs, including low orders and near-double configurations **[RH]**; uniform heat count **[FS]**. [Finite-head reduction](../../../formal/GaloisForLFunctions/RHTower/XiSliceHeatFiniteHeadReduction.lean).

### TG — Integer trace below one

**Current:** Winding, cubic transgression and central-gap receivers; Gaussian coprime-divisibility covariance signs.

**A:** Finite projection and transgression data with residual and trace kept apart.

**B:** A matrix-complete decomposition with nonnegative residual and integer trace below one on every disc, or a zero-rate central-gap bound **[RH]**. [Index estimate](../../../formal/GaloisForLFunctions/RHTower/RestrictedProjectionIndexOperatorNormCriterion.lean).

### HF — Arithmetic Hodge positivity

**Current:** Full Hodge/Weil sign, zero Hecke defect and small source work are exact receivers. The complete form is positive definite on atomic families at every fixed ratio \(0<c\le1+10^{-18}\) for one plateau [L], selective against the Liouville twin there [S] (§2). The complete source has the multiresolution, single-cell floors, the Haar identity and uniform finite index on every layer except \(k=1\) (§7). Index equals right-zero count and is priced by \(\mathcal E_{\rm crit}\) (§4). The RH-complete atomic family needs overlap \(c_N\asymp\log\log N\) (§3).

**A:** Explicit head sizes in every finite-index theorem; first-layer constants \(C_P\) along growing prime sets; complete-cell Grams in multiresolution coordinates; floor of the Trans-Metzler argument as a function of \(c\) beyond \(1+10^{-18}\) by the same perturbation scheme; integration of the Haar prime-edge and twin-selectivity sources.

**B:**
- Positivity on an RH-complete overlapping family, complete residual sign, complete-cell index zero, or a work ceiling at an RH threshold **[RH]**.
- Uniform finite index, finite \(\mathcal E_{\rm crit}\) **[FS]**.
- Non-perturbative positivity at every fixed overlap ratio, and its uniformity in \(c\) **[open]** (Q1).

[Trans-Metzler positivity](../../../formal/GaloisForLFunctions/TransMetzlerWeilPositivity/TransMetzlerPositivity.lean), [index capture](../../../formal/GaloisForLFunctions/ArithmeticIndexDescent/TheCompleteCellsCaptureEveryFiniteIndex.lean).

### CHMD — Causal hyperbolic–modular duality

**Current:** Wave/Doob receivers; completed aperture core; residual radical equals Weil radical; ordered entries are Chebyshev integrals; actual generator heads with uniform Gamma bounds and complete even-power error \(\le\delta\Gamma(f)\) [K]; finite generator orbits approximate cell sources in \(L^2\) but are not compact.

**A:** Domain and cutoff theorems on fixed sources; signed residual with the primitive defect; bounded-window transport.

**B:** The complete one-sided wave bound or odd Doob/nodal inequality, paying first-prime, coarse and polar terms **[RH]**. [Odd criterion](../../../formal/GaloisForLFunctions/RHTower/CHMDOddSectorCriterion.lean).

### TH — Theta moment positivity

**Current:** All ranks strictly positive on nonnegative coefficient vectors at one common small time; fixed-rank stable regions.

**A:** Finite signed blocks with explicit degree and time dependence.

**B:** Signed vectors at every degree under one common time **[RH]**. [Orthant theorem](../../../formal/GaloisForLFunctions/RHTower/XiHeatHankelFormOrthantPositivity.lean).

### RN — Renewal and singular comparison

**Current:** Theta renewal solvers, a compact cone-positive operator, exact determinant resonances.

**A:** Finite packet and resolvent data in the admitted topology with cusp and seam terms.

**B:** Directed boundary-work orientation, or mixed prime-plus-Gamma versus pole **[RH]**; cone positivity does not give real spectrum. [Exact spectrum](../../../formal/GaloisForLFunctions/RHTower/ThetaRenewalFredholmSpectrum.lean).

### WD — Ward caps and collision

**Current:** A nonnegative integrated cap vanishes iff RH; shallow Cauchy energy \(O(N)\) at depth \(1/\log T\) [L]; uniform-depth heat counting and the \(2/3\) horizon [L]. Finite support iff bounded heat counts [S]; on finite index the collision mass is twice the wave number plus multiplicity excess [L/S].

**A:** Cap and head data on compact regions; explicit \(N(t)\) bounds on compact time ranges; shallow-energy constants; the localized energy evolution estimate.

**B:** Cap extinction or all-height coefficient sign as \(t\downarrow0\) **[RH]**; uniform nonreal count **[FS]**; uniform high count **[LH]**. [Ward receiver](../../../formal/GaloisForLFunctions/RHTower/XiWardGlobalCapAndFiniteHeadArithmetic.lean).

### LI — Paired Li balances

**Current:** Every-positive-rate floors for the prime–Gamma clock are RH-equivalent [L]; RH is primitive nonpositivity of the Cayley–Li Toeplitz ladder, whose couplings do not decay [S].

**A:** Fixed paired histories; finite Cayley ladders.

**B:** A subexponential floor for the literal primitive, or an arithmetic proof of the ladder sign **[RH]**. [Cayley ladder](../../../formal/GaloisForLFunctions/ArithmeticLorentzianGeometry/RHIsReflectionPositivityOfTheCayleyLadder.lean).

### SZ — Suzuki first variation

**Current:** Compact-\(L^2\) first variation equals the full Weil form [L]; RH iff nonnegativity on factorial and grid tent families with all terms retained [S].

**A:** Moving-aperture limits on specified tent families.

**B:** The sign on the tent families, especially low and mixed modes **[RH]**. [RH-complete transfer](../../../formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiCriticalRHCompleteFamilyTransfer.lean).

### PM — Haar approximation / damped admission

**Current:** Global Haar approximation, cofinal signed-damping admission and positive gauge mass for every escape state are exact receivers; actual cofactor families are singletons or continua; record-minimum limits still permit zero gauge mass.

**A:** Fixed compact cofactor Grams; energy-transfer formulas with effective pole orders.

**B:** Positive gauge mass for every escape state, or a complete-energy bound as damping \(\to0\) **[RH]**; exterior tightness **[open]**. [Haar receiver](../../../formal/GaloisForLFunctions/RHTower/FermiNymanHaarApproximationEquivalence.lean).

### JAS — Joint ancestry

**Current:** Level-one prime-product positivity and finite-power square-shell bounds are receivers; unconditional signs reach a logarithmic prime budget.

**A:** Support and grade formulas; budget gaps on chosen shells.

**B:** The half-power prime budget or all-amplitude shell control **[RH]**. [Capstones](../../../formal/GaloisForLFunctions/RHTower/JointAncestryLevelOneCapstones.lean).

### CTF — Chronological / Báez–Duarte approximation

**Current:** Residual \(=(1-\Lambda\text{-readout})^2+\)centered pronic energy; vanishing error is RH-equivalent; literal \(-\mu\) aligns the readout.

**A:** Optimized finite rows with both components reported.

**B:** Bounded rows with complete error \(\to0\), or the dual-sampling bound **[RH]**. [Readout criterion](../../../formal/GaloisForLFunctions/BezoutValuationIncidence/VonMangoldtReadoutFormOfTheBaezDuarteCriterion.lean).

### HCF — Gaussian heat trace and two-grid signs

**Current:** Exact archimedean-minus-prime Gaussian traces; positivity on both literal \(\log2/\log3\) grids with polar cancellation is RH-equivalent; one grid aliases. Two-prime phase separation is polynomial away from coalescence [S]; two prime lattices carry the whole index [S].

**A:** Finite degrees and heights on both grids with explicit errors.

**B:** Both grid signs at all degrees and heights **[RH]**; a many-node Gram floor from pairwise phase separation **[open]**. [Two-grid receiver](../../../formal/GaloisForLFunctions/RHTower/XiGaussianHeatTwoPrimeSourceSampling.lean).

### XN — Newton invariant discs

**Current:** Line-centred self-map discs covering all zeros give RH; exact curvature formula for the interior margin.

**A:** Certified discs and curvature integrals.

**B:** A covering family with nonnegative interior margin **[RH]**. [Disc criterion](../../../formal/GaloisForLFunctions/RHTower/XiNewtonSchwarzPickCriticalLine.lean).

### BAG — Deterministic self-return

**Current:** Actual-\(\zeta\) recurrence through the right strip, or cutoff-uniform positive Haar mass of target-\(\zeta\) twists, is an RH receiver; finite-head returns keep target-zero exceptions.

**A:** Finite-head return estimates on zero-free compact targets.

**B:** Recurrence at every right-strip point and tolerance **[RH]**. [Return receiver](../../../formal/GaloisForLFunctions/RHTower/ZetaStrongRecurrenceReceiver.lean).

### EWU — Even pole-weight uniqueness

**Current:** Attained even blind minima give an all-aperture criterion; positivity in high windows and locally through radius \(181/500\); RH iff for every aperture some real weights make \(\zeta\)'s full Weil functional nonnegative up to that aperture [L].

**A:** Certified finite even blind problems; finite-level feasibility.

**B:** Nonnegative blind minima at every aperture **[RH]**. [Existence form](../../../formal/GaloisForLFunctions/RHTower/WeilPositivityFiniteLevelExistenceDecidesRH.lean).

### GTA — Transverse Schur charge

**Current:** Rank-uniform decay of the quartic Schur charge is RH-equivalent; positive charge and finite-prefix convergence.

**A:** Finite-rank charges.

**B:** Rank-uniform transverse decay **[RH]**. [Decay equivalence](../../../formal/GaloisForLFunctions/RHTower/Hedenmalm/HedenmalmThetaSchurQuarticSpectralDecayEquivalence.lean).

### OWU — Odd Weil-weight uniqueness

**Current:** Odd/pole-hyperplane and dilation-ray criteria; smooth odd witnesses separate \(\Lambda\) from the Liouville twin and the first-prime flip at radii \(181/500\) and \(23/40\). These finite-aperture separations persist under small \(n^{-\eta}\) perturbations, so they cannot decide (§5–6).

**A:** Collar accounting with signed autocorrelations and both pole corrections.

**B:** The all-aperture odd sign **[RH]**; conductor/forcing compatibility **[open]**. [Dilation criterion](../../../formal/GaloisForLFunctions/RHTower/WeilDilationRayCriterion.lean).

### PBM — Pole-regularized prime series

**Current:** Convergence of pole-subtracted coefficients at every real \(\sigma>1/2\) is RH-equivalent.

**A:** Regularized partial sums in controlled half-planes.

**B:** Critical-abscissa cancellation **[RH]**; any fixed abscissa \(<1\) **[≥QRH]**. [Criterion](../../../formal/GaloisForLFunctions/RHTower/RegularizedLogZetaAbscissa.lean).

### RB — Robin / Nicolas extremizers

**Current:** Eventual criteria; reduction to colossally abundant integers; valuation-defect margins; large counterexamples need growing prime cores.

**A:** Certified finite extremal ranges.

**B:** The square-root-scale remainder on prime-saturated extremizers **[RH]**. [CA reduction](../../../formal/GaloisForLFunctions/RHTower/RobinColossallyAbundantReduction.lean).

### SRT — Lag localization and atomic visibility

**Current:** Every-width lag bounds; atomic RH receiver at \(c_N=(\log\log N)(\log\log\log N)^\beta\), \(\beta>2\) [L]; fixed-ratio complete positivity up to \(1+10^{-18}\) [L] and fixed-width Liouville-twin witnesses [S]; integer atoms and fine two-prime towers carry the whole index [S]; one-prime tower positivity of every small pole-free generator is RH [L]; tower positivity is precision-exact [S].

**A:** Improve \(\beta>2\) toward \(\beta>1\) with weaker Denjoy–Carleman weights (inference); atomic Grams beyond \(c=1+10^{-18}\) with Markov, full and pole-hyperplane forms apart; an explicit shrinking full-index schedule from the existence proof.

**B:** Late-lag bound, all-generator tower bound, or full sign at overlap \(c_N\to\infty\) **[RH]**; positivity uniform in overlap up to \(\log\log N\) **[open]** (Q1); \(c_N=O(\log\log N)\) completeness **[open]**. [Lag receiver](../../../formal/GaloisForLFunctions/SquareRootThreshold/EveryWidthDecidesTheCriticalLine.lean), [super-Gevrey](../../../formal/GaloisForLFunctions/TransMetzlerWeilPositivity/SuperGevreyCriticalGrowth.lean).

### ACT — One-shift arithmetic criticality

**Current:** One fixed theta shift with a full all-profile variation inequality gives odd positivity and RH; short collars are absorbed with support-dependent shifts.

**A:** Signed moment ledgers for prescribed profiles and shifts.

**B:** One shift paying every support and profile, including exterior primes and the polar remainder **[RH]**. [Short-profile scope](../../../formal/GaloisForLFunctions/ArithmeticCriticalityTheory/ShortProfilePoleFreeVariationInequality.lean).

### AIP — Arithmetic incidence allocation

**Current:** Global joint allocation is the odd sign. The route shares the complete-cell transfer, the atomic receivers, the finite-index chain, selection and margin, the gap/scalar reduction and the fixed-ratio complete positivity (§§1–3, 7).

**A:** Complete incidence matrices in multiresolution coordinates; touching-level costs against the margin; primitive-curvature and prime-window drafts brought to operator form.

**B:** Signed allocation on source-complete cells **[RH]**; overlap growth **[open]** (Q1). [Allocation criterion](../../../formal/GaloisForLFunctions/ArithmeticIncidencePositivity/GlobalIncidenceAllocationCondition.lean).

### ACS — Arithmetic effectivity and the census

**Current:** Source RR, effectivity, Rosati-height and chirality receivers; complete-cell realization and index capture; one-prime tower law; Haar identities; fixed-ratio positivity [L]. The census module carries the exchange rates, capacity law and slack calculus (§11). Positive-genus and loop-group foundations live here and in HTGeometry (§14).

**A:** Fixed source families in complete cells; the slack calculus at \(\lambda\in[3/4,1)\); the full constant-term computation of the affine \(A_1\) Eisenstein series over the genus-one base.

**B:** Full-source quadratic RI with degree-zero subquadratic growth, a Rosati-height lower bound, or complete-cell index zero **[RH]**; uniform finite index **[FS]**; a census input beyond \(2/3\): prime surplus \(\le N/18\) at bandwidth \(4/3\), \(E(1/9)\le4\), or zero-side slack \(\ge N/30\) near bandwidth one **[open]**; a positivity or holomorphy constraint on the polar divisor of positive-genus affine Eisenstein series **[open]** (Q3). [Effectivity receiver](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/ExactArithmeticSourceEffectivity.lean).

## Route candidates and promotion obstacles

A candidate lacks an independent source construction or its landing. Every promotion gap is **[open]** and becomes **[RH]** once it is the final sign. A sufficient hypothesis must fail for the battery: the Liouville twin, single-prime flips with the maximal margin, cofinite flips, \(\Lambda+\varepsilon n^{-\eta}\), \(\Lambda+1/n\) for positivity statements, the golden curve on the lattice, over-regular Beurling systems. Locality is twin-blind, so no candidate can land through local tower data alone.

| Candidate | Established mechanism | A — Just work | B — Promotion gap |
|---|---|---|---|
| **APF** Arithmetic paired Fredholm | Fredholm index; cycle traces have arithmetic Fourier reconstruction. | Fixed cycles and mixtures with truncation control. | Zero-independent divisor exhaustion and trace vanishing. [Source](../../../formal/GaloisForLFunctions/RHTower/PaperZetaCycleFourierReconstruction.lean) |
| **BSH** Arithmetic mate curvature | Framed curvature vanishes at critical half-density; finite cutoffs are trace-blind. | Finite curvature and cocycle identities. | A pre-divisor section and mate identity forcing the vanishing. [Source](../../../formal/GaloisForLFunctions/RHTower/Deninger/DeningerOneSidedFramedMateCurvatureTransgression.lean) |
| **CDC** Constitutive dagger | Calibrated confluent potentials exist exactly on the line. | Finite repair and exchange defects. | One arithmetic potential descending on every fibre and forcing confluence at actual zeros. [Source](../../../formal/GaloisForLFunctions/RHTower/ConstitutiveDaggerConfluence.lean) |
| **DR** Dyadic roots | Dyadic levels reach the Littlewood zero-free cusp; finite Kummer data. | Roots on known zero-free charts. | Source-driven continuation and compatible roots on the whole strict-right domain; global monodromy. [Source](../../../formal/GaloisForLFunctions/RHTower/XiSymmetricLittlewoodZeroFreeCuspDyadicRoots.lean) |
| **EGC** Pole-safe contour | Complete copy correction; nonzero Gamma baseline. | Corrected contours. | Outer-contour orientation excluding off-line copies; raw decay cannot beat the Gamma floor. [Source](../../../formal/GaloisForLFunctions/RHTower/PaperEGCSourceRayBaseline.lean) |
| **EWJ** Euler/Wold jets | Three-channel histories converge; compact quotient character. | Fixed jets. | Source admission and norm exhaustion across depth. [Source](../../../formal/GaloisForLFunctions/RHTower/PaperEulerWoldDepthHistory.lean) |
| **FEL** Theta likelihood | Entropy bookkeeping; convergent BSY zero sum. | Predeclared finite histories. | Cofinal balance from arithmetic, independent of zeros. [Source](../../../formal/GaloisForLFunctions/RHTower/BalazardSaiasYorZeroSum.lean) |
| **HJ** Hurwitz reflection | Two-seed residual equals SEC charge; all-divisor vanishing matches the HCF two-grid sign. | Convergent fibres. | Pre-divisor forcing of residual vanishing. [Source](../../../formal/GaloisForLFunctions/RHTower/PrimeTailSeedHurwitzReflection.lean) |
| **IRK** Rotation-algebra trace | Completed Xi-jet relation invertible exactly off the line. | Finite jet inverses. | Charged arithmetic Poisson lift with integral count. [Source](../../../formal/GaloisForLFunctions/RHTower/PrimeRotationXiCompletedResolution.lean) |
| **MSC** Möbius–Sonin transport | Squarefree Hilbert source recovers moments; divisor multiplicity preserved. | Evaluation jets. | Source-faithful nonnegative Sonin/Weil energy. [Source](../../../formal/GaloisForLFunctions/RHTower/SquarefreeDiscrepancyHilbertTransport.lean) |
| **PCS** Singular prime co-shift | Shift-plus-defect decomposition; strong finite-prime convergence with norm gap. | Retained defect and cutoff errors. | Wall annihilation retaining the forward mode. [Source](../../../formal/GaloisForLFunctions/RHTower/PCSChronologicalDilationCarrierObstruction.lean) |
| **PTR** Photonic realization | Lossless products real-rooted; Xi-limit criterion; gapless realization law. | Finite stacks. | Prime-faithful nonlocal port built without Xi zeros. [Source](../../../formal/GaloisForLFunctions/RHTower/PhotonicLosslessProductPortRH.lean) |
| **RFHM** Support/grade forcing | Full support, phase and grade admission; cutoff exhaustion. | Coherent defects. | A source law sensitive to phase and depth orientation. [Source](../../../formal/GaloisForLFunctions/RHTower/PaperRFHMSurvivalInformation.lean) |
| **SC** Stokes/Witt–Krein | Rigged chambers; finite index is positive minus finite rank; tempered orbit index equals the supremum over consecutive-ratio or fine two-prime towers [S]. | Finite cross-fibre coordinates. | A source-fixed cross-fibre sign or index ceiling; locality is twin-blind, and a finite index lands only in [FS]. [Source](../../../formal/GaloisForLFunctions/RHTower/PaperKreinWallFourierCompletion.lean) |
| **SEC** Adjacent prime seam | Seam-charge/essential-norm and Fock criteria. | Finite jets and seam charges. | All-order Fock boundedness or eventual compactness at actual zeros. [Source](../../../formal/GaloisForLFunctions/RHTower/TimeOneGammaJetFockRHCriterion.lean) |
| **W1C** Clifford–Dirac / Lee–Yang | Ferromagnetic Ising limits to Riemann's law force RH. | Finite couplings. | Source-defined centred couplings; a Bohr-torus Lee–Yang lift is the natural landing. [Source](../../../formal/GaloisForLFunctions/RHTower/IsingLawConvergenceRH.lean) |
| **WBF** Source certificates | Abstract genealogy Gram and Fredholm recovery. | Certificate streams. | Arithmetic stream with uniform-depth landing. [Source](../../../formal/GaloisForLFunctions/HTGeometry/PaperCriticalGenealogyCompletion.lean) |
| **PW-B** PM cusp branch | Native two-response action with cutoff-independent limit. | Positive-damping actions. | Remove zero indexing; ceiling, optical magnitude, cap, extinction chain. [Source](../../../formal/GaloisForLFunctions/RHTower/ThetaCusp/ThetaCuspHawkingBMPWNativeTwoResponseAction.lean) |

## Supporting programmes

| Programme | Contribution | Unresolved input |
|---|---|---|
| TM | Complete positivity at fixed ratio \(\le1+10^{-18}\); Liouville breakdown above \(c_{\rm RE}\); super-Gevrey RH receiver; zero-side stratum | Overlap growth; flips at fixed ratio; bounded-overlap completeness |
| HKT, AKLT | Index theory: global law and parity form, two-prime/Nyquist/blind primes, fine towers, locality twin-blind, exceptional waves, compressions, twist tower | An index ceiling from local data; a producer of the one-sided count |
| ASRP | Count versus positivity precision; battery and deciding-input theorem; integrality lattice and exponent; inversion at Mertens precision; Stirling split; two-prime phase separation | An analytic certificate for small integrals; signed inversion at square-root precision |
| SMAP, ACP | Selection; margin; flip classification; conductor coordinates for every pattern | A selector beyond finite flips |
| AID, SAHT, ACS cells | Finite-index chain; Chebyshev identity; Gamma reserve; generator heads [K]; Haar identities | \(k=1\) layer [FS]; residual sign; upper bound on \(\mathcal E_{\rm crit}\) |
| RAPT, CACT | Sharp gap; adjunction spectrum; per-conductor eigenlines; positivity through touching; Ramanujan frames; primitive curvature | Growing conductors; operator-norm transfer; the touching capstone audit |
| SSHA, ALG | Atomic receivers; Markov failure above \(e/2\pi\); gap/scalar reduction; count-based local-to-global over \(\mathbb F_q\) | Local-to-global over \(\mathbb Z\) |
| Census (Zeta23, IGP, TTPC, ACS, SCP) | \(2/3\), \(HD(1)\), \(0.8876\); exchange rates; slack; dichotomy | A two-sided coalescent pair estimate or displacement-sensitive slack |
| RHTower heat/depth | Strata; \(2/3\) horizon; uniform-depth counts; local cofactor | Near-axis count; any vanishing mechanism |
| Density (RHTower Sieve, RDPS2, BVI) | Guth–Maynard, \(30/13\), \(17/30\); DH \(\sigma\ge5/6\); VK; QRH dictionaries | Any fixed power saving |
| HLF, HTGeometry, AET | Hecke continuation; finite-field elliptic base; loop-group Bruhat/Iwasawa; affine \(A_1\) Weyl poles | Hecke functional equation; arithmetic quotient and constant term; Maass–Selberg |

## External mathematical status

RH is unsolved ([Clay](https://www.claymath.org/millennium/Riemann-Hypothesis/)). External proofs below are not validated by this review.

- **Alpöge–Furman two-thirds theorem.** External formalized package `Zeta23`; the census builds on it.
- **Guth–Maynard large values theorem.** Published; formalized unconditionally in the corpus.
- **Quasi-RH manuscript (Chen–Gupta–Li).** Claims Dirichlet zero-freeness for \(\operatorname{Re}s>7/8\) [E]; the intake has no capstone; its detector floor \(288\) against the collision quantum \(2\) blocks an RH endpoint, not the \(7/8\) claim.
- **Ordinary-correlation manuscript.** Claims fixed-form Liouville two-point bounds \(X/(\log X)^c\) [E]: no power saving, no uniformity in growing shifts.
- **Context.** Bourgain's \(\mu(1/2)\le13/84\); DH for \(\sigma\ge25/32\); de Bruijn–Newman \(0\le\Lambda\le0.2\); Montgomery's pair correlation on \(|\alpha|\le1\) under RH; Diaconu–Paşol–Popa on affine quadratic multiple Dirichlet series over \(\mathbb F_q(t)\); Garland's loop Eisenstein series; the integer Chebyshev constant of \([0,1]\) is about \(0.42>1/e\), so sup-norm integer auxiliaries cannot reach the prime number theorem (classical). None supplies zero exclusion.
