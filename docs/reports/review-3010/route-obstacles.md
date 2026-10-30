# Research routes and their mathematical obstacles

Status: 30 October 2026, corpus `66f67bc27f`. **RH remains open.** The inventory is 32 live routes, 17 standalone candidates and the PW-B branch of PM. Every live route has an exact RH receiver; none has the arithmetic input that receiver needs.

**The frontier in five sentences.**

- **Complete Weil positivity on atomic families is a theorem at every fixed overlap, and now on every fixed conductor packet at slowly growing overlap.** The margin is the Poisson aliasing tail \(E(c)\); fixed packets stay positive up to \(c\le(\log N)^{A}\), \(A<1/48\).
- **The zeros read an atomic vector only through the Euler–Maclaurin boundaries of its Möbius horizons.** Single-horizon charges cannot see the real part of a zero; depth is visible only through two-horizon windows, i.e. through growing conductors.
- **Selectivity has become a resolution theory.** At fixed overlap a twisted form is decided by a finite Ramanujan-packet form; each twist has an exact resolution threshold; pole-free twins fall at one bounded overlap, while twins that share \(\zeta\)'s pole need overlap \(\asymp p^{1/7}\).
- **RH sits, conjecturally, on one critical curve \(E(c_N)\log N\asymp1\).** Margin, Gamma reserve and synthesis error are the same Fourier tail, separated only by the archimedean weight \(\log N\); for Gevrey and Steklov profiles the RH receiver already lies on this curve.
- **Over \(\mathbb Z\) no producer exists, and vanishing on the Adams fixed locus is exactly Bézout-sharp.** \(x^q=x\) lives on characters; turning character vanishing into a prime count is a duality step that no current object supplies.

Companions: [summary, open problems, next questions](obstacles-summary.md) · [walls ledger](walls-ledger.md) · [route unification](route-unification-ledger.md) · [frontier map](../rh-current-frontier-map.md) · [scoped obstructions](../rh-killed-routes.md). Research record: [working log](../../../logs/review-3010-rev2-research-2026-10-30.md).

## How to read this report

Evidence comes from corpus searches, Lean statements, module docstrings and proof structure. No builds or axiom audits were run.

| Label | Meaning |
|---|---|
| **[L]**, **[S]**, **[K]** | As in the frontier map: integrated; working or unintegrated; individually checked. |
| **[Lean]** | Lean statement read in this review; integration not assessed. |
| **[P]** | Paper proof only. |
| **[E]** | External claim. |
| **(inference)** | A conclusion of this review, not a Lean theorem. |

**Obstacle classes.**

- **A, just work.** The ingredients exist: certified computation, composition of proved theorems, quantification of a qualitative proof, transport between proved dictionaries, formalization of a written proof, or integration. An A-item never promises that a desired sign holds.
- **B, open mathematics.** A missing inequality, construction or uniformity, tagged by strength:

| Tag | Strength |
|---|---|
| **[RH]** | Equivalent to RH. |
| **[RH+]** | Strictly stronger than RH. |
| **[FS]** | Finitely many off-line zeros (RH above a height); implies LH and a fixed strip. |
| **[LH]** | At least Lindelöf strength. |
| **[≥QRH]** | Implies a fixed zero-free strip \(\Theta<1\). |
| **[open]** | Intermediate; no known solution; not known to imply RH. |

## Part I — The frontier in fourteen results

### 1. The overlap window of complete Weil positivity

Atomic families are \(f_x=\sum_{n\le N}x_n\,\varphi((u-\log n)/w)\), width \(w=c/N\). The complete Weil matrix \(W(\varphi,c,N)\) keeps every prime power, the Gamma factor and both poles.

| Regime | Statement |
|---|---|
| Every fixed \(c\) [L] | Every \(C^2\) profile on \([0,1]\) without real Fourier zeros is eventually positive definite. |
| Bounded ranges [K] | Tilted spline: one horizon for all \(0<c\le K\). |
| Fixed packets, growing \(c\) [L] | Tilted spline, every fixed finite conductor set \(S\): one horizon gives energy \(\ge (C/M)\,c^{-7}\sum a_m^2\) for all \(1\le c\le(\log N)^A\), \(0\le A<1/48\). Every fixed power of \(\log\log N\) is inside. The CAF variant reaches \(\alpha<1/40\) [S]. |
| Residual [L] | \(\|(W-E_m)v_m\|^2\le C_m[c^{10}(\log N/N)^2+c^6/\sqrt{\log N}]\), with all eight residual terms retained. |
| Gamma reserve [L] | \(\mathrm{arch}(f_x)\ge(\kappa c^{-7}\log N-bc)\cdot\)atom mass; it diverges along every schedule with \(c_N^8=o(\log N)\). |
| Existential growth [L] | Some unbounded schedule is positive, with no rate. |
| RH receivers [L/K] | \(C^2\): \(c_N^4\gg\log N\) (tilted spline \(c_N=2(\log N)^\alpha\), \(\alpha>1/4\)). Gevrey \(s\): \((\log\log N)^{s+}\). Steklov: \(L(\log L)^2\log\log L\), \(L=\log\log N\). |

**Margin and mechanism [L].** \(E_m(c)=\frac{2}{M\varphi(m)}\sum_{(a,m)=1}\frac ma\int_{ac/m}^\infty|\hat\varphi(2\pi t)|^2dt\). Successor shells \(n=km+h\) enter with Ramanujan weights; Möbius inversion and Poisson summation on the successor lattice repay the overlap loss; \(E(c)=E_1(c)\to0\) by Stirling. The arithmetic input is the prime number theorem in progressions to a fixed modulus, at every inverse-logarithmic rate.

**Where the window's losses sit (inference).**

- Arithmetic errors decay faster than any power of \(1/\log N\).
- The \(1/\sqrt{\log N}\) comes from harmonic boundary rows near the horizon. Several other terms are \(O(c^k/\log N)\) and were coarsened.
- With floor \(c^{-7}\), a loss of relative size \(1/\log N\) crosses the floor at \(c\asymp(\log N)^{1/7}\). Polynomial losses \(c^{k}\) push the reachable range to \((\log N)^{1/(k+7)}\).

**The critical curve (inference).** Three quantities are one Fourier tail:

- the margin \(E(c)\), the aliasing tail of sampling at overlap \(c\);
- the synthesis error energy behind every RH receiver, (aliasing error)\(^2\times\log N\), the \(\log N\) being the archimedean weight \(\log|t|\) at the atom bandwidth;
- the Gamma reserve \(\approx E(c)\log N\).

They meet on \(E(c_N)\log N\asymp1\). For Gevrey profiles this curve is \(c\asymp(\log\log N)^s\) and the receiver is \((\log\log N)^{s+}\). For the Steklov profile the curve is \(L(\log L)^2\) and the receiver \(L(\log L)^2\log\log L\). For \(C^2\) the curve is \((\log N)^{1/7}\) and the receiver \((\log N)^{1/4}\); the gap is the second-order trapezoid synthesis, which ignores \(\hat\varphi\)-decay.

Conjecture: the RH receiver lies on \(\{E(c_N)\log N\to0\}\) for every profile, and \(\{E(c_N)\log N\to\infty\}\) is the natural unconditional range. Past the curve the atomic family synthesizes every fixed test, so positivity there is Weil's criterion itself.

[Fixed packets](../../../formal/GaloisForLFunctions/CriticalArithmeticCorrelationTheory/FixedConductorPacketsStayPositiveAtGrowingOverlap.lean), [quasimode residual](../../../formal/GaloisForLFunctions/CriticalArithmeticCorrelationTheory/CompletedConductorQuasimodesHavePolynomialError.lean), [Gamma reserve](../../../formal/GaloisForLFunctions/CriticalArithmeticCorrelationTheory/TheGammaReserveSurvivesGrowingOverlap.lean), [every fixed overlap](../../../formal/GaloisForLFunctions/CriticalArithmeticCorrelationTheory/EveryProfileWithoutRealFourierZerosIsPositiveAtEveryOverlap.lean), [shells repay](../../../formal/GaloisForLFunctions/RenormalizedArithmeticPotentialTheory/TheShellsRepayEveryConductor.lean), [second-order synthesis](../../../formal/GaloisForLFunctions/SpacingScaleHarmonicAnalysis/TheSecondOrderSynthesis.lean), [log overlap](../../../formal/GaloisForLFunctions/RenormalizedArithmeticPotentialTheory/LogarithmicOverlapOfTheCompleteWeilMatrixIsTheRiemannHypothesis.lean), [Gevrey](../../../formal/GaloisForLFunctions/SpacingScaleHarmonicAnalysis/TheDenjoyCarlemanProfiles.lean), [Steklov](../../../formal/GaloisForLFunctions/TransMetzlerWeilPositivity/TheFixedProfileReachesAnIteratedLogEndpoint.lean).

### 2. The conductor spectrum is an arithmetic Weyl law

| Fact | Statement |
|---|---|
| Log law | \(\log m+F(c)-B(c)\le E_m(c)\) for all \(m\), and \(E_p(c)\le\log p+F(c)+B(c)+1\) for primes [L]. Hence \(E_m(c)/\log m\to1\) at fixed \(c\) [S]. |
| Heat threshold [L] | \(\sum_m e^{-\beta E_m(c)}<\infty\iff\beta>1\); prime conductors force divergence at \(\beta=1\). |
| Overlap decay | Tilted spline: \(E_m(c)\asymp_m c^{-7}\) for \(c\ge m\) [S]; \(E_m(c)\le(m/\varphi(m))E_1(c/m)\) [L]. |
| Green coordinates [L] | Optimal full-inverse cost \(1/E_1(c)\). Finitely many Ramanujan readings control \(W^{-1}\) at fixed \(c\). \(\mathrm{diag}(E_m^{-1})\) is compact with norm \(1/E_1\), yet \(\sum E_m^{-k}=\infty\). |
| Frames [L] | Ramanujan families of conductor \(\le Q\) have harmonic Gram \(\ge(\log(N+1)-2\log Q)\sum d_m^2\): well-conditioned up to \(Q\approx\sqrt N\). |

**Structure (inference).** The spectrum has a Fermi level at \(m\approx c\). Conductors \(m\lesssim c\) are near-degenerate, with energies \(\asymp c^{-7}\); conductors \(m\gg c\) have energies \(\approx\log(m/c)\). There are about \(c\) near-degenerate modes, and these carry the growing-overlap problem. The heat threshold \(\beta=1\) is the Bost–Connes critical temperature, which the corpus identifies with the critical line in Hecke-exponent units [L].

[Heat threshold](../../../formal/GaloisForLFunctions/CompletedArithmeticForms/ConductorHeatThreshold.lean), [log law](../../../formal/GaloisForLFunctions/CompletedArithmeticForms/ConductorLogLaw.lean), [Green tail](../../../formal/GaloisForLFunctions/CompletedArithmeticForms/WeilGreenTail.lean), [frames](../../../formal/GaloisForLFunctions/CriticalArithmeticCorrelationTheory/GrowingRamanujanFamiliesHaveASquareRootHorizon.lean), [Bost–Connes](../../../formal/GaloisForLFunctions/ArithmeticPositiveDuality/TheBostConnesTemperatureIsTheHeckeExponent.lean).

### 3. The horizon law: how the zeros see an atomic vector

Write \(x_n=\sqrt n\,y_n=(a*1)(n)\), \(a=x*\mu\).

| Law | Statement |
|---|---|
| Horizon law [L] | For every vector, profile and horizon: \(Q(f_y)=\operatorname{Re}\sum_\rho m_\rho\,\hat g(\gamma_\rho)\overline{\hat g(\bar\gamma_\rho)}\,H_a(1-\rho)H_a(\rho)\), with \(H_a(s)=\sum_{d\le N}a_dd^{-s}B_{\lfloor N/d\rfloor}(s)\) and \(B_M\) the Euler–Maclaurin boundary of \(\sum_{k\le M}k^{-s}\). |
| Pole mode [L] | \(a=\delta_1\): product \(B_N(1-\rho)B_N(\rho)\); pole parts give the Li charge \(N/(\rho(1-\rho))\). The tail parts are the Poisson dual of the successor shells. |
| Charge blindness [L] | \(\|P_a(s)P_a(1-s)\|\le N(\sum|a_d|/d)^2/|s(1-s)|\) on \(0\le\operatorname{Re}s\le1\); \(\operatorname{Re}1/(\rho(1-\rho))>0\) for every strip zero. A single horizon carries no growth \(N^{|\beta-1/2|}\). |
| Aperture modes [L] | \(y_n=n^{\kappa-1}\): charge \(N^{2\kappa}/(\kappa^2-z^2)\), \(z=\rho-\tfrac12\); summed over zeros it is the theta center-mixed current at aperture \(\kappa\). |
| Windows [L] | On \(M<n\le N\) the cross terms have modulus \(N^\kappa M^\kappa(N/M)^{\pm\operatorname{Re}z}\) against the diagonal \(N^{2\kappa}\). Windowed aperture modes are Weil's exponential box tests plus aliasing. |
| Theta [L] | The theta horizon transform is \(-\hat f_1(\gamma_\rho)B_N(\rho)\); the atomic pole mode reads \(B_N(1-\rho)\). Both read one horizon boundary, from the two sides of the functional equation. |

**Consequence (inference).** A fixed conductor packet has horizons \(N/d\), \(d\mid m\), so its window ratio is at most \(m\) and an off-line zero gains at most \(m^{|\beta-1/2|}\). Fixed packets are depth-blind, which is consistent with their unconditional positivity. Depth enters only through growing conductors, long windows and sub-pole apertures \(\kappa<|\beta-\tfrac12|\).

[Möbius horizons](../../../formal/GaloisForLFunctions/RenormalizedArithmeticPotentialTheory/TheZerosSeeEveryAtomicVectorThroughItsMobiusHorizons.lean), [pole mode](../../../formal/GaloisForLFunctions/RenormalizedArithmeticPotentialTheory/ThePoleModeMeetsTheZerosOnlyAtTheHorizon.lean), [charge blindness](../../../formal/GaloisForLFunctions/RenormalizedArithmeticPotentialTheory/TheHorizonChargeIsBlindToTheRealPartsOfTheZeros.lean), [aperture modes](../../../formal/GaloisForLFunctions/RenormalizedArithmeticPotentialTheory/TheApertureModesCarryTheThetaApertureCharge.lean), [windows](../../../formal/GaloisForLFunctions/RenormalizedArithmeticPotentialTheory/AWindowedApertureModeIsAnExponentialBoxTest.lean), [theta horizon](../../../formal/GaloisForLFunctions/RenormalizedArithmeticPotentialTheory/TheThetaSourceSharesTheHorizonOfThePoleMode.lean).

### 4. Resolution theory of twists

A real twist \(\lambda\) of \(\Lambda\) with summable defect \(d_\lambda(k)=(\Lambda(k)-\lambda(k))/\sqrt k\) defines a twisted complete matrix \(W_\lambda(c,N)\).

| Result | Statement |
|---|---|
| Packet decision [L] | At fixed \(c\), the sign of \(W_\lambda\) is the sign of \(E_\lambda(T,\beta)=\sum\beta_m^2E_m(c)+2\sum_kd_\lambda(k)k^{-1/2}M(y\cdot y(k\cdot))\) on finite Ramanujan packets. The packet span is almost invariant and its complement costs at least any prescribed \(T\). |
| Exact threshold [L] | The resolution bottom decreases in \(c\), strictly past zero. \(c_0(\lambda)\) is exact: positive below, negative on an atomic test above. |
| Flips [L] | \(\lambda_p(c)\ge E(c)-\kappa_p^2/(4(E(c/p)-\kappa_p-E(c)))\), \(\kappa_p=4\log p\sqrt p/(p-1)\). Tilted spline: \((p/\log p)^{1/7}\lesssim c_0(\omega_p)\lesssim p^{1/7}\). Every finite flip set has an exact threshold. |
| Pole-free twins [L] | One profile at one bounded overlap above its Robin–Euler ratio \(<1\) separates \(\zeta\) from every completely multiplicative \(\pm1\) gauge with bounded harmonic sums: the Liouville twin and every cofinite flip. |
| Liouville twin [K] | One explicit profile: \(\zeta\) positive and the twin negative at every fixed \(c\ge1\). |

**Consequence (inference).** The pole decides bounded-overlap selectivity. Twins without \(\zeta\)'s pole fall at one bounded overlap. Twins that keep the pole (finite flips, close to \(0\) on the gauge torus) need overlap growing like a power of the distance. A hypothetical \(\zeta\) with an off-line zero also keeps the pole, and its perturbation of \(\psi\) is not summable. Fixed overlap therefore resolves exactly the summable-defect class.

[Packets decide](../../../formal/GaloisForLFunctions/RenormalizedArithmeticPotentialTheory/ATwistedCompleteWeilMatrixIsDecidedByItsRamanujanPackets.lean), [exact threshold](../../../formal/GaloisForLFunctions/RenormalizedArithmeticPotentialTheory/TheOverlapThatResolvesATwistIsAnExactThreshold.lean), [set by conductors](../../../formal/GaloisForLFunctions/RenormalizedArithmeticPotentialTheory/TheFlipThresholdIsSetByTheConductorsOfThePrime.lean), [power of the prime](../../../formal/GaloisForLFunctions/RenormalizedArithmeticPotentialTheory/TheFlipThresholdGrowsLikeAPowerOfThePrime.lean), [cofinite flips](../../../formal/GaloisForLFunctions/CriticalArithmeticCorrelationTheory/FixedOverlapPositivityIsSelectiveAgainstEveryCofiniteFlip.lean), [pole-free twins](../../../formal/GaloisForLFunctions/TransMetzlerWeilPositivity/EveryPoleFreeSignTwinBreaksAboveTheRobinEulerRatio.lean).

### 5. The gauge torus: RH is an exponent at one point

For a source \(a\) and gauge point \(x\), \(\theta_a(x)\) is the least power bounding \(\sum_{n\le N}a(n)\chi_x(n)\).

| Fact | Statement |
|---|---|
| Typical value [L] | \(\theta_\mu=1/2\) Haar-a.e.; \(\theta_\mu(0)=\Theta=\sup\operatorname{Re}\rho\); RH \(\iff\) \(0\) is typical. |
| No multiplicative certificate [L] | Gauge-invariant bounds give \(\ge3/4\) at \(0\); finitely determined ones give \(\ge1\). |
| Coherence and antipode [L] | Nonnegative statistics are maximal at \(0\); the pole is coherence. \(S_N(\ell)+S_N(0)=2\psi(\sqrt N)\). |
| Twin inequality [L] | \(\exp_\mu(x+\ell)\le(1+2\exp_1(x)+\exp_\mu(2x)/2)/3\). Quadratic Dirichlet twins \(\le(2+\Theta)/6\). A universal floor \(1/2\) would force \(\Theta=1\). |
| Special locus [L] | Dirichlet points read GRH and are typical on average (large sieve). |
| Short shells [L] | For \(c\le2\) the shells satisfy \(|n-km|\le2\) and every level-\(q\ge3\) Dirichlet average vanishes. The sign at small overlap is a property of the trivial point alone. |
| Level of distribution [L] | Over primitive Dirichlet points of conductor \(\le Q\): \(\sum|P|\le\|g\|_1\|a\|_1(N+Q^2)\|x\|_2^2\). The trivial point is the single term \(q=1\). |
| Affine positivity [L] | Positive dilation- and successor-invariant forms are \(c\,\delta_0+d\,\)Haar; index \(\le1\), carried by the pole. Arithmetic positivity must come from the shells. |
| Function field [L] | Over \(\mathbb F_q[T]\) the Möbius sums are \(1-q\): the trivial point is *better* than typical, and its Liouville twin has exponent \(1\). |

The bounded-overlap mechanism uses linear prime sums in fixed residue classes (Ramanujan weights, additive major arcs). For \(c\le2\) no multiplicative level average sees the shells at all.

[Not gauge invariant](../../../formal/GaloisForLFunctions/ArithmeticGaugeTheory/TheExponentIsNotGaugeInvariant.lean), [twin inequality](../../../formal/GaloisForLFunctions/ArithmeticGaugeTheory/TheLiouvilleTwinInequality.lean), [short shells](../../../formal/GaloisForLFunctions/ArithmeticGaugeTheory/TheShortShellsHaveNoConductor.lean), [level 1/2](../../../formal/GaloisForLFunctions/ArithmeticGaugeTheory/TheShellsHaveLevelOfDistributionOneHalf.lean), [affine positivity](../../../formal/GaloisForLFunctions/ArithmeticGaugeTheory/AffinePositivityIsThePoleAndHaar.lean), [function field](../../../formal/GaloisForLFunctions/ArithmeticGaugeTheory/TheFunctionFieldCalibrationIsDerived.lean).

### 6. Index theory of the Weil kernel

| Law | Statement |
|---|---|
| Index [S] | \(\kappa(K_\zeta)=\#\)distinct right zeros; RH iff \(\kappa\le1\) (even, so \(0\)). |
| Global law [S] | \(\kappa=0\iff\psi(x)-x\le C\sqrt x\log^2x\) eventually \(\iff\) the odd Liouville class has an upper count. |
| Heights and carriers [L/K] | \(\kappa_T=O(T\log T)\); towers \(3^k/2^j\) certify height \(T\); boxes \(p^iq^j\) carry finite spectra. |
| Towers [L/K/S] | Fine towers decide; attained depth seen by almost every prime; on finite support almost every prime tower decides. |
| Waves [L/S] | Index = least number of exceptional waves; collision mass \(=2(\kappa+\)excess\()\). |
| Polar divisor [L] | For curve data, index = number of right pole classes. |
| Local constituents [S] | Axis-supported kernels on \(\mathbb Z^S\) have index \(0\) or \(\infty\). |
| Finite stratum [S/L] | Finite index \(\iff\) finite off-line support; implies LH and \(\Theta<1\). |

### 7. Precision and counting

- **Stabilizers [L/K/S].** The count's stabilizer is the square-root class \(\mathcal Q\); tower positivity is precision-exact. Finite aperture cannot decide.
- **Battery [S/L].** Anything implying the count rejects the Liouville twin. An upper count for a majorant of \(\Lambda\), or a lower count for a minorant, proves RH.
- **Chebyshev ledger [L].** \(\psi\) is two Möbius moments, a sawtooth inversion of size \(<n\) and a Mertens remainder.

### 8. Producers: one ledger, no Frobenius, Bézout-sharp Adams vanishing

| Fact | Statement |
|---|---|
| Ledger [L] | \(\sum m_x\le\deg P\) over \(\mathbb F_q\); \(\sum m_p\log p\le\log A\) over \(\mathbb Z\). |
| Bézout / Riemann–Roch for \(\mathbb G_m(\mathbb Q)\) [K/L] | \(\prod p^{m_p}\le N\); \(h^0(N,m)=\lfloor N/\prod p^{m_p}\rfloor\): exact and linear. |
| Small = divisible [L] | Integer auxiliaries small on long progression stretches are divisible. |
| No Frobenius [L] | Bounded-defect ring endomorphisms of \(\mathbb N\) are trivial. |
| Adams operations [L] | \(\psi^q\)-fixed twists are the \((q-1)\)-torsion twists; \(\psi^2\) fixes only \(0\). |
| Adams vanishing [L] | Full multiplicity \(r\) on the \(q\)-torsion grid or the \(\psi^{q+1}\)-fixed locus forces support \(\ge2^{qr}\); \((\chi(2)^q-1)^r\) is sharp. |
| Jets [L] | Vertical jets miss transverse directions (transcendental coefficients); with algebraic coefficients the first vertical jet is faithful (Baker); two-prime log monomials are independent. |
| Factorial ratios [L] | Balanced ratios have valuations periodic in \(n\bmod p\) and cost \(\log A_n\ge(2\log2-\varepsilon)mn\); the central binomial is optimal. Square-root precision needs non-periodic valuations. |
| Twist tower [L] | Collapses to level \(0\) over \(\mathbb Z\). |

**Consequence (inference).** Vanishing on the Adams fixed locus is as cheap as \(x^q-x\), but only along one prime coordinate, and it is exactly Bézout-sharp. The fixed locus consists of characters, while Stepanov counts points. An Adams producer therefore needs a duality step that converts character vanishing into a prime count, and that step is the explicit formula itself.

[Adams multiplicity](../../../formal/GaloisForLFunctions/ArithmeticHarmonicAnalysis/AdamsMultiplicityResolution.lean), [boundary](../../../formal/GaloisForLFunctions/ArithmeticHarmonicAnalysis/TorsionMultiplicityBoundary.lean), [first jets](../../../formal/GaloisForLFunctions/ArithmeticHarmonicAnalysis/AlgebraicVerticalFirstJets.lean), [Chebyshev precision](../../../formal/GaloisForLFunctions/ArithmeticGaugeTheory/FactorialRatiosHaveChebyshevPrecision.lean), [Riemann–Roch](../../../formal/GaloisForLFunctions/EffectiveArithmeticHodgeTheory/TheRiemannRochTheoremOfTheMultiplicativeGroup.lean).

### 9. The complete source on Haar cells

- **Haar identities [L].** Gamma pays every detail; \(W\ge\)mass\(/10\) per cell; \(W+G=D_X+P+\sum V_X(a)u_a^2\), \(G\ge0\), \(V_X\) signed.
- **Prime edges [K].** Literal prime edges keep a Gamma reserve; full-Weil prime-edge entries are negative.
- **Finite index [L/S/K].** Uniform on every layer except the first prime layer; prime–polar cancellation carries an \(e^R\) loss [S].

### 10. Theta moments (TH)

- **Hierarchy [L].** Rank seven strict for \(0<a<1/2\); the all-rank sign is RH.
- **Rank eight.** The odd \(4\times4\) native block is nonnegative for \(q\ge6\) [L]. An aperture-free seam split reduces rank eight to one inequality [L]. The three-atom model and the Cauchy tail beyond three atoms are explicit [L]. Piecewise \(LDL^T\) certificates cover \(31/10\le q\le8\) [S].
- **Open.** \(\int_{(0,r_c]}r^2\min(Q_r(v),0)+\int_{(r_c,\infty)}r^2Q_r(v)\ge0\) for every \(v\in\mathbb R^4\), \(r_c=\log(6/\pi)\); then all ranks.

### 11. Heat flow (WD, LA)

- \(2/3\) horizon [L]; localized dissipation through collisions and \(t=0\) [K]; collision mass \(\to\infty\) iff tower indices are unbounded [L].
- **Open.** Outer-energy absorption and a uniform count as \(t\downarrow0\) [FS].

### 12. Critical-line census

- Simple critical \(\ge HD(1)+10^{-8}\); simple or critical \(\ge0.8876\) [L]. Dichotomy: \(70\%\), or a simple near-line off-line core [K].
- Exchange rates: \(E(1/9)\le4\Rightarrow70\%\); prime surplus \(\le N/18\Rightarrow75\%\) [L].

### 13. Quasi-RH, density and Dirichlet \(L\)-inputs

- Guth–Maynard \(30/13\), DH on \(\sigma\ge5/6\), Vinogradov–Korobov and Siegel are formalized [L]. Density envelopes never force a zero to vanish.
- **New [L].** A conductor-uniform zero-free region \(\beta\le1-c/\log^2(q(|\gamma|+3))\) for every nonprincipal \(\chi\), except real zeros of real characters, together with the \(3\)–\(4\)–\(1\) inequality and a uniform partial fraction.
- **Missing.** Siegel–Walfisz and Bombieri–Vinogradov (lexical search: no declarations).
- **External [E].** Dirichlet zero-freeness for \(\operatorname{Re}s>7/8\); no corpus capstone.

[Uniform zero-free region](../../../formal/GaloisForLFunctions/RHTower/DirichletLUniformZeroFreeRegion.lean).

### 14. Foundations

Hecke continuation and functional equations [K]; genus-one base over \(\mathbb F_3\) [K]; real loop group [K]; Baker, six-exponentials and Matveev machinery in RHTower. These are tools; none carries a selective sign.

## Part II — Live routes

Each entry: **State**, then **A** (just work) and **B** (open, tagged).

### WL — Weil lag / prime-error energy

**State.**

- Critical-deficit energy, linear prime-error budget and the one-sided \(\sqrt x\log^2x\) count are each RH; the count is \(\kappa=0\) and the odd-class upper count [S].
- Chebyshev ledger [L]. Integer approximate vanishing is divisibility [L]. Factorial-ratio producers have Chebyshev precision \(2\log2\) [L]. Adams vanishing costs support \(2^{qr}\) [L].

**A.**

- Certified truncations with high-zero tails.
- Product-bias classification in Lean [P].
- Classification of auxiliaries attaining the \(2^{qr}\) boundary.

**B.**

- The one-sided count or odd-class upper count **[RH]**.
- Joint square-root control of moments, sawtooth and Mertens **[RH]**.
- A parity-selective auxiliary with non-periodic valuations and controlled size **[open]**.
- Subtracted lag **[FS]**; genus saturation **[RH+]**.

[Receiver](../../../formal/GaloisForLFunctions/BiScaleUncertainty/WeilLagCriticalDeficitEndpointAndLimitLaw.lean).

### RW — Restricted Weil ground energy

**State.** RH iff \(\mu(A)>0\) at every aperture. \(\mu\) is strictly decreasing; positive floors must decay doubly exponentially. The Gamma boundary norm \(\pi/2\) has no uniform relative reserve [S].

**A.** Certified finite-aperture minima; transfer of the Poisson-margin method to the aperture filtration (audit).

**B.** Cumulative aperture relaxation bounded by the initial reserve, paying low modes, collars and polar energy **[RH]**. [Aperture flow](../../../formal/GaloisForLFunctions/ArithmeticContinuationAndCriticalEnergy/TheApertureFlowNeverStalls.lean).

### FU — Signed prime scheduling

**State.** RH iff the normalized completed Abel moment is bounded above. Narrow prime channels have a useful sign [L]; wide channels can be positive [S].

**A.** Seed, drift, cross-block and endpoint ledgers on fixed schedules.

**B.** A joint signed total over a prime-exhaustive schedule **[RH]**. [Receiver](../../../formal/GaloisForLFunctions/RHTower/CCM/CCMFUSuzukiMobiusDivisorOneSided.lean).

### CFC — CCM first-clock lower bound

**State.** RH iff the literal first-clock source sine coefficient is bounded below on an aperture tail; under ¬RH it is unbounded below on every tail. Phase-natural transport is the identity.

**A.** Certified coefficient evaluations on finite aperture ranges.

**B.** The tail lower bound **[RH]**. [Completeness](../../../formal/GaloisForLFunctions/RHTower/CCM/CCMFirstClockTailLowerBoundCompleteness.lean).

### RP — Matched-quantile history floor

**State.** RH iff an eventual linear floor \(-B(K+2)\); the history drops below \(-\delta(K+2)\) cofinally, so no sublinear floor exists [L].

**A.** Low-LCM instantiation; the escape constant on computed ranges.

**B.** A linear floor paying high-LCM pairs, moving core and transport **[RH]**. [Floor](../../../formal/GaloisForLFunctions/RHTower/SPEQuantileRieszRoutePLinearFloorCriterion.lean).

### PA — Prime–archimedean passivity

**State.** Current-sign, Bernstein-mismatch and compact-moment receivers; each fixed Hausdorff order is positive at large shift.

**A.** Explicit thresholds for finite order blocks.

**B.** All-order, all-shift sign **[RH]**. [Moments](../../../formal/GaloisForLFunctions/RHTower/PrimeArchThetaFirstAtomHighOrderMomentBounds.lean).

### MC — Möbius cancellation

**State.**

- Strict half-power and subpower energy are RH; \(M=o(\sqrt x)\) is false.
- \(\theta_\mu(0)=\Theta\); typical \(1/2\); no gauge-invariant certificate below \(3/4\) [L].
- Twin inequality [L]. Short shells have no conductor; shells have level of distribution \(1/2\) [L].
- Uniform Dirichlet zero-free region [L]. Successor defects recover gauge values with logarithmic loss [L].

**A.**

- Siegel–Walfisz from the uniform zero-free region and Siegel's theorem; then Bombieri–Vinogradov from the gauge-form large sieve.
- An exponent-inequality calculus from \(\mu^2=\sum_{d^2\mid n}\mu(d)\), \(\mu*1=\delta\), \(\Lambda*1=\log\).

**B.**

- Every strict half-power, or the odd-class upper count **[RH]**.
- Linear Mertens budget **[RH+]**.
- Any fixed one-sided power saving **[≥QRH]**.
- Any \(0\)-specific, non-gauge-invariant inequality improving \(\theta_\mu(0)\) below \(1\) **[≥QRH]**.

[Hilbert criterion](../../../formal/GaloisForLFunctions/RHTower/MobiusHilbertFormEquivalence.lean), [trivial point](../../../formal/GaloisForLFunctions/ArithmeticGaugeTheory/TheTrivialPointIsNeverBetterThanTypical.lean).

### TT — Theta tails and directed covariance

**State.** Seam, Wold and odd-Weil receivers; sharp \(t<1/2\) threshold. The truncated theta transform at a zero is \(-\hat f_1\,B_N(\rho)\), the tail \(+\hat f_1\,B_N(\rho)\) [L]: TT reads the same horizon boundary as the atomic pole mode.

**A.** Fixed directed-covariance and reflected-prime terms; transport of the horizon law to theta windows.

**B.** Signed nonlocal covariance at every scale, or complete odd positivity **[RH]**. [Wold receiver](../../../formal/GaloisForLFunctions/RHTower/PaperWoldDirectedCovarianceRH.lean).

### LA — Line anchor

**State.** Finite-head and heat receivers; ordinary \(\xi\) coefficients are Turán [L] and Lorentzian [S]; \(2/3\) horizon [L]; localized dissipation [K].

**A.** Certified heads and low degrees; heat-tail errors with the local cofactor.

**B.** All-height, all-degree head signs **[RH]**; a uniform heat count **[FS]**. [Finite head](../../../formal/GaloisForLFunctions/RHTower/XiSliceHeatFiniteHeadReduction.lean).

### TG — Integer trace below one

**State.** Winding, cubic-transgression and central-gap receivers; Gaussian coprime-divisibility covariance.

**A.** Finite projection and transgression data with residual and trace separated.

**B.** A matrix-complete decomposition with nonnegative residual and trace below one on every disc **[RH]**. [Index estimate](../../../formal/GaloisForLFunctions/RHTower/RestrictedProjectionIndexOperatorNormCriterion.lean).

### HF — Arithmetic Hodge positivity

**State.**

- **Atomic branch.**
  - Positive at every fixed overlap [L].
  - Fixed conductor packets positive for \(1\le c\le(\log N)^A\), \(A<1/48\) [L].
  - Conductor spectrum \(\log m+O_c(1)\) [L/S]; Green coordinates [L].
  - Gamma reserve at growing overlap [L].
  - Resolution theory: Ramanujan-packet decision, exact thresholds, flips \(\asymp p^{1/7}\), pole-free twins at bounded overlap [L].
  - Horizon law for every vector [L].
- **Haar branch.** Haar identities with a signed diagonal; finite index except the first prime layer.
- **Prefix branch.** Exact Schur reduction [K]; uniform mixed-entry payment with constant \(20\) [L].

**A.**

- Make the residual constant \(C_m\) explicit and polynomial in \(m\); then extend packet positivity to all conductors \(m\le M(c)\) and the complement. Deliverable: an explicit unconditional full-matrix schedule \(c_N\to\infty\).
- Sharpen \(c^{10}/\sqrt{\log N}\) to the true term-by-term exponents.
- Siegel–Walfisz for conductors \(\le(\log N)^A\).
- Higher-order synthesis for \(C^2\) profiles, moving the receiver to \((\log N)^{1/7+}\).
- Tilted Steklov and Gevrey profiles without real Fourier zeros.
- The one-zero damage law via the horizon law.
- Removal of the \(\log p\) gap in flip thresholds.

**B.**

- Positivity on an RH-complete schedule, complete-cell index zero, residual sign or work ceiling **[RH]**.
- Loss-free control of the near-degenerate conductors \(m\lesssim c\), reaching the critical curve \(E(c_N)\log N\asymp1\) **[open]**.
- The sign of the complete form at the critical curve **[open]**; past it **[RH]**.
- Uniform finite index; finite \(\mathcal E_{\rm crit}\) **[FS]**.
- Haar-branch joint payment of the non-arithmetic Gamma graph, signed diagonal, first prime and poles **[open]**.

[Fixed packets](../../../formal/GaloisForLFunctions/CriticalArithmeticCorrelationTheory/FixedConductorPacketsStayPositiveAtGrowingOverlap.lean), [prefix payment](../../../formal/GaloisForLFunctions/CompletedArithmeticForms/WeilPrefixPayment.lean).

### CHMD — Causal hyperbolic–modular duality

**State.** Wave, Doob and nodal receivers; actual generator heads have uniform Gamma bounds; complete even-power error \(\le\delta\Gamma(f)\) [K]; literal prime edges keep fraction \(1-\log2/\log3\); full-Weil prime-edge entries negative [K].

**A.** Domain and cutoff theorems on fixed sources; signed residual with the primitive defect.

**B.** The one-sided wave bound or odd Doob inequality, paying first-prime, coarse, head and polar terms and the retained-orbit sign **[RH]**. [Odd criterion](../../../formal/GaloisForLFunctions/RHTower/CHMDOddSectorCriterion.lean).

### TH — Theta moment positivity

**State.** Rank seven strict; all-rank sign \(\iff\) RH. Rank eight reduced to one aperture-free compensation inequality; native bulk \(\ge0\) for \(q\ge6\) [L]; three-atom model and Cauchy tail [L]; piece certificates on \(31/10\le q\le8\) [S]. Heated orthant signs hold at all ranks.

**A.**

- Audit and integrate the piece certificates; extend them below \(q=31/10\).
- Certified evaluation of the \(r^2\)-weighted compensation integral for all \(v\in\mathbb R^4\). This is a finite certified computation; it may fail, and then TH stops at rank seven.

**B.**

- All ranks with strictness and radical control, or signed heated coefficients at one common time **[RH]**.
- A rank-uniform compensation mechanism, the theta analogue of shell repayment **[open]**.

[Seam split](../../../formal/GaloisForLFunctions/RHTower/ThetaCusp/ThetaCuspOddFourSeamSplit.lean), [native bulk](../../../formal/GaloisForLFunctions/RHTower/ThetaCusp/ThetaCuspOddFourNativeBulk.lean), [completeness](../../../formal/GaloisForLFunctions/RHTower/ThetaCusp/ThetaCuspCenterMixedSignedJetCompleteness.lean).

### RN — Renewal and singular comparison

**State.** Green/BV realization; compact cone-positive renewal operator with exact regularized determinant.

**A.** Finite packet and resolvent data with cusp and seam terms.

**B.** Directed mixed prime+Gamma \(\ge\) pole **[RH]**. Cone positivity does not give real spectrum. [Spectrum](../../../formal/GaloisForLFunctions/RHTower/ThetaRenewalFredholmSpectrum.lean).

### WD — Ward caps and collision

**State.** A nonnegative integrated cap vanishes iff RH. Collision mass \(=2(\kappa+\)excess\()\) on finite index; \(\to\infty\) iff tower indices unbounded [L]. Localized dissipation through collisions and \(t=0\) [K].

**A.** Explicit \(N(t)\) on compact ranges; summed localized estimates on fixed height windows.

**B.** Cap extinction **[RH]**; uniform nonreal count **[FS]**; uniform high count **[LH]**. [Ward receiver](../../../formal/GaloisForLFunctions/RHTower/XiWardGlobalCapAndFiniteHeadArithmetic.lean).

### LI — Paired Li balances

**State.** The guarded history-zero set is finite, and RH iff it is empty; RH iff the Cayley–Li ladder is primitive nonpositive, with non-decaying couplings [S].

**A.** Fixed paired histories; finite Cayley ladders.

**B.** Payment at every possible guarded zero, a subexponential history floor, or the ladder sign **[RH]**. [Cayley ladder](../../../formal/GaloisForLFunctions/ArithmeticLorentzianGeometry/RHIsReflectionPositivityOfTheCayleyLadder.lean).

### SZ — Suzuki first variation

**State.** Ward-defect lower-bound receiver; compact-\(L^2\) first variation = full Weil form; factorial/grid tent families are RH [S]. Bare-source \(\ell^2\), uniform causal recovery and positive unital finite parts are excluded [L].

**A.** Moving-aperture limits on specified tent families.

**B.** The tent-family sign, including low and mixed modes **[RH]**. [Transfer](../../../formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiCriticalRHCompleteFamilyTransfer.lean).

### PM — Haar approximation / damped admission

**State.** Positive gauge mass of every escape state is RH; power-growth escape has zero gauge mass [L]; the Möbius escape state is an Euler product leaning to the Liouville point, blind to zeros [L].

**A.** Fixed cofactor Grams; effective pole orders.

**B.** Positive gauge mass for every escape state **[RH]**; exterior tightness **[open]**. [Visibility](../../../formal/GaloisForLFunctions/ArithmeticCorrelationGeometry/RHIsTheVisibilityOfEveryEscapeState.lean).

### JAS — Joint ancestry

**State.** Level-one prime-product positivity and square-shell receivers; unconditional sign at a logarithmic prime budget.

**A.** Budget gaps on chosen shells.

**B.** The square-root power budget **[RH]**. [Capstones](../../../formal/GaloisForLFunctions/RHTower/JointAncestryLevelOneCapstones.lean).

### CTF — Báez–Duarte approximation

**State.**

- Residual \(=(1-\Lambda\text{-readout})^2+\)centered energy; divisor covariance = completed cyclotomic Gram [K].
- Every superlinear Chebyshev exponent is carried by the nonnegative cyclotomic remainder [K].
- Free-terminal dual cost \(D_T\); a fixed probe costs \(D_T+(Tb_T)^2\) [L]; Euler completion error \(\le(M+1)^2/(T+1)\), \(1\le X<M\) [L].

**A.** Optimized finite rows with both residual components and the terminal edge reported.

**B.** Complete error \(\to0\): upper covariance cancellation along compatible cutoffs, \(BX^\varepsilon\) in the inner cutoff for every zero and \(\varepsilon\) **[RH]**. [Readout](../../../formal/GaloisForLFunctions/BezoutValuationIncidence/VonMangoldtReadoutFormOfTheBaezDuarteCriterion.lean), [source probe](../../../formal/GaloisForLFunctions/CompletedArithmeticForms/SourceProbeBoundary.lean).

### HCF — Gaussian heat trace on two grids

**State.** Positivity on both \(\log2/\log3\) grids is RH; one grid aliases; two-prime phase separation is polynomial [S].

**A.** Finite degrees and heights on both grids.

**B.** Both grid signs at all degrees **[RH]**; a many-node Gram floor from phase separation **[open]**. [Two grids](../../../formal/GaloisForLFunctions/RHTower/XiGaussianHeatTwoPrimeSourceSampling.lean).

### XN — Newton invariant discs

**State.** Line-centred self-map discs covering every zero give RH; exact Laplacian of the interior margin.

**A.** Certified discs.

**B.** A covering family with nonnegative interior margin **[RH]**. [Criterion](../../../formal/GaloisForLFunctions/RHTower/XiNewtonSchwarzPickCriticalLine.lean).

### BAG — Deterministic self-return

**State.** Strong recurrence through the right strip is an RH receiver; the archimedean line through \(0\) carries the exponent \(\Theta\) at every point [L].

**A.** Finite-head returns on zero-free targets.

**B.** Returns near every right-strip point, including possible zeros **[RH]**. [Receiver](../../../formal/GaloisForLFunctions/RHTower/ZetaStrongRecurrenceReceiver.lean).

### EWU — Even pole-weight uniqueness

**State.** Attained aperture-antitone blind minima; RH iff some real weights make the full functional nonnegative up to each aperture [L].

**A.** Certified finite blind problems.

**B.** Nonnegative actual blind minima at every aperture **[RH]**. [Existence](../../../formal/GaloisForLFunctions/RHTower/WeilPositivityFiniteLevelExistenceDecidesRH.lean).

### GTA — Transverse Schur charge

**State.** Rank-uniform decay of the quartic Schur charge is RH.

**A.** Finite-rank charges.

**B.** Rank-uniform arithmetic decay **[RH]**. [Equivalence](../../../formal/GaloisForLFunctions/RHTower/Hedenmalm/HedenmalmThetaSchurQuarticSpectralDecayEquivalence.lean).

### OWU — Odd Weil-weight uniqueness

**State.** Odd and dilation-ray criteria; smooth odd witnesses separate \(\Lambda\) from the Liouville twin and the first flip at fixed radii; finite apertures cannot decide. Windowed aperture modes realize box tests inside atomic families [L].

**A.** Collar accounting with both pole corrections.

**B.** All-aperture odd sign **[RH]**; conductor/forcing compatibility **[open]**. [Dilation ray](../../../formal/GaloisForLFunctions/RHTower/WeilDilationRayCriterion.lean).

### PBM — Pole-regularized prime series

**State.** Convergence at every \(\sigma>1/2\) is RH.

**A.** Partial sums in controlled half-planes.

**B.** Critical-abscissa cancellation **[RH]**; a fixed abscissa \(<1\) **[≥QRH]**. [Criterion](../../../formal/GaloisForLFunctions/RHTower/RegularizedLogZetaAbscissa.lean).

### RB — Robin / Nicolas extremizers

**State.** Eventual criteria; reduction to colossally abundant integers; large counterexamples need growing prime cores.

**A.** Certified finite extremal ranges.

**B.** The square-root remainder on prime-saturated extremizers **[RH]**. [Reduction](../../../formal/GaloisForLFunctions/RHTower/RobinColossallyAbundantReduction.lean).

### SRT — Lag localization and atomic visibility

**State.**

- Every-width lag receivers; explicit \((\log\log N)^\alpha/N\) schedules reach \(\kappa\), \(\alpha>1\) [L].
- The atomic window, packet positivity and resolution theory (§1, §4).
- Twins seen by every large Gevrey section [L]; tower positivity precision-exact.

**A.**

- Full-index exhaustion at the Steklov schedule; removal of the extra \(\log\log L\).
- Tilted Steklov profile; explicit schedules (shared with HF).

**B.**

- Late lag, all-generator tower sign or RH-schedule sign **[RH]**.
- Unattained-depth tower detection **[open]**.
- Reaching the critical curve from below **[open]**.

[Lag receiver](../../../formal/GaloisForLFunctions/SquareRootThreshold/EveryWidthDecidesTheCriticalLine.lean).

### ACT — One-shift arithmetic criticality

**State.** One fixed theta shift with an all-profile variation inequality gives odd positivity and RH; short collars absorbed only with support-dependent shifts.

**A.** Signed moment ledgers for prescribed profiles.

**B.** One shift for every support and profile **[RH]**. [Scope](../../../formal/GaloisForLFunctions/ArithmeticCriticalityTheory/ShortProfilePoleFreeVariationInequality.lean).

### AIP — Arithmetic incidence allocation

**State.** Global joint allocation is the odd sign. AIP shares HF's atomic window, packet positivity, resolution theory, Haar results and prefix payment.

**A.** As HF; complete incidence matrices in conductor coordinates.

**B.** Signed allocation on source-complete cells **[RH]**; window positivity up to the critical curve **[open]**. [Allocation](../../../formal/GaloisForLFunctions/ArithmeticIncidencePositivity/GlobalIncidenceAllocationCondition.lean).

### ACS — Arithmetic effectivity and the census

**State.**

- Effectivity, Rosati and chirality receivers; HF's atomic and Haar results.
- Riemann–Roch for \(\mathbb G_m(\mathbb Q)\) is exact and linear; Adams multiplicity is Bézout-sharp [L].
- Census as in §12. Polar confinement is the lower count [L]. Elliptic, Hecke and loop foundations.

**A.**

- Slack calculus at \(\lambda\in[3/4,1)\); \(E_{\rm proj}\) on explicit near-line configurations.
- The affine \(A_1\) constant term over the genus-one base.
- HF's window tasks.

**B.**

- Full-source quadratic RI, a Rosati bound or complete-cell index zero **[RH]**.
- Uniform finite index **[FS]**.
- Census inputs beyond \(2/3\) **[open]**.
- A characteristic-zero surface whose sections count quadratically **[open]**.

[Effectivity](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/ExactArithmeticSourceEffectivity.lean).

## Part III — Route candidates

A candidate lacks an independent source construction or its landing. A promotion gap is **[open]**, and becomes **[RH]** once it is the final sign. Every landing must fail the battery:

- the Liouville twin, every flip \(\omega_p\), finite and cofinite flips, twin tails;
- \(\Lambda+\varepsilon n^{-\eta}\), and \(\Lambda+1/n\) for positivity statements;
- the golden datum on the lattice; over-regular Beurling systems; Haar-random gauge points.

**Rules (theorems).**

- No landing can be gauge-invariant, pointwise-closed or finitely determined.
- A landing that sees only single-horizon charges is depth-blind.
- Twins that share \(\zeta\)'s pole are resolved only at growing resolution.

| Candidate | Established | A — just work | B — promotion gap |
|---|---|---|---|
| **APF** paired Fredholm | Fredholm index; cycle-trace Fourier reconstruction. | Fixed cycles with truncation control. | Zero-independent divisor exhaustion and trace vanishing. [Source](../../../formal/GaloisForLFunctions/RHTower/PaperZetaCycleFourierReconstruction.lean) |
| **BSH** mate curvature | Framed curvature; finite cutoffs trace-blind. | Finite curvature identities. | A pre-divisor section forcing the mate identity. [Source](../../../formal/GaloisForLFunctions/RHTower/Deninger/DeningerOneSidedFramedMateCurvatureTransgression.lean) |
| **CDC** constitutive dagger | Calibrated confluence iff \(\operatorname{Re}s=1/2\). | Repair and exchange defects. | One arithmetic potential descending on all fibres. [Source](../../../formal/GaloisForLFunctions/RHTower/ConstitutiveDaggerConfluence.lean) |
| **DR** dyadic roots | Cusp roots, Kummer data, capped atlas. | Roots on known zero-free charts. | Compatible roots on the whole strict-right domain; global monodromy. [Source](../../../formal/GaloisForLFunctions/RHTower/XiSymmetricLittlewoodZeroFreeCuspDyadicRoots.lean) |
| **EGC** pole-safe contour | Complete copy correction; nonzero Gamma baseline. | Corrected contours. | Outer-contour orientation excluding off-line copies. [Source](../../../formal/GaloisForLFunctions/RHTower/PaperEGCSourceRayBaseline.lean) |
| **EWJ** Euler/Wold jets | Finite-depth jets; compact-quotient character. | Fixed jets. | Source admission and norm exhaustion across depth. [Source](../../../formal/GaloisForLFunctions/RHTower/PaperEulerWoldDepthHistory.lean) |
| **FEL** theta likelihood | Entropy bookkeeping; BSY zero sum. | Predeclared histories. | Cofinal balance from arithmetic, independent of zeros. [Source](../../../formal/GaloisForLFunctions/RHTower/BalazardSaiasYorZeroSum.lean) |
| **HJ** Hurwitz reflection | Residual = SEC charge; all-divisor vanishing = HCF two-grid sign. | Convergent fibres. | Pre-divisor forcing of residual vanishing. [Source](../../../formal/GaloisForLFunctions/RHTower/PrimeTailSeedHurwitzReflection.lean) |
| **IRK** rotation-algebra trace | Completed Xi-jet relation classified. | Finite jet inverses. | A charged arithmetic Poisson lift with integral count. [Source](../../../formal/GaloisForLFunctions/RHTower/PrimeRotationXiCompletedResolution.lean) |
| **MSC** Möbius–Sonin | Divisor multiplicity preserved; critical discrepancy in \(L^2\). | Evaluation jets. | Source-faithful nonnegative Sonin/Weil energy. [Source](../../../formal/GaloisForLFunctions/RHTower/SquarefreeDiscrepancyHilbertTransport.lean) |
| **PCS** prime co-shift | Shift-plus-defect; strong convergence with norm gap. | Retained defect and cutoff errors. | Wall annihilation keeping the forward mode. [Source](../../../formal/GaloisForLFunctions/RHTower/PCSChronologicalDilationCarrierObstruction.lean) |
| **PTR** photonic realization | Lossless products real-rooted; gapless realization law. | Finite stacks. | A prime-faithful nonlocal port without \(\Xi\) zeros. [Source](../../../formal/GaloisForLFunctions/RHTower/PhotonicLosslessProductPortRH.lean) |
| **RFHM** support grade | Full support/phase/grade admission. | Coherent defects. | A symmetry-breaking phase/depth wall law. [Source](../../../formal/GaloisForLFunctions/RHTower/PaperRFHMSurvivalInformation.lean) |
| **SC** Stokes/Witt–Krein | Rigged fibres; fine-tower exhaustion; height certificates; carriers; polar confinement = index zero; prefix index \(\le N-M\). | Finite cross-fibre coordinates. | A source-fixed cross-fibre index ceiling; unattained-depth detection. [Source](../../../formal/GaloisForLFunctions/RHTower/PaperKreinWallFourierCompletion.lean) |
| **SEC** adjacent seam | Essential norm = seam jump; Fock criteria. | Finite seam charges. | Eventual compactness or Fock boundedness at actual zeros. [Source](../../../formal/GaloisForLFunctions/RHTower/TimeOneGammaJetFockRHCriterion.lean) |
| **W1C** Lee–Yang | Finite Lee–Yang; Ising-limit receiver. | Finite couplings. | Source-defined centred couplings converging to Riemann's measure. [Source](../../../formal/GaloisForLFunctions/RHTower/IsingLawConvergenceRH.lean) |
| **WBF** certificates | Genealogy Gram and Fredholm recovery. | Certificate streams. | An arithmetic stream with uniform-depth landing. [Source](../../../formal/GaloisForLFunctions/HTGeometry/PaperCriticalGenealogyCompletion.lean) |
| **PW-B** PM cusp branch | Native two-response action; positive-damping admission. | Positive-damping actions. | Remove zero indexing; complete-energy ceiling to all-divisor extinction. [Source](../../../formal/GaloisForLFunctions/RHTower/ThetaCusp/ThetaCuspHawkingBMPWNativeTwoResponseAction.lean) |

## Part IV — Supporting programmes

| Programme | Contribution | Unresolved input |
|---|---|---|
| CACT, RAPT | Fixed-overlap positivity; growing-overlap packets; polynomial residuals; Gamma reserve; horizon law; resolution theory | Growing conductors and complement; the critical curve |
| CAF | Conductor log law, heat threshold, Green coordinates, prefix payment, terminal and probe costs, native theta tails, odd-four seam | Loss-free conductor uniformity; rank-eight compensation |
| TM, SSHA | Plateau and prefix Schur; zero-side stratum; second-order synthesis; Gevrey and Steklov receivers; Gamma reserves; pole-free twin breaking | Profile-adapted synthesis at the critical curve |
| AGT | Gauge exponent; coherence; antipode; twin inequality; special locus; shells (major arcs, short shells, level \(1/2\)); affine positivity; Adams operations; function-field calibration | A \(0\)-specific non-gauge-invariant inequality |
| AHA | Adams/torsion multiplicity cost \(2^{qr}\); Newton and Euler jets; vertical jets; two-prime log rigidity; successor rigidity | Controlled-height parity-selective auxiliaries; minimum-support rigidity |
| HKT, AKLT, EAHT | Index; global and parity laws; towers; heights; carriers; polar index; Bézout and Riemann–Roch for \(\mathbb G_m(\mathbb Q)\); small = divisible | Index ceiling; producer |
| ASRP | Precision classes; battery; Chebyshev ledger; complex lifts | Signed square-root control |
| AID, SAHT, ACS cells | Finite-index chain; Haar identities; even-power approximation | First prime layer [FS]; residual sign |
| ACP, SMAP | Finite-flip gap classification; source selection | Selector beyond summable twists |
| APD | Bost–Connes temperature = Hecke exponent; positive-duality rigidity | Source-compatible mixed positivity |
| Census, SCP | \(2/3\), \(0.8876\); dichotomy; exchange rates; projected credit | Two-sided coalescent estimate |
| RHTower density / Dirichlet | \(2/3\) horizon; dissipation; Guth–Maynard; DH; VK; Siegel; uniform Dirichlet zero-free region | Siegel–Walfisz; any vanishing mechanism |
| HLF, HTGeometry, AE | Hecke FE; genus-one base; loop group; Baker machinery | Uniform bounds; arithmetic quotient and constant term |

## External status

RH is unsolved ([Clay](https://www.claymath.org/millennium/Riemann-Hypothesis/)). External proofs are not validated here.

- **Alpöge–Furman two-thirds theorem.** A pinned formal dependency of the census.
- **Guth–Maynard, Vinogradov–Korobov, Siegel.** Formalized in the corpus.
- **Quasi-RH preprint.** Dirichlet zero-freeness for \(\operatorname{Re}s>7/8\) [E]; no corpus capstone.
- **Ordinary-correlation preprint.** Fixed-form Liouville two-point savings [E]; no power saving.
- **Context, none of which excludes zeros.** Rodgers–Tao \(\Lambda_{\rm dBN}\ge0\); Bourgain \(\mu(1/2)\le13/84\); Montgomery pair correlation for \(|\alpha|\le1\) under RH; Goldston–Montgomery; Bombieri–Vinogradov, Zhang, Maynard; Friedlander–Iwaniec parity breaking for \(x^2+y^4\); Bost–Connes; Zagier–Sarnak horocycle equidistribution (an RH equivalent not in the corpus).
