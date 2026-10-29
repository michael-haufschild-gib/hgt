# Research routes and their mathematical obstacles

Status: 29 October 2026, corpus HEAD `718f741cc7` plus working tree. **RH remains open.** The inventory is 32 live routes, 17 standalone candidates and the PW-B branch of PM; ISC-polar is retired to support. Every live route has an exact RH receiver, and none has the arithmetic input that receiver needs.

The frontier as of this checkpoint:

- **Selectivity has exactly two sources** [L]. The pole and Gamma terms do not move under vertical shifts. Gauge charge enters through non-ratio lags, that is, through additive structure. Every multiplicative statement is shared by the whole gauge orbit of \(\Lambda\), Liouville twin and prime flips included.
- **Bounded overlap has an exact certified range.** For one plateau the complete form is eventually positive for every fixed \(0<c<c_*\), with \(c_*>1+10^{-16}\); the matrix floor at \(1+10^{-16}\) is \(1/400\) [K]. The Liouville twin fails for \(c\ge1/2\), and \(\omega_{11}\) for \(c\ge99/100\). The boundary \(c_*\) optimizes the full Young-parameter family and exact reference floor at the existing analytic constants; it is not the actual spectral boundary.
- **Overlap growth means additive structure.** Above \(c=1\), successor shells \(n=km+j\), \(|j|\lesssim c\), enter the prime form. Every nonpolar reference energy falls like \(-\log c\). Atom-normalized floors fail. The RH receiver needs overlap \(L(\log L)^2\log\log L\), with \(L=\log\log N\) [S].

Companions: [summary, open problems, next questions](obstacles-summary.md) · [walls ledger](walls-ledger.md) · [route unification](route-unification-ledger.md) · [frontier map](../rh-current-frontier-map.md) · [scoped obstructions](../rh-killed-routes.md). Research record: [working log](../../../logs/review-2910c-research-2026-10-29.md).

## How to read this report

Evidence comes from corpus searches, Lean statements, module docstrings and proof structure. Entries marked [K] also have individual Lean checks and standard-only transitive-axiom audits; no umbrella build is implied.

**Evidence labels**

| Label | Meaning |
|---|---|
| **[L]** | Integrated source (frontier-map convention). |
| **[S]** | Working or unintegrated source (frontier-map convention). |
| **[K]** | Individually checked source (frontier-map convention). |
| **[Lean]** | A Lean statement read in this review, integration not assessed. |
| **[E]** | An external claim. |
| **(inference)** | A conclusion of this review, not a Lean theorem. |

**Obstacle classes.**

- **A, just work.** The ingredients exist: a finite computation with certified errors, an instantiation or composition of proved theorems, sharper constants in a proved scheme, transport of a supplied bound between proved dictionaries, formalization of a written proof, or integration of working source. An A-item never promises that a desired sign is true.
- **B, open mathematics.** A missing inequality, construction or uniformity. Each B-item carries one strength tag:

| Tag | Strength |
|---|---|
| **[RH]** | Equivalent to RH. |
| **[RH+]** | Strictly stronger than RH. |
| **[FS]** | Equivalent to finitely many off-line zeros, that is, RH above a height. It implies the Lindelöf hypothesis and a fixed zero-free strip. |
| **[LH]** | At least Lindelöf strength. |
| **[≥QRH]** | Implies a fixed strip \(\Theta<1\). |
| **[open]** | Intermediate; no known solution, possibly below RH. |

## Part I — The frontier in fifteen results

### 1. The two-source law of selectivity

- **Weil positivity is pointwise-closed, so its selectivity sits in the shift-fixed terms [L].** The logarithms of the primes are \(\mathbb Q\)-independent. By Kronecker, every unitary completely multiplicative twist is a pointwise limit of vertical shifts \(n\mapsto a(n)n^{i\tau}\); this covers the Liouville twin, every flip \(\omega_p\) and every cofinite flip. A pointwise-closed, shift-invariant statement can therefore never be selective. Weil positivity reads finitely many weights per test, so its selectivity lives in the terms that do not move with the weights: the pole and the Gamma factor. [Pointwise-closed statements](../../../formal/GaloisForLFunctions/ArithmeticKreinLangerTheory/PointwiseClosedStatementsAreTwinBlind.lean).
- **Diamagnetic inequality [Lean].** For \(|\omega|\le1\): \(\mathrm{arch}(f)-\mathrm{prime}_\omega(f)\ge\) the Markov form of \(\zeta\) at \(|f|\). On families closed under \(|\cdot|\), \(\zeta\) is the ground state of its gauge orbit. A margin in \(\zeta\)'s favour must come from the pole (the one anti-Markov term) or from families that are not \(|\cdot|\)-closed, such as overlapping atoms. [Diamagnetic](../../../formal/GaloisForLFunctions/SpacingScaleHarmonicAnalysis/TheDiamagneticInequality.lean).
- **The gauge enters only through non-ratio lags [Lean].** For a completely multiplicative sign gauge, twisted minus untwisted prime form is \(\sum_k\Lambda_k\sum_{m,n}(\omega(k)-\omega(m)\omega(n))x_mx_n(\dots)\). The factor vanishes on ratio lags \(n=km\). Non-ratio lags do not exist below the atom spacing and do exist from overlap of order one. [Non-ratio lags](../../../formal/GaloisForLFunctions/SpacingScaleHarmonicAnalysis/TheGaugeEntersThroughNonRatioLags.lean).
- **The gauge torus [L].** Twists \(\Lambda\chi_x\), \(x\in\widehat{\mathbb Q_{>0}^\times}\), form a probability space.
  - Haar-almost every twist has no pole and square-root partial sums.
  - The point \(x=0\) has the pole, and RH says that the pole is its only atypicality.
  - The exceptional set of the Möbius half-power law is comeager and null, and \(0\) lies in its closure.
  - Successor correlations, near-incidences \(ab-cd=h\) and the census coalescent surplus are pure gauge charge: mean zero over the orbit, square-root size almost surely.
  - Multiplicative data cannot certify their value at \(0\).

  [Typical except for the pole](../../../formal/GaloisForLFunctions/ArithmeticCorrelationGeometry/ThePrimeSourceIsTypicalExceptForItsPole.lean), [comeager and null](../../../formal/GaloisForLFunctions/ArithmeticCorrelationGeometry/TheMoebiusExceptionalSetIsComeagerAndNull.lean), [successor charge](../../../formal/GaloisForLFunctions/ArithmeticCorrelationGeometry/SuccessorCorrelationsArePureGaugeCharge.lean), [coalescent surplus](../../../formal/GaloisForLFunctions/ArithmeticCorrelationGeometry/TheCoalescentSurplusIsPureGaugeCharge.lean).
- **The main term of gauge charge is carried by finite gauge subgroups [Lean].** Averaging over Dirichlet characters mod \(q\) keeps a successor pair \((n,n+h)\) iff \(q\mid h\). The Hardy–Littlewood singular series is the average over these stabilizers; the discrepancy lives in the remaining gauge directions. [Finite gauge subgroups](../../../formal/GaloisForLFunctions/ArithmeticCorrelationGeometry/FiniteGaugeSubgroupsResolveWhatTheArchimedeanLineCannot.lean).

Consequence (inference): a selective input has two possible sources. One is the archimedean boundary (pole, Gamma), which carries only linear precision. The other is gauge charge at the single point \(0\), which is additive structure. Every RH-strength obstacle below is the second source at square-root precision.

### 2. Bounded overlap: the certified bound family has an exact boundary

- **Positivity [K].** For $\varphi_0=\mathrm{plateau}(1/1000)$ and scaled width $c=Nw$,
  the complete Weil matrix is eventually positive definite at every fixed $0<c<c_*$.
  The exact spacing ratio $w/\log(1+1/N)$ tends to $c$.
  The boundary satisfies $1+10^{-16}<c_*$, and the actual matrix has eventual floor
  $\|x\|^2/400$ at $c=1+10^{-16}$.
  [Optimized actual floor](../../../formal/GaloisForLFunctions/TransMetzlerWeilPositivity/TransMetzlerYoungOptimization.lean).
- **Exact reference floor [K].** Write $q_0=(\int\varphi_0)^2/\int\varphi_0^2$,
  $\alpha=cq_0$, $r=1-\alpha$, $\psi=\log4+4/e$,
  $s=\beta(\varphi_0)/\|\varphi_0\|_2^2-\log(2\pi c)$ and $f=s+\alpha$.
  When $\alpha<1$, every strict floor below $f$ eventually holds for the reference
  matrix; conductor one has limiting energy $f$, excluding any larger floor.
  [Reference floor](../../../formal/GaloisForLFunctions/TransMetzlerWeilPositivity/TransMetzlerReferenceFloor.lean).
- **Full parameter optimization [K].** Put $A=\alpha^2\psi$,
  $R=1276c^2+\alpha(\psi+15)-s$, and
  $d_*=(\sqrt A+\sqrt{A+r(R+f)})^2/r^2$. The certified floor is
  $L(c)=f-2000(c-1)(1+d_*)$.
  It is continuous and strictly decreasing on $1\le c<1/q_0$, with a unique zero
  $c_*\in(1,(1+1/q_0)/2)$. The complete matrices eventually have every strict
  floor below $L(c)$ for $1\le c\le c_*$.
  Scalar data satisfying every Young inequality attain the floor; after its reserve
  is spent the exact tail is $-R-e-A/(r-e)$, and for $e\ge r$ it is unbounded below.
  Thus a positive certificate from these bounds exists exactly when $c<c_*$.
  [Young optimization](../../../formal/GaloisForLFunctions/HTGeometry/OptimalYoungDefectFloor.lean),
  [actual boundary](../../../formal/GaloisForLFunctions/TransMetzlerWeilPositivity/TransMetzlerYoungOptimization.lean).

The older three fixed estimates give the smaller exact range
$\delta<1/107520002048050000$; their saturation does not preclude optimizing the
underlying reference floor and Young parameter. The constants 1276 and 2000 remain
fixed. Improving them or using further information can move the certified boundary.

- **Selectivity [S].** The Liouville twin has negative witnesses in two regimes: for every \(C^2\) profile at \(c>c_{\rm RE}(\varphi)\), and for \(\varphi_0\) at every \(c\ge1/2\). It is nonnegative at narrow ratios. The flip \(\omega_{11}\) has negative tests at every large horizon for every fixed \(c\ge99/100\), including \(c_0\) and \(c=2\). The negative test is a three-conductor prime-square trial (conductors \(1,11,121\)). The sign conjugacy changes only the prime matrix; Gamma and both poles are identical on both sides. [Twin](../../../formal/GaloisForLFunctions/TransMetzlerWeilPositivity/LiouvilleTwinSelectivity.lean), [eleven flip](../../../formal/GaloisForLFunctions/TransMetzlerWeilPositivity/BoundedOverlap/ElevenFlipAtEveryHorizon.lean).

Consequence (inference): on \([99/100,c_*)\) the complete form separates \(\zeta\) from the Liouville twin and from \(\omega_{11}\). Both separations go through the pole, as the two-source law predicts. Bounded overlap has not yet used gauge charge.

### 3. Overlap growth: successor shells, nonpolar losses, degenerate atoms

- **RH receiver [L/S].** One Steklov–Denjoy–Carleman profile gives RH iff eventual atomic positivity at \(c_N=L(\log L)^\beta\), \(L=\log\log N\), \(\beta>2\) [L]. The same holds at \(L(\log L)^2\log\log L\) [S]. For every \(\alpha>1\), the explicit families at width \((\log\log N)^\alpha/N\) have atomic indices converging to \(\kappa(K_\zeta)\in\mathbb N\cup\{\infty\}\) [L]. Compact Gevrey-\(\le1\) profiles vanish [S]. [Super-Gevrey](../../../formal/GaloisForLFunctions/TransMetzlerWeilPositivity/SuperGevreyCriticalGrowth.lean), [iterated log](../../../formal/GaloisForLFunctions/TransMetzlerWeilPositivity/TheFixedProfileReachesAnIteratedLogEndpoint.lean), [schedules reach the index](../../../formal/GaloisForLFunctions/EffectiveArithmeticHodgeTheory/TheExplicitSchedulesReachTheIndex.lean).
- **Successor shells [K/S].** A pair \(1\le a\le N\), \(b\ge a+k\) becomes eligible at overlap \(c_{N,k}=N\log(1+k/N)\to k\). A non-ratio lag \(\log k'\) within width \(c/N\) of \(\log(n/m)\) means \(|n-k'm|\lesssim c\). At overlap \(c\), the prime form therefore reads the additive shells \(n=k'm+j\), \(|j|\lesssim c\). At fixed \(c>1\) the plateau's \(n^{-1/2}\)-weighted successor fibre grows like a positive multiple of \(\log(N+1)\): all divisors of the product have the same lag, and their Mangoldt weights sum to \(\log(N+1)\) [K]. [Shell thresholds](../../../formal/GaloisForLFunctions/CriticalArithmeticCorrelationTheory/ExactHigherShellThresholds.lean), [divisor rows](../../../formal/GaloisForLFunctions/TransMetzlerWeilPositivity/FixedOverlapHasLogarithmicDivisorRows.lean).
- **Nonpolar losses [S].** The separated Ramanujan reference energy of a conductor \(m\ne1\) is \(E_m(1)-\log c\), which is negative for \(c>e^{E_m(1)}\). The actual diagonal keeps this loss while \(c/N\le1\). [Overlap forces new terms](../../../formal/GaloisForLFunctions/RenormalizedArithmeticPotentialTheory/OverlapForcesNewRamanujanTerms.lean).
- **Atom norms degenerate [S].** At \(c_N\to\infty\), the adjacent dipole has synthesized mass ratio \(1-C_\varphi(t_N)/C_\varphi(0)\to0\), so no atom-normalized floor exists. A Montgomery–Vaughan band bound survives for the bare Dirichlet polynomial: \(\int_N^{101N}|D_x|^2\ge48N\sum x_n^2\). [No uniform floor](../../../formal/GaloisForLFunctions/TransMetzlerWeilPositivity/GrowingOverlapHasNoUniformGramFloor.lean).
- **Exact Schur reduction [S].** The length-\(M\) prefix is the matrix at overlap \(cM/N\), which positivity through touching pays. Full positivity is then exactly \(D-B^*A^{-1}B\ge0\), with every prime, Gamma and polar entry retained. [Schur reduction](../../../formal/GaloisForLFunctions/TransMetzlerWeilPositivity/APositivePrefixGivesTheExactSchurReduction.lean).
- **Zero side [S].**
  - Under RH every ratio is positive.
  - Finite support bounds the atomic index by \(\#\)right zeros, uniformly in \(c\).
  - A tempered lattice-plus-one-pair model is negative at every \(c\) for every nonnegative \(C^2\) profile on \([0,1]\).

  [Zero-side stratum](../../../formal/GaloisForLFunctions/TransMetzlerWeilPositivity/ZeroSideStratum.lean).

Consequence (inference): under RH the matrix is positive at every \(c\). The \(-\log c\) loss of the nonpolar conductors must then be repaid by the terms absent at separation: archimedean overlaps, which are gauge-blind, and successor-shell prime lags, which are gauge-charged. Overlap growth is the entry of additive structure into the multiplicative form.

### 4. One coordinate: length over height

Overlap is \(X/T\) and bandwidth is \(\log X/\log T\). A fixed overlap above one still has bandwidth tending to one. The atomic transform is \(h_\varphi(z/T)D_x(z)\), a mollified Dirichlet polynomial of length \(N\); it has no hard Fourier cutoff. The census cutoff \((T/2\pi)^\lambda\) has overlap \((T/2\pi)^{\lambda-1}/2\pi\) [K]. [Coordinates](../../../formal/GaloisForLFunctions/SpacingScaleHarmonicAnalysis/OverlapCoordinates.lean), [transform](../../../formal/GaloisForLFunctions/SpacingScaleHarmonicAnalysis/TheNormalizedAtomicTransform.lean), [census coordinates](../../../formal/GaloisForLFunctions/RHTower/CensusLengthHeightCoordinates.lean).

| Statement | Overlap \(X/T\) | Status |
|---|---|---|
| Montgomery pair correlation | \(\to0\) (\(\lambda<1\)) | classical |
| Complete positivity | fixed \(c<c_*\), \(c_*>1+10^{-16}\) | proved |
| RH (atomic receiver) | \(L(\log L)^2\log\log L\) | RH-equivalent |
| \(70\%\) census | \(\asymp T^{1/9}\) (\(\lambda=10/9\)) | open |
| \(75\%\) census | \(\asymp T^{1/3}\) (\(\lambda=4/3\)) | open |

Consequence (inference): the atomic programme and the census meet at one crossing, length \(\approx\) height. There, mean values change from diagonal to off-diagonal dominance, and the prime side starts to read additive correlations. RH asks for a sign just past the crossing; the census asks for averaged information far past it.

### 5. Index theory of the Weil kernel (HKT, AKLT, EAHT)

| Law | Statement |
|---|---|
| Index [S] | \(\kappa(K_\zeta)=\#\)distinct right zeros; Gram matrices of the orbit kernel are prime-side Weil Grams. |
| Global law, parity form [S] | \(\kappa=0\iff\psi(x)-x\le C\sqrt x\log^2x\) eventually \(\iff\) the odd Liouville class has an upper count. [Parity form](../../../formal/GaloisForLFunctions/ArithmeticKreinLangerTheory/TheParityFormOfTheGlobalLaw.lean) |
| Heights [L] | \(\kappa_T=O(T\log T)\), \(\kappa=\sup_T\kappa_T\). The tower \(3^k/2^j\), \(k\le\lfloor T\log2/\pi\rfloor+1\), certifies \(\kappa_T\). At most \(\binom{\kappa_T}2\) primes alias. [Hasse with heights](../../../formal/GaloisForLFunctions/EffectiveArithmeticHodgeTheory/TheHassePrincipleWithHeights.lean) |
| Carriers [L] | Every box \(p^iq^j\), \(i,j<|S|\), carries the index of a finite zero spectrum \(S\). [Carriers](../../../formal/GaloisForLFunctions/EffectiveArithmeticHodgeTheory/IndexCarriersOfFiniteSpectra.lean) |
| Attained depth [L] | If \(\inf\operatorname{Re}\rho<\tfrac12\) is attained, only finitely many prime towers are positive. Hence RH iff infinitely many positive prime towers, under attainment. The unattained case is open. [Attained depth](../../../formal/GaloisForLFunctions/ArithmeticKreinLangerTheory/AttainedDepthIsSeenByAlmostEveryPrime.lean) |
| Finite stratum [K] | At most \(\binom\kappa2\) blind primes; one positive non-blind tower or infinitely many positive towers \(\iff\) RH. [Finite support](../../../formal/GaloisForLFunctions/ArithmeticKreinLangerTheory/FiniteSupportMakesAlmostEveryPrimeDecideZeta.lean) |
| Locality [L] | Unitary twists preserve tower faithfulness and the tower Hasse principle. Fine towers have unbounded Nyquist windows. [Locality](../../../formal/GaloisForLFunctions/ArithmeticKreinLangerTheory/LocalityIsTwinBlind.lean) |
| Parity twin [L] | Over \(\mathbb F_q\), the quadratic twist of base changes is a vertical shift. Over \(\mathbb Z\), a shift equals \(-1\) at no more than one prime. The Liouville twin is a limit of shifts on every finite prime set and equals none of them. [Bohr closure](../../../formal/GaloisForLFunctions/ArithmeticKreinLangerTheory/TheParityTwinIsGeometricOnlyInTheBohrClosure.lean) |
| Function-field ceiling [L/S] | Over \(\mathbb F_q[T]\), \(D-P_N\ge0\iff D\ge N\log q\) exactly, because the pole vector is an exact eigenvector. The second rung has window width \(\le(|Q|/(|Q|-1))\log|Q|\), which is \(2\log2\) at \(|Q|=2\). Over \(\mathbb Z\) the ceiling is \(\log N-\gamma\): Euler's constant is the archimedean defect of Mertens. [Ceiling](../../../formal/GaloisForLFunctions/ArithmeticKreinLangerTheory/TheFunctionFieldCeilingIsExact.lean) |
| Waves, stability, price [L/S] | Exceptional-wave number \(=\kappa\); collision mass \(=2(\kappa+\sum(m_\rho-1))\); index continuous off the discriminant; \(m\) negative squares cost \(\mathcal E_{\rm crit}\ge50m^2-3m/2\). |
| Compressions [S] | They never raise the index; Euler compressors are index-neutral; over \(\mathbb F_q\) the characteristic polynomial annihilates every trace kernel. |

### 6. Precision (ASRP)

- **The count's stabilizer is the square-root class [L/K].** Count\((a)\iff a-1\in\mathcal Q\), and \(\iff a-u\in\mathcal Q\) for every successor model \(u\). Over-regular Beurling systems share that class [K]. Every real torus gauge has a complex lift with the same count criterion [K]. [Successor class](../../../formal/GaloisForLFunctions/ArithmeticOfSquareRootPrecision/TheSuccessorEntersOnlyModuloTheSquareRootClass.lean).
- **Random signs satisfy the count [S].** Independent signs with arbitrary biases and \(|a_n|\le\log n\) have centered sums \(O(\sqrt x\log^2x)\) almost surely. [Independent signs](../../../formal/GaloisForLFunctions/HTGeometry/LogarithmicIndependentSigns.lean).
- **Deciding-input theorem [S].** Any property implying the count rejects the Liouville twin and rejects \(\Lambda+\varepsilon n^{-\eta}\). It is not finitely determined.
- **Tower positivity is precision-exact [S]**: its stabilizer is trivial.
- **Finite aperture cannot decide [K].** Aperture \(A\) reads only \(n\le e^{2A}\). If aperture positivity implied the count, RH would fail. Below \(\log2/2\) the test is weight-blind. [Finite aperture](../../../formal/GaloisForLFunctions/ArithmeticOfSquareRootPrecision/FiniteAperturePositivityCannotDecide.lean).
- **Chebyshev ledger [L].** \(|\psi(n)-n((\log n-1)m(n)-\ell(n))-I_n(h)|\le3(1+\tfrac12\log n)\max_{k\le n}|M(k)|\), with \(|I_n(h)|<n\). The count is a statement about the two Möbius moments, the sawtooth inversion and Mertens. [Smooth term](../../../formal/GaloisForLFunctions/ArithmeticOfSquareRootPrecision/TheSmoothTermInvertsToMobiusMoments.lean).
- **Two primes [S].** \(|e_p|\log q+|e_q|\log p\ge c\min(|\Delta|,(2+|\Delta|)^{-C})\) (Baker); one prime aliases.

### 7. Producers: one ledger over \(\mathbb F_q\) and \(\mathbb Z\)

- **The ledger [L].** An auxiliary vanishing to order \(m\) on the counted set has size at least \(m\) times the counted mass: \(\sum_x m_x\le\deg P\) over \(\mathbb F_q\), and \(\sum_pm_p\log p\le\log A\) over \(\mathbb Z\).
  - Stepanov reaches multiplicity \(\approx\sqrt q\) through \(x^q=x\) and bounds both Legendre classes by \(q/2+(\deg h+1)\sqrt q\). Over \(\mathbb F_q\) this gives index zero for split hyperelliptic kernels.
  - Binomials have multiplicity \(\le1\) above \(\sqrt N\), and their short-interval ledger is trivial, so the sieve parity rung is out of their reach.
  - Divisibility sees prime powers, not parity: \(0\le\log\mathrm{lcm}(O_x)-\theta(x)\le2\sqrt x\log x\) for the odd Liouville class \(O_x\).

  [Linear counts](../../../formal/GaloisForLFunctions/ArithmeticKreinLangerTheory/IntegralityProducesLinearCounts.lean), [Stepanov's order](../../../formal/GaloisForLFunctions/ArithmeticKreinLangerTheory/StepanovsOrderOverTheFiniteField.lean).
- **Sup-norm versus divisibility [L].** Sup-norm-certified integer polynomials are capped at \(\psi(x)\ge cx\), \(c\le-\log t_{\mathbb Z}\approx0.8644\) (classical). Chebyshev's factorial ratio gives \(c\ge0.89\). Divisibility producers are not capped this way, but they stay at linear precision. [Chebyshev cap](../../../formal/GaloisForLFunctions/ArithmeticKreinLangerTheory/ChebyshevsProducerPassesTheIntegerChebyshevCap.lean).
- **Integrality [S/K].** Integer-polynomial integrals form \(\mathrm{lcm}(1,\dots,N)^{-1}\mathbb Z\), and the integrality exponent is \(\Theta\). Fixed polynomial ideals preserve every integrality scale and criterion [K]. Sup-norm ceilings force vanishing at \(0,\tfrac12,1\) [L].

Consequence (inference): over \(\mathbb Z\), a producer must vanish on one parity class in a sense finer than divisibility, with multiplicity that grows as Stepanov's grows through Frobenius. No such mechanism is known.

### 8. The complete source: the finite-index chain ends at the first prime layer

Gamma pays every detail, and each Haar cell has energy \(\ge\) mass\(/10\) [L]. The full Haar identity \(W+G=D_X+P+\sum V_X(a)u_a^2\) holds with \(G\ge0\) and \(V_X\) signed [L]. Literal prime edges keep a Gamma reserve, and their full-Weil entries are negative [L]. Uniform finite index holds on every layer except \(k=1\) [L/S/K]. Prime–polar cancellation holds with an \(e^R\) loss [S]. Uniform finite index of the complete form is [FS].

### 9. Ordered entries are centered Chebyshev integrals

For \(\operatorname{supp}f<b<\operatorname{supp}g\): \(W(f,g)=-\int_0^\infty(e^h-\psi(e^h)-c)\,q'_{f,g}(h)\,dh-\Gamma_{\rm tail}(f,g)\). The Gamma boundary operator has norm \(\pi/2\) and no maximizer [S]. [Chebyshev identity](../../../formal/GaloisForLFunctions/ArithmeticIndexDescent/TheOrderedWeilSourceIsACenteredChebyshevDefect.lean).

### 10. The finite-support stratum is RH above a height

The following are equivalent [S]:

- finite index;
- finite index on a two-prime lattice;
- finitely many off-line zeros;
- bounded heat counts;
- every zero above some height is critical.

Finite support makes zeros approach the line, hence LH and \(\Theta<1\) [L]. Within the stratum, the atomic index is bounded by \(\#\)right zeros, and almost every prime decides [S/K].

### 11. Heat flow

For \(0<t\le1/8\), zeros of \(H_t\) beyond \(2\pi e^{(2/3+\varepsilon)/t}\) are real and simple [L]. Deep counts are \(\le C\log X\cdot N(t)\) [L]. The localized energy inequality \(E_w(b)-E_w(a)+2\int N_w\le C\log X\int E_{\rm outer}\) crosses collisions and \(t=0\) [K]. Open: outer-energy absorption, and a uniform count as \(t\downarrow0\). [Dissipation](../../../formal/GaloisForLFunctions/RHTower/Heat/HeatLocalizedEnergyDissipation.lean).

### 12. Critical-line census

| Statement | Value |
|---|---|
| Simple critical | \(\ge HD(1)+10^{-8}\approx0.67250071\) [L] |
| Simple or critical | \(\ge0.8876\) [L] |
| \(70\%\) dichotomy [K] | \(N_0\ge0.7N\), or at least \((HD(1)-\tfrac25-\tfrac1A-\varepsilon)N\) simple off-line zeros within \(A/\log T\). [Dichotomy](../../../formal/GaloisForLFunctions/RHTower/Zeta23SeventyPercentOrSimpleNearLine.lean) |
| Exchange rates [L] | \(E(1/9)\le4\Rightarrow70\%\); prime surplus \(\le N/18\) at \(\lambda=4/3\Rightarrow75\%\); \(3/4\iff\kappa\le5/4\) |
| Projected credit [K] | \(2(aL^2)^{-1}E_{\rm proj}\le2\operatorname{tr}Q_-\le\) zero-side slack, all cross-pair cancellation retained. [Projected credit](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/ProjectedDisplacementPaysNegativePartCredit.lean) |
| Model thresholds [K] | \(70\%\) needs \(\eta\ge1/18\), \(75\%\) needs \(\eta\ge1/6\) in the displaced-pair model. |

The coalescent surplus budget holds with \(\beta=0\) for Haar-almost every gauge twist. Its value at the primes is a property of the point \(0\).

### 13. Quasi-RH: translation complete, production absent

- **Dictionaries [L].** Every fixed strip has exact one-sided readings: escaped Möbius rates, Hecke-defect caps, theta prefixes, Vaughan savings, balanced short windows, the Chebyshev Cesàro energy and the integrality exponent.
- **Inputs [L].**
  - Guth–Maynard \(N(\sigma,T)\ll T^{(30/13)(1-\sigma)+\varepsilon}\) on \([1/2,5/6]\);
  - DH on \(\sigma\ge5/6\);
  - primes in \((x,x+x^{17/30+\varepsilon}]\);
  - Vinogradov–Korobov.

  A density envelope never drops below \(1\).
- **External [E].** The quasi-RH preprint claims Dirichlet zero-freeness for \(\operatorname{Re}s>7/8\) by a cubic-theta continuation argument. The corpus `ChenGuptaLi*` modules formalize density and detector components from the Chen–Gupta–Li zero-density paper; that paper does not claim the strip. No zero-free capstone exists.

### 14. Infinite symmetry is settled

For every curve datum with zeros in the strip, every zero is a pole of exact multiplicity of the complete affine \(A_1\) Weyl sum. Confinement of the polar divisor is equivalent to the lower square-root point count [L]. The closed chamber certifies only \(\operatorname{Re}\rho\ge1\) [K]. The golden datum has the same calculus and an off-line pole. ISC-polar is retired to support. [Confinement](../../../formal/GaloisForLFunctions/RHTower/InfiniteSymmetry/ConfinementIsTheSquareRootCount.lean).

### 15. Foundations (number fields, curves, loop groups)

- Hecke: global continuation and \(\operatorname{Re}s=1\) nonvanishing [L]. The completed functional equation for finite-primitive finite-order characters holds, with removable values [K].
- Genus-one base \(y^2=x^3-x\) over \(\mathbb F_3\): adeles, Haar, ideal norms, local integrals, pole semigroup [K].
- Real loop group: Bruhat, Iwasawa, \(K\cap B=M\), spherical function [K].
- These are tools; none carries a selective sign.

## Part II — Live routes

Each entry gives the state, then **A** (just work) and **B** (open, tagged).

### WL — Weil lag / prime-error energy

**State.** Bounded critical-deficit energy, coprime cross-work and a linear prime-error budget are each RH-equivalent. Either one-sided \(\sqrt x\log^2x\) count is RH, equals \(\kappa(K_\zeta)=0\), and is already the odd-class upper count [S]. The Chebyshev ledger reduces \(\psi\) to two Möbius moments, the sawtooth and Mertens [L]. The prime error is the separated off-diagonal of the complete form (§9). Genus saturation is RH plus simple zeros.

**A.** Certified truncations with high-zero tails; tabulate \(d\mapsto W(f,T_{d\log2}g)\); compute \(I_n(F)\), \(I_n(h)\) and their cancellation on certified ranges; formalize the product-bias classification, which has a paper proof [P].

**B.**

- The one-sided count, or the odd-class upper count **[RH]**.
- Joint square-root control of the moments, sawtooth and Mertens remainder **[RH]**.
- Subtracted lag **[FS]**.
- Genus saturation **[RH+]**.

[Receiver](../../../formal/GaloisForLFunctions/BiScaleUncertainty/WeilLagCriticalDeficitEndpointAndLimitLaw.lean).

### RW — Restricted Weil ground energy

**State.** RH iff the ground minimum is positive at every finite aperture. The minimum strictly decreases, and positive floors must decay doubly exponentially. Finite-aperture Gårding allows a nonzero index. The Gamma boundary norm is \(\pi/2\) with no uniform relative reserve [S].

**A.** Certified finite-aperture variational bounds and shell ledgers.

**B.** Cumulative aperture relaxation bounded by the initial energy, paying low modes, collars and polar terms **[RH]**. [Aperture flow](../../../formal/GaloisForLFunctions/ArithmeticContinuationAndCriticalEnergy/TheApertureFlowNeverStalls.lean).

### FU — Signed prime scheduling

**State.** An eventual upper bound on the normalized completed Abel moment is RH-equivalent. Narrow prime channels have a useful sign [L]; wide channels can be positive [S].

**A.** Seed, drift, history, cross-block and endpoint ledgers for fixed schedules.

**B.** A joint signed total over a prime-exhaustive schedule **[RH]**. [Receiver](../../../formal/GaloisForLFunctions/RHTower/CCM/CCMFUSuzukiMobiusDivisorOneSided.lean).

### CFC — CCM first-clock lower bound

**State.** RH iff the literal published first-clock source sine coefficient is bounded below on an aperture tail. Under ¬RH it is unbounded below on every tail. Phase-natural transport is the identity. Arbitrary completed Markov orientation exists universally iff RH.

**A.** Certified evaluations of the coefficient on finite aperture ranges, with prime, archimedean and endpoint terms apart.

**B.** The tail lower bound itself **[RH]**; transport feasibility restates it. [Completeness](../../../formal/GaloisForLFunctions/RHTower/CCM/CCMFirstClockTailLowerBoundCompleteness.lean).

### RP — Matched-quantile history floor

**State.** RH iff an eventual floor \(-B(K+2)\) holds. Unconditionally the history drops below \(-\delta(K+2)\) cofinally, so no sublinear floor exists [L].

**A.** Fixed histories; low-LCM instantiation; the escape constant \(\delta\) on computed ranges.

**B.** A linear floor paying high-LCM pairs, the moving core and transport together **[RH]**. [Floor](../../../formal/GaloisForLFunctions/RHTower/SPEQuantileRieszRoutePLinearFloorCriterion.lean).

### PA — Prime–archimedean passivity

**State.** Current-sign, Bernstein-mismatch and signed compact-moment receivers. Each fixed Hausdorff order is positive after a large shift.

**A.** The first-atom analytic tail; explicit thresholds for finite order blocks.

**B.** An all-order, all-shift sign; high-frequency accretivity; or an every-rate mismatch bound **[RH]**. [Moments](../../../formal/GaloisForLFunctions/RHTower/PrimeArchThetaFirstAtomHighOrderMomentBounds.lean).

### MC — Möbius cancellation

**State.** Every strict half-power bound and subpower Hilbert energy is RH-equivalent. Fixed strips have complete dictionaries. \(M=o(\sqrt x)\) is false; a linear Mertens budget is RH plus simple zeros. The battery is formal (§6). The exceptional set of the half-power law is comeager and null, and a.e. twist satisfies it (§1). Pointwise-closed weight classes containing all shifts contain every flip [L].

**A.** Fixed-modulus estimates; rate normalizations; transport of any supplied strip bound.

**B.**

- Every strict half-power, or the odd-class upper count **[RH]**.
- The linear Mertens budget **[RH+]**.
- Any fixed one-sided power saving **[≥QRH]**.

[Hilbert criterion](../../../formal/GaloisForLFunctions/RHTower/MobiusHilbertFormEquivalence.lean).

### TT — Theta tails and directed covariance

**State.** Seam, Wold and odd-Weil receivers; sharp \(t<1/2\) threshold; restricted current and light-cone signs.

**A.** Fixed directed-covariance and reflected-prime terms.

**B.** Signed nonlocal covariance at every scale, or complete odd positivity **[RH]**. [Wold receiver](../../../formal/GaloisForLFunctions/RHTower/PaperWoldDirectedCovarianceRH.lean).

### LA — Line anchor / Jensen and heat signs

**State.**

- Finite-head and heat receivers.
- Ordinary \(\xi\) coefficients are Turán [L] and Lorentzian [S].
- Local cofactor \(\deg P=O(\log T)\).
- Reality horizon \(2\pi e^{(2/3+\varepsilon)/t}\) [L]; localized dissipation [K].

**A.** Certified heads and low degrees; heat-tail errors with the local cofactor.

**B.** All-height, all-degree head signs, near-double pairs included **[RH]**; a uniform heat count **[FS]**. [Finite-head reduction](../../../formal/GaloisForLFunctions/RHTower/XiSliceHeatFiniteHeadReduction.lean).

### TG — Integer trace below one

**State.** Winding, cubic-transgression and central-gap receivers; Gaussian coprime-divisibility covariance.

**A.** Finite projection and transgression data with residual and trace apart.

**B.** A matrix-complete decomposition with nonnegative residual and trace below one on every disc **[RH]**. [Index estimate](../../../formal/GaloisForLFunctions/RHTower/RestrictedProjectionIndexOperatorNormCriterion.lean).

### HF — Arithmetic Hodge positivity

**State.**

- Hodge sign, zero Hecke defect and small source work are exact receivers.
- Complete positivity on atomic families holds for \(0<c<c_*\), \(c_*>1+10^{-16}\), and is selective against the Liouville twin and \(\omega_{11}\) (§2). The optimized Young family is exact at \(c_*\) for its constants, and its method ends at pole charge one.
- Growing overlap brings successor shells and nonpolar \(-\log c\) losses; atom norms degenerate; the Schur reduction is exact (§3).
- The complete source carries a multiresolution and the Haar identity, with finite index on every layer except \(k=1\) (§8).
- Cyclotomic Gram completion, exact Dirichlet–Schur cost and actual prime-prefix domination hold for fixed conductors and windows [K/S].

**A.**

- Sharper operator-level constants for the optimized Young family (the coefficients \(2000\) and \(1276c^2\), the plateau estimates), moving \(c_*\) toward the charge barrier \(c<1/q_0\).
- Numerical spectra of the complete matrix at fixed \(c\in(1,3]\) in conductor coordinates.
- Exact first-shell calculus (§3).
- The Schur complement on computed ranges.
- Head sizes and first-layer constants.

**B.**

- Positivity at the RH overlap, complete-cell index zero, residual sign, or work ceiling **[RH]**.
- Uniform finite index, or finite \(\mathcal E_{\rm crit}\) **[FS]**.
- Positivity at every fixed \(c\ge c_*\) and its uniformity in \(c\); what repays \(-\log c\) on nonpolar conductors; a synthesized-mass floor **[open]**.

[Trans-Metzler](../../../formal/GaloisForLFunctions/TransMetzlerWeilPositivity/TransMetzlerPositivity.lean), [index capture](../../../formal/GaloisForLFunctions/ArithmeticIndexDescent/TheCompleteCellsCaptureEveryFiniteIndex.lean).

### CHMD — Causal hyperbolic–modular duality

**State.**

- Wave and Doob receivers; completed aperture core; residual radical = Weil radical.
- Ordered entries are Chebyshev integrals.
- Actual generator heads have uniform Gamma bounds, and the complete even-power error is \(\le\delta\Gamma(f)\) [K].
- Literal prime edges keep a fraction \(1-\log2/\log3\) of divisor energy [L].

**A.** Domain and cutoff theorems on fixed sources; signed residual with the primitive defect.

**B.** The complete one-sided wave bound or the odd Doob inequality, paying first-prime, coarse and polar terms **[RH]**. [Odd criterion](../../../formal/GaloisForLFunctions/RHTower/CHMDOddSectorCriterion.lean).

### TH — Theta moment positivity

**State.**

- Signed center-mixed hierarchy: rank seven is strictly positive for every \(0<a<1/2\); the all-rank sign is RH.
- Arbitrary three-node Grams are positive; six-node clusters are strictly positive.
- Heated orthant signs hold at all ranks.

**A.** The native successor integral at rank eight on computed parameter ranges; finite signed blocks.

**B.** The successor-integral sign at every rank, or signed heated coefficients at one common time **[RH]**. [Orthant theorem](../../../formal/GaloisForLFunctions/RHTower/XiHeatHankelFormOrthantPositivity.lean).

### RN — Renewal and singular comparison

**State.** Theta renewal solvers; compact cone-positive renewal operator with an exact regularized determinant.

**A.** Finite packet and resolvent data with cusp and seam terms.

**B.** Directed mixed prime+Gamma \(\ge\) pole **[RH]**; cone positivity does not give real spectrum. [Spectrum](../../../formal/GaloisForLFunctions/RHTower/ThetaRenewalFredholmSpectrum.lean).

### WD — Ward caps and collision

**State.**

- A nonnegative integrated cap vanishes iff RH; shallow Cauchy energy is \(O(N)\) [L].
- Collision mass \(\to\infty\) iff tower indices are unbounded [L]; on finite index it is \(2(\kappa+\)excess\()\) [L].
- Localized dissipation crosses collisions and \(t=0\) [K].

**A.** Explicit \(N(t)\) on compact time ranges; sum localized estimates on fixed height windows.

**B.** Cap extinction **[RH]**; a uniform nonreal count **[FS]**; a uniform high count **[LH]**. [Ward receiver](../../../formal/GaloisForLFunctions/RHTower/XiWardGlobalCapAndFiniteHeadArithmetic.lean).

### LI — Paired Li balances

**State.**

- Actual theta clock with an exact outside/near budget.
- The guarded history-zero set is finite unconditionally, and RH iff it is empty.
- RH iff the Cayley–Li ladder is primitive nonpositive; its couplings do not decay [S].

**A.** Fixed paired histories; finite Cayley ladders.

**B.** Payment at every possible guarded zero, a subexponential history floor, or the ladder sign **[RH]**. [Cayley ladder](../../../formal/GaloisForLFunctions/ArithmeticLorentzianGeometry/RHIsReflectionPositivityOfTheCayleyLadder.lean).

### SZ — Suzuki first variation

**State.**

- The Ward-defect lower-bound receiver.
- Compact-\(L^2\) first variation equals the full Weil form.
- RH iff nonnegativity on factorial and grid tent families [S].
- Bare-source \(\ell^2\), uniform causal recovery and positive unital finite parts are excluded [L].

**A.** Moving-aperture limits on specified tent families.

**B.** The tent-family sign, especially low and mixed modes **[RH]**. [Transfer](../../../formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiCriticalRHCompleteFamilyTransfer.lean).

### PM — Haar approximation / damped admission

**State.** Global Haar approximation, cofinal signed-damping admission and positive gauge mass of every escape state are exact receivers. Escape states are spectral measures on the gauge torus. Power-growth escape, the signature of an off-line zero, has zero gauge mass [L].

**A.** Fixed cofactor Grams; effective pole orders.

**B.** Positive gauge mass for every escape state **[RH]**; exterior tightness **[open]**. [Visibility](../../../formal/GaloisForLFunctions/ArithmeticCorrelationGeometry/RHIsTheVisibilityOfEveryEscapeState.lean).

### JAS — Joint ancestry

**State.** Level-one prime-product positivity and square-shell bounds are receivers. Unconditional signs reach a logarithmic prime budget.

**A.** Budget gaps on chosen shells.

**B.** The half-power budget **[RH]**. [Capstones](../../../formal/GaloisForLFunctions/RHTower/JointAncestryLevelOneCapstones.lean).

### CTF — Báez–Duarte approximation

**State.**

- Residual \(=(1-\Lambda\)-readout\()^2+\) centered pronic energy; literal \(-\mu\) aligns the readout.
- The divisor covariance has exact cyclotomic coercivity [S].
- The dual Dirichlet bound gives a lower estimate, not vanishing.

**A.** Optimized finite rows with both components reported.

**B.** Complete error \(\to0\) with the infinite tail **[RH]**. [Readout](../../../formal/GaloisForLFunctions/BezoutValuationIncidence/VonMangoldtReadoutFormOfTheBaezDuarteCriterion.lean).

### HCF — Gaussian heat trace and two grids

**State.** Exact arch-minus-prime traces. Positivity on both \(\log2/\log3\) grids is RH-equivalent, and one grid aliases. Two-prime phase separation is polynomial [S].

**A.** Finite degrees and heights on both grids.

**B.** Both grid signs at all degrees **[RH]**; a many-node Gram floor from phase separation **[open]**. [Two grids](../../../formal/GaloisForLFunctions/RHTower/XiGaussianHeatTwoPrimeSourceSampling.lean).

### XN — Newton invariant discs

**State.** Line-centred self-map discs covering all zeros give RH; exact curvature of the interior margin.

**A.** Certified discs.

**B.** A covering family with nonnegative margin **[RH]**. [Criterion](../../../formal/GaloisForLFunctions/RHTower/XiNewtonSchwarzPickCriticalLine.lean).

### BAG — Deterministic self-return

**State.** Strong recurrence of \(\zeta\) through the right strip is an RH receiver. Its Bohr hull in \(\operatorname{Re}s>\tfrac12\) is the gauge orbit of §1 (inference). Finite-head returns keep target-zero exceptions.

**A.** Finite-head returns on zero-free targets.

**B.** Recurrence at every right-strip point **[RH]**. [Receiver](../../../formal/GaloisForLFunctions/RHTower/ZetaStrongRecurrenceReceiver.lean).

### EWU — Even pole-weight uniqueness

**State.** Attained even blind minima. RH iff, for every aperture, some real weights make \(\zeta\)'s full functional nonnegative up to that aperture [L]; the dual certificate is \(\Lambda\) itself.

**A.** Certified finite blind problems.

**B.** Nonnegative blind minima at every aperture **[RH]**. [Existence](../../../formal/GaloisForLFunctions/RHTower/WeilPositivityFiniteLevelExistenceDecidesRH.lean).

### GTA — Transverse Schur charge

**State.** Rank-uniform decay of the quartic Schur charge is RH-equivalent.

**A.** Finite-rank charges.

**B.** Rank-uniform decay **[RH]**. [Equivalence](../../../formal/GaloisForLFunctions/RHTower/Hedenmalm/HedenmalmThetaSchurQuarticSpectralDecayEquivalence.lean).

### OWU — Odd Weil-weight uniqueness

**State.** Odd and dilation-ray criteria. Smooth odd witnesses separate \(\Lambda\) from the Liouville twin and the first-prime flip at radii \(181/500\) and \(23/40\). These are finite-aperture separations, so they cannot decide (§6).

**A.** Collar accounting with both pole corrections.

**B.** The all-aperture odd sign **[RH]**; conductor/forcing compatibility **[open]**. [Dilation criterion](../../../formal/GaloisForLFunctions/RHTower/WeilDilationRayCriterion.lean).

### PBM — Pole-regularized prime series

**State.** Convergence of the pole-subtracted series at every \(\sigma>\tfrac12\) is RH-equivalent.

**A.** Partial sums in controlled half-planes.

**B.** Critical-abscissa cancellation **[RH]**; a fixed abscissa \(<1\) **[≥QRH]**. [Criterion](../../../formal/GaloisForLFunctions/RHTower/RegularizedLogZetaAbscissa.lean).

### RB — Robin / Nicolas extremizers

**State.** Eventual criteria; reduction to colossally abundant integers; large counterexamples need growing prime cores.

**A.** Certified finite extremal ranges.

**B.** The square-root remainder on prime-saturated extremizers **[RH]**. [Reduction](../../../formal/GaloisForLFunctions/RHTower/RobinColossallyAbundantReduction.lean).

### SRT — Lag localization and atomic visibility

**State.**

- Every-width lag receivers.
- Atomic RH receivers at \(L(\log L)^\beta\), \(\beta>2\) [L] and \(L(\log L)^2\log\log L\) [S]; explicit schedules reach the index [L].
- Complete positivity for \(c<c_*\) [K]; Liouville and \(\omega_{11}\) witnesses [S].
- Integer atoms and fine two-prime towers carry the index; tower positivity is precision-exact.

**A.** Full-index exhaustion at the Steklov schedule; remove the \(\log\log L\) factor with weaker Denjoy–Carleman weights; flips \(\omega_p\) for other \(p\).

**B.**

- Late lag, all-generator tower sign, or the RH-overlap sign **[RH]**.
- Uniform positivity up to the RH overlap, or bounded-overlap completeness **[open]**.

[Lag receiver](../../../formal/GaloisForLFunctions/SquareRootThreshold/EveryWidthDecidesTheCriticalLine.lean).

### ACT — One-shift arithmetic criticality

**State.** One fixed theta shift with an all-profile variation inequality gives odd positivity and RH. Short collars are absorbed only with support-dependent shifts.

**A.** Signed moment ledgers for prescribed profiles.

**B.** One shift for every support and profile **[RH]**. [Scope](../../../formal/GaloisForLFunctions/ArithmeticCriticalityTheory/ShortProfilePoleFreeVariationInequality.lean).

### AIP — Arithmetic incidence allocation

**State.** Global joint allocation is the odd sign. The route shares HF's atomic, complete-cell, Haar and Schur results, and the \(\omega_{11}\) rejection.

**A.** Complete incidence matrices in conductor coordinates; first-shell incidence calculus.

**B.** Signed allocation on source-complete cells **[RH]**; overlap growth **[open]**. [Allocation](../../../formal/GaloisForLFunctions/ArithmeticIncidencePositivity/GlobalIncidenceAllocationCondition.lean).

### ACS — Arithmetic effectivity and the census

**State.**

- Effectivity, Rosati and chirality receivers; complete-cell realization; HF's atomic and Haar results.
- The census module: exchange rates, capacity, slack, the \(70\%\) dichotomy and projected credit (§12).
- Elliptic base, Hecke completion and loop foundations (§15).
- Polar confinement is the lower count (§14).

**A.**

- Slack calculus at \(\lambda\in[3/4,1)\).
- \(E_{\rm proj}\) on explicit near-line configurations.
- The constant term of the affine \(A_1\) series over the genus-one base.

**B.**

- Full-source RI, a Rosati bound, or complete-cell index zero **[RH]**.
- Uniform finite index **[FS]**.
- A census input beyond \(2/3\) (\(E(1/9)\le4\), surplus \(\le N/18\), or a positive lower bound for \(E_{\rm proj}\)) **[open]**.

[Effectivity](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/ExactArithmeticSourceEffectivity.lean).

## Part III — Route candidates

A candidate lacks an independent source construction or its landing. Every promotion gap is **[open]** and becomes **[RH]** once it is the final sign. A landing must fail the battery:

- the Liouville twin;
- \(\omega_{11}\) and the other flips;
- cofinite flips;
- \(\Lambda+\varepsilon n^{-\eta}\);
- \(\Lambda+1/n\), for positivity statements;
- the golden curve on the lattice;
- over-regular Beurling systems;
- Haar-random gauge points.

Pointwise-closed shift-invariant statements are twin-blind, so no landing can be local or multiplicative-only.

| Candidate | Established | A — just work | B — promotion gap |
|---|---|---|---|
| **APF** paired Fredholm | Cycle traces have arithmetic Fourier reconstruction. | Fixed cycles with truncation control. | Zero-independent divisor exhaustion and trace vanishing. [Source](../../../formal/GaloisForLFunctions/RHTower/PaperZetaCycleFourierReconstruction.lean) |
| **BSH** mate curvature | Framed curvature vanishes at critical half-density; finite cutoffs are trace-blind. | Finite curvature identities. | A pre-divisor section forcing the vanishing. [Source](../../../formal/GaloisForLFunctions/RHTower/Deninger/DeningerOneSidedFramedMateCurvatureTransgression.lean) |
| **CDC** constitutive dagger | Calibrated confluence iff \(\operatorname{Re}s=\tfrac12\). | Finite repair and exchange defects. | One arithmetic potential descending on every fibre. [Source](../../../formal/GaloisForLFunctions/RHTower/ConstitutiveDaggerConfluence.lean) |
| **DR** dyadic roots | Roots reach the Littlewood zero-free cusp. | Roots on known zero-free charts. | Compatible roots on the whole strict-right domain; global monodromy. [Source](../../../formal/GaloisForLFunctions/RHTower/XiSymmetricLittlewoodZeroFreeCuspDyadicRoots.lean) |
| **EGC** pole-safe contour | Complete copy correction; nonzero Gamma baseline. | Corrected contours. | Outer-contour orientation excluding off-line copies. [Source](../../../formal/GaloisForLFunctions/RHTower/PaperEGCSourceRayBaseline.lean) |
| **EWJ** Euler/Wold jets | Three-channel histories converge. | Fixed jets. | Source admission and norm exhaustion across depth. [Source](../../../formal/GaloisForLFunctions/RHTower/PaperEulerWoldDepthHistory.lean) |
| **FEL** theta likelihood | Entropy bookkeeping; convergent BSY zero sum. | Predeclared histories. | Cofinal balance from arithmetic, independent of zeros. [Source](../../../formal/GaloisForLFunctions/RHTower/BalazardSaiasYorZeroSum.lean) |
| **HJ** Hurwitz reflection | Residual = SEC charge; all-divisor vanishing = HCF two-grid sign. | Convergent fibres. | Pre-divisor forcing of residual vanishing. [Source](../../../formal/GaloisForLFunctions/RHTower/PrimeTailSeedHurwitzReflection.lean) |
| **IRK** rotation-algebra trace | Completed Xi-jet relation invertible exactly off the line. | Finite jet inverses. | A charged arithmetic Poisson lift with integral count. [Source](../../../formal/GaloisForLFunctions/RHTower/PrimeRotationXiCompletedResolution.lean) |
| **MSC** Möbius–Sonin | Squarefree source recovers moments; divisor multiplicity preserved. | Evaluation jets. | Source-faithful nonnegative Sonin/Weil energy. [Source](../../../formal/GaloisForLFunctions/RHTower/SquarefreeDiscrepancyHilbertTransport.lean) |
| **PCS** prime co-shift | Shift-plus-defect; strong finite-prime convergence with norm gap. | Retained defect and cutoff errors. | Wall annihilation keeping the forward mode. [Source](../../../formal/GaloisForLFunctions/RHTower/PCSChronologicalDilationCarrierObstruction.lean) |
| **PTR** photonic realization | Lossless products real-rooted; gapless realization law. | Finite stacks. | Prime-faithful nonlocal port without Xi zeros. [Source](../../../formal/GaloisForLFunctions/RHTower/PhotonicLosslessProductPortRH.lean) |
| **RFHM** support grade | Full support/phase/grade admission; cutoff exhaustion. | Coherent defects. | A symmetry-breaking phase/depth wall law. [Source](../../../formal/GaloisForLFunctions/RHTower/PaperRFHMSurvivalInformation.lean) |
| **SC** Stokes/Witt–Krein | Rigged chambers; fine-tower exhaustion; height certificates; carriers. | Finite cross-fibre coordinates. | A source-fixed cross-fibre index ceiling; detection at unattained depth. [Source](../../../formal/GaloisForLFunctions/RHTower/PaperKreinWallFourierCompletion.lean) |
| **SEC** adjacent seam | Essential norm = seam jump; Fock criteria. | Finite seam charges. | Eventual compactness at actual zeros. [Source](../../../formal/GaloisForLFunctions/RHTower/TimeOneGammaJetFockRHCriterion.lean) |
| **W1C** Lee–Yang | Ferromagnetic Ising limits to Riemann's law force RH. | Finite couplings. | Source-defined centred couplings; Bohr-torus lift. [Source](../../../formal/GaloisForLFunctions/RHTower/IsingLawConvergenceRH.lean) |
| **WBF** certificates | Abstract genealogy Gram and Fredholm recovery. | Certificate streams. | An arithmetic stream with uniform-depth landing. [Source](../../../formal/GaloisForLFunctions/HTGeometry/PaperCriticalGenealogyCompletion.lean) |
| **PW-B** PM cusp branch | Native two-response action with cutoff-independent limit. | Positive-damping actions. | Remove zero indexing; ceiling-to-extinction chain. [Source](../../../formal/GaloisForLFunctions/RHTower/ThetaCusp/ThetaCuspHawkingBMPWNativeTwoResponseAction.lean) |

## Part IV — Supporting programmes

| Programme | Contribution | Unresolved input |
|---|---|---|
| TM | Positivity for \(c<c_*\); exact Young-family boundary; reference floor to the charge barrier; Liouville and \(\omega_{11}\) witnesses; RH receivers; Schur reduction; zero side | Positivity across the first successor shell; nonpolar repayment; synthesized-mass floor |
| HKT, AKLT, EAHT | Index; global and parity laws; heights and carriers; attained depth; locality; Bohr-closure twin; function-field ceiling; producer ledger | An index ceiling from structure; a producer finer than divisibility |
| ASRP | Precision classes; deciding input; finite aperture; random signs; Chebyshev ledger; integrality | Signed square-root control of moments, sawtooth and Mertens |
| ACG (gauge torus) | Typicality except for the pole; comeager-null exceptional set; gauge charge; finite gauge subgroups | Gauge charge at the point \(0\) |
| SSHA | Diamagnetic inequality; non-ratio lags; coordinates; unbounded overlap = RH | Positivity through gauge charge |
| SMAP, ACP | Selection; margin; flip classification | A selector beyond finite flips |
| AID, SAHT, ACS cells | Finite-index chain; Chebyshev identity; Haar identities | \(k=1\) layer [FS]; residual sign |
| RAPT, CACT, CAF | Ramanujan spectra; touching positivity; cyclotomic Gram; Dirichlet–Schur cost; prime-prefix domination | Growing conductors; overlap-uniform comparison |
| Census | \(2/3\), \(HD(1)\), \(0.8876\); exchange rates; dichotomy; projected credit | A two-sided coalescent estimate; a positive \(E_{\rm proj}\) bound |
| RHTower heat/density | \(2/3\) horizon; dissipation; Guth–Maynard; DH \(\sigma\ge5/6\); VK | Uniform count; any vanishing mechanism |
| HLF, HTGeometry, AET | Hecke FE; genus-one base; loop group; affine Weyl poles | Uniform bounds; arithmetic quotient and constant term |

## External mathematical status

RH is unsolved ([Clay](https://www.claymath.org/millennium/Riemann-Hypothesis/)). External proofs are not validated by this review.

- **Alpöge–Furman two-thirds theorem.** An external formalized package; the census builds on it.
- **Guth–Maynard.** Formalized unconditionally in the corpus.
- **Quasi-RH preprint** (September 2026). Claims Dirichlet zero-freeness for \(\operatorname{Re}s>7/8\) by a cubic-theta continuation [E]. The corpus has density and detector components, not this argument.
- **Ordinary-correlation preprint.** Fixed-form Liouville two-point savings \(X/(\log X)^c\) [E]; no power saving.
- **Context.**
  - Rodgers–Tao: \(\Lambda_{\rm dBN}\ge0\).
  - Bourgain: \(\mu(1/2)\le13/84\).
  - DH for \(\sigma\ge25/32\).
  - Montgomery's pair correlation on \(|\alpha|\le1\) under RH.
  - Bombieri–Vinogradov, Zhang and Maynard (level of distribution).
  - Friedlander–Iwaniec: parity broken for \(x^2+y^4\).
  - Soundararajan: no escape of mass for \(\mathrm{SL}_2(\mathbb Z)\) QUE.

  None supplies zero exclusion.
