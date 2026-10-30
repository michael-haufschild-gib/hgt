# Research routes and their mathematical obstacles

Status: 30 October 2026, corpus `a0e8154924` plus working tree. **RH remains open.** The inventory is 32 live routes, 17 standalone candidates and the PW-B branch of PM. Every live route has an exact RH receiver; none has the arithmetic input that receiver needs.

**The frontier in four sentences.**

- **Weil positivity on atomic families is a theorem at every fixed overlap.** Shells repay the overlap loss exactly by Poisson summation, and the margin is the conductor-one Fourier tail \(E(c)\), which tends to \(0\) by Stirling's formula.
- **RH is the same positivity once the overlap grows.** For a \(C^2\) profile the threshold is \(c_N^4/\log N\to\infty\); for the Steklov profile it is an iterated logarithm. RH is therefore a rate problem inside an explicit overlap window.
- **Every RH-strength input must distinguish the gauge point \(0\) from Haar-typical points at square-root precision.** No gauge-invariant certificate bounds the Möbius exponent at \(0\) below \(3/4\); finitely determined certificates give \(1\).
- **Over \(\mathbb Z\) no producer exists.** Bézout and Riemann–Roch for \(\mathbb G_m(\mathbb Q)\) are exact and linear. \(\mathbb Z\) has no Frobenius among its self-maps, and the Frobenius equation \(x^q=x\) lives only on the gauge torus, as the fixed points of the Adams operations.

Companions: [summary, open problems, next questions](obstacles-summary.md) · [walls ledger](walls-ledger.md) · [route unification](route-unification-ledger.md) · [frontier map](../rh-current-frontier-map.md) · [scoped obstructions](../rh-killed-routes.md). Research record: [working log](../../../logs/review-3010-research-2026-10-30.md).

## How to read this report

Evidence comes from corpus searches, Lean statements, module docstrings and proof structure. No builds or axiom audits were run for this review.

| Label | Meaning |
|---|---|
| **[L]**, **[S]**, **[K]** | As in the frontier map: integrated; working or unintegrated; individually checked. |
| **[Lean]** | Lean statement read in this review; integration not assessed. |
| **[P]** | Paper proof only (pipeline stage 2); contents not audited here. |
| **[E]** | External claim. |
| **(inference)** | A conclusion of this review, not a Lean theorem. |

**Obstacle classes.**

- **A, just work.** The ingredients exist: certified computation, composition of proved theorems, quantification of a qualitative proof, transport between proved dictionaries, formalization of a written proof, or integration. An A-item never promises that a desired sign holds.
- **B, open mathematics.** A missing inequality, construction or uniformity, with a strength tag:

| Tag | Strength |
|---|---|
| **[RH]** | Equivalent to RH. |
| **[RH+]** | Strictly stronger than RH. |
| **[FS]** | Equivalent to finitely many off-line zeros (RH above a height); implies LH and a fixed strip. |
| **[LH]** | At least Lindelöf strength. |
| **[≥QRH]** | Implies a fixed zero-free strip \(\Theta<1\). |
| **[open]** | Intermediate; no known solution; not known to imply RH. |

## Part I — The frontier in twelve results

### 1. The overlap window of complete Weil positivity

Atomic families are \(f_x=\sum_{n\le N}x_n\,\varphi((u-\log n)/w)\) with width \(w=c/N\). The complete Weil matrix keeps every prime power, the Gamma factor and both poles.

**Every fixed overlap is positive.**

- **Statement [L].** Every \(C^2\) profile \(\varphi\) supported in \([0,1]\) whose Fourier transform has no real zero has an eventually positive definite complete Weil matrix at every fixed \(c>0\). [Every profile](../../../formal/GaloisForLFunctions/CriticalArithmeticCorrelationTheory/EveryProfileWithoutRealFourierZerosIsPositiveAtEveryOverlap.lean).
- **Uniformity [K].** For the tilted spline, one horizon serves all \(0<c\le K\). [One horizon](../../../formal/GaloisForLFunctions/CriticalArithmeticCorrelationTheory/OneHorizonMakesEveryBoundedOverlapPositive.lean).
- **Existential growth [L].** Some unbounded schedule \(c_N\to\infty\) is positive, by diagonalization; it comes with no rate.

**The spectrum is identified [L].**

- The low spectrum is the completed conductor spectrum, with multiplicity:
  \[
  E_m(c)=\frac{2}{M\varphi(m)}\sum_{a\ge1,(a,m)=1}\frac ma\int_{ac/m}^\infty|\hat\varphi(2\pi t)|^2\,dt\ \ge0 .
  \]
- Conductor one is the unique ground state, with a gap, and the bottom eigenvalue tends to \(E(c)=E_1(c)\).
- For the tilted spline \(E_m(c)\ge C/c^7\) uniformly in \(m\) [K].
- [Spectrum bottom](../../../formal/GaloisForLFunctions/RenormalizedArithmeticPotentialTheory/TheBottomOfTheCompleteWeilSpectrumIsTheCompletedShellEnergy.lean), [pole ground state](../../../formal/GaloisForLFunctions/CriticalArithmeticCorrelationTheory/TheCompleteWeilGroundStateIsThePole.lean).

**The mechanism is Poisson summation on the successor lattice [L].**

- Past touching, successor shells \(n=km+h\), \(1\le h<c\), enter with Ramanujan weights \(c_m(h)\).
- The increment law \(E(c)-E(C)=\frac2M\sum_k\frac1k\int_{kc}^{kC}|\hat\varphi(2\pi t)|^2dt\) is Poisson summation of the autocorrelation on the lattice \(\mathbb Z/s\).
- Möbius inversion collapses the Ramanujan signs to coprimality, so every nonpolar \(-\log c\) loss is repaid exactly.
- \(E(c)\to0\) is Stirling's formula: \(-\log2\pi\) is Stirling's constant.
- [Shells repay every conductor](../../../formal/GaloisForLFunctions/RenormalizedArithmeticPotentialTheory/TheShellsRepayEveryConductor.lean), [positive Fourier integral](../../../formal/GaloisForLFunctions/RenormalizedArithmeticPotentialTheory/TheCompletedShellEnergyIsAPositiveFourierIntegral.lean).

**The arithmetic input is linear and of fixed modulus [L/K].**

- On a Ramanujan mode the upward prime rows are weighted affine prime windows:
  \[
  \sum_{k\le X}\frac{\Lambda(k)}k\,c_q(kn+h)F(k/X)\to\frac{c_q(n)c_q(h)}{\varphi(q)}\int F(t)\frac{dt}t ,
  \]
  uniformly in \(n,h\).
- This needs only the prime number theorem in progressions to a fixed modulus. The error is \(X\exp(-a(\log X)^{1/10})\), giving every inverse-logarithmic rate [K].
- The downward rows cancel the near-Gamma pairing through \(\Lambda*1=\log\).
- [Affine windows](../../../formal/GaloisForLFunctions/CriticalArithmeticCorrelationTheory/WeightedAffinePrimeWindowsAreUniform.lean), [log decay](../../../formal/GaloisForLFunctions/CriticalArithmeticCorrelationTheory/PrimeResidueSourcesHaveQuantitativeLogDecay.lean), [downward cancellation](../../../formal/GaloisForLFunctions/CriticalArithmeticCorrelationTheory/TheNearGammaAndDownwardPrimeRowsCancel.lean).

**Growing overlap is RH.**

- **\(C^2\) profiles [L].** Whenever \(c_N^4/\log N\to\infty\) and \(c_N=o(N)\), eventual positivity is RH. For the tilted spline this covers \(c_N=2(\log N)^\alpha\), \(\alpha>1/4\). [Log overlap](../../../formal/GaloisForLFunctions/RenormalizedArithmeticPotentialTheory/LogarithmicOverlapOfTheCompleteWeilMatrixIsTheRiemannHypothesis.lean).
- **Smoother profiles.** \((\log N)^\varepsilon\) for smooth profiles [L]; \((\log\log N)^s\) for Gevrey class \(s\) [L]; \(L(\log L)^2\log\log L\), \(L=\log\log N\), for the Steklov profile [K].
- **The threshold is a synthesis threshold.** Atoms at overlap \(c\) synthesize a fixed test with an error whose Weil energy carries a factor \(\log N\).

**Selectivity at bounded overlap.**

| Twin | Result |
|---|---|
| Each flip \(\omega_p\) | Rejected at every fixed \(c\ge c_0(p)\) by a prime-square trial, while \(\zeta\) stays positive [L]. |
| All flips at once | No fixed \(c\) rejects them: for \(p\) large the flip perturbation \(\le8\log p/\sqrt p\cdot\)mass is below \(E(c)/2\) [L]. |
| Liouville twin | Negative at every fixed \(c\ge1\) for a tilted box plateau, while \(\zeta\) is positive [S]; \(c\ge1/2\) for the plateau [S]. |

Consequence (inference): the overlap window \([\text{fixed }c,\ c_N^4\gg\log N]\) is the place where RH sits for atomic families. The fixed-overlap margin is an exact Poisson remainder, and all of its arithmetic is fixed-modulus prime counting. RH asks for positivity once that margin has fallen below the synthesis error. In the window the margin \(E(c_N)\) is positive and tends to \(0\), while selectivity against every flip requires \(c_N\to\infty\).

### 2. The two-source law and the gauge torus

- **Twin-blindness [L].** Pointwise-closed shift-invariant statements contain every unitary twist; locality is twin-blind.
- **Two sources [L].** The gauge enters Weil's form only through non-ratio lags. Selectivity therefore comes from the pole and Gamma, or from gauge charge, i.e. additive structure.
- **Coherence principle [L].** Every nonnegative statistic is maximal at the trivial point. The pole is coherence: \(\psi(N)\sum\Lambda^2\le\log N\,\psi(N)^2\). Repayment by shells can happen only on signed nonpolar directions. [Coherence](../../../formal/GaloisForLFunctions/ArithmeticGaugeTheory/TheCoherencePrinciple.lean).
- **The Liouville point is the antipode [L].** \(S_N(\ell)+S_N(0)=2\psi(\sqrt N)\). No size statement separates the twins; only the sign of the pole does. [Antipode](../../../formal/GaloisForLFunctions/ArithmeticGaugeTheory/TheLiouvillePointIsTheAntipode.lean).
- **Shell decomposition [L].** The Haar average of the prime pair form deletes every shell. Level-\(q\) Dirichlet averaging keeps exactly the shells with \(q\mid j\), and these are the major arcs. [Major arcs](../../../formal/GaloisForLFunctions/ArithmeticGaugeTheory/TheMajorArcsOfTheShells.lean).

### 3. The gauge exponent: RH is a Diophantine exponent at one point

For a source \(a\) and gauge point \(x\), \(\theta_a(x)\) is the least power bounding \(\sum_{n\le N}a(n)\chi_x(n)\).

| Fact | Statement |
|---|---|
| Typical value [L] | Exactly \(1/2\) Haar-a.e., for every bounded source unimodular at primes (Paley–Zygmund on the top prime block plus a zero–one law). |
| The trivial point [L] | \(\theta_\mu(0)=\Theta=\sup\operatorname{Re}\rho\). The trivial point is never better than typical. RH \(\iff\) \(0\) is typical. |
| Invariances [L] | \(\Theta\) is constant along the archimedean line through \(0\) and under finite prime modifications. RH is a tail property. |
| Liouville points [L] | Twin tails have exponent \(1\). The exceptional set is residual and null; exponent \(\ge3/4\) is already residual. |
| No multiplicative certificate [L] | A gauge-invariant bound on the Möbius exponent gives at least \(3/4\) at \(0\); a finitely determined one gives at least \(1\). |
| Special locus [L] | A primitive Dirichlet point has Möbius exponent \(\Theta_\chi\), and GRH for \(\chi\) is its typicality. The large sieve makes the special locus typical on average, never at a single point. |
| Constant source [L] | Exponent \(0\) at nonprincipal Dirichlet points (periodicity cancels) and \(1\) at \(0\) (the pole). No special point is typical. |
| Twin inequality [S] | \(\exp_\mu(x+\ell)\le(1+2\exp_1(x)+\exp_\mu(2x)/2)/3\). Twins of nonprincipal Dirichlet points are at most typical unconditionally. If every point had exponent \(\ge1/2\), then \(\Theta=1\): \(1/2\) is not a floor on \(G\). |
| Escape state [L] | The limit of \(|S_N|^2dx/N\) is an Euler product leaning to the Liouville point, blind to zeros. |

[Gauge exponent](../../../formal/GaloisForLFunctions/ArithmeticGaugeTheory/TheGaugeExponent.lean), [typical exponent](../../../formal/GaloisForLFunctions/ArithmeticGaugeTheory/TheTypicalExponentIsOneHalf.lean), [not gauge invariant](../../../formal/GaloisForLFunctions/ArithmeticGaugeTheory/TheExponentIsNotGaugeInvariant.lean), [special locus](../../../formal/GaloisForLFunctions/ArithmeticGaugeTheory/TheSpecialLocusReadsGRH.lean), [twin inequality](../../../formal/GaloisForLFunctions/ArithmeticGaugeTheory/TheLiouvilleTwinInequality.lean).

Consequence (inference): RH is an *exponent* statement about a special point. That is the class in which Roth's and Siegel's theorems succeeded; distribution statements such as the normality of \(\sqrt2\) remain out of reach.

### 4. Index theory of the Weil kernel

| Law | Statement |
|---|---|
| Index [S] | \(\kappa(K_\zeta)=\#\)distinct right zeros. |
| Global and parity law [S] | \(\kappa=0\iff\) one-sided \(\psi\) count \(\iff\) the odd Liouville class has an upper count. |
| Heights and carriers [L/K] | \(\kappa_T=O(T\log T)\). Towers \(3^k/2^j\) certify height \(T\), and boxes \(p^iq^j\) carry finite spectra. |
| Towers [L/K] | Fine consecutive-ratio towers decide. Attained depth is seen by almost every prime. On finite support, almost every prime tower decides. |
| Waves [L/S] | Index = least number of exceptional waves; collision mass \(=2(\kappa+\)excess\()\). |
| Polar divisor [L] | For curve data, index = number of right pole classes of the affine Weyl sum; confinement \(\iff\) index zero. |
| Local constituents [S] | On \(\mathbb Z^S\), \(|S|\ge2\), axis-supported kernels have index \(0\) or \(\infty\). Finite nonzero index needs the archimedean off-axis constituent. |
| Compressions [S] | Receivers only; Euler compressors are index-neutral. |
| Finite stratum [S/L] | Finite index \(\iff\) finite off-line support \(\iff\) bounded heat counts; implies LH and \(\Theta<1\). |

### 5. Precision and counting (ASRP)

- **Stabilizers [L/K/S].** The count's stabilizer is the square-root class \(\mathcal Q\); tower positivity is precision-exact (stabilizer \(\{0\}\)) [S]. Finite aperture cannot decide [K].
- **Battery [S/L].** Deciding-input theorem [S]: anything implying the count rejects the Liouville twin. One-signed perturbations [L]: an upper count for any majorant of \(\Lambda\), or a lower count for any minorant, proves RH.
- **Complex lifts [K].** Every real torus gauge has a complex count lift. Product conjugation precision is the mean sine current.
- **Chebyshev ledger [L].** \(\psi\) is two Möbius moments, a sawtooth inversion of size \(<n\), and a Mertens remainder.

### 6. Producers: one ledger, no Frobenius over \(\mathbb Z\)

| Fact | Statement |
|---|---|
| Ledger [L] | \(\sum m_x\le\deg P\) over \(\mathbb F_q\); \(\sum m_p\log p\le\log A\) over \(\mathbb Z\). Stepanov reaches multiplicity \(\approx\sqrt q\) through \(x^q=x\). |
| Bézout for \(\mathbb G_m(\mathbb Q)\) [K] | A length-\(N\) Dirichlet polynomial vanishing to order \(m_p\) along \(2\pi i\mathbb Z/\log p\) has \(\prod p^{m_p}\le N\), attained by Euler factors. |
| Riemann–Roch for \(\mathbb G_m(\mathbb Q)\) [L] | \(h^0(N,m)=\lfloor N/\prod p^{m_p}\rfloor\): exact and linear in \(e^{\deg}\). A Hodge index needs a quadratic Euler characteristic. |
| Approximate vanishing [L] | For integer auxiliaries, \(|D|<1/\sqrt2\) along a long stretch of a progression already forces exact divisibility. "Small" is no cheaper than "zero". |
| Ring endomorphisms [L] | Completely multiplicative maps of \(\mathbb N\) with bounded additive defect are the identity or unit-ball gauge points; integer-valued ones take values in \(\{-1,0,1\}\). |
| Adams operations [L] | \(\psi^kx=kx\) on the gauge torus. \(\psi^q\)-fixed twists are the \((q-1)\)-torsion twists; \(\psi^2\) fixes only \(0\). \(x^q=x\) lives on characters, not on integers. |
| Factorial ratios [L] | Balanced ratios have \(v_p\le\#T-1\) above the square root of their length; binomials have multiplicity \(\le1\) above \(\sqrt N\). |
| Twist tower over \(\mathbb Z\) [L] | Collapses: levels \(j\ge1\) live on proper prime powers, inside \(\mathcal Q\). |
| Divisibility is parity-blind [L] | \(0\le\log\operatorname{lcm}(O_x)-\theta(x)\le2\sqrt x\log x\) for the odd Liouville class. |

[Bézout](../../../formal/GaloisForLFunctions/EffectiveArithmeticHodgeTheory/TheBezoutTheoremOfTheMultiplicativeGroup.lean), [Riemann–Roch](../../../formal/GaloisForLFunctions/EffectiveArithmeticHodgeTheory/TheRiemannRochTheoremOfTheMultiplicativeGroup.lean), [small auxiliaries](../../../formal/GaloisForLFunctions/EffectiveArithmeticHodgeTheory/SmallIntegerAuxiliariesAreDivisible.lean), [ring endomorphisms](../../../formal/GaloisForLFunctions/ArithmeticGaugeTheory/ApproximateRingEndomorphisms.lean), [Adams](../../../formal/GaloisForLFunctions/ArithmeticGaugeTheory/TheAdamsOperations.lean), [linear counts](../../../formal/GaloisForLFunctions/ArithmeticKreinLangerTheory/IntegralityProducesLinearCounts.lean).

### 7. The complete source on Haar cells

- **Haar identities [L].** Gamma pays every detail, and each Haar cell has \(W\ge\) mass\(/10\). The Haar identity \(W+G=D_X+P+\sum V_X(a)u_a^2\) holds with \(G\ge0\) and \(V_X\) signed.
- **Prime edges [K].** Literal prime edges keep a Gamma reserve; their full-Weil entries are negative.
- **Finite index [L/S/K].** Uniform finite index holds on every layer except the first prime layer. Full prime–polar cancellation carries an \(e^R\) loss [S].
- **Chebyshev identity [L].** Ordered entries are centered Chebyshev integrals.

### 8. Theta moments (TH, CAF)

- **Hierarchy [L].** The signed center hierarchy is strict at rank seven for \(0<a<1/2\); the all-rank sign is RH.
- **Center tails [L/K].** Integration by parts gives \(s_k(a)=\int(\sinh ar+ar\cosh ar)U_k(r)\,dr\) with aperture-free tails \(U_k\). The seam tail is a Plancherel Gram at every order. The eighth section reduces to one aperture-free odd first-moment tail form, with an aperture-free seam split as a sufficient condition.
- **Native tails [K].** Complete native tails are strict beyond a logarithmic rank horizon and decrease in Loewner order.
- **Boundary [K].** First-atom all-rank positivity fails at every fixed center.
- **Open.** Compact-center compensation of the odd \(4\times4\) block, then all ranks.

### 9. Heat flow (WD, LA)

Unchanged since the last checkpoint.

- **Horizon [L].** For \(0<t\le1/8\), zeros of \(H_t\) beyond \(2\pi e^{(2/3+\varepsilon)/t}\) are real and simple.
- **Dissipation [K].** The localized energy inequality crosses collisions and \(t=0\).
- **Index link [L].** Collision mass \(\to\infty\) iff the tower indices are unbounded.
- **Open.** Outer-energy absorption and a uniform count as \(t\downarrow0\) [FS].

### 10. Critical-line census

Unchanged.

- **Census [L].** Simple critical \(\ge HD(1)+10^{-8}\); simple or critical \(\ge0.8876\).
- **Dichotomy [K].** \(70\%\), or a simple near-line off-line core.
- **Exchange rates [L].** \(E(1/9)\le4\Rightarrow70\%\); prime surplus \(\le N/18\Rightarrow75\%\).
- **Projected credit [K].** Bounds the negative-part credit.
- **Open.** Two-sided coalescent estimates, or a positive lower bound for \(E_{\rm proj}\).

### 11. Quasi-RH and density

- **Formalized [L].** Guth–Maynard \(30/13\), DH on \(\sigma\ge5/6\), Vinogradov–Korobov and Siegel's theorem. A density envelope never forces a zero to vanish.
- **External [E].** The quasi-RH preprint claims Dirichlet zero-freeness for \(\operatorname{Re}s>7/8\); no corpus capstone.
- **Missing.** Siegel–Walfisz and Bombieri–Vinogradov are not in the corpus (lexical search).

### 12. Foundations

- **Hecke [K].** Global continuation and completed functional equations.
- **Curves [K].** Genus-one base \(y^2=x^3-x\) over \(\mathbb F_3\): adeles, Haar measure, local integrals.
- **Loop group [K].** Real loop group: Bruhat, Iwasawa and the spherical function.

These are tools; none carries a selective sign.

## Part II — Live routes

Each entry: **State**, then **A** (just work) and **B** (open, tagged).

### WL — Weil lag / prime-error energy

**State.**

- Critical-deficit energy, linear prime-error budget and the one-sided \(\sqrt x\log^2x\) count are each RH; the count is \(\kappa=0\) and the odd-class upper count [S].
- The Chebyshev ledger reduces \(\psi\) to moments, sawtooth and Mertens [L].
- The prime error is the separated off-diagonal of the complete form.
- Integer approximate vanishing forces divisibility, but no auxiliary producer exists [L].

**A.** Certified truncations with high-zero tails. Tabulate \(W(f,T_{d\log2}g)\) and \(I_n(h)\). Formalize the product-bias classification [P].

**B.**

- The one-sided count or odd-class upper count **[RH]**.
- Joint square-root control of moments, sawtooth and Mertens **[RH]**.
- Subtracted lag **[FS]**.
- Genus saturation **[RH+]**.

[Receiver](../../../formal/GaloisForLFunctions/BiScaleUncertainty/WeilLagCriticalDeficitEndpointAndLimitLaw.lean).

### RW — Restricted Weil ground energy

**State.** RH iff \(\mu(A)>0\) at every aperture. \(\mu\) is strictly decreasing, and positive floors must decay doubly exponentially. Gårding gives a finite index. The Gamma boundary norm \(\pi/2\) has no uniform relative reserve [S].

**A.** Certified finite-aperture minima; shell ledgers.

**B.** Cumulative aperture relaxation bounded by the initial reserve, with low modes, collars and polar energy paid **[RH]**. [Aperture flow](../../../formal/GaloisForLFunctions/ArithmeticContinuationAndCriticalEnergy/TheApertureFlowNeverStalls.lean).

### FU — Signed prime scheduling

**State.** RH iff the normalized completed Abel moment is bounded above. Narrow prime channels have a useful sign [L]; wide channels can be positive [S].

**A.** Seed, drift, cross-block and endpoint ledgers for fixed schedules.

**B.** A joint signed total over a prime-exhaustive schedule **[RH]**. [Receiver](../../../formal/GaloisForLFunctions/RHTower/CCM/CCMFUSuzukiMobiusDivisorOneSided.lean).

### CFC — CCM first-clock lower bound

**State.** RH iff the literal first-clock source sine coefficient is bounded below on an aperture tail; under ¬RH it is unbounded below on every tail. Phase-natural transport is the identity.

**A.** Certified coefficient evaluations on finite aperture ranges, with prime, archimedean and endpoint terms separated.

**B.** The tail lower bound **[RH]**. [Completeness](../../../formal/GaloisForLFunctions/RHTower/CCM/CCMFirstClockTailLowerBoundCompleteness.lean).

### RP — Matched-quantile history floor

**State.** RH iff an eventual linear floor \(-B(K+2)\). The history drops below \(-\delta(K+2)\) cofinally, so no sublinear floor exists [L].

**A.** Low-LCM instantiation; the escape constant \(\delta\) on computed ranges.

**B.** A linear floor paying high-LCM pairs, moving core and transport together **[RH]**. [Floor](../../../formal/GaloisForLFunctions/RHTower/SPEQuantileRieszRoutePLinearFloorCriterion.lean).

### PA — Prime–archimedean passivity

**State.** Current-sign, Bernstein-mismatch and compact-moment receivers. Each fixed Hausdorff order is positive at large shift.

**A.** Explicit thresholds for finite order blocks.

**B.** All-order, all-shift sign **[RH]**. [Moments](../../../formal/GaloisForLFunctions/RHTower/PrimeArchThetaFirstAtomHighOrderMomentBounds.lean).

### MC — Möbius cancellation

**State.**

- Strict half-power and subpower energy are RH. \(M=o(\sqrt x)\) is false.
- Gauge exponent: \(\theta_\mu(0)=\Theta\), typical value \(1/2\), RH \(\iff\) \(0\) is typical [L].
- No gauge-invariant certificate below \(3/4\); finitely determined certificates give \(1\) [L].
- Dirichlet points read GRH [L]. The Liouville twin inequality transfers strips between points [S].

**A.**

- Fixed-modulus estimates.
- An exponent-inequality calculus from \(\mu^2=\sum_{d^2\mid n}\mu(d)\), \(\mu*1=\delta\), \(\Lambda*1=\log\).
- Transport of supplied strip bounds through it.

**B.**

- Every strict half-power, or the odd-class upper count **[RH]**.
- Linear Mertens budget **[RH+]**.
- Any fixed one-sided power saving **[≥QRH]**.
- Any non-gauge-invariant, \(0\)-specific inequality improving \(\theta_\mu(0)\) **[≥QRH]**.

[Hilbert criterion](../../../formal/GaloisForLFunctions/RHTower/MobiusHilbertFormEquivalence.lean), [trivial point](../../../formal/GaloisForLFunctions/ArithmeticGaugeTheory/TheTrivialPointIsNeverBetterThanTypical.lean).

### TT — Theta tails and directed covariance

**State.** Seam, Wold and odd-Weil receivers; sharp \(t<1/2\) threshold; restricted current and light-cone signs.

**A.** Fixed directed-covariance and reflected-prime terms.

**B.** Signed nonlocal covariance at every scale, or complete odd positivity **[RH]**. [Wold receiver](../../../formal/GaloisForLFunctions/RHTower/PaperWoldDirectedCovarianceRH.lean).

### LA — Line anchor

**State.** Finite-head and heat receivers. Ordinary \(\xi\) coefficients are Turán [L] and Lorentzian [S]. Shrinking-depth transfer, the \(2/3\) horizon [L] and localized dissipation [K].

**A.** Certified heads and low degrees; heat-tail errors with the local cofactor.

**B.** All-height, all-degree head signs **[RH]**; a uniform heat count **[FS]**. [Finite head](../../../formal/GaloisForLFunctions/RHTower/XiSliceHeatFiniteHeadReduction.lean).

### TG — Integer trace below one

**State.** Winding, cubic-transgression and central-gap receivers; Gaussian coprime-divisibility covariance.

**A.** Finite projection and transgression data with residual and trace separated.

**B.** A matrix-complete decomposition with nonnegative residual and trace below one on every disc **[RH]**. [Index estimate](../../../formal/GaloisForLFunctions/RHTower/RestrictedProjectionIndexOperatorNormCriterion.lean).

### HF — Arithmetic Hodge positivity

**State.**

- **Atomic branch.** Positivity at every fixed overlap for profiles without real Fourier zeros [L]. Spectrum = completed conductor spectrum; pole ground state; floor \(C/c^7\) [K]. RH at \(c_N^4\gg\log N\) [L] and at the Steklov iterated-log schedule [K].
- **Shell mechanism.** The \(-\log c\) loss is repaid exactly by Poisson summation; fixed-modulus PNT in progressions suffices.
- **Selectivity.** Per-flip and Liouville selectivity at bounded overlap [L/S].
- **Haar branch.** Haar identities with a signed diagonal; finite index except the first prime layer.
- **Prefix branch.** Exact prefix Schur reduction [K]; prefix index ceiling \(\le N-M\) [K].

**A.**

- Formalize the paper cards on growing-overlap rates [P].
- Siegel–Walfisz intake.
- Conductor-uniform quasimodes for \(m\le M(c)\).
- An explicit unconditional schedule \(c_N\to\infty\).
- A tilted Steklov profile combining fixed-overlap positivity with the iterated-log receiver (inference).
- Profile-adapted synthesis to sharpen the RH threshold.
- Flip thresholds \(c_0(p)\).
- Head sizes and first-layer constants.

**B.**

- Positivity on an RH-complete schedule, complete-cell index zero, residual sign or work ceiling **[RH]**.
- Uniform finite index; finite \(\mathcal E_{\rm crit}\) **[FS]**.
- Positivity throughout the window \(E(c_N)\log N\to\infty\) with polynomial losses; the exact location of the transition **[open]**.
- Haar-branch joint payment of the non-arithmetic Gamma graph, signed diagonal, first prime and poles **[open]**.

[Fixed overlap](../../../formal/GaloisForLFunctions/CriticalArithmeticCorrelationTheory/TheCompleteWeilFormIsPositiveAtEveryFixedOverlap.lean), [window](../../../formal/GaloisForLFunctions/RenormalizedArithmeticPotentialTheory/TheBottomOfTheCompleteWeilSpectrumIsTheCompletedShellEnergy.lean).

### CHMD — Causal hyperbolic–modular duality

**State.**

- Wave, Doob and nodal receivers; completed aperture core.
- Actual generator heads have uniform Gamma bounds, and the complete even-power error is \(\le\delta\Gamma(f)\) [K].
- Literal prime edges keep the fraction \(1-\log2/\log3\) of divisor energy; full-Weil prime-edge entries are negative [K].

**A.** Domain and cutoff theorems on fixed sources; the signed residual with the primitive defect.

**B.** The one-sided wave bound or odd Doob inequality, paying first-prime, coarse, head and polar terms and the retained-orbit sign **[RH]**. [Odd criterion](../../../formal/GaloisForLFunctions/RHTower/CHMDOddSectorCriterion.lean).

### TH — Theta moment positivity

**State.**

- Rank seven strict; all-rank sign \(\iff\) RH.
- Aperture-free center tails; the seam tail is a Plancherel Gram.
- The eighth section reduces to one aperture-free odd tail form plus a seam split.
- Native tails strict beyond a logarithmic rank horizon.
- First-atom all-rank positivity fails at fixed center.

**A.**

- Certified evaluation of the odd first-moment tail form and of the seam-split constants.
- The explicit integrated physical successor reserve (WIP [S]).

**B.**

- Compact-center compensation of the odd \(4\times4\) block **[open]**.
- All ranks with strictness and radical control, or signed heated coefficients at one common time **[RH]**.

[Odd four tail](../../../formal/GaloisForLFunctions/RHTower/ThetaCusp/ThetaCuspOddFourMomentTail.lean), [seam split](../../../formal/GaloisForLFunctions/RHTower/ThetaCusp/ThetaCuspOddFourSeamSplit.lean), [completeness](../../../formal/GaloisForLFunctions/RHTower/ThetaCusp/ThetaCuspCenterMixedSignedJetCompleteness.lean).

### RN — Renewal and singular comparison

**State.** Green/BV realization; compact cone-positive renewal operator with an exact regularized determinant.

**A.** Finite packet and resolvent data with cusp and seam terms.

**B.** Directed mixed prime+Gamma \(\ge\) pole **[RH]**. Cone positivity does not give real spectrum. [Spectrum](../../../formal/GaloisForLFunctions/RHTower/ThetaRenewalFredholmSpectrum.lean).

### WD — Ward caps and collision

**State.**

- A nonnegative integrated cap vanishes iff RH.
- Collision mass \(=2(\kappa+\)excess\()\) on finite index; it is \(\to\infty\) iff tower indices are unbounded [L].
- Localized dissipation through collisions and \(t=0\) [K].

**A.** Explicit \(N(t)\) on compact ranges; summed localized estimates on fixed height windows.

**B.** Cap extinction **[RH]**; uniform nonreal count **[FS]**; uniform high count **[LH]**. [Ward receiver](../../../formal/GaloisForLFunctions/RHTower/XiWardGlobalCapAndFiniteHeadArithmetic.lean).

### LI — Paired Li balances

**State.** The guarded history-zero set is finite, and RH iff it is empty. RH iff the Cayley–Li ladder is primitive nonpositive; its couplings do not decay [S].

**A.** Fixed paired histories; finite Cayley ladders.

**B.** Payment at every possible guarded zero, a subexponential history floor, or the ladder sign **[RH]**. [Cayley ladder](../../../formal/GaloisForLFunctions/ArithmeticLorentzianGeometry/RHIsReflectionPositivityOfTheCayleyLadder.lean).

### SZ — Suzuki first variation

**State.** Ward-defect lower-bound receiver; compact-\(L^2\) first variation = full Weil form; factorial/grid tent families are RH [S]. Bare-source \(\ell^2\), uniform causal recovery and positive unital finite parts are excluded [L].

**A.** Moving-aperture limits on specified tent families.

**B.** The tent-family sign, especially low and mixed modes **[RH]**. [Transfer](../../../formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiCriticalRHCompleteFamilyTransfer.lean).

### PM — Haar approximation / damped admission

**State.**

- Positive gauge mass of every escape state is RH.
- Power-growth escape has zero gauge mass [L].
- The Möbius escape state is an Euler product leaning to the Liouville point, blind to zeros [L].

**A.** Fixed cofactor Grams; effective pole orders.

**B.** Positive gauge mass for every escape state **[RH]**; exterior tightness **[open]**. [Visibility](../../../formal/GaloisForLFunctions/ArithmeticCorrelationGeometry/RHIsTheVisibilityOfEveryEscapeState.lean), [escape state](../../../formal/GaloisForLFunctions/ArithmeticGaugeTheory/TheEscapeStateLeansToTheLiouvillePoint.lean).

### JAS — Joint ancestry

**State.** Level-one prime-product positivity and square-shell receivers; unconditional sign at a logarithmic prime budget.

**A.** Budget gaps on chosen shells.

**B.** The square-root power budget **[RH]**. [Capstones](../../../formal/GaloisForLFunctions/RHTower/JointAncestryLevelOneCapstones.lean).

### CTF — Báez–Duarte approximation

**State.**

- Residual \(=(1-\Lambda\)-readout\()^2+\) centered energy.
- Divisor covariance = completed cyclotomic Gram\(/(T+1)\); the omitted tail is \(\le(M+1)^2/(T+1)\) [K].
- Every superlinear Chebyshev exponent is carried by the nonnegative cyclotomic remainder [S].

**A.** Optimized finite rows with both residual components reported.

**B.** Complete error \(\to0\): upper covariance control along compatible cutoffs, \(BX^\varepsilon\) for every zero and \(\varepsilon\) **[RH]**. [Readout](../../../formal/GaloisForLFunctions/BezoutValuationIncidence/VonMangoldtReadoutFormOfTheBaezDuarteCriterion.lean).

### HCF — Gaussian heat trace on two grids

**State.** Positivity on both \(\log2/\log3\) grids is RH; one grid aliases. Two-prime phase separation is polynomial [S].

**A.** Finite degrees and heights on both grids.

**B.** Both grid signs at all degrees **[RH]**; a many-node Gram floor from phase separation **[open]**. [Two grids](../../../formal/GaloisForLFunctions/RHTower/XiGaussianHeatTwoPrimeSourceSampling.lean).

### XN — Newton invariant discs

**State.** Line-centred self-map discs covering every zero give RH; exact Laplacian of the interior margin.

**A.** Certified discs.

**B.** A covering family with nonnegative interior margin **[RH]**. [Criterion](../../../formal/GaloisForLFunctions/RHTower/XiNewtonSchwarzPickCriticalLine.lean).

### BAG — Deterministic self-return

**State.** Strong recurrence through the right strip is an RH receiver. The archimedean line through \(0\) carries the exponent \(\Theta\) at every point [L], so the Bohr hull of vertical translates sees \(\Theta\) uniformly.

**A.** Finite-head returns on zero-free targets.

**B.** Returns near every right-strip point, including possible zeros **[RH]**. [Receiver](../../../formal/GaloisForLFunctions/RHTower/ZetaStrongRecurrenceReceiver.lean).

### EWU — Even pole-weight uniqueness

**State.** Attained aperture-antitone blind minima. RH iff some real weights make the full functional nonnegative up to each aperture [L].

**A.** Certified finite blind problems.

**B.** Nonnegative actual blind minima at every aperture **[RH]**. [Existence](../../../formal/GaloisForLFunctions/RHTower/WeilPositivityFiniteLevelExistenceDecidesRH.lean).

### GTA — Transverse Schur charge

**State.** Rank-uniform decay of the quartic Schur charge is RH.

**A.** Finite-rank charges.

**B.** Rank-uniform arithmetic decay **[RH]**. [Equivalence](../../../formal/GaloisForLFunctions/RHTower/Hedenmalm/HedenmalmThetaSchurQuarticSpectralDecayEquivalence.lean).

### OWU — Odd Weil-weight uniqueness

**State.** Odd and dilation-ray criteria. Smooth odd witnesses separate \(\Lambda\) from the Liouville twin and the first flip at fixed radii; finite-aperture separations cannot decide.

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

- Every-width lag receivers.
- The atomic overlap window (§1).
- Explicit \((\log\log N)^\alpha/N\) schedules reach \(\kappa\) for \(\alpha>1\) [L].
- Twins are seen by every large Gevrey section, eventually and not intermittently [L].
- Integer atoms and fine two-prime towers carry the index; tower positivity is precision-exact.

**A.**

- Full-index exhaustion at the Steklov schedule.
- Removal of the extra \(\log\log L\) factor.
- The tilted Steklov profile.
- Explicit unconditional schedules (shared with HF).

**B.**

- Late lag, all-generator tower sign or RH-schedule sign **[RH]**.
- Unattained-depth tower detection **[open]**.
- Positivity throughout the window below the RH threshold **[open]**.

[Lag receiver](../../../formal/GaloisForLFunctions/SquareRootThreshold/EveryWidthDecidesTheCriticalLine.lean), [sections](../../../formal/GaloisForLFunctions/EffectiveArithmeticHodgeTheory/TwinsAreSeenByEveryLargeSection.lean).

### ACT — One-shift arithmetic criticality

**State.** One fixed theta shift with an all-profile variation inequality gives odd positivity and RH. Short collars are absorbed only with support-dependent shifts.

**A.** Signed moment ledgers for prescribed profiles.

**B.** One shift for every support and profile **[RH]**. [Scope](../../../formal/GaloisForLFunctions/ArithmeticCriticalityTheory/ShortProfilePoleFreeVariationInequality.lean).

### AIP — Arithmetic incidence allocation

**State.** Global joint allocation is the odd sign. AIP shares HF's atomic window, spectral identification, Haar results, prefix Schur reduction and flip rejection.

**A.** As HF; complete incidence matrices in conductor coordinates.

**B.** Signed allocation on source-complete cells **[RH]**; window positivity below the RH threshold **[open]**. [Allocation](../../../formal/GaloisForLFunctions/ArithmeticIncidencePositivity/GlobalIncidenceAllocationCondition.lean).

### ACS — Arithmetic effectivity and the census

**State.**

- Effectivity, Rosati and chirality receivers; HF's atomic and Haar results.
- Riemann–Roch for \(\mathbb G_m(\mathbb Q)\) is exact and linear, so a Hodge index needs a surface with quadratic Euler characteristic [L].
- Census as in §10. Polar confinement is the lower count [L]. Elliptic, Hecke and loop foundations.

**A.**

- Slack calculus at \(\lambda\in[3/4,1)\).
- \(E_{\rm proj}\) on explicit near-line configurations.
- The affine \(A_1\) constant term over the genus-one base.
- HF's window tasks.

**B.**

- Full-source quadratic RI, a Rosati bound or complete-cell index zero **[RH]**.
- Uniform finite index **[FS]**.
- Census inputs beyond \(2/3\) **[open]**.
- A characteristic-zero surface whose sections count quadratically **[open]**.

[Effectivity](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/ExactArithmeticSourceEffectivity.lean).

## Part III — Route candidates

A candidate lacks an independent source construction or its landing. A promotion gap is **[open]**; it becomes **[RH]** once it is the final sign. Every landing must fail the battery:

- the Liouville twin;
- every flip \(\omega_p\), cofinite flips, twin tails;
- \(\Lambda+\varepsilon n^{-\eta}\), and \(\Lambda+1/n\) for positivity statements;
- the golden datum on the lattice;
- over-regular Beurling systems;
- Haar-random gauge points.

**Rule (theorem):** No landing can be gauge-invariant, pointwise-closed or finitely determined.

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
| **SC** Stokes/Witt–Krein | Rigged fibres; fine-tower exhaustion; height certificates; carriers; finite-support tower decisions; polar confinement = index zero; prefix index \(\le N-M\). | Finite cross-fibre coordinates. | A source-fixed cross-fibre index ceiling; unattained-depth detection. [Source](../../../formal/GaloisForLFunctions/RHTower/PaperKreinWallFourierCompletion.lean) |
| **SEC** adjacent seam | Essential norm = seam jump; Fock criteria. | Finite seam charges. | Eventual compactness or Fock boundedness at actual zeros. [Source](../../../formal/GaloisForLFunctions/RHTower/TimeOneGammaJetFockRHCriterion.lean) |
| **W1C** Lee–Yang | Finite Lee–Yang; Ising-limit receiver. | Finite couplings. | Source-defined centred couplings converging to Riemann's measure. [Source](../../../formal/GaloisForLFunctions/RHTower/IsingLawConvergenceRH.lean) |
| **WBF** certificates | Genealogy Gram and Fredholm recovery. | Certificate streams. | An arithmetic stream with uniform-depth landing. [Source](../../../formal/GaloisForLFunctions/HTGeometry/PaperCriticalGenealogyCompletion.lean) |
| **PW-B** PM cusp branch | Native two-response action; positive-damping admission. | Positive-damping actions. | Remove zero indexing; complete-energy ceiling to all-divisor extinction. [Source](../../../formal/GaloisForLFunctions/RHTower/ThetaCusp/ThetaCuspHawkingBMPWNativeTwoResponseAction.lean) |

## Part IV — Supporting programmes

| Programme | Contribution | Unresolved input |
|---|---|---|
| CACT, RAPT | Fixed-overlap positivity; spectral identification; shell repayment; flip thresholds; RH window | Rates in the window; growing-conductor spectral control |
| TM | Plateau reference floor and Young family (now superseded by tilted profiles past \(c_*\)); successor fibres; prefix Schur; zero-side stratum; Steklov receiver | Single-profile window (tilted Steklov) |
| SSHA | Gamma reserves for profiles without real Fourier zeros; synthesis laws; coordinates; diamagnetism; non-ratio lags | Sharp synthesis thresholds per profile |
| AGT | Gauge exponent; coherence; antipode; special locus; ring endomorphisms; Adams operations; shells' major arcs | A \(0\)-specific non-gauge-invariant inequality |
| HKT, AKLT, EAHT | Index; global and parity laws; towers; heights; carriers; polar index; Bézout and Riemann–Roch for \(\mathbb G_m(\mathbb Q)\); approximate vanishing | Index ceiling; producer |
| ASRP | Precision classes; battery; Chebyshev ledger; complex lifts | Signed square-root control |
| CAF | Completed Grams and Green inverses; Dirichlet–Schur cost; native theta tails; prefix index | Compact-center compensation; complete-Weil inverse identification |
| AID, SAHT, ACS cells | Finite-index chain; Haar identities; even-power approximation | First prime layer [FS]; residual sign |
| ACP, SMAP | Finite-flip gap classification; source selection | Selector beyond finite flips |
| Census, SCP | \(2/3\), \(0.8876\); dichotomy; exchange rates; projected credit | Two-sided coalescent estimate |
| RHTower heat/density | \(2/3\) horizon; dissipation; Guth–Maynard; DH; VK; Siegel | Uniform count; any vanishing mechanism |
| HLF, HTGeometry, AE | Hecke FE; genus-one base; loop group | Uniform bounds; arithmetic quotient and constant term |

## External status

RH is unsolved ([Clay](https://www.claymath.org/millennium/Riemann-Hypothesis/)). External proofs are not validated here.

- **Alpöge–Furman two-thirds theorem.** A pinned formal dependency of the census.
- **Guth–Maynard, Vinogradov–Korobov, Siegel.** Formalized in the corpus.
- **Quasi-RH preprint.** Dirichlet zero-freeness for \(\operatorname{Re}s>7/8\) [E]; no corpus capstone.
- **Ordinary-correlation preprint.** Fixed-form Liouville two-point savings [E]; no power saving.
- **Context, none of which excludes zeros.**
  - Rodgers–Tao: \(\Lambda_{\rm dBN}\ge0\).
  - Bourgain: \(\mu(1/2)\le13/84\).
  - Montgomery: pair correlation for \(|\alpha|\le1\) under RH.
  - Goldston–Montgomery: pair correlation \(\iff\) variance of primes in short intervals.
  - Bombieri–Vinogradov, Zhang, Maynard: level of distribution.
  - Friedlander–Iwaniec: parity broken for \(x^2+y^4\).
