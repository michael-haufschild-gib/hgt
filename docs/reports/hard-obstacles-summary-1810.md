# Hard obstacles: corrected mathematical status

Originally 18 October 2026; corrected 19 October 2026 after comparison with the [current route ledger](rh-current-frontier-map.md), four program READMEs, and relevant Lean declarations. Detailed research recommendations: [19 October review](review-1910/astra.md).

**RH remains open. None of the 27 live routes or 18 candidates has a source-derived closing estimate.** Substantial structural progress has occurred since the original summary. In particular, BVI is no longer restricted to sub-horizon nonpositivity, and THIM already connects valuation clocks to prime-chain energies.

The six families below organize missing estimates and proposed approaches. They are **not six proved irreducible problems**, and their simultaneous solution is not necessary for RH. Some targets are RH-equivalent; others are stronger, optional, or not yet connected to an RH receiver. No literature audit can establish that an entire proposed discipline has never been developed.

## 1. Corrections that change the research agenda

### 1.1 The Nyman–Beurling tail measure was inverted incorrectly

For the fractional-part functions used in the original formula, the standard space is
\[
H=L^2((0,\infty),dx),\qquad \rho_k(x)=\{1/(kx)\},\qquad \chi=\mathbf1_{(0,1]}.
\]
RH is equivalent to \(\chi\) belonging to the closed span of the \(\rho_k\), with integer \(k\ge1\). This is the [Báez–Duarte criterion](https://arxiv.org/abs/math/0202141).

For a finite coefficient row \(a_{N,k}\), the correctly transformed origin tail is
\[
\int_0^{1/N}\left|\sum_{k\le N}a_{N,k}\{1/(kx)\}\right|^2dx
=
\int_N^\infty\left|\sum_{k\le N}a_{N,k}\{u/k\}\right|^2\frac{du}{u^2}.
\]
The former expression with **both** \(\{1/(kx)\}\) and \(dx/x^2\) instead becomes \(\int_N^\infty|\sum a_{N,k}\{u/k\}|^2du\). Its integrand is periodic. Unless that periodic function is zero almost everywhere, this integral diverges. Also, \(\mathbf1_{(0,1]}\notin L^2(dx/x^2)\). Thus that stated target was invalid, not a difficult open estimate.

**Correct weak-closure principle.** Let \(q_N\in\operatorname{span}\{\rho_1,\ldots,\rho_N\}\). If \(\sup_N\|q_N\|_H<\infty\) and \(q_N\to\chi\) locally in \(L^2([a,b])\) for every \(0<a<b<\infty\), then \(q_N\rightharpoonup\chi\). The closed linear span is weakly closed, so RH follows. Proof: test first against functions supported on such compact intervals, then use their density and the uniform norm bound. This gives strong approximants in the span; it does **not** imply strong convergence of the original rows. A tail bound alone requires separately proved local convergence and control of the rest of the norm.

### 1.2 Selberg damping does not preserve exact divisor cancellation

For \(N>1\), put \(c_{N,d}=\mu(d)\log(N/d)/\log N\). At every integer \(2\le k\le N\),
\[
\sum_{d\mid k}c_{N,d}
=-\frac{1}{\log N}\sum_{d\mid k}\mu(d)\log d
=\frac{\Lambda(k)}{\log N},
\]
not zero. At \(k=1\), the sum is one. Exact cancellation for undamped Möbius coefficients cannot be assigned to the tapered row. The ledger already distinguishes Barban–Vehov's prime-power head from literal Möbius cancellation. See [SelbergMobiusApproximation.lean](../../formal/GaloisForLFunctions/RHTower/SelbergMobiusApproximation.lean) and [BarbanVehovLogarithmicDiagonalAndKerPCauchyPinch.lean](../../formal/GaloisForLFunctions/BiScaleUncertainty/BarbanVehovLogarithmicDiagonalAndKerPCauchyPinch.lean).

### 1.3 The stated Euler-product asymptotic had the wrong order

As written in the original summary,
\[
\frac{\zeta(1+\varepsilon)\zeta(1+2\varepsilon)}{\zeta(2+2\varepsilon)}
\sim \frac{1}{2\zeta(2)\varepsilon^2}\quad(\varepsilon\downarrow0),
\]
not \(1/(2\varepsilon)\). This follows from the residue-one pole of \(\zeta\) at one. The exact drift being estimated must be taken from its actual definition; different Euler factors cannot be substituted for one another.

More consequentially, the current PM/BVI receiver does **not** demand one bound uniform in damping. It demands bounds uniform in the horizon at arbitrarily small fixed positive dampings; those bounds may depend on damping. See §3.1.

### 1.4 Spectral threshold control is not compactness

[CHMDNoWeylAboveThreshold.lean](../../formal/GaloisForLFunctions/RHTower/CHMDNoWeylAboveThreshold.lean), `weyl_value_le_half`, excludes weakly null unit approximate eigenvectors above \(1/2\). It does not assert that the arithmetic resolvent is compact. The infinite-dimensional threshold radical in [CHMDCriticalBandReduction.lean](../../formal/GaloisForLFunctions/RHTower/CHMDCriticalBandReduction.lean), identified with the \(1/2\)-eigenspace by the resolvent dictionary, is incompatible with compactness of that full resolvent.

Likewise, finite multiplicity of each eigenvalue above \(1/2\) does not imply that the entire band \((1/2,1)\) has finite dimension: eigenvalues could accumulate at \(1/2\). A trace argument must establish the relevant projection's trace class property or work on spectral subbands separated from the threshold. The ledger's finite total dimension formula has an explicit finite-off-line-zero hypothesis.

### 1.5 A signed quotient does not inherit every source norm

The signed form descends through `signedRadical`. The original source mass does not: [CHMDQuotientParityAndCoercivity.lean](../../formal/GaloisForLFunctions/RHTower/CHMDQuotientParityAndCoercivity.lean), `not_sourceMass_descends`, proves this obstruction. Use the actual source domain or the canonical quotient representative and specified graph norm. Writing an unspecified Poincaré inequality on `OddSector / signedRadical` does not settle these choices.

### 1.6 Arithmetic detection is not arithmetic exclusion

Valuation clocks detect Ramanujan modes; finite translated moments recover coefficients; inserted off-line waves have positive radial chain excess. None of those facts contradicts the existence of an actual off-line zero. A contradiction needs an independently proved upper bound or sign for the **same complete source energy**.

The precise clock reconstruction is
\[
\Lambda(d)=
\begin{cases}
\log(d/D(d)),&d/D(d)\text{ is prime},\\
0,&\text{otherwise},
\end{cases}
\qquad D(d)=d/\operatorname{rad}(d),\quad d\ge1.
\]
It is not \(\log(d/D(d))\) for arbitrary composites: \(d=6\) already disproves that formula. The conditional statement is proved in [ValuationClockChainBridge.lean](../../formal/GaloisForLFunctions/TransHorizonIncidenceMechanics/ValuationClockChainBridge.lean). The visibility condition concerns a compressed Ramanujan multiplier; it is not a rule saying an individual integer's valuation changes exactly at those lags.

### 1.7 A sharp recovery theorem can miss the arithmetic source stratum

The highest-dyadic local classification in [SieveLocalVisibilityClassification.lean](../../formal/GaloisForLFunctions/BiScaleUncertainty/SieveLocalVisibilityClassification.lean) assumes
\(Y_{N,c}(2^{\lfloor\log_2N\rfloor})\ne0\).
For any coefficient row supported on squarefree integers, \(Y_{N,c}(q)=0\) whenever \(q\) is not squarefree: every multiple contributing to the defining sum has zero coefficient. Consequently the required anchor is zero for every \(N\ge4\). This includes literal Möbius coefficients and their multiplicative tapers. These implications are now formalized in [SieveArithmeticSourceAnchors.lean](../../formal/GaloisForLFunctions/BiScaleUncertainty/SieveArithmeticSourceAnchors.lean). That module also proves that a terminal-prime anchor for a Möbius taper survives exactly when the taper is nonzero; for Barban–Vehov cutoff \(X\), the condition is \(p<X\).

This does not invalidate that classification. It means its highest-dyadic hypothesis excludes these actual sources. The next application needs an appropriate lower-support classification and quantitative constants, not an invocation of the existing theorem without its anchor premise.

## 2. What has already been achieved

The former Section 1 was marked “all done” while retaining obsolete future-tense tasks and some overstrong identification claims. The ledger is the current inventory. Its `[L]` label means committed, umbrella-imported source at its recorded checkpoint, **not a fresh rebuild**.

| Area | Current established result | What remains |
|---|---|---|
| Classical receivers | Mertens/Littlewood connections, RH-to-Cramér mean square, Báez–Duarte equivalences and classical baselines are recorded. | An unconditional arithmetic estimate satisfying a receiver. |
| BVI/THIM trans-horizon control | Exact octave laws, rough checkpoints, finite-band strict defect margins, cofinal sublinear discrepancy, and negative renormalized defects on fixed polynomial windows. | Complete coefficient-weighted energy, including means, endpoints, mixed covariance and growing cutoffs. |
| BVI source laws | Fixed linear-horizon moments, source alphabets, signed one-point frequencies and shifted magnitude laws. | Signed joint estimates at the required moving scales. |
| Arithmetic/analytic bridges | Clock-to-prime-chain identities, exact Fermi/pronic transfers, and common-core signed-form identifications. | Uniform bounds in the receiving norm; common-core identities need not identify completed Hilbert spaces. |
| CHMD | Exact signed quotient, parity decomposition, cardinal spanning/band identification and odd-sector RH criterion. | Actual-source sign excluding sign-changing odd eigenstates above \(1/2\). |
| APT | High-scale restricted-span positivity; critical-envelope prime-channel admission and limiting kernel representations. | Complete-form sign on a sufficiently rich family and control of changing coefficient patterns. |
| BiScale | Sharp finite moment/phase recovery, quantitative stability and explicit infinite-grid/cycle obstructions. | Energy control with horizon-dependent losses paid, plus a source-specific sign. |

BVI's source is not dormant beyond \(N\): for \(N<k\le2N\),
\[
s_{N,\mu}(k)=-\mu(k),\qquad
s_{N,\mu}(k)s_{N,\mu}(k+1)=\mu(k)\mu(k+1)\quad(k+1\le2N).
\]
These identities are already proved in [QuotientDualOctaveReciprocityAndValuationSwitching.lean](../../formal/GaloisForLFunctions/BezoutValuationIncidence/QuotientDualOctaveReciprocityAndValuationSwitching.lean). Trans-horizon effects involve omitted **divisors**, including composites, not just primes larger than the cutoff. The least full period divides \(\operatorname{lcm}(1,\ldots,N)\); \(N!\) is a convenient common period, not the same number.

## 3. Six families of open work, with their logical status

### 3.1 Complete signed trans-horizon energy

**Main receivers:** MC, CTF and PM/FZZ-P. BVI and THIM supply arithmetic interfaces. Connections to other routes require their own stated bridges.

A precise existing sufficient target is
\[
\forall\delta>0\;\exists\varepsilon\in(0,\delta)\;\exists B_\varepsilon<\infty\;
\forall T\ge1:\quad
\mathcal I_\varepsilon(T)
:=\sum_{n=1}^{T}\frac{I_\varepsilon(n)^2}{n(n+1)}\le B_\varepsilon,
\]
where \(I_\varepsilon(n)\) is the literal `pmBezoutInteriorPrefix ε n`. This is exactly the premise of `riemannHypothesis_of_pmBezoutInteriorPronicEnergy_bounded` in [PronicPotentialSelfCancellationAndInteriorGradientConservation.lean](../../formal/GaloisForLFunctions/BezoutValuationIncidence/PronicPotentialSelfCancellationAndInteriorGradientConservation.lean).

**Quantifiers matter:** \(B_\varepsilon\) may diverge as \(\varepsilon\downarrow0\). What is missing is its finiteness uniformly in \(T\) for an arbitrarily small sequence of positive \(\varepsilon\). A theorem asserting an \(O_\varepsilon(1)\) difference between two uncontrolled quantities does not supply this bound.

**Known baseline:** the actual PM source is already in \(L^2\) for every
\(\varepsilon\ge1/2\), including equality, by
[PMPowerDampedMobiusEndpoint.lean](../../formal/GaloisForLFunctions/RHTower/PMPowerDampedMobiusEndpoint.lean).
Its horizon-uniform discrete budget, together with
\(\mathcal I_\varepsilon(T)\le2E_\varepsilon(T)+1/2\), gives the now-exposed
`exists_pmBezoutInteriorPronicEnergy_budget_of_half_le` in the receiver module.
The open range is \(0<\varepsilon<1/2\), ultimately cofinal at zero. A uniform
bound in natural Ramanujan cutoff \(Q\) is a separate sufficient approximation
condition; it does not follow merely from this source-energy endpoint.

**Use the actual weights:** the PM Selberg coordinate is
\(Y_\varepsilon(q)=\operatorname{Re}\sum_{m\ge1}\mu(qm)(qm)^{-1-\varepsilon}\),
not \(\mu(q)q^{-\varepsilon}\). For prime \(p\), \(p\nmid r\), and
\(\varepsilon>0\), it satisfies
\(Y_\varepsilon(pr)=-Y_\varepsilon(r)/(p^{1+\varepsilon}-1)\).
See [RoutePMCofactorSieveBridgeAndUnifiedEnergyEquivalence.lean](../../formal/GaloisForLFunctions/BezoutValuationIncidence/RoutePMCofactorSieveBridgeAndUnifiedEnergyEquivalence.lean)
and [CrossDepthEulerOperatorFactorizationAndPrimePairGramIdentity.lean](../../formal/GaloisForLFunctions/BezoutValuationIncidence/CrossDepthEulerOperatorFactorizationAndPrimePairGramIdentity.lean).
Restricted prime-head identities do not give a scalar recursion for the complete variance.

Alternative CTF target: construct admissible rows satisfying the corrected weak-closure principle in §1.1, or prove vanishing Nyman error directly. Do not conflate those different sufficient criteria.

**Research mechanism, not established theorem:** retain signed cross-depth coupling before taking absolute values; isolate and estimate the complete log-renormalized remainder. Positive active-pair drift, shared-birth covariance, conditional-head means and signed clock complements cannot be discarded. Uncentered active-pair budgets are already known to diverge in the relevant small-damping regime.

The first-octave identity above explains a second boundary: a complete signed successor law would confront fixed-shift Möbius correlations of Chowla type. Magnitude-pattern laws do not supply it. Such a full law is not known to be necessary for the one-sided complete-energy bound; it may be an unnecessarily strong research target.

This is not a claim that every binary correlation problem remains unsolved in current literature. The September 2026 preprint [Ordinary two-point correlations of multiplicative functions](https://github.com/openai/math/blob/main/preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/final.pdf) claims qualitative ordinary Möbius cancellation for fixed affine forms. Its statements were inspected, but its proof was not independently verified in this review. They do not assert the growing-coefficient uniformity or quantitative Möbius rate required for the present complete-energy application.

### 3.2 Complete odd-sector arithmetic positivity

**Main receivers:** CHMD, RW, OWU and related Weil/screw/passivity formulations.

The precise source-domain criterion is
\[
\mathcal E_{\rm arch}(v)+\sum_{n\ge0}\int_{\mathbb R}\phi\mathrm{DoobPrimeJump}(v,n,x)\,dx
\ge \phi\mathrm{DoobCoshMass}(v^2)
\]
for every odd compactly supported \(C^2\) real test \(v\). See [WeilPhiDoobArchimedeanJumpAndHalfLineFolding.lean](../../formal/GaloisForLFunctions/RHTower/WeilPhiDoobArchimedeanJumpAndHalfLineFolding.lean), `riemannHypothesis_iff_forall_odd_phiDoob_dirichlet_poincare`. This criterion is **RH-equivalent**, not a smaller solved spectral task.

The prime-chain factorization is valuable but gives positivity of one contribution. The complete comparison still includes the ground/polar potential, reflected-prime terms and nodal coupling. Modulus contraction changes the parity constraint; quotienting a radical removes degeneracy, not negative directions.

**Research targets:** an independently quantified bound on the remaining low-prime diagonal potential after exact collar cancellation; or an actual-source nodal estimate that pays the primitive ground-projection defect. Every support radius and rapidity dependence must be retained. The `coshSinhPolarRatio ≤ θ ≤ 1` absorption condition and its residual source pairing are not automatically satisfied.

A source-defined factorization \(L-1=Q^*Q\) would suffice on the correctly specified domain. Defining \(Q\) as a square root after assuming positivity is circular. Finite off-line chain excess alone supplies no contradiction.

### 3.3 Source families that retain both sign information and limit control

**Relevant programs:** APT and BiScale; relevant receivers include RW, EWU and OWU.

Factorial families already have strong unconditional positivity and approximation results. Positivity on those restricted families is compatible with either truth value of RH. A new family must either reach a dense admissible test class in a topology controlling the complete Weil form, or carry a proved separating property for hypothetical negative directions.

Single-autocorrelation prime-blind synthesis is **one optional strategy**, not a missing theorem every RH proof needs. A difference of autocorrelations cannot be used as a single positive-definite autocorrelation. Conversely, the known no-go results concern specified families; they do not forbid every possible prime-blind construction.

**Research targets:** complete critical-envelope form estimates, quantitative approximation errors for growing patterns, and a compactness or profile decomposition that accounts for origin concentration, distant polar mass and increasing oscillation. Scalar pointwise convergence, finite moment recovery and bounded unweighted \(L^2\) mass are insufficient by themselves.

### 3.4 Scale-sensitive signed correlation and transport

**Relevant receivers:** MC and prime-deficit/prime-history routes; other transfers must be checked individually.

The obstacle is preserving cancellation under the actual weights, truncations, transformations and scale growth. An additive phase estimate cannot be transported to a logarithmic phase without paying the transformation kernel, any stationary points and residues. Some existing isolation methods lose too much under zero clustering; that is a limitation of those methods, not a universal impossibility theorem about all linear arguments.

**Research targets:** a quantitative signed bilinear estimate for an already defined source remainder, or a cluster-level comparison retaining all cross terms. Valuation-clock recovery can identify finite arithmetic data but does not itself perform the required cancellation or bypass an analytic saddle.

An existing concrete receiver is the one-sided subpower bound for the strict off-diagonal additive Möbius triangle in [MobiusAdditiveTriangleChowlaFrontier.lean](../../formal/GaloisForLFunctions/RHTower/MobiusAdditiveTriangleChowlaFrontier.lean). It must be proved from arithmetic, not reintroduced as a renamed independence assumption.

### 3.5 Conditioned recurrence and tails

**Main receiver:** BAG.

Finite Kronecker return and unconditional mean-square control do not automatically give a small **centered** tail on the same return heights, uniformly on the required right-strip disc. The centering, head approximation, cutoff and order of limits are part of the problem.

If a conditioning event has density \(\kappa\), an unconditional mean-square estimate \(A_N\) yields only the generic conditional bound \(A_N/\kappa\). The previous claimed necessity \(N\gg\exp(\delta^{-\pi(P)})\) was unsupported. Even the schematic bound \(A_N\asymp N^{1-2\sigma}\) would instead lead to \(N^{2\sigma-1}\kappa\to\infty\). For \(\kappa\asymp\delta^{\pi(P)}\), this is a different scale. It is not a proof that such an estimate is available for the actual centered tail.

**Research target:** a conditional tail estimate with all parameters stated, sufficient for the existing common-height recurrence receiver. Polynomial cutoff in \(P\) is an additional proposed ambition, not an established necessary condition or a theorem supplied by BVI observability.

### 3.6 All-degree positivity, phase orientation and geometric realization

**Relevant routes:** TH, TT, HCF, WD, XN and several geometric/candidate routes, each with its own receiver.

Fixed-degree positivity at sufficiently large shift is not positivity at all degrees with a common admissible parameter. Forward heat flow, functional-equation symmetry and finite positive matrices do not provide the missing global orientation.

A pole-deflated Lee–Yang theorem is **speculative**. The former assertion that real-rootedness holds “if and only if” coefficients satisfy \(\Lambda(p^r)=\log p\) had no specified class of partition functions or hypotheses and is not a valid theorem statement. Ordinary arithmetic multiplicativity does not by itself establish a positive Hilbert realization or the required complete-form sign.

**Research targets:** source-defined all-degree bounds on the actual moment matrices, or a concrete arithmetic interaction/domain construction with a proved limit to the actual completed function. Distinguish finding an independent producer from building another equivalent determinant or operator model.

## 4. What kind of new mathematics is actually needed?

**The shared deficit is a source-specific signed estimate that survives the required scale limits.** Existing work supplies identities, finite classifications, conditional transfers and useful counterexamples. It does not yet supply that estimate.

THIM already implements much of the original proposal to connect continuous and discrete structures. Starting another umbrella under “valuation-clock spectral theory” would repeat its remit. The productive division is:

| Program | Next mathematical responsibility |
|---|---|
| Arithmetic Positivity Theory | Bound the complete critical form, including cross terms and polar terms, for explicitly specified growing source families. |
| BiScale Uncertainty | Quantify the observation/approximation loss in the norm required by that form; classify and account for escaping profiles. |
| Bézout–Valuation Incidence | Extract and estimate the literal signed remainder on changing cutoffs; separate magnitude information from sign information. |
| Trans-Horizon Incidence Mechanics | Prove the transfer estimate with all cutoff, damping, boundary and coefficient costs paid; retain the exact receiver quantifiers. |

These responsibilities suggest research directions, not a proof that one unified theory will solve all six families. A new program warrants its own identity only after it produces a distinct, falsifiable theorem beyond these remits and survives comparison with established harmonic analysis, sieve/correlation methods and arithmetic spectral approaches.

## 5. Constraints that survive this correction

1. Never replace the complete signed energy by a positive component or an unsigned majorant without a quantitative error bound.
2. Never infer a cofinal estimate from fixed horizon ratios, fixed coefficient patterns, finite observation sets or fixed damping identities alone.
3. Never infer absence of negative directions from self-adjointness, nondegeneracy, injectivity, finite-dimensional recovery or a spectral threshold statement.
4. Keep countermodel hypotheses exact. Shifted zeta products change poles/completion data; Beurling systems share much multiplicative algebra. These refute specified implication attempts, not every argument using an explicit formula or an Euler product.
5. Scope no-go results to their proved mechanism and retain their positive survivors. Universal finite cones, sharp conditioning laws and exact decomposition identities remain useful even when a proposed RH shortcut fails.
6. Record the first unproved arithmetic inequality explicitly. A bridge, a reformulation and a new source estimate are different achievements.
