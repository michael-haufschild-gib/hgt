# RH research: consolidated mathematical assessment

7 November 2026

The research has substantially solved **representation, source matching, finite-scale control, and classification of failed mechanisms**. It has not yet supplied an arithmetic estimate that closes an RH-complete family. The remaining difficulty is more specific than “prove positivity”: preserve the actual prime arithmetic through growing scales, signed cross terms, exceptional returns, and limiting operations, with enough quantitative control to exclude every off-line zero.

There is no complete proof path to quasi-RH in the material examined. There is a particularly concrete route to 70%, with an actual finite-height prime statistic and an explicit sufficient bound, but that bound remains open. My preferred intermediate structural question is the asymptotic abscissa law, equivalently exclusion of a finite leading oscillation of the prime error. Under the stipulated ban on positivity and spectral methods, my preferred quantitative question changes: obtain cancellation of the Möbius sum beyond the Vinogradov–Korobov exponent by direct arithmetic means, while stopping short of a fixed power saving.

## Basis and conventions

This assessment uses the six requested reports, the programme list in its stated chronological order, corpus searches, and inspection of the resulting Lean declarations and mathematical arguments. Linked programme READMEs and other Markdown sources were not consulted. No builds, web searches, or proof-integrity audits were performed. “Established” below describes results present in the inspected corpus; it does not claim a new compilation audit. Proposed questions and methods are identified as proposals.

Write

\[
\Theta=\sup_{\zeta(\rho)=0,\ 0<\Re\rho<1}\Re\rho,
\qquad
\Theta_\infty=\inf\{\sigma\ge\tfrac12:
\#\{\rho:\Re\rho>\sigma\}<\infty\}.
\]

Multiplicity does not affect finiteness here. **Quasi-RH** means a fixed zero-free half-plane inside the strip: \(\Theta<1\), equivalently all nontrivial zeros lie in \(\Re\rho\le\tfrac12+\alpha\) for some \(\alpha<\tfrac12\). It does not mean “RH except for finitely many zeros.” The 70% question means an asymptotic lower proportion, with multiplicities in the denominator; a lower bound for simple critical-line zeros is stronger.

## 1. Big picture: what has been solved, and what remains

### 1.1 What the chronological programmes reveal

The programme list records a mathematical progression, including deliberate returns to earlier programmes. Its main movement is from finding a representation of the desired sign to identifying the arithmetic information that representations fail to retain.

| Chronological phase | Mathematical contribution | Frontier exposed |
|---|---|---|
| Arithmetic positivity, bi-scale uncertainty, trans-horizon incidence, Bézout valuation, criticality and square-root threshold | Exact prime channels, source regularization, incidence decompositions, quantitative uncertainty and depth bounds | A favorable channel or diagonal does not decide the complete source; growing scales matter |
| Compensation, Castelnuovo–Severi, signed energy, trans-threshold correlation, orientation and local divisor geometry | Complete signed arithmetic forms; quantitative census receivers; identification of missing mixed terms | Unsigned counts lose precisely the cancellation needed at the critical scale |
| Biarithmetic geometry, multiplicative positivity, duality, Künneth, correspondence, polarization and effectivity | Many exact translations of the same form; finite-field calibrations; height and count criteria | An abstract Hodge or effectivity law can merely restate the desired sign; a count over the integers is still needed |
| Renormalized potentials, spacing-scale analysis, Gabor pinching, index descent and selective multiscale methods | Explicit subtraction laws, better critical-line census, finite-index and multiscale receivers | Finite rank, finite index and typical behavior require separate uniformity or recurrence inputs |
| Square-root precision, critical correlation, completed forms, gauges, harmonic analysis and degeneration | Necessary conditions on any deciding arithmetic input; source/domain closure; conductor and cross-scale structure | Integrality, local positivity and formal completion do not manufacture the missing precision |
| Window cohomology, window towers, canonical systems, growing windows and signed criticality | A common window object, exact precontact dynamics, unconditional critical regimes and local sign tests | Extension to every aperture; control through contact; full Schur payment at arbitrary critical ratios |
| Zero configurations, arithmetic production, Hardy cones, finite-free probability, inner functions and auxiliary dynamics | RH split into two logically different assertions; rigid alternatives; exact rate dictionaries | The remaining input is a quantitative arithmetic theorem, not another equivalent criterion |
| Scattering, metaplectic descent, nodal flow, prime torus, rigid cuts, tail arithmetic and sum-product arithmetic | Actual realizations, nonzero cubic residue, exceptional-tail laws, return-time bounds, exact arithmetic selection and count rigidity | Transfer to actual Möbius/prime cancellation; atypical tails; fixed-precision returns; integer arithmetic beyond the known cancellation range |

This is substantial progress. It has removed many ambiguities about *which object* must be controlled and *which discarded term* could carry a counterexample. The number of named routes consequently overstates the number of independent mathematical mechanisms. The ledger's “38 formulations, 9 candidates” is a checkpoint inventory, not 47 independent chances of success.

### 1.2 Three cores, with a useful limitation on unification

The three-core organization remains sound:

* **Σ: complete window sign.** Control the full arithmetic form at every aperture, including Gamma, poles, primes, and mixed terms.
* **Π: prime precision and production.** Obtain sufficiently strong cancellation or a genuinely arithmetic count/producer with the required error.
* **Γ: selection and recurrence.** Distinguish the actual zeta function from admissible models and exclude exceptional zero configurations that survive average estimates.

There are genuine identities between many readings: the window form, its lattice restrictions, Hardy bands, canonical contact, and several index or inner-factor quantities. There are also routes connected only because both endpoints are equivalent to RH. The latter connection transfers truth, **not an estimate or a proof mechanism**.

The “dark range” is a useful common diagnosis: conditioning on a growing prime head, long Dirichlet polynomials, and near-unit mollifiers all demand information beyond the range of present diagonal estimates. But the corpus does not establish that every route must pass through one identical dark-range theorem. Similarly, an independent count would solve several geometric formulations; it is not proved that every conceivable RH proof must construct such a count.

### 1.3 The most informative global split

The exact split is

\[
\boxed{\mathrm{RH}\iff\mathrm{ZAL}\ \wedge\ \mathrm{AAL}}.
\]

Here:

* **ZAL:** for every \(h>0\), only finitely many zeros satisfy \(\Re\rho>\tfrac12+h\). Thus \(\Theta_\infty=\tfrac12\).
* **AAL:** for every \(h\ge0\), a finite set of zeros to the right of \(\tfrac12+h\) must be empty. Thus \(\Theta=\Theta_\infty\).

ZAL controls zeros at unbounded height. AAL excludes a finite exceptional layer farther right than the persistent population. They address different defects. AAL still allows infinitely many off-line zeros, even zeros approaching \(\Re s=1\); it gives no fixed strip on its own. ZAL permits finitely many off-line exceptions but already implies quasi-RH and Lindelöf. [Exact split](../../../formal/GaloisForLFunctions/RHTower/ZetaWeakRecurrenceLadderCollapse.lean), [ZAL consequences](../../../formal/GaloisForLFunctions/RHTower/LindelofCosineFiniteDefectDepth.lean).

The failure of AAL has become unusually rigid: a finite separated extremal layer, \(\Theta<1\), and a finite leading oscillation of \(\psi(x)-x\). Consequently

\[
\neg\mathrm{AAL}\Longrightarrow\mathrm{quasi\!-!RH}\land\neg\mathrm{RH},
\qquad
\mathrm{quasi\!-!RH}\ \vee\ \mathrm{AAL}.
\]

The disjunction is a deduction, not a way to choose its first branch. Proving AAL would leave ZAL open. Disproving AAL would itself falsify RH. [Finite-oscillation equivalence](../../../formal/GaloisForLFunctions/ZeroConfigurationGeometry/TheOneOffsAreFiniteOscillationsOfThePrimeError.lean), [rigidity](../../../formal/GaloisForLFunctions/ZeroConfigurationGeometry/PrimeErrorFiniteOscillationRigidityAndSignChanges.lean).

### 1.4 Hard obstacles genuinely overcome

**Exact realization and matching.** Many former “find the right object” problems have been solved: complete source identities, lattice/window equivalence, precontact canonical systems, several heat/cosine/Jensen receivers, and physical scattering realizations carrying the actual divisor. These are mathematically useful because missing information can now be located in a precise term, domain, limit, or inequality. Realization alone does not give the required sign or damping.

**Subcritical and one critical matrix regime.** For the tilted-spline family, the complete matrix is positive in every subcritical range \(c\le(\log N)^\alpha\), \(\alpha<1/8\), and through one fixed small multiple of \((\log N)^{1/8}\). This includes complete Schur payment. At every fixed ratio \(R=c^8/\log N\), a growing low-conductor packet through \(\lfloor(\log N)^{13/32}\rfloor\) retains a positive diagonal and its signed polar part. There is an explicit interval of ratios with complementary coercivity. These are genuine uniform results, stronger than positivity of a fixed finite collection of test vectors. [Critical matrix result](../../../formal/GaloisForLFunctions/CriticalArithmeticCorrelationTheory/CriticalMultipleCompleteWeilPositivity.lean), [low packet](../../../formal/GaloisForLFunctions/CriticalArithmeticCorrelationTheory/TheCriticalLowPacketRetainsItsSignedPolarPart.lean).

**Localization of the remaining matrix difficulty.** Current source develops all-ratio Gårding bounds and confines nonpositive directions to a top logarithmic window. The resulting inequality still contains a collar \(L^2\) debit. Localization narrows the unknown sign; it does not settle it. The associated conductor-first splitting is consequential: a physical prefix/collar split retains a nonvanishing Schur interaction. [Top-window analysis](../../../formal/GaloisForLFunctions/CriticalArithmeticCorrelationTheory/NegativeDirectionsCannotEscapeLogarithmicWindows.lean), [splitting obstruction](../../../formal/GaloisForLFunctions/CriticalArithmeticCorrelationTheory/PrefixCollarSchurObstructionAndFarDecoupling.lean).

**Canonical dynamics up to contact.** The Hamiltonian, absolute continuity, soft prime kicks and reflection dynamics are constructed before contact. The exact scalar criterion is now a Lean theorem:

\[
\mathrm{RH}\iff\Psi=\tfrac12\log H_1
\text{ is bounded on each finite interval of the precontact domain}.
\]

The quantifier includes approaching a hypothetical finite contact. A bound on each compact set strictly inside the precontact interval is weaker. The remaining task is an arithmetic bound that survives that approach. [Canonical potential criterion](../../../formal/GaloisForLFunctions/ArithmeticInnerFunctionTheory/ThePotentialIsLocallyBoundedIffRH.lean).

**Finite-rank and census progress.** The corpus has full-theta finite-rank results, central PF and Li rungs, and a critical-line census stronger than older conventional benchmarks: at least \(0.67250071-o(1)\) of all zeros are simple and on the line. The last result is discussed precisely in §4. Finite-rank progress is valuable, but a sequence of separately proved rungs is not an all-rank argument.

**Exceptional configurations are classified.** Failure of AAL forces a unique leading prime-error profile, a sharp remainder gap, prescribed coefficients, and persistent long-shift prime correlations after the diagonal and short shifts have vanished. This is substantially more informative than “a sparse exceptional set might exist.” It gives arithmetic signatures to attack. [Rigidity](../../../formal/GaloisForLFunctions/ZeroConfigurationGeometry/PrimeErrorFiniteOscillationRigidityAndSignChanges.lean), [persistent correlations](../../../formal/GaloisForLFunctions/ZeroConfigurationGeometry/FiniteExceptionalLayersForcePersistentLowJets.lean).

**Several older entries need narrower or updated wording.**

| Older unresolved face | Current source | What remains |
|---|---|---|
| Nonvanishing of the cubic Eisenstein residue | `cubicEisensteinResidue_ne_zero`; the residue and its \(8/9\) eigenrelation are constructed | Rational-integer Möbius transfer and the arithmetic coefficient estimate |
| Potential boundedness only recorded as a deduction | Explicit `riemannHypothesis_iff_canonicalPotential_locallyBounded` | Prove the bound from arithmetic |
| Calibration beyond genus one | Actual odd-degree squarefree hyperelliptic curves over finite fields of odd characteristic, in every genus; point-count identity, effectivity and naive heights | Transfer over \(\mathbb Z\); this is not a construction for every proposed arithmetic surface |
| Bounded-error positive integer-norm countermodels | In the discrete positive integer-norm class, even count error \(o(\log n)\) forces the rational-prime system | Larger error classes and the relation between count discrepancy and new zeros |
| Sparse lag control phrased using finite-measure exceptional sets | Abel-density-zero excursion receivers, plus upper/lower-density refinements | Prove the required excursion estimate for the actual source |

Sources: [cubic residue](../../../formal/GaloisForLFunctions/MetaplecticMobiusDescent/TheCubicResidueIsNonzero.lean), [hyperelliptic calibration](../../../formal/GaloisForLFunctions/ArithmeticEffectivityTheory/TheHyperellipticCalibration.lean), [logarithmic count floor](../../../formal/GaloisForLFunctions/SumProductArithmeticOfTheLogarithm/LogarithmicCountFloor.lean), [lag excursion refinements](../../../formal/GaloisForLFunctions/RHTower/WeilLagFunctionDensityZeroExcursion.lean).

### 1.5 The remaining walls

| Wall | Exact missing mathematics | Why a nearby result does not cross it |
|---|---|---|
| All-aperture sign | Pay the complete signed form on every window; equivalently prevent finite contact | A single critical multiple, a fixed rank, or a finite aperture does not exhaust the family |
| Critical coupling | Control growing conductors, coalescing frequencies and the low/complement Schur term after retaining both poles | A positive low block and a positive far block need not make their coupled matrix positive |
| Uniform arithmetic precision | A fixed power saving for quasi-RH; square-root precision for RH | VK savings remain subpower; rate/producer dictionaries preserve this limitation |
| Exceptional-tail selection | Control actual Euler tails on the atypical returns relevant to right zeros | Typical Gaussian-type estimates and positive-density universality avoid precisely those zero-bearing targets |
| Independent count or height | Construct a concrete arithmetic quantity with controlled difference from the complete quadratic form | Defining a “height” from the form, or assuming the needed Riemann inequality, only moves the premise |
| Exact-line census | Bound a signed trans-threshold prime surplus, or eliminate a sufficiently large simple near-line off-line core | Small depth and low multiplicity are not membership in the line |
| AAL / ZAL | Exclude isolated extremal layers / force persistent zeros toward the line | Neither implication follows from the other; average depth estimates can miss both the last exception and zeros extremely close to the line |

Two concrete traps deserve emphasis. First, the particular certified floor tower freezes below \(0.3621\); it is not an aperture exhaustion. Second, the terminal polar corrector has a nontrivial zero-source kernel. Improving that corrector alone cannot settle directions on which its gain is identically zero.

The prime-tail obstruction is especially sharp. With \(M_y\) the finite Euler mollifier, \(\zeta M_y\) has exactly the same zeros as \(\zeta\) in \(\Re s>0\). A return to a target containing a right zero is tail-bad at **every** finite cut, with a cut-independent tolerance, and such returns have density zero. Conversely, nonvanishing targets on the prescribed discs have positive-density universality. Thus ordinary typical-tail estimates cannot be silently upgraded to the exceptional recurrence needed by AAL. [Tail dichotomy and its scope](../../../formal/GaloisForLFunctions/TailArithmeticOfThePrimeOrbit/TheQuestionsOfTheField.lean).

### 1.6 What the killed routes actually teach

The no-go results eliminate specified mechanisms, not whole branches of mathematics.

* **Separate positive factors fail; complete signed gluing survives.** Finite Euler heads and separate semilocal factors can have large negative index. This does not prove negativity of the complete zeta form. The positive survivor is the exact joint decomposition, with its original Gamma and polar reserves.
* **A generic wave or Hecke system does not select zeta.** Even functional equation, unitarity and Hecke structure admit countermodels with incorrect damping in the stated graph class. Actual finite-field point counts supply an additional law. The lesson is to identify the arithmetic law missing from the model, not to infer that all spectral mathematics is impossible.
* **Integrality does not create the desired precision.** Fixed factorial and divisibility constructions have sharp size or multiplicity barriers. Their survivors identify the required producer: arithmetic, parity-sensitive, and quantitative at growing scale.
* **Finite or typical information cannot select an infinite exceptional object.** Finite prime agreement, typical hull behavior, and finite readings of an effectivity cone leave too much freedom. Exact count and floor identities can distinguish systems, but distinguishing a system is not yet estimating its cancellation.

The current count results illustrate the last distinction well. Nonclassical discrete positive integer-norm systems have logarithmic discrepancy arbitrarily far out, whereas a positive near-count example has a precise nonzero Riesz deficit of order \(X\log X\). The latter example preserves zeta's right-half-plane zeros through its Euler factor; it is not an off-line-zero counterexample to RH. [Count rigidity](../../../formal/GaloisForLFunctions/SumProductArithmeticOfTheLogarithm/CountDistanceRigidity.lean), [exact near-count average](../../../formal/GaloisForLFunctions/SumProductArithmeticOfTheLogarithm/PositiveNearCountExactAverage.lean), [Euler factor](../../../formal/GaloisForLFunctions/SumProductArithmeticOfTheLogarithm/PositiveNearCountEuler.lean).

### 1.7 Proof versus falsification

The representation work helps both directions. A rigorously negative value of the **complete actual** Weil form on an admissible test would falsify RH. So would a certified off-line zero. The localized critical matrices and finite-oscillation alternative provide structured places to look for such an obstruction.

No inspected result supplies that witness. Negative isolated channels, countermodels, hypothetical nullvectors, or negativity of a truncated Euler system do not falsify RH. Conversely, eliminating those artifacts does not prove it. The current corpus sharpens the decision problem without deciding it.

## 2. Opportunities for substantial progress

I see several opportunities with clear mathematical outputs. Their value lies in reducing a genuine unknown or producing a quantitative estimate, rather than adding another RH equivalence.

### 2.1 Use the stronger actual cosine census receiver

The most concrete numerical target is now the signed surplus of the actual cosine prime Gram. Its diagonal, trace, zero-side bridge and pinching credit are matched for fixed bandwidth through two. At bandwidth \(4/3\), a bound of \(0.1132N+o(N)\) for this surplus would give 70%; §4 states the exact normalization.

This is attractive because it asks for one finite quantitative improvement. It does not require an all-aperture sign theorem. The remaining work must preserve the signed cross terms and the same profile on both sides. An unsigned sieve estimate for a superficially similar sum is not a substitute.

### 2.2 Attack AAL through source-forced excursions

The new lag results change the role of averages. A generic density estimate can miss a single zero. But the actual lag source forces an attained off-line top to generate a positive-density family of large excursions. Thus an appropriate density estimate for this source can exclude an isolated extremal layer.

A precise sufficient input already in Lean is: for every \(a>0\), there exist \(M\) and an Abel-density-zero set \(E\) such that

\[
\Phi(L)\le M e^{aL}\qquad(L\ge0,\ L\notin E).
\]

Here \(\Phi\) is `weilLagFunctionReal`, not a freely chosen surrogate. This implies AAL. It is a one-sided bound and permits exceptional scales; it is not a uniform RH bound. It actually excludes an attained top, a condition stronger than merely excluding a finite isolated top. [Exact receiver](../../../formal/GaloisForLFunctions/RHTower/WeilLagFunctionDensityZeroExcursion.lean).

**Opportunity:** derive this excursion law directly from the arithmetic expression, or first obtain a quantitative excursion bound for a restricted depth range. **Unresolved:** every useful estimate must retain enough source information; the receiver supplies no such estimate itself.

### 2.3 Study the long correlations forced by a finite exceptional layer

Under failure of AAL, the corpus produces a genuine extremal zero \(\rho=\beta+i\gamma\), multiplicity \(m>0\), and

\[
a_{k,n}=\frac{\Lambda(n)(\log n)^k}{k!\,n^{\rho+1}}
\]

with

\[
\sum_n a_{k,n}\longrightarrow-m,\qquad
\sum_n|a_{k,n}|^2\longrightarrow0,\qquad
\Re\sum_{n\ne j}a_{k,n}\overline{a_{k,j}}\longrightarrow m^2.
\]

More strongly, subtracting all additive shifts \(h\le\lfloor r^k\rfloor\) still leaves the same limit whenever \(1<R<\beta+\tfrac12\) and \(0\le r<R^2\). Proper prime powers can also be removed. The hypothetical obstruction must live in a specified long-shift prime correlation, not on the diagonal or among the already-paid short shifts. [Exact statements](../../../formal/GaloisForLFunctions/ZeroConfigurationGeometry/FiniteExceptionalLayersForcePersistentLowJets.lean).

**Opportunity:** classify possible persistent long-shift limits for these moving logarithmic weights. Excluding the finite-layer pattern would give AAL. A weaker classification that locates an indispensable family of shifts would still concentrate several programmes on one arithmetic object.

**Boundary:** a vanishing diagonal does not imply a vanishing sum. The corpus also has the real-center case \(s=2\), where the normalized sum tends to \(1\) while its diagonal tends to zero. Any proposed argument that excludes this case for the same reason is invalid. A blanket cancellation theorem for every complex center may also be much stronger than the intended AAL target.

### 2.4 Improve the critical window theorem without pretending to solve all ratios

At fixed \(R\), localization identifies a finite logarithmic window and a specific residual coupling. A useful next theorem would extend the interval of ratios with a paid collar debit and complete Schur bound, or prove compactness for actual critical minimizing sequences with the required prefix control.

Such a theorem would be real partial progress. It must control the original complete energy, not a physically torn approximation. Increasing \(N\) does not make fixed losses in \(R\) and \(R^2\) disappear. Iterating a fixed-aperture result also does not create a cofinal aperture sequence unless the aperture growth is proved.

### 2.5 Move from finite-tail moments to exceptional-tail transport

The conditional-tail theorem is strong but has a visible boundary. If a smooth head polynomial and the \(k\)-th tail moment together have arithmetic length at most \(N\), then the moment has a Gaussian-type upper bound with an error of size \(N\log N\). It is useful when this is small relative to the averaging height \(T\). It is not a theorem that the infinite Euler tail has a Gaussian conditional law at arbitrary head resolution. [Conditional moments](../../../formal/GaloisForLFunctions/TailArithmeticOfThePrimeOrbit/TheConditionalMomentsOfTheTail.lean).

Two possible advances would be significant:

1. A conditional estimate for a growing head beyond that length boundary, with an explicit residual term small enough for a named receiver.
2. An existence or transport theorem for the rare bounded returns on right-edge discs that matter to AAL, despite their zero density.

The first-return results give a separate foothold. The square-root exponential lower bound is available at precision of order \(y^{-9/2}\), not at fixed precision. Proportional saving requires control of returns on subsets carrying most of the weight. Full-set nonalignment does not automatically control those subsets. The moving logarithmic jet bounds and the smooth-integer comb are plausible tools for narrowing this gap. [Current six questions and tools](../../../formal/GaloisForLFunctions/TailArithmeticOfThePrimeOrbit/TheQuestionsOfTheField.lean).

### 2.6 Make the new constructions produce arithmetic

The nonzero cubic residue changes the metaplectic task. Re-proving nonvanishing would add nothing; the next useful object is an explicit arithmetic coefficient or transfer identity connecting this residue to rational-integer Möbius cancellation, with every conductor and archimedean loss retained.

Likewise, the hyperelliptic calibration shows how an actual count can supply the desired law. Its transfer to integer arithmetic must identify the set or height being counted and prove the comparison error. A quadratic form renamed as a count does not cross that wall.

These two opportunities are less mature as routes to a numerical theorem than the census surplus target. Their potential value is a genuinely new arithmetic input.

## 3. Is there a clear path to quasi-RH?

**No complete path is currently established. There are exact targets, but no independently proved input reaching one of them.**

The clean arithmetic target is a fixed power saving

\[
|M(x)|\ll x^{1-\sigma}\qquad\text{for some }\sigma>0,
\]

or the corresponding Liouville bound, with the usual slack in exponent when passing between growth and zero-free statements. This is qualitatively stronger than every stretched-exponential saving \(x\exp[-c(\log x)^\nu]\) with \(\nu<1\).

The auxiliary-dynamics programme now makes the distinction explicit. Existence of a polynomial stencil rate is equivalent to existence of a Mertens power saving. The equivalence is arithmetic, not obtained by assuming a zero-free strip. Quantitative exponents have losses: one theorem sends rate \(K^{-a}\) to each Mertens saving \(\sigma<a/2\). Thus a proposed fast stencil is a possible *construction of* the missing cancellation, but its rate is not an easier independent fact merely because it uses different notation. [Rate dictionary](../../../formal/GaloisForLFunctions/ArithmeticAuxiliaryDynamics/TheRateAndTheMertensScaleCoincide.lean), [Liouville exponent dictionary](../../../formal/GaloisForLFunctions/RigidArithmeticOfCuts/TheParityExponentIsTheZeroAbscissa.lean).

Other exact targets include a ground-energy floor with exponent strictly below the strip endpoint, a suitable ringdown gap, or a sufficiently strong cosine/heat width bound. The missing quantitative input persists under those translations.

There are three qualifications that prevent false shortcuts:

* **ZAL would suffice**, even though it permits finitely many exceptions. Take a positive depth below \(1/2\): the remaining tail is confined, and the finite exceptions each have real part strictly below one. But ZAL is itself an unresolved strong assertion.
* **Failure of AAL would suffice**, while falsifying RH. The finite-layer theorem gives \(\Theta<1\). The disjunction “quasi-RH or AAL” provides no estimate in the AAL branch.
* **Cosine and heat deformation have different information content.** The converse from an all-real cosine shift below half-width to quasi-RH is stated under Lindelöf in the relevant source. Positive-time heat finite-defect results are unconditional and do not supply that missing hypothesis or the corresponding cosine conclusion. [Cosine threshold](../../../formal/GaloisForLFunctions/RHTower/LindelofQuasiRHCosineThreshold.lean), [finite-defect distinction](../../../formal/GaloisForLFunctions/RHTower/LindelofCosineFiniteDefectDepth.lean).

The most credible incremental programme is therefore to demonstrate a new arithmetic cancellation mechanism at a scale strictly beyond VK before claiming a fixed strip. That would still leave quasi-RH open, but would test whether the new machinery improves the arithmetic input rather than only translating it.

## 4. Is there a clear path to at least 70% on the line?

**There is a clear quantitative target, closer to a usable research problem than the present quasi-RH targets. There is not yet a proof of its missing estimate.**

### 4.1 Current unconditional baseline

The corpus states

\[
\forall\varepsilon>0,\quad
N_{0,\mathrm{simple}}(T)\ge
(0.67250071-\varepsilon)N(T)
\quad\text{for all sufficiently large }T.
\]

The stronger symbolic bound is \(H_D(1)+10^{-8}\), where

\[
H_D(1)=\frac32-\frac{1}{\sqrt2}\cot\frac1{\sqrt2}
=0.672500703679\ldots.
\]

This is an actual zeta census, including cumulative and native completed-\(\xi\) formulations. The improvement comes from incompatible triple configurations in the cosine kernel: a positive proportion of suitable triples cannot make every pair orthogonal, so the rank/energy inequality retains a nonzero credit. The proved credit is small; its existence is a new mechanism, not evidence that its constant can automatically be enlarged to 70%. [Census theorem](../../../formal/GaloisForLFunctions/IncommensurableGaborPinching/CriticalLineZeroProportion.lean), declaration `simple_critical_proportion_ge_67250071`.

### 4.2 Best concrete receiver found: the actual cosine surplus

Let \(N_T=N(T,2T)\), and set

\[
S_\lambda(T)=\texttt{zetaCosineFrobSurplus}\ \lambda\ T.
\]

This is the signed surplus of the actual prime Gram for the canonical shape-one cosine window, divided by the normalization \((a_TL_T)^2\). It is a finite-height arithmetic quantity. The corpus proves, for every fixed \(0<\lambda\le2\),

\[
N_{0,\mathrm{simple}}(T,2T)
\ge
\bigl(h_{\cos}(\lambda)+p_\lambda-\varepsilon\bigr)N_T
-S_\lambda(T),
\qquad
p_\lambda=\frac{\texttt{cosinePairFloor}(\lambda)^2}{200}\ge0.
\]

In particular its explicit lower certificates give

\[
\begin{aligned}
\lambda=4/3:&\qquad h_{\cos}(\lambda)\ge\frac34+\frac{79}{1250}=0.8132,\\
\lambda=2:&\qquad h_{\cos}(\lambda)\ge\frac56+\frac{43}{3750}=0.8448.
\end{aligned}
\]

Therefore either of the following **proposed arithmetic bounds** would suffice for at least 70% simple critical-line zeros:

\[
\boxed{S_{4/3}(T)\le\frac{283}{2500}N_T+o(N_T)}
\quad(283/2500=0.1132),
\]

or

\[
\boxed{S_2(T)\le\frac{181}{1250}N_T+o(N_T)}
\quad(181/1250=0.1448).
\]

These conservative thresholds leave the nonnegative pinching credit unused. Uniform dyadic estimates then give the cumulative lower proportion. The wider bandwidth permits a larger surplus, but its arithmetic sum is harder; the larger allowance is not by itself a reason to prefer bandwidth two. [Actual Gram and normalization](../../../formal/GaloisForLFunctions/TransThresholdPairCorrelation/CosinePrimeGramCertificate.lean), [actual counting certificate](../../../formal/GaloisForLFunctions/TransThresholdPairCorrelation/CosinePrimeSurplusCriterion.lean).

This is the most useful refinement over a purely limiting form-factor proposal: the actual diagonal, trace, bounded tail and explicit-formula bridge have already been matched. The new work is an upper bound for **this** surplus.

### 4.3 A second, transparent exchange-rate target

For the triangular form-factor normalization, define

\[
E_\delta=\frac{2}{\delta^2}
\int_1^{1+\delta}(1+\delta-\alpha)F(\alpha)\,d\alpha.
\]

When the sub-threshold normalization is \(F(\alpha)=\alpha\) on \([0,1]\), the exact algebra is

\[
c(1+\delta)=\frac{4+6\delta+3\delta^2E_\delta}{3(1+\delta)^2}.
\]

At \(\delta=1/9\), \(E_{1/9}\le4\) gives \(c(10/9)\le13/10\), hence the receiver value \(2-c\ge7/10\). Equivalently, the weighted integral over \([1,10/9]\) must be at most \(2/81\). [Narrow-strip exchange rate](../../../formal/GaloisForLFunctions/TransThresholdPairCorrelation/NarrowStripClosePairEnergyAndExchangeRate.lean).

This formula is a normalization guide. An arbitrary continuous model \(F\), or a form factor defined assuming RH, would not prove the result. It must be realized by the actual finite-height statistic with the required error. Nor may its constants be mixed with the cosine-surplus constants above: those retain a different profile.

### 4.4 A distinct route: eliminate the forced near-line core

The corpus also proves, for every fixed \(A>0\), an eventual dyadic alternative:

\[
N_0(T,2T)\ge0.7N_T
\quad\text{or}\quad
N_{\mathrm{simple,off,near}}(A/\log T;T,2T)
\ge\left(H_D(1)-\frac25-\frac1A-\varepsilon\right)N_T.
\]

For \(A=10\), failure of 70% forces at least \(0.1725007036\ldots-\varepsilon\) of all zeros to be **simple, off-line and within \(10/\log T\) of the line**. A strict upper bound below that coefficient would give 70%. No such upper bound is supplied by the alternative itself. [Seventy-percent dichotomy](../../../formal/GaloisForLFunctions/RHTower/Zeta23SeventyPercentOrSimpleNearLine.lean).

The existing second-depth-moment estimate does not give it. The theorem

\[
\sum_{0<\Im\rho\le V}m_\rho(\Re\rho-\tfrac12)_+^2=o(V)
\]

is compatible, at the level of this statistic, with a positive fraction of \(V\log V\) zeros at depth \(1/\log V\): their contribution is only \(O(V/\log V)\). [Depth theorem](../../../formal/GaloisForLFunctions/SquareRootThreshold/TheOffLineSecondMomentIsLittleO.lean).

Thus 70% and quasi-RH are genuinely different targets. A fixed strip does not force a single zero onto the line. A 70% line proportion does not control the rightmost member of the remaining 30%. Of the available approaches, I would prioritize the actual cosine surplus, with the near-line alternative as an independent diagnostic of what a failure must look like.

## 5. One structural question with the greatest cross-route value

> **Can the actual prime error have a nonzero finite leading oscillation above square-root scale?**
>
> More precisely, can there exist \(\beta>1/2\), \(\eta>0\), and a nonzero finite real trigonometric polynomial \(P\) such that
> \[
> \psi(x)-x=x^\beta P(\log x)+O(x^{\beta-\eta})?
> \]

My preferred outcome to pursue is exclusion. The corpus proves that existence is **exactly failure of AAL**. This is not a newly discovered equivalence; the opportunity is to prove one side of a now sharply classified alternative.

### Why this question has unusually high value

An exclusion theorem would remove the same exceptional-layer obstruction from weak recurrence, sparse lag bounds, finite-index arguments, finite off-line support, bounded Jensen defects and several eventual-sign receivers. Under AAL, such receivers that only establish finiteness can become decisive. The residual RH problem would be ZAL rather than an unspecified combination of tail behavior and exceptional zeros.

An existence theorem for the **actual** prime error would falsify RH and give quasi-RH through the finite-layer classification. A model with this asymptotic would only test the proposed method; it would not answer the question for primes.

AAL is logically weaker than RH and demands no fixed zero-free strip. It is not known to be easier to prove, and it is not simply a weaker version of quasi-RH: it constrains a different aspect of the zero configuration. The reason to prefer it as an intermediate structural problem is the amount of quantitative information it avoids and the number of existing receivers it would activate, not a claimed theorem about proof difficulty.

### What the corpus has already forced

The candidate oscillation has little freedom:

* \(\beta=\Theta<1\).
* Its nonzero frequencies are ordinates of the actual extremal zeros; in the complex expansion the coefficient at \(\rho\) is \(-m_\rho/\rho\).
* The leading exponent and profile are unique. The permissible power-saving remainder is governed by the gap to the next abscissa.
* The error changes sign with bounded gaps in logarithmic scale. An ordinary sign-change argument therefore cannot refute it.
* The long-shift moment pattern in §2.3 must occur.

These are useful constraints because they connect an exceptional zero configuration to a concrete arithmetic asymptotic. [Prime-error rigidity](../../../formal/GaloisForLFunctions/ZeroConfigurationGeometry/PrimeErrorFiniteOscillationRigidityAndSignChanges.lean).

There is also an exact dilation formulation. For \(D_bf(x)=f(x/b)\), define

\[
A_b=\prod_{\omega\in S}
\left(1-2b^\beta\cos(\omega\log b)D_b+b^{2\beta}D_b^2\right).
\]

This annihilates the proposed leading oscillation. At two distinct prime bases, bounds

\[
A_p\psi(x)=\kappa_px+O(x^{\beta-\eta}),\qquad
A_q\psi(x)=\kappa_qx+O(x^{\beta-\eta})
\]

give the finite-layer characterization when accompanied by the source theorem's nontriviality condition: a zero exists above the remainder line. That condition cannot be dropped; otherwise sufficiently accurate prime error with no exceptional layer could satisfy an annihilated bound as well. Two incommensurable bases reduce the possible ordinate lattices to a finite set. [Exact two-prime theorem](../../../formal/GaloisForLFunctions/ZeroConfigurationGeometry/MultiplicativeDilationAnnihilationOfPrimeError.lean).

### Proposed attack and success criteria

The most useful attack is to exploit what a finite leading layer forces on primes, rather than attempt to rule out an arbitrary finite oscillation abstractly.

1. Use the long-shift signature to identify the prime pairs that must retain a nonzero limit. Prove a statement about those actual weights, with the moving degree and shift range retained.
2. Alternatively, prove the source excursion estimate from §2.2. This would exclude the extremal configuration through a density theorem rather than a pointwise bound.
3. Develop a bounded-return theorem on right-edge discs only if it handles the tail-bad, density-zero return class. Requiring a return on a disc crossing the critical line can introduce a stronger obstruction and defeat the intended weakening.

A meaningful partial result would exclude finite layers in a stated depth range, with a stated gap or multiplicity restriction, or classify a necessary long-shift configuration more tightly. Such a partial theorem must retain its restrictions in every downstream application. A general theorem excluding all possible finite layers would be the breakthrough.

## 6. One question under the ban on positivity and spectral proofs

Under this restriction I would choose a quantitative arithmetic problem whose statement and proposed mechanism do not use a form, operator, zero spectrum or purity principle:

> **Can exact integer factorization and floor-division identities yield Möbius cancellation beyond the VK exponent?**
>
> Prove, for some fixed \(3/5<\nu<1\) and \(c>0\),
> \[
> \boxed{\left|\sum_{n\le x}\mu(n)\right|
> \ll x\exp\!\left[-c(\log x)^\nu\right]}
> \]
> for all sufficiently large \(x\), by a direct arithmetic mechanism.

The benchmark \(\nu=2/3\) is concrete, but any exponent strictly above \(3/5\) would answer the proposed question. This is a proposal, not a result found in the corpus.

### Why this is genuinely below the requested end goals

A fixed power saving \(x^{1-\sigma}\) implies this bound for every \(\nu<1\). The displayed bound remains larger than every fixed power-saving bound at sufficiently large \(x\); it therefore does not itself establish quasi-RH. It also permits any fixed hypothetical prime-error contribution of size \(x^\beta\), \(\beta<1\). No AAL, 70% or RH conclusion should be attached to it without an additional theorem.

The existing corpus reaches the VK range: in the rate language, every stretched exponent below \(3/5\). Its exact arithmetic rate dictionary says that stencil rates and Mertens rates coincide at stretched-exponential scales. Crossing \(3/5\) would therefore improve several current prime/Möbius formulations at once and establish that a new mechanism supplies arithmetic precision beyond their common present input. It would also rule out the claim that the new construction is merely the existing VK estimate in another coordinate system. [VK stencil result](../../../formal/GaloisForLFunctions/ArithmeticAuxiliaryDynamics/TheStencilRateReachesVinogradovKorobov.lean), [arithmetic transfer of rates](../../../formal/GaloisForLFunctions/ArithmeticAuxiliaryDynamics/TheRateAndTheMertensScaleCoincide.lean).

This would not automatically kill all competing routes. Its value is a substantial partial crossing of the common precision wall and a new arithmetic route worth developing. Conversely, a sharp obstruction for a specified class of floor-based constructions could retire that class while identifying what extra arithmetic information a replacement must retain.

### Why the recent cut programme is relevant

The exact identities

\[
\sum_{d\le N}\mu(d)\Big\lfloor\frac Nd\Big\rfloor=1,
\qquad
\sum_{k\le N}L\!\left(\Big\lfloor\frac Nk\Big\rfloor\right)
=\lfloor\sqrt N\rfloor,
\quad L(N)=\sum_{n\le N}\lambda(n),
\]

already encode more than a generic parity-blind approximation. The second identity determines \(\lambda\) uniquely. Thus the problem is not to add a label distinguishing parity: it is to extract quantitative cancellation from information already exact at every integer. [Exact parity selection](../../../formal/GaloisForLFunctions/RigidArithmeticOfCuts/TheExactIdentityDeterminesTheParity.lean).

The new difficulty is stability under growing, coupled cuts. Triangular inversion identifies the sequence, but estimates using absolute values lose its cancellation. Fixed polynomial combinations can preserve the old precision threshold. A new method must use relationships between many cuts and retain the signed discrepancy they transport.

A potential mechanism is joint control of multiplicative decompositions and additive carries. The exact identity

\[
\lfloor kx\rfloor-k\lfloor x\rfloor=\lfloor k\{x\}\rfloor
\]

shows the obstruction to importing finite-field self-similarity verbatim. The corpus classifies exact self-similar integer-norm counts: they force geometrically supported, growing multiplicities, incompatible with a nontrivial bounded-multiplicity integer count. The carry must be estimated, not declared absent. [Carry and self-similarity theorem](../../../formal/GaloisForLFunctions/RigidArithmeticOfCuts/TheCarryOfTheFloor.lean).

This problem is ambitious. I do not have an argument producing the improvement. It is preferable to an RH-equivalent “arithmetic positivity” premise under the stated ban because its input, desired estimate, and possible failure mechanism are all explicit without that premise.

## 7. What new mathematics could address the walls?

### Proposed field: effective arithmetic completion

The central question would be:

> **Which arithmetic information survives completion from finite exact data to an infinite, critical object, and what quantitative law controls the surviving defect?**

“Completion” here means a concrete operation: increasing a prime cut, enlarging an aperture, increasing a rank or conductor, taking a boundary limit, or conditioning on a longer arithmetic head. The field would study the error and cross-coupling through those operations. It would not begin by axiomatizing a positive limit.

Much of its foundation already exists in the listed programmes. Calling it a new field would be justified only by a new theorem controlling these operations in a regime the current programmes cannot reach. Another common vocabulary or list of equivalent criteria would not suffice.

### 7.1 Viewpoint and objects

The basic object should be **a finite arithmetic approximation together with its exact remainder and scale information**. For example:

\[
\mathcal A=(Q_{N,c},\ \text{prime and polar data},\
\text{head/tail coupling},\ \text{comparison map},\ \text{error bound}).
\]

These components have different mathematical roles. The comparison map identifies the intended complete source. The error bound specifies the range in which an estimate survives. The coupling records information destroyed by separate treatment of the pieces.

Other objects would include the actual Euler head/tail pair, canonical Hamiltonians on their maximal precontact intervals, arithmetic counts with an explicit quadratic comparison, and finite-height prime Gram forms with matched zero-side census data. Zeros may be used as diagnostic invariants, but the source of a new estimate must be identified independently.

| Object | Language needed | Question it must answer |
|---|---|---|
| Coupled conductor/window blocks | Exact block identities, Schur residuals, weighted compactness | Can the complement debit and mixed term be paid uniformly at a new critical ratio? |
| Prime head and retained tail | Joint moments, arithmetic length, conditioning cost, exceptional sets | What survives conditioning beyond the present \(N\log N\ll T\) boundary? |
| Counts and quadratic forms | Actual finite sets or heights, growth under multiplication, comparison error | Which arithmetic count yields the complete primitive term? |
| Canonical continuation | Potential, reflection, source increments, contact criterion | Which arithmetic bound remains uniform on approach to contact? |
| Exceptional prime-error patterns | Leading exponents, remainder gaps, long-shift limits | Which patterns are compatible with the exact integer source? |
| Actual census forms | Matched profile, signed surplus, rank deficit, error normalized by \(N(T)\) | Can a finite numerical surplus target be proved? |

### 7.2 Foundational principles

**Exact source first.** Every model needs a proved comparison to the actual arithmetic object. A construction with the right symmetries but the wrong coefficients is a calibration object, not an RH input.

**The remainder is part of the object.** Truncating a tail or moving a boundary creates a mathematical term. It cannot disappear merely because each fixed finite approximation behaves well.

**Couplings have their own scale.** Small mass, weak convergence, or separate positivity need not make a mixed term small. The receiving-charge and Schur examples show why a field based only on norms of components is inadequate.

**Limit order is explicit.** “For every fixed rank,” “for all ranks uniformly,” “for every fixed critical ratio,” and “along a cofinal aperture schedule” are different statements. The theory must expose the relevant dependence of constants.

**Arithmetic selection must be quantitative.** The exact cut identity distinguishes \(\lambda\), and count rigidity distinguishes rational primes in a precise class. Neither alone gives the required rate. A useful selection law controls how a permitted approximation can approach the actual source at increasing resolution.

**Typical and exceptional laws are separate.** A theorem about almost every torus point does not decide the Liouville point. A theorem about positive-density returns does not provide a zero-bearing return of density zero. The field needs a way to carry information into the exceptional class, or to exclude that class by an independent source constraint.

**A successful sign must have a cause.** In finite-field calibrations the cause can be a cardinality or height. In the integer problem a proposed sign principle must be traced to arithmetic data and an estimate, not inserted as an effectivity axiom.

### 7.3 Research topics and first substantial theorems

1. **Critical compactness with coupling retained.** Establish compactness for actual minimizing sequences, including prefix mass and polar moments, and identify the complete limiting form. First target: a new paid interval of critical ratios. Ultimate target: every ratio.
2. **Conditional arithmetic beyond the diagonal range.** Replace the crude length error in a head-conditioned moment by a signed arithmetic expression that is estimable in a larger range. First target: one growing-head estimate beyond the present barrier, with an explicit useful remainder.
3. **Exceptional continuation.** Develop estimates that remain meaningful on rare return sets. First target: a source excursion restriction or a restricted AAL theorem, rather than full pointwise control.
4. **Arithmetic counts for primitive directions.** Construct a count that sees more than the two bidegrees and compare it with the actual primitive form. First target: a nontrivial family beyond the already calibrated or known-positive subspaces, with no assumed sign.
5. **Signed trans-threshold correlations.** Prove a bound for the actual cosine surplus in §4. This is a strong early test because success has a definite consequence below RH.
6. **Quantitative model discrimination.** Classify which approximation errors allow new zeros, lost count rigidity, or lost cancellation. The logarithmic count floor supplies a prototype: a theorem with a sharp scale and explicit scope.

### 7.4 Criteria for accepting this as new mathematics

A result should improve an estimate, enlarge a uniform regime, classify a previously uncontrolled defect, or construct a new arithmetic object with a proved comparison. It should work on examples where both the successful arithmetic law and the obstructed model can be computed.

The calibration set should include actual finite-field curves, the rational-prime source, finite Euler truncations, positive near-count systems, signed-generator countermodels, and the graph models with incorrect damping. The theory must distinguish them using an explicit hypothesis each really satisfies or fails. It must not turn a countermodel lacking the classical functional equation into a no-go for all systems possessing that equation.

The decisive benchmark is an output such as the 70% surplus bound, a beyond-VK cancellation estimate, a nontrivial AAL case, or a new all-coefficient critical interval. If the field yields only “the complete defect vanishes if the complete defect has the desired sign,” it has not addressed the wall.

## 8. What field remains under the positivity/spectral ban?

### Proposed field: quantitative arithmetic of factorization and carries

Its central question would be:

> **How do exact multiplicative identities and additive carry laws force cancellation in signed arithmetic sums at growing scales?**

This proposal uses no Hilbert-space realization, positive-kernel criterion, spectral decomposition, Weil-form premise or purity principle. Its outputs are estimates for explicit sums over integers. Finite counts and ordinary inequalities enter as arithmetic operations; they are not used to postulate a sign for an RH-equivalent form.

The field would extend the existing rigid-cut, sum-product and auxiliary-dynamics programmes. The missing addition is a quantitative theory that can exploit the full exact identities without losing their cancellation during inversion, truncation or passage between scales.

### 8.1 Objects and language

**Factorization data.** Divisors, prime powers, squarefree factorizations, Möbius inversion, completely multiplicative signs, and the actual incidence relations among them. The coefficients \(\mu,\lambda,\Lambda\) remain explicit throughout.

**Cuts and remainders.** For integers \(N,d\ge1\), retain both

\[
q_N(d)=\Big\lfloor\frac Nd\Big\rfloor,
\qquad r_N(d)=N-dq_N(d),\quad0\le r_N(d)<d.
\]

An approximation replacing \(q_N(d)\) by \(N/d\) then has a named signed remainder. Several such remainders must be studied jointly as \(N\), \(d\), and factorization constraints vary.

**Carry configurations.** Products and additive shifts of the same integers, together with their exact floor discrepancies. The elementary identity relating a dilation carry to a sum of translations is the basic conversion law. Its size is not assumed negligible.

**Signed transport across scales.** Exact hyperbola decompositions and recurrences for partial sums, with separate terms for the portion already controlled and the remaining tail. The arithmetic rate dictionary is an example of a useful transport theorem: it proves exactly which cancellation level a construction contains.

**Quantitative distinction of sequences.** Exact identities may uniquely determine a sequence; a second theorem must control its partial sums. This separation prevents “parity has been identified” from being mistaken for “parity cancellation has been proved.”

**Finite dilation recurrences.** Combinations of \(\psi(x/b^j)\), \(M(\lfloor x/b^j\rfloor)\), or \(L(\lfloor x/b^j\rfloor)\), with explicit coefficients and remainders. They would be studied directly as arithmetic identities. No operator-spectrum interpretation is needed. Any use of the AAL dilation characterization would retain its nontriviality condition; otherwise one has not excluded an exceptional layer.

### 8.2 Foundational principles

1. **Uniqueness and cancellation are distinct theorems.** The exact floor identity already identifies Liouville. New work must produce a quantitative bound.
2. **Signed terms remain signed until a justified estimate.** Taking absolute values at every decomposition can erase the intended saving. Each such step must have a quantified cost.
3. **Multiplicity and size are separate resources.** More divisibility can increase the size of the constructed integer by the same amount. A useful producer proves both its divisibility and its size bound.
4. **No exact Frobenius over the integers is assumed.** The carry theorem identifies why this analogy fails. A replacement must measure and accumulate the carry correctly.
5. **Growth of complexity is explicit.** Fixed-order identities cannot automatically handle moving degree, a growing alphabet, or the full hyperbola tail. A theorem must state which complexity may grow with \(N\).
6. **The actual sequence is tested.** Random signs, averaged multiplicative functions or weights agreeing at finitely many primes can calibrate an estimate. They do not replace \(\mu\) or \(\lambda\).
7. **Every new structure has a numerical output.** Its value is judged by an improved signed-sum bound or a sharp classification of constructions that cannot improve one.

The existing deciding-input theorem supplies a stringent eventual RH test: a universal property of weights that implies square-root prime precision must distinguish the Liouville twin, detect perturbations above that precision, and use unbounded aperture. These are necessary conditions, not a recipe. [Deciding-input theorem](../../../formal/GaloisForLFunctions/ArithmeticOfSquareRootPrecision/TheDecidingInputTheorem.lean).

### 8.3 Questions the field should answer

| Question | First useful output | Larger consequence if extended |
|---|---|---|
| Can floor identities be inverted with cancellation retained across coupled scales? | An estimate stronger than the current VK input for an actual Möbius sum | The target in §6; eventually a possible power-saving mechanism |
| Which families of carries reinforce, and which cancel, under multiplicative constraints? | A joint signed bound unavailable from separate absolute-value bounds | A replacement for exact finite-field self-similarity |
| Can a producer obtain extra arithmetic multiplicity without paying the known factorial size cost? | A construction outside the classified fixed factorial classes, with explicit size and multiplicity | A genuinely new arithmetic precision input |
| What does simultaneous control of several cuts force? | A stability or rigidity theorem with an effective error threshold | Quantitative selection of the actual arithmetic sequence |
| Can the prime error satisfy a finite dilation recurrence with a genuine exponent drop? | A restricted exclusion or a sharp necessary arithmetic pattern | Progress on AAL without a sign-form proof |
| Which near-count integer systems can acquire new right-half-plane zeros? | A classification in a stated error class, preserving positivity of generators and the exact norm assumptions where required | A better account of which arithmetic laws actually select the rational-prime system |

### 8.4 A concrete first programme

Start with the exact Möbius hyperbola identity used in the rate theorem. Retain the signed contribution above the moving cut rather than bounding it by a uniform supremum. Decompose this contribution simultaneously by quotient intervals and factorization type, recording the carry terms at the boundaries. The task is to prove an aggregate cancellation estimate for the resulting *actual* coefficients.

A partial theorem should specify a growing range in which its error is smaller than the current estimate. It should also state what happens to the complementary range; an unexplained tail cannot be absorbed into a new interface. The target is the stretched-exponential improvement of §6. Only after such an improvement should one infer that this mechanism has a credible quantitative route toward a fixed power saving.

A second line would study the finite-dilation prime-error pattern of §5 directly on the integer side. An exclusion for a restricted class of recurrences could give structural progress even before a global Möbius bound. The proof must use a property of actual factorization or carry statistics absent from arbitrary functions with the same asymptotic shape.

The new field would succeed by proving such arithmetic statements. Its name, analogy with geometry, or ability to express RH would not be evidence of progress. The corpus has already supplied a large part of the exact language; the missing contribution is a quantitative law that this language makes possible to state but does not yet prove.
