# RH frontier: arithmetic polarization, source selection, and boundary

**Assessment, 26 October 2026.** The strongest opportunity is to construct an arithmetic mechanism that makes positivity, Hecke transport, and fidelity to the actual Euler source compatible. The corpus already supplies unusually strong detection theorems, exact reductions, and countermodels. It does not yet supply that compatibility. I see credible research directions, but no completed new proof mechanism and no justification for announcing that a wall has fallen.

My three priorities are:

| Priority | Open question | First meaningful payoff |
|---|---|---|
| 1 | Can arithmetic congruence information bound the **signed coalescent prime surplus at the actual source**? | A certified improvement in the project's critical-line proportion, with existing transfers to off-line moments. |
| 2 | Can arithmetic compute the **same-zero positive diagonal** and control its Hecke defect? | An arithmetic upper bound on a positive depth observable; ultimately a faithful polarization. |
| 3 | Can a **mixed additive–multiplicative boundary law** prevent actual cofactor energy from escaping with zero gauge mass? | A source-specific restriction on actual escape states, leading toward subpower receiver energy. |

These have different roles. The first offers a concrete intermediate theorem short of RH. The second is the main geometric construction problem. The third asks how arithmetic information survives the critical limit. They can share tools without being counted as three independent proofs.

This report uses the five requested ledgers and all 28 distinct requested programme READMEs; the repeated MultiplicativePositivityGeometry entry was read once. Corpus searches supplied additional Lean statements, including recent ConjugateDiagonalGeometry results. No other Markdown documents were opened, and no builds or web searches were run. “Established” below refers to results recorded in the supplied corpus; working-source status is not silently promoted to a new verification claim. Research log: [astra-research-2026-10-26.log](../../../logs/astra-research-2026-10-26.log).

**What the programmes collectively establish.** The [frontier map](../rh-current-frontier-map.md), [route unification](route-unification-ledger.md), [hard obstacles](hard-obstacles.md), [walls ledger](walls-ledger.md), and [killed routes](../rh-killed-routes.md) support a sharper interpretation than “many approaches have failed.” They identify which information each approach retains, which it discards, and where the discarded information becomes indispensable.

| Programme family | Strongest shared contribution | Missing mathematical input |
|---|---|---|
| arithmetic-positivity-theory, BiScaleUncertainty, SquareRootThreshold, ArithmeticCastelnuovoSeveri | Off-line zeros have effective negative signatures; towers and suitable tests detect much more than older fixed-test obstructions suggested. | Positivity or quantitative control on the actual arithmetic tests that detect them. |
| BezoutValuationIncidence, ArithmeticCriticalityTheory, ArithmeticContinuationAndCriticalEnergy, ArithmeticCompensationTheory, ArithmeticDefectRigidity | Exact receiver identities, critical thresholds, cancellation of leading terms, and a detailed theory of actual cofactor limits. | A signed estimate admitting smaller damping, or excluding the corresponding actual escape. |
| TransHorizonIncidenceMechanics, ArithmeticIncidencePositivity, ScaleSignedIncidenceCriticality, SignedArithmeticEnergyIncidence, TransThresholdPairCorrelation | Exact incidence decompositions, shared-budget constraints, non-product support savings, and usable certificates beyond the elementary support threshold. | Quantitative control of the remaining signed incidence term after every channel is charged. |
| ArithmeticOrientationTheory, ArithmeticOrientationGeometry, ArithmeticLocalDivisorGeometry, SignedSuccessorArithmetic | Precise orientation obstructions, local divisor models, and additive observables that multiplicative summaries miss. | A quantitative source law turning that additional information into the required sign. |
| ArithmeticCorrelationGeometry, BiarithmeticGaugeGeometry | Classification of multiplicative gauge blindness, finite-character stabilizers, successor holonomy, actual escape visibility, and exact cell remainders. | Control at the distinguished arithmetic gauge point, with uniformity through growing horizons and levels. |
| BiarithmeticGeometry, MultiplicativePositivityGeometry, ArithmeticPositiveDuality, ArithmeticKunnethTheory, ArithmeticCorrespondencePositivity, ArithmeticPolarization, ArithmeticEffectivityTheory | Faithfulness and closure obstructions; distinctions between reflection and conjugate pairings; exact counting, height, effectivity, and polarization receivers. | An independently constructed arithmetic object satisfying the necessary sign and growth laws together. |
| StripBochnerWeilForcing | Strong pole-budget rigidity, a sharp collar, and identification of the degree-one simple-pole class with real multiples of zeta. | A mechanism constraining the zeros of that uniquely identified source to the critical line. |

Three cautions change the interpretation of this table.

First, **detection is substantially ahead of production**. The corpus has a single-test RH receiver at each prime for actual zeta. Resonant collisions still matter when counting distinct zeros, but “one prime cannot see the defect” is no longer a valid general description. Developing another detector has lower priority unless it demonstrably reduces the arithmetic price. See [OneTestCarriesTheDefectOfZetaAtEachPrime](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/OneTestCarriesTheDefectOfZetaAtEachPrime.lean).

Second, **equivalence to RH does not disqualify a construction programme**. Constructing an arithmetic section count or height with independently proved properties could be exactly the missing breakthrough. The unproductive step is repeatedly defining such a count from the desired quadratic form and proving another equivalence. The finite-field example succeeds because geometry produces the inequalities.

Third, **the negative results have scopes**. Multiplicative lattice blindness does not prove that every completed arithmetic construction is blind. The golden countermodel satisfies its curve-type functional equation, not the full degree-one Riemann functional equation. The failure of particular product and ray lattices does not exclude every two-variable geometry. A wall constrains specified objects and operations; it is not a theorem that mathematics has no possible tools.

**The central mathematical distinction.** Write

\[
\rho^\ast=1-\overline{\rho},\qquad
\delta_\rho=\Re\rho-\tfrac12,\qquad
F_f(s)=\int_{\mathbb R}f(u)e^{(s-\frac12)u}\,du.
\]

For compact \(C^2\) tests, compare

\[
W(f,g)=\sum_\rho m_\rho F_f(\rho)
                      \overline{F_g(\rho^\ast)},\qquad
D(f)=\sum_\rho m_\rho|F_f(\rho)|^2.
\]

The first uses reflection across the critical line; the second pairs each zero with its own conjugate amplitude. Their distinction is the mathematical centre of the frontier:

| Form | Available property | Missing property |
|---|---|---|
| Weil form \(W\) | Arithmetic explicit formula and Hecke invariance | Nonnegativity on all required tests |
| Collided form \(D\) | Positivity and convergence | Arithmetic control of Hecke transport |

The exact decomposition is

\[
\Re W(f,f)=D(f)-C(f),\qquad
C(f)=\frac12\sum_\rho m_\rho
       |F_f(\rho)-F_f(\rho^\ast)|^2.
\]

Here \(C\) denotes capacity, leaving spectral width a separate quantity. RH is equivalent to equality of the two forms on all real compact \(C^2\) tests. Weil positivity asks for \(C(f)\le D(f)\) on all such tests; the resulting RH then forces \(C=0\). Computing two nonnegative quantities does not establish their required comparison. These statements and actual-zeta convergence are in [TheOscillatoryCapacity](../../../formal/GaloisForLFunctions/ArithmeticPolarization/TheOscillatoryCapacity.lean).

For \(T_Lf(u)=f(u-L)\),

\[
D(T_Lf)=\sum_\rho m_\rho e^{2\delta_\rho L}|F_f(\rho)|^2.
\]

Thus the positive Hecke defect is

\[
E_f(L):=D(T_Lf)+D(T_{-L}f)-2D(f)
       =\sum_\rho m_\rho\,4\sinh^2(L\delta_\rho)|F_f(\rho)|^2.
\]

Hecke invariance of \(D\), for all tests and translations, is already an RH equivalence. Moreover, the positive depth-profile rate law already identifies

\[
\lim_{L\to\infty}\frac{\log D(T_Lf)}{L}
 =2\sup\{\delta_\rho:F_f(\rho)\ne0\}
\]

when the test sees a zero. Neither the positive depth measure nor the subexponential-growth reduction is a new proposal here. See [HeckeInvarianceOfTheCollidedPolarizationIsRH](../../../formal/GaloisForLFunctions/ArithmeticPolarization/HeckeInvarianceOfTheCollidedPolarizationIsRH.lean) and [TheDepthProfileCarriesTheGlobalCollision](../../../formal/GaloisForLFunctions/ArithmeticPolarization/TheDepthProfileCarriesTheGlobalCollision.lean).

The newer ConjugateDiagonalGeometry source sharpens this further. Put \(k_L(\delta)=4\sinh^2(L\delta)\) and \(w_\rho=m_\rho|F_f(\rho)|^2\). It establishes

\[
k_{2L}=4k_L+k_L^2,\qquad
E_f(2L)-4E_f(L)=\sum_\rho w_\rho k_L(\delta_\rho)^2,
\]

\[
E_f(L)^2\le D(f)\bigl(E_f(2L)-4E_f(L)\bigr).
\]

The difference between the right and left sides is a weighted variance. Equality concentrates the visible divisor on **one absolute-depth shell**, which may be off-line. A visible critical zero would anchor such a shell at depth zero, but arithmetic equality and joint visibility still require proof. The same source gives

\[
k_L(b)\sum_{|\delta_\rho|\ge b}w_\rho\le E_f(L),\qquad
4L^2\sum_\rho w_\rho\delta_\rho^2\le E_f(L)
\quad(b>0).
\]

These are ready-made receivers for an arithmetic upper bound. They do not provide that bound. See [ZetaDepthDistribution](../../../formal/GaloisForLFunctions/ConjugateDiagonalGeometry/ZetaDepthDistribution.lean) and [TwoScaleDepthRigidity](../../../formal/GaloisForLFunctions/ConjugateDiagonalGeometry/TwoScaleDepthRigidity.lean).

**Opportunity for a mechanism that crosses a wall.** The most promising structural move is to construct the positive diagonal arithmetically in a setting that retains the information lost by one-variable collision, and then prove a transport law with a controlled boundary.

The one-variable collision obstruction is exact: infinitely many collided points \(2\Re\rho-\frac12\), with their required orders, cannot be the divisor of a nonzero analytic function on the specified connected neighbourhood of the compact collision interval. A positive weighted distribution remains possible; the depth profile already demonstrates this. What is missing is an arithmetic construction and estimate for it. See [TheCollisionLaw](../../../formal/GaloisForLFunctions/ArithmeticPolarization/TheCollisionLaw.lean).

A candidate construction should retain two variables, or a correspondence and its adjoint, until the same-zero trace is taken. This avoids prematurely identifying all ordinates with their real depths. It must recover multiplicity \(m_\rho\). Multiplying two explicit formulas generally creates independent zero pairs; squaring residues can produce \(m_\rho^2\). Neither operation supplies the required diagonal for free.

The proposed mechanism is a **finite arithmetic trace with a boundary identity**:

1. Construct positive finite forms \(D_{N,q}\) from explicit arithmetic data at horizon \(N\) and torsion level \(q\), with additive and multiplicative operations both present.
2. Derive their Hecke transport defect by a genuine change of variables, incidence identity, or section-count identity, including every boundary term.
3. Prove a source-specific bound on that boundary and a faithful limit identifying \(D_{N,q}\) with \(D\).
4. Feed the resulting defect or growth bound into the existing spectral receivers.

One possible target is a finite approximation to

\[
E_f(2L)-4E_f(L)\le0.
\]

The spectral identity shows how strong this is: at nonzero \(L\), it kills every visible off-line contribution. The research content would be an arithmetic finite-level identity yielding this upper bound after its boundary is paid. Merely imposing the inequality is another RH formulation. A weaker upper bound could already give quantitative depth-tail control.

This is a **construction proposal**, not an established arithmetic identity. Its prospective novelty lies in producing compatibility from mixed arithmetic and boundary geometry. The diagonal, its depth moments, and their forcing implications are already present in the corpus.

There is also an analytic opportunity: constrain only source-selected, sign-changing detectors at hypothetical zero ordinates, then force a quantitative proliferation of off-line zeros. This could avoid asking for positivity on an unnecessarily broad family. But two serious obstacles remain.

The known odd-sector theorem gives a companion, not a contradiction. A finite cluster can provide mutual companions indefinitely. A usable proliferation theorem needs an independently proved increase in depth, distance, weighted mass, or branching that defeats a zero-count bound.

Furthermore, the available sign theorem and forcing theorem do not currently meet. For the established polar-corrected companion certificate, recent source proves that forcing requires

\[
768A\log(|\gamma|+3)<e^{2\delta a},
\]

whereas the conductor horizon requires

\[
C+(4+\epsilon)e^a+2\le\log(1+|\gamma|/8).
\]

For \(0\le\delta\le\frac12\), these certificates have **no common aperture at any height**. This strengthens the earlier asymptotic comparison. It rules out composing these particular estimates; it does not rule out a new detector or a source-specific sign theorem beyond the horizon. See [TheForcingHalfOfEllipticLocalization](../../../formal/GaloisForLFunctions/ArithmeticPolarization/TheForcingHalfOfEllipticLocalization.lean) and [TheConductorForcingGap](../../../formal/GaloisForLFunctions/ConjugateDiagonalGeometry/TheConductorForcingGap.lean).

I would therefore keep elliptic proliferation as a secondary direction, activated by a genuine new signed estimate. Generic all-height positivity, density-zero exceptional sets, or a companion relation alone do not complete it. Exceptional sets must be controlled at the scale of a negative witness; every hypothetical off-line zero could lie in an exceptional set of density zero.

**Priority question 1: Can finite congruence information control the signed coalescent surplus at the actual Euler source?**

This is the clearest intermediate target because almost all surrounding transfer has already been done. At bandwidth \(4/3\), the corpus gives, for suitable smooth profiles,

\[
N_0^\ast(T,2T)\ge
\left(\frac{29}{36}-\epsilon\right)N(T,2T)
-\mathcal S_{u,\eta}(T).
\]

\(N_0^\ast\) counts distinct critical-line zeros; \(N\) counts total multiplicity. The remaining statistic \(\mathcal S\) is the normalized signed coalescent surplus. An eventual bound

\[
\mathcal S_{u,\eta}(T)\le(\beta+\epsilon)N(T,2T)
\]

with the profile and certificate quantifiers matched gives a proportion \(29/36-\beta\), up to arbitrary slack. Thus:

| Surplus budget | Consequence within the existing receiver |
|---|---|
| \(\beta<5/36\) | Exceeds the project's \(2/3\) reference proportion |
| \(\beta\le577/4500\) | Reaches \(254/375\), strictly exceeding the stronger \(HD(1)\) benchmark |
| \(\beta\le1/18\) | Reaches \(3/4\), with existing dyadic, cumulative, and off-line moment transfers |

None of these conclusions is RH. The first threshold diagnoses passage beyond the basic support barrier; the \(HD(1)\) threshold is the more useful first benchmark for improving the existing frontier. This distinction makes the question valuable: it can reward a new arithmetic technique before that technique is strong enough to solve the endpoint.

The precise target is the existing CoalescentSurplusAtMost condition. It asks, for every accuracy, for a compatible exponent and smooth profile carrying both the certificate and the surplus bound. An estimate uniform over every profile would suffice but is stronger than necessary. See [SmoothWeightedCertificateAtFourThirds](../../../formal/GaloisForLFunctions/TransThresholdPairCorrelation/SmoothWeightedCertificateAtFourThirds.lean) and [CoalescentSurplusAndTransThresholdProportionLaws](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/CoalescentSurplusAndTransThresholdProportionLaws.lean).

The arithmetic target is also well localized. With \(0<\eta<1/3\), prime-power removal costs at most

\[
\frac{128\sqrt2}{\pi}\log T\,T^{2/3+\eta}=o(N(T,2T)).
\]

The remaining pairs are odd primes with even shifts, logarithmic separation at most \(T^{-1+\eta}\), and length on the \(T^{4/3}\) scale. The sign of the oscillatory kernel is essential. A bound on the corresponding absolute pair sum can consume the entire saving. See [CoalescentPrimeReductionAndParitySieve](../../../formal/GaloisForLFunctions/TransThresholdPairCorrelation/CoalescentPrimeReductionAndParitySieve.lean).

ArithmeticCorrelationGeometry supplies an exact entry point. For \(2qT^{-1+\eta}<1\), averaging over Dirichlet characters modulo \(q\) extracts the pairs congruent modulo \(q\). The actual statistic splits into that stabilizer contribution and a noncongruent discrepancy. The discrepancy has zero subgroup average, while its value at the actual source remains uncontrolled. Full gauge averaging likewise gives excellent cancellation without determining the distinguished point. See [TheCoalescentSurplusDecomposesOverItsStabilizers](../../../formal/GaloisForLFunctions/ArithmeticCorrelationGeometry/TheCoalescentSurplusDecomposesOverItsStabilizers.lean).

The signed comparison model is also developed. The Ramanujan transfer cancels the apparent Dirichlet-kernel pole across divisors and exposes a negative singular-series contribution, with explicit endpoint and finite-height errors. Thus “use Ramanujan sums to retain lobe cancellation” is already an accomplished step. The missing estimate compares actual weighted prime pairs with this arithmetic model. See [RamanujanDirichletCoalescentTransfer](../../../formal/GaloisForLFunctions/TransThresholdPairCorrelation/RamanujanDirichletCoalescentTransfer.lean).

The research question is therefore concrete: **can a growing collection of congruence levels bound the actual signed discrepancy from the singular-series model at zero gauge?** A promising approach would combine residue-class information across levels while retaining the oscillation before applying inequalities. Character orthogonality and model cancellation are already available; the new theorem must control the remaining actual-source error.

The model calibration makes the required accuracy visible. Its Hardy–Littlewood/GUE surplus is \(-1/144\), while the \(3/4\) budget is \(1/18\), leaving a normalized allowance \(1/16\). Establishing an actual comparison within that allowance, including model truncation and window errors, would suffice. This is a proposed weighted comparison theorem, not an invocation of an unproved prime-pair asymptotic as a premise. A full uniform Hardy–Littlewood theorem would impose much more than the receiver needs.

The first deliverable should be a bound for this actual weighted statistic, with an explicit surplus budget and compatible window profile. Smaller model estimates are useful only if their transfer error is stated. Another Haar mean-square estimate, a finite-prime prescription, or a multiplicative moment calculation does not address the missing value.

**Priority question 2: Can an arithmetic object produce the positive diagonal together with a Hecke-defect upper bound?**

The central question has two inseparable parts:

\[
\text{arithmetic construction of }D
\quad+\quad
\text{arithmetic control of }D(T_Lf).
\]

Either part alone falls short. A formal sum over known zeros defines \(D\) immediately. A divisor-current representation reconstructs it analytically. An abstract positive Hilbert space can be manufactured. The difficult theorem is a representation whose arithmetic construction gives an independent estimate on transport.

There are two serious producer specifications in the existing work.

**A same-zero trace.** Construct finite arithmetic correspondences with a positive adjoint pairing whose limiting trace counts each zero with multiplicity \(m_\rho\). Establish a Hecke transformation law before passing to the limit. The depth-tail inequalities then turn any useful upper bound into a measurable zero-distribution conclusion. A subexponential bound for both translation directions, on a family that sees every zero, reaches the RH endpoint through the existing rate law.

**A section count or height.** ArithmeticEffectivityTheory states the geometric requirement with unusual precision. On the relevant polar surface, construct an actual \(h\) satisfying

\[
\frac12x\cdot(x-\kappa)+\chi_0\le h(x)+h(\kappa-x),
\]

and subquadratic growth on degree-zero rays. The formal receiver needs only arbitrarily large \(n\), for every \(c>0\), with

\[
h(nx)+h(\kappa-nx)<cn^2
\qquad(x\cdot A=0).
\]

Full \(o(n^2)\) growth is sufficient but stronger than this minimal condition. These properties force the Hodge index. The alternative naive-height programme asks for a bounded-below arithmetic height approximating the relevant quadratic form with enough control under doubling or convexity. See [TheEffectivityCalculus](../../../formal/GaloisForLFunctions/ArithmeticEffectivityTheory/TheEffectivityCalculus.lean) and the [ArithmeticEffectivityTheory programme](../../../formal/GaloisForLFunctions/ArithmeticEffectivityTheory/README.md).

The two inequalities must concern the **same arithmetic object**. Riemann–Roch-shaped identities alone admit trivial fake counts; growth bounds alone do too. Degree-only theta counts do not supply the surface growth law. A construction defined by the positive part of the target quadratic form has not independently established its sign.

A useful first milestone would be a finite-level, source-defined correspondence object in which a mixed additive operation changes the adjoint trace in a computable way, with a complete boundary formula. It should reproduce genuine finite-field polarization and expose exactly which property the golden and complex-quartet countermodels lack. Moving toward zeta then requires a faithful limit, including multiplicities and the pole/Gamma normalization.

This is a high-risk construction problem. Its attraction is that it attacks the incompatibility directly. Its main failure mode is to make a beautiful positive object whose spectral image is blind, uses the wrong diagonal, or has uncontrolled transport.

**Priority question 3: What arithmetic boundary law prevents actual cofactor limits from having zero gauge mass?**

This question has a sharper endpoint than “classify escape states.” Let \(E_\varepsilon(N)\) be the established damped Möbius receiver energy,

\[
E_\varepsilon(N)=
\sum_{n\le N}\frac{A_\varepsilon(n)^2}{n(n+1)}.
\]

For every actual common cofactor limit \(L\), the corpus constructs a gauge spectral measure with total mass

\[
\operatorname{mass}(L)=\inf_{d\ge1}dK_L(d,d).
\]

The diagonal is squeezed by ratios of receiver energies at horizons approximately \(N/d\) and \(N\). Admission gives mass one. More strongly, record horizons turn any positive-power failure into an actual zero-mass limit, without assuming finitely many dominant zeros, simple poles, or an attained maximal depth. The exact criterion is

\[
\mathrm{RH}\quad\Longleftrightarrow\quad
\forall\,0<\varepsilon<\tfrac12,\ 
\forall\,L\text{ actual at }\varepsilon,\ 
\operatorname{mass}(L)>0.
\]

Under RH these masses are all one. See [TheGaugeMassOfAnEscapeStateIsItsEnergyRatio](../../../formal/GaloisForLFunctions/ArithmeticCorrelationGeometry/TheGaugeMassOfAnEscapeStateIsItsEnergyRatio.lean) and [RHIsTheVisibilityOfEveryEscapeState](../../../formal/GaloisForLFunctions/ArithmeticCorrelationGeometry/RHIsTheVisibilityOfEveryEscapeState.lean).

Consequently, exhaustive residue classification is not a prerequisite for this route. The missing theorem is an arithmetic reason why **actual** limits cannot lose all scale-invariant mass. Cauchy-kernel positivity and positive semidefinite finite Grams permit precisely such loss.

The additive information must enter before the limit forgets it. The programmes show why fixed successor operations, generic affine positivity, and finite local gauge constraints are insufficient. Finite successor dynamics carry boundary loss; pure multiplicative data retain only a gauge orbit. At the critical exponent, dilation boundary mass has a nonzero limiting contribution. Discarding that boundary erases the normalization one is trying to force.

BiarithmeticGaugeGeometry supplies a particularly concrete starting object. Put

\[
w_a=\log\frac{a+1}{a}.
\]

For a cell-constant profile, multiplicative translation has the exact decomposition

\[
\operatorname{Corr}_{m,X}(c)
=\sum_{a\le X}w_ac_ac_{am}+R_{m,X}(c),
\]

\[
R_{m,X}(c)=
\sum_{a\le X}c_a\sum_{0\le r<m}
w_{am+r}(c_{am+r}-c_{am}).
\]

The established estimate

\[
R_{m,X}(c)^2
\le
\left(\sum_{a\le X}w_ac_a^2\right)
\left(\sum_{k\le Xm+m}k(c_{k+1}-c_k)^2\right)
\]

has constant one, uniformly in \(m\). This exactly locates the interaction between divisibility and additive remainders. See [EuclideanCellRemainderAndPolarNeutralCollapse](../../../formal/GaloisForLFunctions/BiarithmeticGaugeGeometry/EuclideanCellRemainderAndPolarNeutralCollapse.lean).

The next question is the **aggregate signed remainder**, with the critical prime weights and the actual source profile. Summing the individual absolute bounds loses the prime budget. The available polar-neutral lattice calculation also removes the hoped-for free diagonal reserve. A useful new theorem must exploit relationships between different \(m\), additive positions, and the source coefficients.

I would investigate moving additive scales and growing torsion levels inside this finite-horizon identity. Their dependence on the horizon must be specified; fixed successor correlations can disappear in normalized escape. The target is a source-dependent balance law that survives normalization and obstructs zero-mass limits.

The first milestone is a nontrivial bound on a prime-weighted mixed remainder for actual receiver profiles, including smoothing, outer boundary, and common-limit errors. The endpoint is positive mass for every actual limit at every subcritical damping. A sufficient analytic formulation is

\[
\forall\,0<\varepsilon<\tfrac12,\ \forall\,\kappa>0,\qquad
E_\varepsilon(N)\ll_{\varepsilon,\kappa}(N+1)^\kappa.
\]

This is already an RH receiver, not an available estimate. Even a genuine fixed-strip gain would be major progress. Constants may depend on damping and slack; asking for uniform control at zero damping would impose an unnecessary stronger problem.

**The proposed field: arithmetic correspondence geometry with boundary.** The corpus already contains much of its algebraic skeleton. Its defining problem would be:

> How can finite arithmetic incidences produce a faithful positive adjoint trace, while their additive and multiplicative operations remain compatible through a critical limit with a controlled boundary?

This point of view treats the three walls as failures of compatibility:

| Wall family | Question for the proposed field |
|---|---|
| Critical arithmetic sign, Wall 1 | Which mixed incidence law controls the distinguished Euler source, beyond information constant on its multiplicative gauge orbit? |
| Transfer and localization, Wall 3 | Which norm and boundary identity preserve that law through smoothing, dilation, summation, and infinite horizon? |
| Realization and forcing, Wall 14 | Which actual arithmetic count, section space, or trace makes positivity and Hecke transport compatible without losing zeros? |

Its **objects** should retain the following data together:

- Finite arithmetic correspondences generated by divisibility, congruence, and additive displacement, with explicit horizon and modulus.
- Source vectors carrying the actual Euler coefficients and normalization; prime-gauge twists retained as comparison objects.
- Positive forms, adjoints, and both reflection and conjugate pairings, so their difference is visible.
- Boundary defects of composition and adjointness, including the archimedean contribution.
- Section counts, heights, or trace functionals defined independently of the desired sign.
- Completion maps carrying multiplicities and distinguishing an actual limit from a freely chosen positive kernel.

Its **language** should include mixed incidence, source charge, boundary flux, adjoint defect, effectivity, and faithful trace. These terms should denote computable quantities. For example, the existing successor connection

\[
A_\omega(n)=\overline{\chi_\omega(n)}\chi_\omega(n+1)
\]

records information absent from equal-product observables. Its flatness through a finite interval fixes the corresponding prime phases. The identities on \(2\to3\to4\) reconstruct the phases at 2 and 3. That is a source-identification theorem. The field must add a quantitative law connecting such data to a signed correlation, transport defect, or boundary energy.

The distinction between **identifying a source** and **controlling it** is foundational. Almost every gauge twist can satisfy square-root cancellation while the distinguished source remains the unresolved point. Conversely, prescribing finitely many prime phases leaves uncontrolled tails. No amount of exact reconstruction at fixed level replaces a horizon-uniform arithmetic estimate.

The field's **foundational principles** should be mathematical requirements, not additional axioms asserting the endpoint.

1. **Source fidelity.** The arithmetic construction must distinguish the actual source using information that affects its estimates. Exact Euler normalization, the pole, and Gamma terms must survive.
2. **Adjoint fidelity.** Reflection pairing and conjugate pairing remain distinct until a proved comparison identifies them. A norm square cannot be substituted for the Weil form.
3. **Boundary exactness.** Truncation and affine composition produce explicit defects. They are retained until estimated. The critical half-density must emerge from the measure and boundary law; an abstract affine relation alone does not fix it.
4. **One signed budget.** Prime, archimedean, polar, smoothing, and localization terms are combined before the final comparison. Positive reserves cannot be spent independently on several errors.
5. **Faithful completion.** The topology must retain off-line evaluation and the relevant divisor data. Closure of a blind or paid subspace in a weak norm cannot be used as payment in a stronger graph norm.
6. **Minimal sufficient strength.** Seek the weakest growth or sign statement that the receiver needs. Avoid gratuitous simplicity, a uniform positive gap, or all-height assertions contradicted by resonance.
7. **Independent effectivity.** Section counts and heights must arise from arithmetic objects. Their defining properties must be proved without importing the target quadratic sign.

These principles explain why the finite stage matters. Adding a nontrivial successor directly to a final atomic unitary spectral model can run into the existing affine-action obstructions. Noninvertible finite correspondences with explicit boundary defects offer a different setting. A limiting unitary representation, if justified, should be an output.

The field should have **three linked research topics**.

**Mixed arithmetic harmonic analysis:** weighted prime-pair discrepancy across congruence levels; sign-preserving summation; mesoscopic successors; prime-gauge connections; quantitative comparison of the actual source with its twists. Its first benchmark is the coalescent surplus budget.

**Arithmetic diagonal and effectivity theory:** same-zero trace constructions; multiplicity-linear diagonal extraction; growing section spaces; arithmetic Riemann inequalities; subquadratic degree-zero growth; Hecke transport of positive forms. Its benchmark is an arithmetic defect upper bound or a genuine height/count satisfying both required inequalities.

**Critical boundary and completion theory:** exact finite-horizon flux; common limits at moving modulus and displacement; graph norms; prime-summed cell remainders; passage between Abel and sharp horizons where needed. Its benchmark is a quantitative source law excluding a class of actual zero-mass escapes, followed by the full visibility theorem.

A proposed construction should face the existing countermodels early:

| Test | What it checks |
|---|---|
| Golden curve datum and its positive count hierarchy | Whether counts and functional equations have been mistaken for a polarization |
| Complex quartets with positive kernel counts | Whether the proposed trace sees the relevant adjoint sign |
| Multiplicative gauge twins | Whether the estimate uses source-selective information |
| Power-growth escape kernels | Whether positivity permits total loss of gauge mass |
| Origin-\(L^2\) closure and finite absorbing boundaries | Whether the completion or truncation erases the obstruction |
| Critical-split height-coupled deformations | Whether an asserted rigidity principle is stronger than its surviving one-sided form |

Passing a test means locating a proved property absent from the countermodel. It does not mean forcing every countermodel to satisfy the full zeta hypotheses.

Several possible benchmarks are deliberately weaker than RH. A finite-character signed discrepancy estimate can improve a critical-line proportion. A defect upper bound can control weighted depth tails. A finite-level mixed trace can distinguish the true adjoint pairing from ordinary kernel counts. A quantitative boundary law can exclude a specific escape mechanism. These would be genuine advances even before the whole field closes.

**What to deprioritize.** The supplied work argues against further iterations of uncharged multiplicative moments, tensor powers with proportional losses, generic positive kernels, source identification alone, and local positivity supported by a large archimedean subsidy. Each can produce valid mathematics; none currently supplies the missing source-specific sign.

Two newer corrections deserve explicit preservation. The degree-one simple-pole positive class is already zeta up to a nonzero real scalar, so identifying that class again will not confine its zeros. Two-sided height-coupled rigidity is false in the later BiarithmeticGaugeGeometry work. The surviving CentralVanishingCeiling is a sufficient one-sided target; its converse is not established. Adding Dirichlet-lattice decay also requires care because the known restriction excludes desired quartet contractions as well as unwanted deformations.

The best evidence of progress would now be one of three concrete outputs: an actual-source surplus budget below a useful threshold; an arithmetic upper bound on the positive Hecke defect; or a mixed boundary estimate preventing zero-mass actual escape. The existing detection and transfer machinery is strong enough to make each such result mathematically consequential.
