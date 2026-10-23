# Where a new mechanism could enter

Research assessment, 23 October 2026. Source inspection and paper arguments; no builds run.

**My answer to the first question is qualified yes: there is an opening for a new mechanism, but I do not find an established route around the walls.** The opening is a quantitative theorem about compensation forced by the *joint arithmetic structure of the actual source*. The corpus already contains the receivers, exact identities, detectors, many counterexamples, and substantial leading-order cancellation. What remains missing is an estimate that turns that cancellation into a bound uniform in the critical cutoff. A new spectral realization, uncertainty principle, positivity criterion, or transport identity would not by itself fill that gap.

**My answer to the second question is a theory of arithmetic compatibility and compensated coercivity.** Its subject would be how simultaneous additive, multiplicative, scale, and boundary constraints force signed cancellation in a critical norm. Much of its language already exists in the nine programmes. The useful new field would be their estimate-producing continuation, not a tenth vocabulary for the same RH-equivalent assertion.

This assessment also produces a concrete paper result: the raw prime-comb cross aggregate can grow like (4e^{2r}), even on smooth odd tests of mass one. Its normalized operator has an explicit translation limit. This answers the counterexample-and-rate alternative in Arithmetic Incidence Positivity's research topic 8. It rules out the proposed universal polynomial bound and identifies a coherent contribution that a successful argument must handle with its compensating terms.

Three statuses are kept separate below: **source-checked** means I inspected relevant Lean statements and proofs, without compiling them or auditing every transitive dependency; **paper deduction** means an argument supplied here from stated unconditional inputs; **open** means a proposed research problem. A conditional Lean implication is evidence for the reduction, not evidence that its analytic premise has been proved. I make no claim of global novelty for the paper deductions.

**The present frontier is further along than a generic RH discussion would suggest.** The governing example is the actual centered receiver

\[
 A_\varepsilon(n)
 =\sum_{d\leq n}\mu(d)d^{-\varepsilon}
       \left\lfloor\frac nd\right\rfloor
       -\frac{n}{\zeta(1+\varepsilon)},
 \qquad
 E_T(\varepsilon)=\sum_{n=1}^{T}
       \frac{|A_\varepsilon(n)|^2}{n(n+1)}.
\]

Admission means \(\exists B_\varepsilon<\infty\;\forall T\;E_T(\varepsilon)\leq B_\varepsilon\). The source-checked theorem `riemannHypothesis_iff_cofinal_budget` identifies RH with admission at positive dampings arbitrarily close to zero. The constants may deteriorate as damping tends to zero. Requiring one bound uniform in both variables would add an unnecessary burden.

The newer theorem `receiverDampingRate_eq_zetaZeroAbscissa_sub_half` identifies the receiver's **accumulation-rate infimum** with

\[
 \Delta=\Theta-\tfrac12,
 \qquad
 \Theta=\sup\{\Re\rho:\rho\text{ a nontrivial zeta zero}\}.
\]

Every \(\varepsilon>\Delta\) is admitted. An isolated admitted damping does not automatically give the corresponding zero-free half-plane: translated zero cancellation is a real distinction in the dictionary. Thus neither the cofinal quantifier nor the accumulation qualifier should disappear in a proposed proof. See [AdmissionBelowHalfDampingAboveTheZeroWidth](../../../formal/GaloisForLFunctions/RHTower/AdmissionBelowHalfDampingAboveTheZeroWidth.lean).

The nine programmes divide the work approximately as follows. “Owned” here refers to the supplied account, supplemented by source inspection where indicated later; it is not a fresh certification of each module.

| Programme | Substantial work already owned | What is still needed |
|---|---|---|
| [Arithmetic Positivity Theory](../../../formal/GaloisForLFunctions/arithmetic-positivity-theory/README.md) | High-scale positivity on large restricted families; source and cone dictionaries; favorable limiting prime symbol. | Controlled passage to an RH-complete family. The archimedean \(\log M\) subsidy cannot be carried into arbitrary tests for free. |
| [BiScale Uncertainty](../../../formal/GaloisForLFunctions/BiScaleUncertainty/README.md) | Sharp node prices and redundancy results in specified cones, universal boosted probes, extensive phase optimization, finite-filter Schur residuals. | An actual-source estimate controlling the residual as complexity grows. Another finite Gram decomposition is insufficient. |
| [TransHorizon Incidence Mechanics](../../../formal/GaloisForLFunctions/TransHorizonIncidenceMechanics/README.md) | All-prefix renormalized sign results; sharp observation and parity obstructions; critical Wiener transfer; extensive moment information. | Origin-sensitive quantitative control in the critical receiver norm. Separation or recovery without a stable bound does not supply it. |
| [Bézout Valuation Incidence](../../../formal/GaloisForLFunctions/BezoutValuationIncidence/README.md) | Exact finite incidence identities; compensated diagonal and predecessor errors \(O_\varepsilon(1)\); sharp generic Type II barriers; actual prime-row improvement in unbalanced ranges. | A quantitative gain for the actual coupled rows in the unresolved scales, especially balanced growing moduli. The compensated interior identity has coefficient one. |
| [Arithmetic Criticality Theory](../../../formal/GaloisForLFunctions/ArithmeticCriticalityTheory/README.md) | Gauge and radical calculus, endpoint obstructions, certified local positivity, an extremely small upper ceiling for the aperture ground energy. | A valid all-aperture signed floor or transport estimate compatible with that ceiling. |
| [SquareRootThreshold](../../../formal/GaloisForLFunctions/SquareRootThreshold/README.md) | Strong visibility and completeness theorems, threshold calibration, graded bridges to zero width. | Production of the bound measured by the detector. Visibility does not constrain the actual source by itself. |
| [Arithmetic Incidence Positivity](../../../formal/GaloisForLFunctions/ArithmeticIncidencePositivity/README.md) | Exact ledger with pole and even parts retained, prime-tower reduction, substantial local allocations and odd-window positivity. | Global signed allocation retaining prime–polar cancellation. The raw prime-comb polynomial target fails, as proved below. |
| [Arithmetic Continuation and Critical Energy](../../../formal/GaloisForLFunctions/ArithmeticContinuationAndCriticalEnergy/README.md) | Exact work and transport identities, inversion and Markov structure, endpoint admission, equivalences for signed averaged budgets. | An independently proved, cutoff-uniform budget on the actual source below half damping. |
| [Scale-Signed Incidence Criticality](../../../formal/GaloisForLFunctions/ScaleSignedIncidenceCriticality/README.md) | Reading/fibre/resolution calculus; exact distinctions between finite refutation, cofinal confirmation, and ambiguity on specified models. | A quantitative source estimate using enough information to escape the relevant fibres. A reading's completeness is not an energy bound. |

Several headline numbers need their qualifiers. The supplied frontier records full-window positivity through radius \(0.3\), odd positivity through \(0.362\), and a joint \(2/3\)-cost payment through \(0.575\). The last is not full positivity through \(0.575\). Likewise the route dictionaries are not all literal equalities between every exponent: some window quantities have only comparison inequalities, and some plain-mass floor converses require an extra local depth bound. The derivative/log-weighted variants have stronger unconditional dictionaries. These distinctions matter when choosing a target.

**The walls are best read as failures of particular information or estimates.** They are not a theorem that every conceivable RH proof must use one prescribed set of tools.

| Wall | Question it leaves open | What would actually get past it |
|---|---|---|
| Source realization without orientation | Why should the faithful arithmetic realization have the required sign? | Derive orientation from arithmetic estimates. Another carrier of the full divisor does not answer this. |
| Sharp arbitrary-row majorants | Which joint constraints distinguish the actual rows from the extremizers? | An estimate on the actual coupled arithmetic family, with all compensating terms retained. |
| Blind readings and origin loss | Which information changes critical admission, and can it be retained stably? | Anchored reconstruction or a direct bound, with constants controlled in the critical norm. |
| Critical norm and scale transfer | What is the exact cost of changing norm, cutoff, gauge, or scale? | A quantitative transfer including boundary and moving-projection terms. Density, compactness in \(c_0\), or totality of residue modes is not enough. |
| Finite positivity versus unbounded aperture | What mechanism prevents a bad profile from appearing at a later scale? | A cofinal transport or graded floor theorem, not additional isolated positive windows. |
| Exact identities with no gain | Which source relation makes the identity coercive? | A strict or summable estimate not obtained by substituting the same unknown energy back into itself. |

The ledgers already exclude many attractive shortcuts: positivity of a faithful operator model without source orientation; sign-blind damping; sectorwise bounds on pieces that diverge separately; a universal contraction extracted from the coefficient-one interior identity; translation-invariant data used as though they fixed the origin; and a fixed positive ground-energy floor at every aperture. These exclusions are scoped. An averaged lemma, for example, can still be useful if a separate argument supplies the missing uniform transfer.

**A concrete new deduction: the prime-comb obstruction has a sharp exponential family and an explicit positive survivor.** This is a paper theorem, not a new Lean declaration.

Write

\[
 A_F(t)=\int_{\mathbb R}F(x)F(x+t)\,dx,
 \qquad
 w_p=\frac{\sqrt p\log p}{p-1},
 \qquad
 C_rF=\sum_{p\leq e^{2r}}w_pF(\,\cdot+\log p).
\]

These are the Euler weights and translate convention in the source. The exact, source-checked identities are

\[
 \mathcal E_r(F):=\|C_rF\|_2^2
   =\sum_{p,q\leq e^{2r}}w_pw_qA_F(\log(q/p))
\]

and

\[
 \mathcal E_r(F)
   =\left(\sum_{p\leq e^{2r}}w_p^2\right)A_F(0)
     +\sum_{\substack{p,q\leq e^{2r}\\p\ne q}}
        w_pw_qA_F(\log(q/p)).
\]

See [PrimeCombEnergyReduction](../../../formal/GaloisForLFunctions/ArithmeticIncidencePositivity/PrimeCombEnergyReduction.lean) and [PrimeTowerLedgerReduction](../../../formal/GaloisForLFunctions/ArithmeticIncidencePositivity/PrimeTowerLedgerReduction.lean). Their Cauchy–Schwarz reduction is valid. The issue is the size of its right-hand side.

Choose a nonzero real odd \(f\in C_c^\infty(\mathbb R)\), supported in \([-1,1]\), with \(\|f\|_2=1\), and set

\[
 F_r(x)=r^{-1/2}f(x/r),\qquad
 S_r=\sum_{p\leq e^{2r}}w_p.
\]

Then every \(F_r\) is an admissible smooth odd test of aperture \(r\), with \(A_{F_r}(0)=1\). The claims are

\[
 \frac{\sqrt r}{S_r}(C_rF_r)(r\,\cdot)
     \longrightarrow f(\,\cdot+2)
       \quad\text{in }L^2(\mathbb R),
 \tag{1}
\]

\[
 \mathcal E_r(F_r)\sim4e^{2r},\qquad
 \sum_{\substack{p,q\leq e^{2r}\\p\ne q}}
       w_pw_qA_{F_r}(\log(q/p))\sim4e^{2r}.
 \tag{2}
\]

Here is a complete proof from the prime number theorem and continuity of translations in \(L^2\).

First, partial summation of \(\vartheta(X)\sim X\) gives

\[
 \sum_{p\leq X}\frac{\log p}{\sqrt p}\sim2\sqrt X.
\]

The difference between this weight and \(w_p\) is
\(\log p/[\sqrt p(p-1)]\), whose sum converges. Consequently
\(S_r\sim2e^r\).

Next put a probability measure on the rescaled prime shifts:

\[
 \nu_r=S_r^{-1}\sum_{p\leq e^{2r}}w_p\delta_{\log p/r}.
\]

For every fixed \(0<\delta<2\),

\[
 \nu_r([0,2-\delta])
  =\frac{\sum_{p\leq e^{(2-\delta)r}}w_p}{S_r}
  \longrightarrow0.
\]

Thus the shifts concentrate at 2. The left side of (1) equals
\(\int f(\,\cdot+t)\,d\nu_r(t)\). Given any tolerance, translation continuity bounds
\(\|f(\cdot+t)-f(\cdot+2)\|_2\) by that tolerance near 2; elsewhere it is at most 2 and the measure tends to zero. This proves (1). Change of variables gives

\[
 \left\|\frac{\sqrt r}{S_r}(C_rF_r)(r\,\cdot)\right\|_2^2
   =\frac{\mathcal E_r(F_r)}{S_r^2}\longrightarrow1.
\]

Finally, \(w_p\leq2\log p/\sqrt p\), so an elementary comparison with all integers gives

\[
 \sum_{p\leq e^{2r}}w_p^2
   \leq4\sum_{2\leq n\leq e^{2r}}\frac{(\log n)^2}{n}
   =O(r^3).
\]

Subtract this diagonal to obtain (2). The triangle inequality also gives
\(\mathcal E_r(F)\leq S_r^2\|F\|_2^2\); hence this family attains the leading universal bound asymptotically. The exponential rate 2 is sharp for the energy.

This is stronger than observing a positive cross term on an aligned train. It answers the README's explicit alternative: exhibit exponential growth and read its rate. Oddness removes the single Fourier value at zero, but not the mass in a shrinking low-frequency neighbourhood. The displayed family has precisely such mass.

The **positive survivor** is (1): the normalized comb becomes a translation on slowly varying rescaled profiles. It is not a rank-one limit. This tells us what the large coherent contribution does, rather than merely showing that a target fails.

There is a further useful separation. The actual first-power charge is the pairing with the original test, and (1) implies

\[
 \frac{1}{S_r}\sum_{p\leq e^{2r}}w_pA_{F_r}(\log p)
   =\left\langle f,\frac{\sqrt r}{S_r}(C_rF_r)(r\,\cdot)\right\rangle
   \longrightarrow\langle f,f(\cdot+2)\rangle=0.
\]

The final equality follows from the disjoint interiors of the supports. Therefore enormous comb energy does **not** establish an enormous adverse signed charge, much less a negative Weil form. Cauchy–Schwarz has discarded important geometry. The estimate needed by the full ledger should retain this geometry and the pole contribution. The conclusion is not that the prime-incidence route is dead; its raw universal comb majorant is too large.

The searched corpus already contains comb reductions, resonant trains, and near-null translate constructions. I did not locate this precise rescaled translation-limit theorem. That is a statement about the search, not a claim that the argument is new to the literature. Its mechanism is classical concentration of translation measures. Formalization remains outstanding because this task explicitly excludes builds.

**Three quantifier corrections sharpen the continuation problem.** The walls ledger already notices the main distinctions; the following arguments make their consequences explicit.

First, signed integrated work and total adverse variation are different targets. Let
\(W_T(\varepsilon)=\langle A_\varepsilon,\partial_\varepsilon A_\varepsilon\rangle_T\), so \(E_T'=2W_T\). The source proves

\[
 \int_a^c\frac{-2W_T(\varepsilon)}{1+E_T(\varepsilon)}\,d\varepsilon
  =\log(1+E_T(a))-\log(1+E_T(c)).
 \tag{3}
\]

With \(c\) admitted, a uniform upper bound on this **signed** integral is equivalent to admission of \(a\). Replacing the integrand by its positive part gives a sufficient, potentially stronger condition. It does not follow from the same equivalence. See [TheDampingAverageOfTheRelativeLossSuffices](../../../formal/GaloisForLFunctions/ArithmeticContinuationAndCriticalEnergy/TheDampingAverageOfTheRelativeLossSuffices.lean), [TheAveragedBudgetIsExactlyAdmission](../../../formal/GaloisForLFunctions/ArithmeticContinuationAndCriticalEnergy/TheAveragedBudgetIsExactlyAdmission.lean), and [TheWorkIntegralIsTheEnergyDrop](../../../formal/GaloisForLFunctions/ArithmeticContinuationAndCriticalEnergy/TheWorkIntegralIsTheEnergyDrop.lean).

A paper countermodel shows that horizon monotonicity does not repair this distinction. Define

\[
 E_T(\varepsilon)=\sum_{k=1}^T2^{-k}
                 \bigl(2+\sin(16^k\varepsilon)\bigr).
\]

These are nonnegative, increasing in \(T\), and bounded by 3 everywhere. On any interval \([a,a+2\pi]\), the signed integral in (3) is zero. But

\[
 E_T'=\sum_{k=1}^T8^k\cos(16^k\varepsilon),\qquad
 \int_a^{a+2\pi}|E_T'|
   \geq4\cdot8^T-4\sum_{k<T}8^k\longrightarrow\infty.
\]

Since the derivative has integral zero and \(1+E_T\leq4\),

\[
 \int_a^{a+2\pi}\frac{(-E_T')_+}{1+E_T}
   \geq\frac18\int_a^{a+2\pi}|E_T'|\longrightarrow\infty.
\]

This proves strictness for general smooth, horizon-monotone energy families. It does not prove failure of that stronger budget for the actual Möbius source. Its practical message is to preserve signed recovery rather than pay every local loss separately.

Global nonnegative work is already unavailable on the actual source. At \(T=1\), \(A_\varepsilon(1)=1-1/\zeta(1+\varepsilon)\); the Laurent expansion at 1 gives \(W_1(\varepsilon)\to-1/2\) as \(\varepsilon\downarrow0\). A usable continuation theorem must therefore accommodate some adverse work.

Second, the integrated prime-harmonic core diverges when the damping interval reaches zero, not on every fixed positive interval. The source identity `integral_workCore_eq_scaleSum` gives, for \(0<\eta<\varepsilon\),

\[
 \int_\eta^\varepsilon\operatorname{core}_x(T)\,dx
 =\sum_{2\leq j\leq T}\frac{\Lambda(j)}{\log j}
       (j^{-\eta}-j^{-\varepsilon})
       \left(\frac1j-\frac1{T+1}\right).
\]

Each summand is nonnegative and at most \(j^{-1-\eta}\). Extend it by zero for \(j>T\), apply dominated convergence, and use the absolutely convergent Euler logarithm. The exact paper limit is

\[
 \lim_{T\to\infty}\int_\eta^\varepsilon
     \operatorname{core}_x(T)\,dx
   =\log\zeta(1+\eta)-\log\zeta(1+\varepsilon)<\infty.
 \tag{4}
\]

The source's divergence theorem `exists_horizon_integral_workCore_ge` uses \([0,\varepsilon]\). Formula (4) is consistent with it: the limit diverges as \(\eta\downarrow0\). Since admission permits constants depending on \(\eta\), that endpoint divergence alone does not kill positive-damping continuation. The remaining deviation and its normalization still have to be controlled. See [TheCoreDebtIsThePrimeHarmonicSeries](../../../formal/GaloisForLFunctions/ArithmeticContinuationAndCriticalEnergy/TheCoreDebtIsThePrimeHarmonicSeries.lean).

Third, positive aperture transport must allow an extraordinarily fast decay of its floor. Write \(\mu(A)\) for the restricted Weil ground energy. The source-checked unconditional ceiling is

\[
 \mu(A)\leq K\exp\!\left(\frac{11}{2}A-\pi e^{2(A-2)}\right),
 \qquad A\geq3.
 \tag{5}
\]

See [GaussianCriticalityRestrictedWeilGroundEnergy](../../../formal/GaloisForLFunctions/ArithmeticCriticalityTheory/GaussianCriticalityRestrictedWeilGroundEnergy.lean). This is an upper bound; without RH it does not say that \(\mu(A)\) tends to zero from above.

The half-summable relative-loss premise in [TheApertureFloorTransportFromTheCertifiedEndpoint](../../../formal/GaloisForLFunctions/ArithmeticContinuationAndCriticalEnergy/TheApertureFloorTransportFromTheCertifiedEndpoint.lean) yields the fixed lower bound \(1/10000\). Along unbounded apertures that premise is therefore impossible, regardless of RH. The implication is valid but cannot be the actual-source producer.

More precisely, if a proposed positive transport yields
\(\mu(A)\geq m_0e^{-B(A)}\), \(m_0>0\), then, enlarging \(K\) to be positive if necessary, (5) forces

\[
 B(A)\geq\pi e^{2(A-2)}-\frac{11}{2}A+\log(m_0/K).
 \tag{6}
\]

This necessary loss rate is the positive information in the obstruction. Products of positive step factors may tend to zero while staying positive at every finite stage; summability of their logarithmic losses is not required for that conclusion. Their permitted decay must be compared with the actual aperture schedule. Even a harmonic product is far too large along linearly growing apertures. Moreover, strict finite-aperture positivity is a stronger goal than the nonnegativity needed for RH. A graded negative floor may be a more appropriate target.

**The most credible new mechanism is a quantitative law of compensation across compatible scales.** This is a proposal, not a result, and its broad motivation is already present in the programmes. The potentially new ingredient would be a theorem that *forces a rate* from the simultaneous arithmetic constraints.

There is unusually strong evidence that compensation is the right object. In [PMRamanujanComplementaryCancellation](../../../formal/GaloisForLFunctions/RHTower/PMRamanujanComplementaryCancellation.lean), the large-prime sector \(L\) and its complement \(C\) satisfy, in the regime of that module,

\[
 \frac{\|C\|^2}{\|L\|^2}\to1,
 \qquad
 \frac{\Re\langle L,C\rangle}{\|L\|^2}\to-1,
 \qquad
 \frac{\|L+C\|^2}{\|L\|^2}\to0.
 \tag{7}
\]

The pieces diverge separately; the source forces their leading cancellation. This is already proved, not a conjecture to rediscover. But the remaining bound can still grow with a positive power. Relative cancellation is not critical admission.

To isolate what a stronger theorem must estimate, project \(C\) onto \(L\). In the real Hilbert space underlying the energy, put

\[
 \alpha=-\frac{\Re\langle L,C\rangle}{\|L\|^2},
 \qquad R=C+\alpha L,
 \qquad \Re\langle L,R\rangle=0.
\]

Then

\[
 \|L+C\|^2=(1-\alpha)^2\|L\|^2+\|R\|^2.
 \tag{8}
\]

Equation (7) says that \(\alpha\to1\) and \(\|R\|^2=o(\|L\|^2)\). It does not give the rates needed in (8). Projection algebra is elementary, and finite-filter Schur residuals are already in [FiniteFilterSchurResidual](../../../formal/GaloisForLFunctions/BiScaleUncertainty/FiniteFilterSchurResidual.lean). The research problem is to control the actual arithmetic amplitude mismatch and transverse remainder, including their interaction when the scale changes.

A promising point of attack is an **overlapping-scale compatibility estimate**. Use the same integers in adjacent prime/cofactor decompositions; keep their common successor boundary, their Möbius inversion relation, and the exact centering. A coherent near-extremizer at one scale must also satisfy the neighbouring decomposition. Prove that these simultaneous constraints either force the compensating component or make the residual quantitatively smaller. This differs from taking an operator norm over arbitrary coefficient rows, where the corpus already supplies sharp obstructions.

The constraints can be written concretely. For the uncentered finite prefix \(B_\varepsilon(n)=A_\varepsilon(n)+n/\zeta(1+\varepsilon)\), one has

\[
 B_\varepsilon(n)-B_\varepsilon(n-1)
   =\sum_{d\mid n}\mu(d)d^{-\varepsilon},
 \qquad
 \partial_\varepsilon B_\varepsilon(n)
   =\sum_{q\leq n}\Lambda(q)q^{-\varepsilon}
                  B_\varepsilon(\lfloor n/q\rfloor).
\]

The first follows by differencing the floor; the second follows by differentiating the finite sum and using \(-\mu\log=\mu*\Lambda\). Centering introduces explicit forcing terms that must remain in the equation. More generally the source already proves \(D^fD^g=D^{f*g}\) and a centered logarithmic dilation law in [TheDilationCalculusOnIntegerPrefixes](../../../formal/GaloisForLFunctions/ArithmeticContinuationAndCriticalEnergy/TheDilationCalculusOnIntegerPrefixes.lean). These are examples of available compatibility, not new identities claimed here. The open step is a coercive consequence of satisfying them together with the boundary and scale constraints.

There are two concrete proof architectures worth pursuing.

*An arithmetic corrector could turn this compatibility into backward continuation.* On each fixed compact damping interval \([a,c]\), with \(a>0\) and \(c\) admitted, seek an explicit finite arithmetic cross term \(\mathcal C_T(\varepsilon)\) such that

\[
 \mathcal H_T=1+E_T+\mathcal C_T,
 \qquad
 m_{a,c}(1+E_T)\leq\mathcal H_T
       \leq M_{a,c}(1+E_T),
 \tag{9}
\]

where \(0<m_{a,c}\leq M_{a,c}<\infty\) are independent of \(T\). Seek, in addition,

\[
 -\partial_\varepsilon\mathcal H_T
       \leq b_{a,c}(\varepsilon)\mathcal H_T,
 \qquad b_{a,c}\in L^1([a,c]),
 \tag{10}
\]

uniformly in \(T\), or a weaker signed block-integrated estimate with the same consequence. Integration gives

\[
 1+E_T(a)
 \leq\frac{M_{a,c}}{m_{a,c}}
       (1+E_T(c))\exp\!\left(\int_a^c b_{a,c}\right).
\]

The propagation argument is routine and largely already represented by ACCE. The proposed advance is a construction of \(\mathcal C_T\) and its bounds from arithmetic cross terms. Choosing a corrector from the desired bound, from the zeros' assumed location, or by defining away the energy would prove nothing. The comparability requirement in (9) prevents a change to an easier but irrelevant norm.

Taking the already admitted \(c=1/2\) and proving this for a cofinal sequence \(a\downarrow0\) would prove RH. Thus the complete corrector target is an RH-strength programme, not a newly discovered weaker substitute. Its intermediate two-scale estimates are where independent progress must first be demonstrated.

The natural first candidates are the mixed large-prime/complement terms in (7), together with the exact Bézout boundary corrections. Their damping derivatives create additional terms; those must be estimated explicitly. A scale-dependent projection also creates a connection term from the derivative of the projection. Omitting it would repeat the free-transfer error identified elsewhere in the corpus.

*A classification of arithmetic blow-up profiles could instead yield a contradiction.* Suppose \(E_T(a)\) were unbounded and normalize an actual receiver sequence by its critical energy. Retain enough scale, cofactor, origin, and frequency data to describe where the unit energy goes. Derive all surviving finite arithmetic identities for the limiting profiles. Then classify the compatible profiles and prove that none can carry the required energy.

This would avoid asking for a uniform estimate on arbitrary rows. Its difficult steps are explicit: a critical compactness/decomposition theorem; control of mass escaping to the horizon or frequency; stability of the arithmetic constraints under the chosen convergence; and exclusion of a nonzero compatible profile. Weak convergence to zero proves none of these. The existing escape and aliasing examples must appear in the defect space, not disappear through a weak topology. I did not find this completed classification in the searched corpus. It is a possible architecture for the missing estimate, not a reason to expect an easy compactness proof.

Neither architecture follows merely from noncommutativity. Multiplicative prefix dilations already have a semigroup calculus; commuting those operators supplies no new constraint. Introducing the additive successor creates genuinely different incidence, but the killed-routes ledger already records indefinite prime–modular commutators. A commutator identity must come with a coercive estimate on the actual source.

**A second, complementary target is compensated prime–polar control in the graded floor.** The prime-comb theorem says to remove or pair the forced coherent contribution *before* taking a norm. It does not authorize throwing away the pole, even-strip gains, or the exact gamma contribution. The complete ledger is the appropriate object.

For the normalization used in [TheIncidenceLedgerGradedByTheZeroWidth](../../../formal/GaloisForLFunctions/SquareRootThreshold/TheIncidenceLedgerGradedByTheZeroWidth.lean), an all-aperture bound of the form

\[
 \widetilde Z(F)\geq-C_\sigma e^{2\sigma r}\|F\|_2^2
 \quad\text{for every eligible odd test supported in }[-r,r]
 \tag{11}
\]

gives \(\Delta\leq\sigma\). Subexponential control, with the appropriate quantifiers, gives RH. This admits negative error and respects the absence of a positive spectral gap. Any fixed \(\sigma<1/2\) would already be a major fixed-strip advance; a better finite aperture alone is not such an advance.

Chebyshev/Abel reorganization of the ledger is already part of the work, including an active modified source file. It should not be advertised as a new mechanism here. What is missing is an estimate of the resulting signed remainder that is valid for every test, with its mass, derivative costs where required, origin, and boundary terms correctly accounted for. Subtracting a smooth prime main term without controlling the error only relocates the same zero-width problem.

**There is also a concrete internal transfer worth doing before inventing new theory.** The source-checked BVI theorem `exists_abs_rowBilinear_centredPrimeRow_le` uses a short-interval exponent \(\alpha>7/12\). It requires a block length \(H\asymp Q^\alpha\), together with

\[
 \frac H2\left(\sum_{k\leq N}\frac1k\right)^2+\frac18
       \leq\eta P,
 \qquad 3P\leq2\eta Q.
 \tag{12}
\]

See [CentredPrimeRowPassesTheCoherentBlockObstruction](../../../formal/GaloisForLFunctions/BezoutValuationIncidence/CentredPrimeRowPassesTheCoherentBlockObstruction.lean). These conditions, including control of \(N\), must remain visible.

The corpus already has `tendsto_psi_short_window_div_seventeenThirtieths`, unconditionally at the inspected statement level, in [PrimeShortIntervalsSeventeenThirtiethsUnconditional](../../../formal/GaloisForLFunctions/RHTower/PrimeShortIntervalsSeventeenThirtiethsUnconditional.lean). Its input is the corpus's Guth–Maynard theorem. The corresponding external result is also explicit in [Guth–Maynard, *New large value estimates for Dirichlet polynomials*, Corollary 1.3](https://arxiv.org/html/2405.20552v2).

There is a plausible dependency bridge: for any \(\alpha>17/30\), choose \(17/30<\beta<\alpha\), tile a longer interval by successive intervals of length \(x^\beta\), and use the uniform tail meaning of the short-window limit. The final remainder has trivial cost \(O(x^\beta\log x)=o(x^\alpha)\). This yields the uniform-in-length version needed by the BVI block argument. The discrete endpoints and existing block constants still need a written and formal proof.

With \(N\) polynomially bounded in \(Q\), the resulting sufficient unbalanced range should extend from
\(P^{1+\delta}\leq Q\leq P^{12/7-\delta}\) to
\(P^{1+\delta}\leq Q\leq P^{30/17-\delta}\), for suitable fixed margins. This is an inference about reusing an already owned input. It is not a new external prime theorem, a proof for balanced \(Q\asymp P\), or an improvement of the union of every existing dispersion regime. It is a precise local target with less conceptual risk than another abstract reformulation.

**The proposed field should study compatibility as a quantitative constraint, rather than introduce positivity as an axiom.** A workable name is *arithmetic compatibility and compensated coercivity*. “Arithmetic compensation theory” is a shorter description. The name matters less than the following mathematical commitments.

Its central question would be:

> When several exact arithmetic descriptions belong to the same source, what signed critical-norm estimates do their compatibility conditions force that none of the descriptions forces separately?

The distinction from generic uncertainty is that the coefficient rows are not independent. The distinction from an inverse problem is that recovering them is not the end: the theory must bound a critical functional. The distinction from an abstract positivity criterion is that the sign or quantitative floor must be derived.

Its primitive objects could be organized as follows.

| Object | Required data | Purpose |
|---|---|---|
| An anchored arithmetic source | Actual coefficients, convolution relations, successor incidence, centering, and boundary normalization. | Prevent replacing the source by a broad class whose extremizers need not be arithmetic. |
| A family of finite critical states | Prefixes, damping, aperture, and scale, together with the exact pronic or Weil normalization. | State estimates before passing to a limit; expose every uniformity requirement. |
| A compensated decomposition | Coherent pieces, their mixed Gram terms, and a residual. | Treat cancellation as data rather than discard it by absolute values. |
| A scale transition | Refinement maps, changes of projections, and boundary/connection terms. | Determine whether local gains survive a growing family or changing norm. |
| A reading with a resolution fibre | Observable data and the set of compatible sources or profiles. | State exactly what information is lost and what additional measurement would restore it. |
| A critical defect profile | Location and structure of energy that escapes under normalization. | Turn failure of a bound into a classification problem with retained arithmetic constraints. |
| A graded estimate | Explicit growth rate, source class, norm, and dependence on parameters. | Measure progress before the RH endpoint without hiding assumptions. |

The source need not be restricted to \(\zeta\) in every lemma. However, broadening a source class is useful only when the theorem's conclusion survives that broadening. Shifted twins, periodic crystals, parity flips, prime modifications, and arbitrary coherent rows belong in different tests; no theorem says every intermediate lemma must distinguish all of them at once.

Its language should make several operations explicit: coherent subtraction, signed pairing, anchored restriction, refinement, compensated transport, and defect extraction. An assertion such as “the correction is bounded” should always specify **which norm**, **uniform in which cutoff**, **on which source class**, and **with which dependence on damping or aperture**. A dense image, a vanishing relative error, and a bounded critical error are different statements and should remain visibly different.

The foundational principles would be obligations on proofs, not new axioms assumed about the primes:

1. **Exact source before estimates.** Derive finite identities from the actual arithmetic laws. A source-selectivity claim must identify the relation that the adversarial model violates.
2. **Compensate before taking absolute values.** Keep mixed terms, poles, even parts, and boundary terms until the cancellation they enable has been used. The separate pieces may be unbounded.
3. **Pay for changes of representation.** Prove quantitative norm and scale comparison. Moving projections have connection terms; changes of origin are not free.
4. **Uniformity is part of the theorem.** A constant depending on a positive damping is acceptable for admission. A constant secretly depending on the horizon is not.
5. **Recovery requires stability.** Exact reconstruction or separation is useful only with the additional estimate required by the target functional.
6. **Measure partial progress by a rate.** Record the residual exponent, logarithmic saving, aperture decay, or resolution threshold. Do not label an identity or another equivalent criterion a bound.
7. **Keep failure constructive.** Classify the obstructing family and extract its strongest positive law. The translation limit (1) is an example.
8. **No analytic input hidden in an interface.** An assumed coercivity, budget, or positive realization is an open obligation, not an unconditional theorem about the actual source.

This formulation makes the field falsifiable. A claimed universal theorem that predicts polynomial raw comb energy fails immediately on (1)–(2). A proposed summable positive-floor transport fails (5)–(6). A purported critical reconstruction that identifies translation-equivalent signals fails when anchored admission distinguishes them. These are useful design constraints, not reasons to abandon estimates altogether.

**Its principal research questions would be the following.** Each is narrower than “prove RH,” although some strongest endpoints would imply it.

| Question | First meaningful theorem | Why it matters |
|---|---|---|
| Can adjacent arithmetic decompositions force a rate of compensation? | A bound for the amplitude mismatch and transverse residual in (8), stronger than the existing relative cancellation, with all scale-transfer terms included. | Converts a known leading cancellation into quantitative control. |
| Can compatible source constraints exclude critical blow-up profiles? | A profile decomposition retaining critical energy, followed by exclusion of a nontrivial class of arithmetic defect profiles. | Supplies a route to coercivity without an arbitrary-row operator bound. |
| Can prime–polar coherence be handled before squaring? | An exact compensated pairing plus a bound on its residual for an expanding test class, with a stated aperture exponent. | Avoids the sharp exponential raw-comb majorant. |
| Can origin information be recovered stably at the threshold? | A quantitative estimate in the anchored pronic norm, not merely uniqueness from all moments. | Bridges the observation theory to the receiver it must control. |
| Can arithmetic cross terms create a useful adapted energy? | Construct (9) with an independently bounded loss on a nontrivial damping interval. | Makes backward continuation a producer rather than an equivalence. |
| Can positivity be replaced by the right graded floor? | An unconditional all-aperture bound (11) with a strictly improved exponent. | Gives measurable zero-width progress while allowing the necessary degeneracy. |
| What is the exact balanced-scale obstruction for actual rows? | A classification or saving for the actual centred prime/Möbius incidence in the remaining comparable-scale regime. | Tests whether the missing gain comes from arithmetic compatibility or whether a proposed observable is still too weak. |

The balanced question should not be reduced to a claim that every fixed-modulus average vanishes. The corpus already computes a nonzero omitted-residue-class term for the fixed-prime statistic in [OmittedResidueClassLawOfThePrimeRow](../../../formal/GaloisForLFunctions/BezoutValuationIncidence/OmittedResidueClassLawOfThePrimeRow.lean). The correct main term must be retained before asking for a remainder estimate.

**Existing mathematics supplies ingredients, but no cited ingredient supplies the missing conclusion automatically.** Hypocoercivity is a useful model for constructing an adapted energy with mixed terms: [Dolbeault–Mouhot–Schmeiser](https://arxiv.org/abs/1005.1495) prove decay from specific coercivity and confinement hypotheses. That does not give backward admission in a new critical arithmetic norm. The analogy suggests how to organize the work, not an available theorem that closes it.

Compensated compactness is a useful model for preserving a nonlinear pairing under differential constraints. [Waurick's functional-analytic div–curl treatment](https://arxiv.org/abs/1703.09593) offers a structural comparison. An arithmetic version would need its own constraint operators, closed-range or compactness statements, and treatment of endpoint defects. Merely naming two constraints “div” and “curl” would add nothing.

Short-interval analytic number theory is directly relevant, as the internal Guth–Maynard transfer illustrates. [Matomäki–Radziwiłł](https://arxiv.org/abs/1501.04585) provides strong almost-all interval information for multiplicative functions. The missing step in these routes is not permission to use averages; it is an actual proof upgrading the available average to the anchored, cutoff-uniform functional required here.

Function fields are a calibration ground, but \(\mathbb F_q[T]\) alone is too easy: its rational zeta function can make the relevant cancellation degenerate. Nontrivial curve or twisted examples should test whether the proposed mechanism explains a source of positivity independently. [Deligne's Weil I](https://numdam.org/item/PMIHES_1974__43__273_0/) is a benchmark for genuine geometric input; assuming the corresponding purity as the new theory's arithmetic premise would be circular as a proposed explanation.

Accordingly, I would not claim that mathematics as a whole has no suitable tools, or that the proposed field has already been shown necessary. The evidence supports a narrower conclusion: the inspected programmes have not yet obtained the source-specific critical estimate, and their no-go theorems identify important features that a successful estimate must preserve.

**The research sequence should prioritize estimates whose outcome is distinguishable from another reformulation.** My proposed order is:

1. Record the prime-comb translation theorem and sharp rate as the completed paper analysis of topic 8's obstruction; formalize that exact survivor in a later build-authorized task. Study the compensated pairing rather than repeat the false polynomial comb target.
2. Keep the signed budget, positive-interval core limit, and permissible aperture-loss rate explicit in the continuation programme. These remove unnecessary or impossible targets without claiming a new RH bound.
3. Transfer the already owned \(17/30\) short-window input into the BVI block theorem, retaining (12). This is a concrete test that the programmes' strongest inputs are actually connected.
4. Choose one actual-source two-scale decomposition and seek a quantified version of (8). State the intended gain before doing algebra: a better residual rate, a stable corrector, or a classified defect family.
5. Only after obtaining such a gain, attempt iteration over scales or damping. Prove the iteration's constants and boundary costs; do not assume local gains sum.
6. Measure any global result through the existing zero-width dictionaries. A fixed strip, cofinal admission, and RH should have separate status labels.

The strongest opportunity I see is therefore specific: **turn the already proved leading arithmetic cancellation into a stable quantitative law by exploiting compatibility between decompositions of the same source.** The prime-comb calculation shows why a majorant can be exponentially large while the relevant signed pairing is much smaller; the complementary-sector theorem shows that the actual arithmetic source already realizes such cancellation. Neither supplies the required uniform remainder. Producing that remainder is the new mathematics, whether developed as a field or as one decisive theorem inside the existing programmes.

**Evidence and scope.** I read all fourteen requested Markdown documents and no other project Markdown as research material. The five route-level sources were [current frontier](../rh-current-frontier-map.md), [killed routes](../rh-killed-routes.md), [route unification](../review-2110/route-unification-ledger.md), [hard obstacles](hard-obstacles.md), and [walls](walls-ledger.md). The nine programme sources are linked in the table above. Newer source statements and the current frontier were used to resolve older or overly broad README descriptions.

Corpus searches used `scripts/formal_tools.py research`, with semantic queries for mechanisms and lexical queries for discovered declaration names. Search hits were checked in Lean before being used as proof evidence. Markdown results outside the requested set were excluded from inspection. The durable [research log](../../../logs/astra-wall-research-2026-10-23.log) records reading checkpoints, searches, source findings, and distinctions between proved and proposed work.

The most consequential source checks are collected here for reproducibility:

| Lean source / declaration | What was checked | Limit of the evidence |
|---|---|---|
| [AdmissionBelowHalfDampingAboveTheZeroWidth](../../../formal/GaloisForLFunctions/RHTower/AdmissionBelowHalfDampingAboveTheZeroWidth.lean), `receiverDampingRate_eq_zetaZeroAbscissa_sub_half`, `riemannHypothesis_iff_cofinal_budget` | Exact rate and cofinal quantifiers. | Does not establish admission below the unknown width. |
| [UniformRenormalizedInteriorEnergyRemainder](../../../formal/GaloisForLFunctions/BezoutValuationIncidence/UniformRenormalizedInteriorEnergyRemainder.lean), `exists_pmBezoutInterior_compensated_energy_bound`, `pmInterior_strict_contraction_iff_bounded_energy` | Bounded compensated errors and coefficient-one identity. | Strict contraction is not produced by the identity. |
| [PMRamanujanComplementaryCancellation](../../../formal/GaloisForLFunctions/RHTower/PMRamanujanComplementaryCancellation.lean), complement energy and mixed-energy ratio theorems | Leading compensation of separately large sectors. | Relative smallness is not a bounded critical remainder. |
| [PrimeCombEnergyReduction](../../../formal/GaloisForLFunctions/ArithmeticIncidencePositivity/PrimeCombEnergyReduction.lean), `combEnergy_eq_diagonal_add_cross`, `cost_le_sqrt_diagonal_mul_mass` | Exact Gram decomposition and the explicit cross-term premise. | The premise is not an unconditional actual-test estimate. |
| [GaussianCriticalityRestrictedWeilGroundEnergy](../../../formal/GaloisForLFunctions/ArithmeticCriticalityTheory/GaussianCriticalityRestrictedWeilGroundEnergy.lean), `exists_ccmRestrictedWeilGroundEnergy_le_doubleExp` | Unconditional aperture upper ceiling. | Nonnegativity is a separate issue. |
| [TheApertureFloorTransportFromTheCertifiedEndpoint](../../../formal/GaloisForLFunctions/ArithmeticContinuationAndCriticalEnergy/TheApertureFloorTransportFromTheCertifiedEndpoint.lean) | Half-summable transport yields a fixed positive floor. | Its premise cannot hold along unbounded apertures in view of the preceding ceiling. |
| [TheAveragedBudgetIsExactlyAdmission](../../../formal/GaloisForLFunctions/ArithmeticContinuationAndCriticalEnergy/TheAveragedBudgetIsExactlyAdmission.lean), `averagedDampingContinuation_iff_admits` | Equivalence for the signed relative-loss integral. | Does not identify positive-part variation with admission. |
| [TheCoreDebtIsThePrimeHarmonicSeries](../../../formal/GaloisForLFunctions/ArithmeticContinuationAndCriticalEnergy/TheCoreDebtIsThePrimeHarmonicSeries.lean), `integral_workCore_eq_scaleSum`, `exists_horizon_integral_workCore_ge` | Exact finite sum and divergence interval starting at zero. | No divergence conclusion on a fixed compact positive interval. |
| [CentredPrimeRowPassesTheCoherentBlockObstruction](../../../formal/GaloisForLFunctions/BezoutValuationIncidence/CentredPrimeRowPassesTheCoherentBlockObstruction.lean) | Actual-row estimate, \(7/12\) input, horizon and block constraints. | Balanced scales are not covered by those constraints. |
| [PrimeShortIntervalsSeventeenThirtiethsUnconditional](../../../formal/GaloisForLFunctions/RHTower/PrimeShortIntervalsSeventeenThirtiethsUnconditional.lean) | Existing \(17/30\) theorem with the corpus's proved input supplied. | Full dependency recompilation was outside scope. |
| [TheIncidenceLedgerGradedByTheZeroWidth](../../../formal/GaloisForLFunctions/SquareRootThreshold/TheIncidenceLedgerGradedByTheZeroWidth.lean) | Graded floor-to-width implications. | Their all-aperture analytic premises remain the work to do. |

No Lean files, programme READMEs, pipeline cards, or existing reports were edited. The paper deductions above remain unformalized; the proposed corrector, compatibility estimate, and defect classification remain open.
