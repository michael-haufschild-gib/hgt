# Research routes and mathematical obstacles

Status: 28 October 2026. **RH remains open. The inventory is 31 live routes, 17 standalone candidates and the PW-B candidate branch of PM.** Most live routes already have an exact receiver. Their missing input is an arithmetic estimate or sign, not another equivalence.

Companions: [summary and priorities](obstacles-summary.md), [walls](walls-ledger.md), [route unification](route-unification-ledger.md), [current frontier map](../rh-current-frontier-map.md), [scoped obstructions](../rh-killed-routes.md).

## Evidence and classification

This report uses corpus searches followed by inspection of Lean statements, hypotheses and proof context across established routes, candidates and current supporting frameworks. It does not infer status from modification dates or module titles. Source references below identify mathematical evidence, not a fresh kernel audit. No builds or compilations were run. Working-source capstones include Haar effectivity, the unbounded-carrier projection, Ramanujan quasimodes and energy separation, the Robin–Euler criterion, Liouville finite-part separation and the torsion index ceiling. Their statements are included with their stated scope; integration or fresh kernel validation is not inferred. Search records and findings are in the [research log](../../../logs/review-2810-research.log), with [declaration evidence](../../../logs/review-2810-source-evidence.jsonl) and [filtered search results](../../../logs/review-2810-search/). Only the six requested inherited Markdown reports were consulted.

Two categories organize each route:

- **A — Just work:** a specified finite calculation, application of an existing theorem, explicit error accounting, or transport whose mathematical ingredients are already available. This can be substantial work. It does not promise that a requested positivity certificate exists.
- **B — Research:** the missing estimate, construction or uniformity principle. An RH-equivalent conclusion is an open mathematical problem. A project-specific intermediate question is labelled unresolved, rather than asserting that nobody worldwide has ever studied or solved its exact formulation.

A false proposed estimate belongs in neither queue: it needs replacement. A proved conditional receiver is not an unconditional proof of its input. Likewise, a published theorem missing from the corpus is a literature/formalization gap, not a new open problem. External announcements need a separate status; their existence prevents an unqualified claim that “nobody has a solution.”

## The present mathematical frontier

### 1. Complete approximation is available; complete positivity is not

Complete logarithmic cells retain every relevant prime translation, the Gamma contribution, mass and both exponential pole moments. For each fixed compact smooth test family, one refinement recovers **every mixed Weil entry**, not just diagonal energies. Pole-preserving smoothing realizes the finite arithmetic form on original smooth tests. These results close the fixed-support transfer problem. They do not prove the finite forms positive. [Complete source transfer](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/CompleteWeilSourceTransfer.lean), [smooth realization](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/SmoothFiniteCellArithmeticForm.lean).

Narrow positive sections have a unique bounded Weil-orthogonal projection in the closed source graph. Its complement satisfies

\[
W(g-Pg,h-Ph)=W(g,h)-W(Pg,Ph).
\]

Every negative square survives in this complement. For each finite probe family, the completed residual index is attained at a finite refinement; complete cells capture every finite actual Weil index. Thus the unresolved object can be stated precisely: **the signed complementary form, or an upper index bound on source-complete cells**. Projection existence and finite mixed-entry recovery are established. [Projection](../../../formal/GaloisForLFunctions/ArithmeticIndexDescent/TheClosedSectionHasABoundedWeilProjection.lean), [finite attainment](../../../formal/GaloisForLFunctions/ArithmeticIndexDescent/TheCompletedIndexIsReachedAtAFiniteStage.lean), [index capture](../../../formal/GaloisForLFunctions/ArithmeticIndexDescent/TheCompleteCellsCaptureEveryFiniteIndex.lean).

Two attempted exhaustions do not supply the sign. At fixed atom count, shrinking widths removes vanishing energy. Recentered high arithmetic bands have increasing coercivity, but their unit-energy balls pair to zero with each fixed compact source. Nested positive sections can therefore remain mathematically useful without exhausting the source. [Shrinking cells](../../../formal/GaloisForLFunctions/ArithmeticIndexDescent/ShrinkingCellsRemoveVanishingEnergy.lean), [moving-band decoupling](../../../formal/GaloisForLFunctions/ArithmeticIndexDescent/MovingArithmeticBandsDecoupleFromFixedTests.lean).

Fixed cells control the **complete source graph**, uniformly over every finite prefix of any prescribed increasing carrier. For any continuous weight at least one, widths can be chosen once so every independently profiled prefix pays that weighted mass; the graph bound can have any factor \(1+\varepsilon\). On the chosen integer-log carrier, its literal graph closure has a unique bounded Weil projection, exact Schur subtraction and projection cost at most \(2\|T_Wf\|^2\). The carrier is **proper**: actual cusp escape eventually lies outside it, and an infinite independent theta radical survives in the complement. Those null directions are not negative witnesses, but exclude strict coercivity on the entire complement. [Fixed graph control](../../../formal/GaloisForLFunctions/ArithmeticIndexDescent/FixedCellsControlTheCompleteSourceGraph.lean), [unbounded-carrier projection](../../../formal/GaloisForLFunctions/ArithmeticIndexDescent/TheUnboundedCellCarrierHasAWeilProjection.lean).

Balanced adjacent-cell Haar sections retain prime pairings only at odd-boundary incidences \((2a+1)m=2b+1\); even multipliers vanish. For their compact BV profile \(f_c\), arbitrary real coefficients satisfy

\[
\begin{aligned}
P(f_c)&\le\sum_{a=1}^{X}\left(16+\frac{\log(2a+1)}{\sqrt2}\right)h_ac_a^2,\\
\mathcal L(f_c)&\ge\sum_{a=1}^{X}\log(a)h_ac_a^2,\\
2C(f_c)^2-2S(f_c)^2&\ge-2\sum_{a=1}^{X}h_ac_a^2,
\end{aligned}
\]

where \(h_a=\operatorname{haarMass}(a)\), \(\mathcal L\) is Lévy energy and \(C,S\) are the hyperbolic pole moments. The assembled full rough-Weil inequality is

\[
W_{\rm rough}(f_c)\ge
\sum_{a=1}^{X}\left((1-1/\sqrt2)\log a+2\theta'(0)-20\right)h_ac_a^2.
\]

Consequently **one lower index \(A\) gives \(W_{\rm rough}(f_c)\ge\sum h_ac_a^2\) for every finite signed section supported at \(a\ge A\), independently of its upper horizon**. This is an actual full-form positive family. Extracting a numerical threshold and applying fixed-family pole-preserving smoothing are work with established inputs. Ordinary mean-zero balance is not polar neutrality; the pole loss is paid. [Prime bound](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/HaarCellPrimeBound.lean), [Gamma](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/HaarCellGammaPayment.lean), [poles](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/HaarCellPoleBound.lean), [full Haar floor](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/HaarCellEffectivity.lean).

More generally, coherent Gamma energy pays \(\sum_i\log(1/|I_i|)\int_{I_i}f^2\) for compact BV sources mean-zero on disjoint intervals of width at most one, allowing unequal touching cells and arbitrary complementary source. **Coarse components, interactions between scales and a source-complete positive decomposition remain research.** Local gains cannot spend the same Gamma reserve repeatedly. [Coherent coercivity](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/GammaMeanZeroCoercivity.lean).

### 2. Overlap has several different boundaries

Write \(\delta_N=\log(1+1/N)\). At a sufficiently small fixed fraction of \(\delta_N\), actual pole-inclusive zeta Grams satisfy Hodge hyperbolicity, weighted trickle-down and link inequalities. Narrow full-form positivity also holds for sign twins, so this regime is not globally selective. [Narrow Hodge](../../../formal/GaloisForLFunctions/ArithmeticLorentzianGeometry/TheHodgeIndexHoldsAtAFixedFractionOfTheSpacing.lean), [polar payment](../../../formal/GaloisForLFunctions/ArithmeticLorentzianGeometry/TheTiltedMarginPaysThePolarDispersion.lean).

For the stated nonnegative smooth profiles positive inside their support, the natural atomic form is Metzler at \(w=\rho\delta_N\), \(0<\rho<1\). Every fixed \(\rho>1\) eventually produces a frustrated triangle, prohibiting every diagonal unimodular Metzler gauge. The endpoint \(\rho=1\) is not settled. This obstructs that gauge method, not full Weil positivity. [Gauge threshold](../../../formal/GaloisForLFunctions/ArithmeticLorentzianGeometry/TheMetzlerThresholdOfTheOverlapRatioIsOne.lean).

Pure Markov positivity is different. For every \(e/(2\pi)<c<1\), some smooth nonnegative plateau has negative Markov energy on pole coefficients \(n^{-1/2}\) at width \(c\delta_N\). A profile-dependent Robin–Euler criterion also excludes the stability regime when

\[
2\theta'(0)+\log(1/(wN))+\kappa_L(\phi)+\gamma+\varepsilon+e^{1/2}w/2<0,
\qquad 0<w\le\delta_N/2.
\]

At sufficiently large \(N\), this gives a negative pole test and rules out a positive weight satisfying \((-M)\pi\le0\). Its hypotheses and width restriction matter; it is not a global exact critical-ratio theorem. The full pole-paid form and the exact pole-hyperplane criterion survive. [Plateau failure](../../../formal/GaloisForLFunctions/SpacingScaleHarmonicAnalysis/TheMarkovFormFailsInsideTheSeparatedRegime.lean), [Robin–Euler criterion](../../../formal/GaloisForLFunctions/ArithmeticLorentzianGeometry/TheStabilityRegimeEndsAtTheRobinEulerThreshold.lean), [pole-hyperplane criterion](../../../formal/GaloisForLFunctions/SpacingScaleHarmonicAnalysis/ThePoleIsTheOnlyNegativeSquareBeyondTheThreshold.lean).

Second-order synthesis is RH-complete at \(w_N=N^{-\theta}\), \(0<\theta<1\), and \(w_N=(\log N)^\alpha/N\), \(\alpha>1/4\). More generally, inverse widths \(\kappa_N\to\infty\) with \((\kappa_N/N)^4\log\kappa_N\to0\) suffice. Eventual full-Weil positivity for **all real coefficient vectors** on each such family is equivalent to RH. These sufficient conditions do not establish sharpness at \(\alpha=1/4\). [Second-order synthesis](../../../formal/GaloisForLFunctions/SpacingScaleHarmonicAnalysis/TheSecondOrderSynthesis.lean).

The exact prime decomposition \(P(f_x)=\|g\|_2^2P_N(x)+NR_w(x)\) has a proved Schur bound. For \(0\le w\le1\), \(w\le K/N\), the non-ratio row is at most \(2(\log4+4)e^{5/2}K+2e^{3/2}K(m/N)(\log m+1)\). This competes with the tilted saving \((m/4N)\log m\); it does not pay arbitrary growing overlap. Separately, \(w\le K\delta_N\) covers measure at most \(K\), so squared L² error against a unit plateau of length \(L\) is at least \(L-K\). The requirement \(K\gtrsim\log N\) concerns simultaneous coverage of the whole growing interval \([0,\log N]\), not approximation of each fixed compact test. [Rows](../../../formal/GaloisForLFunctions/SpacingScaleHarmonicAnalysis/TheRowsAtBoundedOverlap.lean), [coverage](../../../formal/GaloisForLFunctions/ArithmeticLorentzianGeometry/TheOverlapRatioIsTheCoveredMeasure.lean).

Even the corrected bound \(W_\omega+2S^2\ge0\) fails for a bounded sign twist on a wide two-atom dipole. A universal all-twist method therefore cannot cover every width. Neither this nor Fourier–Dirichlet factorization gives a strict bandlimit or Nyquist theorem for zeta zeros. [Universal threshold](../../../formal/GaloisForLFunctions/SpacingScaleHarmonicAnalysis/TheUniversalThresholdIsFinite.lean), [single-zero weights](../../../formal/GaloisForLFunctions/SpacingScaleHarmonicAnalysis/TheWeightOfOneZero.lean).

### 3. Adjunction connects to actual prime modes, with an exhaustion gap

For the prime-only matrix \(P_N\), the sharp ceiling is \(\log N-\gamma+o(1)\), with an exact nonnegative Dirichlet defect. The torsion counterterm is instead \(\varphi\log N+O(1)\), \(\varphi=(1+\sqrt5)/2\). The extremal Rayleigh edges of \(\alpha\operatorname{diag}(\log n)+P_N\) are \(\kappa_\pm\log N+O_\alpha(1)\), where \(\kappa^2=\alpha\kappa+1\). The joint height/prime numerical range has a semicircle upper envelope; no interior spectral-filling theorem follows. Renormalized torsion positive index has a sublinear upper bound \(N^{4/5+\varepsilon}\), alongside polynomial lower bounds; this is not a Weil index bound. [Prime ceiling](../../../formal/GaloisForLFunctions/RenormalizedArithmeticPotentialTheory/ThePoleIsTheTopOfThePrimeForm.lean), [fixed-point family](../../../formal/GaloisForLFunctions/RenormalizedArithmeticPotentialTheory/TheSelfIntersectionFamilyObeysAFixedPointLaw.lean), [torsion index ceiling](../../../formal/GaloisForLFunctions/ArithmeticIntersectionTheory/ThePositiveSquaresOfTheTorsionFormLiveBelowFourFifths.lean).

For each finite prime set \(Q\), the matched adjunction operator on the actual \(Q\)-supported-integer ℓ² carrier is self-adjoint on its maximal logarithmic domain, with complete product-Blaschke eigenbasis, simple energies

\[
E_m=\gamma+\log m+\operatorname{tameDifferent}(m)
=\gamma+2\log m-\operatorname{selfIntersection}(m)
\]

and compact shifted inverse. A fixed-support sieve-horizon defect converges to its quadratic form. The raw one-prime tower finite part is nonnegative at every depth exactly for primes \(p\ge47\); valuation potential pays all fourteen deficits at \(p\le43\). [Adjunction](../../../formal/GaloisForLFunctions/RenormalizedArithmeticPotentialTheory/TheSieveOperatorHasTheAdjunctionEigenbasis.lean), [source landing](../../../formal/GaloisForLFunctions/RenormalizedArithmeticPotentialTheory/TheSieveHorizonDefectIsTheAdjunctionOperator.lean), [compact resolvent](../../../formal/GaloisForLFunctions/RenormalizedArithmeticPotentialTheory/TheAdjunctionResolventIsCompact.lean), [prime threshold](../../../formal/GaloisForLFunctions/RenormalizedArithmeticPotentialTheory/TheTowerDeficitChangesSignBetweenFortyThreeAndFortySeven.lean), [valuation payment](../../../formal/GaloisForLFunctions/RenormalizedArithmeticPotentialTheory/TheArchimedeanPlacePaysTheTowerDeficit.lean).

The **full finite prime matrix** has an actual fixed-mode comparison. Ramanujan coefficients factor into valuation steps; completed prime-row corrections carry energy \(\log m+\operatorname{tameDifferent}(m)\), with summable tails uniform in the row at fixed \(m\). The profiles \(v_m(n)=c_m(n)/\sqrt{\phi(m)n}\) have Gram divided by \(\log N\) tending to the identity on each fixed conductor family, and

\[
\frac{\|(P_N-(\log N-E_m))v_m\|_2^2}{\log N}\longrightarrow0
\quad(m\text{ fixed}).
\]

All positive conductor labels have distinct \(E_m\). The assembled quasimode and distinct-energy declarations are working source. Nearby finite-matrix eigenvalues can be obtained by applying the existing Hermitian residual lemma. **Growing-mode uniformity, complementary-source control and full Gamma/pole coupling remain open**; neither spectral completeness nor a Xi spectral realization follows. [Completed rows](../../../formal/GaloisForLFunctions/RenormalizedArithmeticPotentialTheory/TheRamanujanPrimeRowsHaveAdjunctionEnergy.lean), [tails](../../../formal/GaloisForLFunctions/RenormalizedArithmeticPotentialTheory/TheRamanujanPrimeCorrectionHasAUniformTail.lean), [Gram limit](../../../formal/GaloisForLFunctions/RenormalizedArithmeticPotentialTheory/TheRamanujanPoleProfilesAreAsymptoticallyOrthonormal.lean), [quasimodes](../../../formal/GaloisForLFunctions/RenormalizedArithmeticPotentialTheory/TheRamanujanPoleProfilesArePrimeQuasimodes.lean), [distinct energies](../../../formal/GaloisForLFunctions/RenormalizedArithmeticPotentialTheory/TheRamanujanAdjunctionEnergiesAreDistinct.lean), [residual lemma](../../../formal/GaloisForLFunctions/HTGeometry/HermitianResidualFindsAnEigenvalue.lean).

The actual prime form has a uniform gap on its **harmonic pole hyperplane**: some \(g>0\) gives \(P_N(x)\le(\log N-\gamma-g+\varepsilon)\|x\|_2^2\) eventually for every \(\sum_{n\le N}x_n/\sqrt n=0\). On this same fixed hyperplane the Liouville-twisted form attains \(\log N-\gamma-o(1)\). This is constrained sign selectivity, not full continuous Weil positivity. The discrete harmonic constraint must be compared with the actual exponential pole coordinates. [Gap](../../../formal/GaloisForLFunctions/RenormalizedArithmeticPotentialTheory/ThePrimeFormHasASpectralGapBelowItsPole.lean), [separation](../../../formal/GaloisForLFunctions/RenormalizedArithmeticPotentialTheory/ThePoleHyperplaneSeparatesZetaFromItsLiouvilleTwin.lean).

Leading polar matching remains nonselective: Euler and finite prime flips have coefficient +1, Liouville −1 and extended nonprincipal real prime-conductor characters 0. A sign gauge with \(A_\epsilon(y)=\kappa\log y+\alpha+o(1)\) has leading polar coefficient \(\kappa\) and finite part \(2\alpha\), with explicit **absolute-profile** errors. Leading-order convergence alone determines \(\kappa\); a mass-scale remainder has a separate logarithmic-mean criterion. Nonprincipal character Mertens sums converge to \(-L'/L(1,\chi)\); real prime-conductor extensions add the ramified term. [Leading-order criterion](../../../formal/GaloisForLFunctions/RenormalizedArithmeticPotentialTheory/PolarMatchingNeedsOnlyTheLeadingOrder.lean), [finite-part law](../../../formal/GaloisForLFunctions/RenormalizedArithmeticPotentialTheory/TheFinitePartIsTwiceTheMertensLimit.lean), [character value](../../../formal/GaloisForLFunctions/RenormalizedArithmeticPotentialTheory/TheCharacterMertensLimitIsTheLogarithmicDerivative.lean).

For Liouville, the finite part is \(2(\gamma+\tau)\), where the convergent even-prime-power correction satisfies \(\tau\ge(\log2)/2>0\); Euler's is \(-2\gamma\). Their difference on pole-neutral step profiles has positive main coefficient \(2(2\gamma+\tau)\). Its error uses the absolute coefficient budget, so this is **not** a uniform mass-relative gap for every signed profile. It is distinct from the uniform prime pole-gap theorem. [Finite-part separation](../../../formal/GaloisForLFunctions/RenormalizedArithmeticPotentialTheory/TheFinitePartSeparatesZetaFromItsLiouvilleTwin.lean).

Fixed BV profiles \(g(\log n/\log N)/\sqrt n\) have Euler finite-part error at most \(\eta\log N+C_{\eta,g}\); arbitrary discrete profiles have variation-squared bounds. Valuation classes have growing-rank leading counterterms, while fixed-modulus unit-residue classes have rank one, \((q/\phi(q))\ell^2\), reading only the class-function mean. Neither fixed-profile asymptotics nor fixed-Q two-horizon uniformity controls growing variation, modulus and prime sets simultaneously. [BV laws](../../../formal/GaloisForLFunctions/RenormalizedArithmeticPotentialTheory/TheHorizonLawsHoldForProfilesOfBoundedVariation.lean), [residue law](../../../formal/GaloisForLFunctions/RenormalizedArithmeticPotentialTheory/TheHorizonSeesOnlyTheMeanOfAClassFunction.lean), [two horizons](../../../formal/GaloisForLFunctions/RenormalizedArithmeticPotentialTheory/TheFiniteSieveUnitGramHasTwoHorizons.lean).

### 4. Canonical critical energy separates finite support from RH

Let \(\mathcal W(R)\) be damped arithmetic source work, \(\Delta\mathcal W(R)=\mathcal W(2R)-\mathcal W(R)\), and \(K(R)=R^2\Delta\mathcal W(R)\), \(R\ge4\). Define

\[
I_*=\frac{1294047}{4000},\qquad Q_*=2I_*=\frac{1294047}{2000}.
\]

These are quadraticIndexUnit and quadraticExclusionQuantum, derived from height-square bound \(431349/2000\). The source rate \(K\) is nonnegative, monotone and converges in the extended nonnegative reals to canonical energy \(\mathcal E_{\rm crit}\). Its pair kernel is entrywise nonnegative; no PSD Gram-kernel assertion follows. Off-line/critical exterior interactions belong to the energy and cannot be discarded. [Monotonicity](../../../formal/GaloisForLFunctions/ArithmeticIndexDescent/TheCriticalSourceRateIsMonotone.lean), [canonical energy](../../../formal/GaloisForLFunctions/ArithmeticIndexDescent/TheCriticalSourceRateHasACanonicalEnergy.lean).

| Arithmetic bound | Exact consequence |
|---|---|
| Bounded \(\mathcal W\) | Finite off-line support; equivalently bounded integer-log spline negative index. |
| \(\Delta\mathcal W(R)\to0\), or eventually \(\Delta\mathcal W(R)\le39/50\) | Finite off-line support. |
| \(\Delta\mathcal W(R)\le39/50\) for **every** \(R\ge4\) | RH. |
| Eventual boundedness of \(K\), or \(\mathcal E_{\rm crit}<\infty\) | Finite off-line support. |
| \(K(R)\le Q_*\) cofinally, or \(\mathcal E_{\rm crit}\le Q_*\) | RH. |
| \(\mathcal W(R)\le2\) cofinally | RH. |

The trichotomy is \(K\equiv0\) under RH; convergence to finite \(L>Q_*\) for finite nonempty off-line support; divergence to infinity for infinite support. In the finite case, \(L=(3/2)\sum_{\text{off-line copies}}\gamma_\rho^2d_\rho F_\rho\). This source moment has signed individual terms, despite the nonnegative pair-energy representation. Every finite actual Weil negative index \(k\) forces

\[
\mathcal E_{\rm crit}\ge\max\{I_*k,\ 50k^2-3k/2\}.
\]

The quadratic cost comes from a global reciprocal-height budget. These are **lower** bounds; arithmetic **upper** control sufficient for finiteness or RH remains missing. [Classification](../../../formal/GaloisForLFunctions/ArithmeticIndexDescent/TheCriticalRateClassifiesAllOffLineSupport.lean), [quantum](../../../formal/GaloisForLFunctions/ArithmeticIndexDescent/TheQuadraticScaleWorkDetectsEveryException.lean), [linear payment](../../../formal/GaloisForLFunctions/ArithmeticIndexDescent/TheCriticalRatePaysEveryNegativeSquare.lean), [quadratic payment](../../../formal/GaloisForLFunctions/ArithmeticIndexDescent/TheSourceBudgetMakesTheIndexCostQuadratic.lean), [unscaled criterion](../../../formal/GaloisForLFunctions/ArithmeticIndexDescent/VanishingScaleIncrementsCharacterizeFiniteSupport.lean).

### 5. Lorentzian closure has an arithmetic identification boundary

Finite products of Lorentzian local polynomials and nonnegative substitutions are mixed-Lorentzian. The Hessians attainable at nonnegative points are exactly symmetric entrywise-nonnegative Lorentzian forms; every such matrix is the Hessian of its quadratic polynomial. A negative entry forbids literal identification in those coordinates. Closure supplies a calculus, not a selective arithmetic construction. [Finite products](../../../formal/GaloisForLFunctions/ArithmeticLorentzianGeometry/TheEulerProductOfLorentzianLocalFactorsIsLorentzian.lean), [exact Hessian class](../../../formal/GaloisForLFunctions/ArithmeticLorentzianGeometry/TheClosureProducesExactlyTheLorentzianForms.lean).

Under the stated positive-coefficient normalization, top coefficient \((\sqrt q)^d\) and Ramanujan trace bound \(a_1\le d\sqrt q\), Lorentzian log-concavity forces the reverse inequality. Equality is the only possible boundary; at prime \(q=p\), integral trace excludes it. For elliptic quadratic factors the Lorentzian condition \(a_1^2\ge4p\) opposes Hasse's bound. Frobenius **Gram** positivity survives; these local L-polynomials cannot supply the proposed Lorentzian factors. [Obstruction and survivor](../../../formal/GaloisForLFunctions/ArithmeticLorentzianGeometry/RamanujanAndLorentzianMeetOnlyAtTheWeilBound.lean).

For the ordinary-coefficient Xi Jensen family, \(dJJ''\le(d-1)(J')^2\) is proved on \(s\ge0\). It gives no negative-half-line or all-degree real-rootedness theorem. Coefficient normalizations remain essential. [Half-line Laguerre law](../../../formal/GaloisForLFunctions/ArithmeticLorentzianGeometry/TheJensenPolynomialsOfXiSatisfyLaguerreOnTheHalfLine.lean).

## Live routes

Each entry separates the existing receiver from the arithmetic input it still needs. Source links are representative entry points; the [frontier map](../rh-current-frontier-map.md#live-routes) supplies additional modules.

### WL — Weil lag / prime-error energy

**Current:** Bounded critical energy, a lower bound on coprime cross-work, and a linear cumulative prime-error budget are exact RH receivers. A sharper Abel-slope saturation asks for RH **and simple zeros**.

**A:** Evaluate fixed truncations with certified archimedean and high-zero tail errors; transport the established lag, count and energy dictionaries with constants intact.

**B:** Prove the actual signed cross-work or linear prime-error energy bound. The relevant cancellation is missing. Simplicity/genus saturation is a stronger separate target and must not be inserted as an RH premise. [Receiver](../../../formal/GaloisForLFunctions/BiScaleUncertainty/WeilLagCriticalDeficitEndpointAndLimitLaw.lean).

### RW — Restricted Weil ground energy

**Current:** RH iff the ground minimum is positive at every finite aperture. Its strict decrease and shell decomposition are known; finite-aperture Gårding bounds permit a nonzero negative index.

**A:** Produce certified finite-aperture variational bounds and explicit shell/error ledgers. Such calculations may certify positivity on a specified window or expose an unpaid term.

**B:** Bound total aperture relaxation by the available initial energy, retaining low modes, prime collars and polar terms. Monotonicity and telescoping do not supply that inequality. [Aperture flow](../../../formal/GaloisForLFunctions/ArithmeticContinuationAndCriticalEnergy/TheApertureFlowNeverStalls.lean).

### FU — Signed prime scheduling

**Current:** An eventual upper bound on the normalized completed Abel moment implies and is equivalent to RH. Narrow translated prime channels have a useful sign; a universal extension of that sign to dyadic windows is false.

**A:** Assemble the exact initial-seed, drift, earlier-history, cross-block and endpoint terms for a fixed schedule; use existing clock kernels to evaluate them.

**B:** Bound their **joint signed total** over a prime-exhaustive schedule. Isolated channel gains or vanishing diagonal costs do not give the required complete-history bound. [Receiver](../../../formal/GaloisForLFunctions/RHTower/CCM/CCMFUSuzukiMobiusDivisorOneSided.lean).

### RP — Matched–quantile history floor

**Current:** An eventual linear defect floor is RH-equivalent. Low-LCM payment and exact signed history identities are available.

**A:** Expand fixed histories, instantiate low-LCM estimates and expose the high-LCM/moving-core remainder in the native domain.

**B:** Prove the complete floor with those remainders and singular-domain transport controlled together. Positive damping-shell traces do not establish it. [Receiver](../../../formal/GaloisForLFunctions/RHTower/SPEQuantileRieszRoutePLinearFloorCriterion.lean).

### PA — Prime–archimedean passivity

**Current:** Exact current-sign, Bernstein-mismatch and signed compact-moment receivers exist. Every fixed moment order eventually becomes positive after a sufficiently large shift.

**A:** Compute explicit thresholds for specified finite order blocks and propagate already proved source/trace errors.

**B:** Establish the all-order/all-shift sign, high-frequency accretivity, or every-positive-rate mismatch estimate. Order-dependent thresholds cannot be exchanged for one common threshold. [Signed completion](../../../formal/GaloisForLFunctions/RHTower/PrimeArchSignedCompactCompletionCollapse.lean).

### MC — Möbius cancellation

**Current:** Every strict half-power cancellation bound, or subpower Hilbert energy, is RH-equivalent. Escaped-endpoint VK decay and exact strip/rate dictionaries are available. Character Burgess estimates and typical-gauge cancellation do not select actual Möbius coefficients.

**A:** Specialize fixed-modulus and below-diagonal estimates; state all rates in one normalization; translate a supplied strip bound through existing dictionaries. Reconcile the external fixed-strip announcement separately.

**B:** Reach every strict half-power for the actual moving arithmetic source, or exclude every subcritical oscillating probe. A linear Mertens energy budget additionally forces simple zeros and inverse-derivative residue summability; it is stronger than an arbitrary RH receiver. [Hilbert criterion](../../../formal/GaloisForLFunctions/RHTower/MobiusHilbertFormEquivalence.lean), [strip dictionary](../../../formal/GaloisForLFunctions/BezoutValuationIncidence/UnconditionalEscapedMoebiusDecayAndCrossRouteBridge.lean).

### TT — Theta tails and directed covariance

**Current:** The theta source has exact seam, Wold and odd-Weil receivers, with the required sub-half parameter range explicit.

**A:** Evaluate fixed directed-covariance and reflected-prime terms; apply established continuum and short-support identities without dropping endpoints.

**B:** Prove signed nonlocal covariance control at every required rapidity and scale, or complete odd/primitive positivity. Translation averaging can erase the transverse information needed here. [Wold receiver](../../../formal/GaloisForLFunctions/RHTower/PaperWoldDirectedCovarianceRH.lean).

### LA — Line anchor / Jensen and heat signs

**Current:** Finite-head/heat receivers and positive complementary tails are available. Ordinary Xi coefficient families satisfy Turán/Lorentzian laws and the Jensen Laguerre inequality on the nonnegative half-line; generic finite-product and substitution closure is established. None gives the required all-degree real-rootedness or signed negative-half-line control.

**A:** Certify selected finite heads and low-degree inequalities; translate coefficient conventions carefully, including factorial normalization; apply existing heat-tail errors.

**B:** Establish the remaining actual all-height/all-degree head signs, especially low orders and near-double configurations. No source supplies all required repairing factors. [Finite-head reduction](../../../formal/GaloisForLFunctions/RHTower/XiSliceHeatFiniteHeadReduction.lean), [Lorentzian scope](../../../formal/GaloisForLFunctions/ArithmeticLorentzianGeometry/TheHessianOfALorentzianPolynomialTricklesDown.lean), [mixed Hessians](../../../formal/GaloisForLFunctions/ArithmeticLorentzianGeometry/TheMixedHessiansOfALorentzianPolynomialAreHyperbolic.lean), [substitution closure](../../../formal/GaloisForLFunctions/ArithmeticLorentzianGeometry/TheLorentzianClassIsClosedUnderNonnegativeSubstitution.lean).

### TG — Integer trace below one

**Current:** Winding, cubic transgression and central-gap receivers are explicit. Gaussian coprime-divisibility covariance has a sign on its stated indicator class.

**A:** Calculate finite projection/transgression data and retain the residual and trace separately.

**B:** Produce a matrix-complete decomposition with nonnegative residual and integer trace below one on every required disc, or a zero-rate central-gap bound. Indicator covariance does not control arbitrary signed Euler-inverted combinations. [Index estimate](../../../formal/GaloisForLFunctions/RHTower/RestrictedProjectionIndexOperatorNormCriterion.lean).

### HF — Arithmetic Hodge positivity

**Current:** Full Hodge/Weil sign, zero Hecke defect and sufficiently small source work are exact receivers. Complete cells capture all finite negative indices; positive sections have bounded projections and fixed-width graph coercivity. Canonical critical energy has a monotone source limit and linear/quadratic index lower costs. Fixed-conductor Ramanujan modes transfer adjunction energies to the actual prime matrix.

**A:** Form actual finite mixed Grams, their projections and residuals; transport existing source-kernel cost bounds; keep distinct-index and multiplicity-weighted energies separate.

**B:** Prove complete-cell/complementary positivity, or an arithmetic upper bound at a sufficient work/defect threshold. Neither positive collided mass nor a computable defect gives this sign. This is a central meeting point for U1 and U2, not a closed route. [Index capture](../../../formal/GaloisForLFunctions/ArithmeticIndexDescent/TheCompleteCellsCaptureEveryFiniteIndex.lean), [work threshold](../../../formal/GaloisForLFunctions/ArithmeticIndexDescent/TheSourceWorkHasAClosedQuantumThreshold.lean).

### CHMD — Causal hyperbolic–modular duality

**Current:** Wave/Doob receivers and supported graph completion are established. One fixed unbounded integer-log cell carrier has full-graph coercivity, a bounded Weil projection and exact residual. The carrier is proper and its complement contains an infinite theta radical; these null directions are not negative witnesses.

**A:** Apply domain/cutoff theorems to fixed sources and compute the signed residual with the retained primitive defect.

**B:** Prove the complete one-sided wave bound or odd Doob/nodal inequality. Domain admission and convergence do not pay reflected-prime interactions. [Odd criterion](../../../formal/GaloisForLFunctions/RHTower/CHMDOddSectorCriterion.lean).

### TH — Theta moment positivity

**Current:** All ranks have strict positivity on nonzero **nonnegative** coefficient vectors over a common small positive-time interval. Fixed-rank stable regions are also known.

**A:** Calculate finite signed test blocks and track degree/time dependence explicitly.

**B:** Obtain positivity for arbitrary signed vectors at every degree under the required common time, or an equivalent full-current sign. Orthant positivity is not positive semidefiniteness. [Orthant theorem](../../../formal/GaloisForLFunctions/RHTower/XiHeatHankelFormOrthantPositivity.lean).

### RN — Renewal and singular comparison

**Current:** Actual theta renewal has solvers, a compact cone-positive operator, exact determinant resonances and multiplicity bookkeeping.

**A:** Compute finite packet/resolvent data in the admitted topology and carry cusp/seam terms through the known formulas.

**B:** Prove directed boundary-work orientation or the full mixed prime-plus-Gamma versus pole inequality. Cone positivity does not imply real spectrum, and an inadmissible unregularized completion cannot replace the source. [Exact spectrum](../../../formal/GaloisForLFunctions/RHTower/ThetaRenewalFredholmSpectrum.lean).

### WD — Ward caps and collision

**Current:** A nonnegative integrated cap vanishes iff RH. Finite-head/tail laws and sharp model heat-repair costs are established.

**A:** Evaluate cap/head data on fixed compact regions using available tail bounds and attained model extremizers.

**B:** Prove actual cap extinction, Euler–Stieltjes saturation, or the requisite all-height coefficient sign as heat becomes arbitrarily small. Knowing the exact repair price does not show the actual divisor pays it. [Ward receiver](../../../formal/GaloisForLFunctions/RHTower/XiWardGlobalCapAndFiniteHeadArithmetic.lean).

### LI — Paired Li balances

**Current:** Every-positive-rate lower floors for the actual prime–Gamma clock are RH-equivalent. The unconditional reciprocal-depth rate bound is not a zero-width result.

**A:** Compute fixed paired histories and compare their first-crossing/outside-correlation terms under existing identities.

**B:** Prove a subexponential lower floor for the literal complete primitive. Removing the adverse terms changes the receiver. [Clock growth](../../../formal/GaloisForLFunctions/RHTower/LiEvenCrossActualClockGrowthLaw.lean).

### SZ — Suzuki first variation

**Current:** The compact-L² first variation equals the full Weil form, including the complete primary contribution. Moving-primary and finite-head limits have scoped transfer theorems.

**A:** Apply those limits to specified source families, keeping low and mixed terms and source-dependent neighborhoods visible.

**B:** Prove first-variation sign on an RH-complete family. High-scale positivity alone does not exhaust it. [Full first variation](../../../formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiCriticalL2FirstVariation.lean).

### PM — Haar approximation / damped admission

**Current:** Global Haar approximation, cofinal signed-damping admission and positive gauge mass for every actual subcritical escape state are exact receivers. Compact maximal-visible-order laws classify possible residue concentration.

**A:** Calculate fixed compact cofactor Grams and apply existing energy-transfer/residue formulas, including effective pole orders.

**B:** Bound complete energy as damping tends to zero, or prove visibility of every escape state. Exterior mass, infinite-height escape, paid-cofactor coercivity and joint horizon control remain unresolved. Compact classification alone does not imply tightness. [Haar receiver](../../../formal/GaloisForLFunctions/RHTower/FermiNymanHaarApproximationEquivalence.lean), [escape criterion](../../../formal/GaloisForLFunctions/ArithmeticCorrespondencePositivity/TheEscapeCompletenessCriterion.lean).

### JAS — Joint ancestry

**Current:** Level-one prime-product positivity and finite-power square-shell bounds are exact receivers. The Gamma–theta source is admitted for all finite supports, phases and grades; unconditional signs reach a logarithmic prime budget.

**A:** Instantiate finite support/grade formulas and measure the exact budget gap on selected shells.

**B:** Reach the half-power prime budget or all-amplitude/every-exponent shell control. Admission of the source does not enlarge the proved positivity budget. [Level-one capstones](../../../formal/GaloisForLFunctions/RHTower/JointAncestryLevelOneCapstones.lean).

### CTF — Chronological / Báez–Duarte approximation

**Current:** The residual splits exactly as `(1 − Λ-readout)² + centered pronic energy`; vanishing global approximation error is RH-equivalent. Readout alignment and logarithmic lower floors are known.

**A:** Optimize/certify finite rows and report both residual components, with explicit moving-tail errors.

**B:** Produce bounded rows whose **complete** error tends to zero, or the arithmetic dual-sampling bound. A diagonal floor does not refute approximation, but diagonal control and aligned readout do not prove it. [Readout criterion](../../../formal/GaloisForLFunctions/BezoutValuationIncidence/VonMangoldtReadoutFormOfTheBaezDuarteCriterion.lean).

### HCF — Gaussian heat trace and two-grid signs

**Current:** Exact archimedean-minus-prime Gaussian traces, inertia and a two-grid RH criterion are available. Both literal log 2/log 3 grids with pole cancellation are required; one grid aliases configurations.

**A:** Compute finite degrees/heights on both grids and propagate explicit trace/polar errors.

**B:** Prove both actual grid signs at all required degrees and heights, or the complete one-sided vertical-growth bound. A second grid supplies detection, not positivity. [Two-grid criterion](../../../formal/GaloisForLFunctions/RHTower/XiGaussianHeatTwoPrimeSourceSampling.lean).

### XN — Newton invariant discs

**Current:** Line-centered self-map discs covering all zeros give RH. The interior margin has an exact curvature formula. Polynomial pole repair is local and preserves root jets.

**A:** Certify specified discs and their curvature integrals using actual source jets.

**B:** Supply a covering family with nonnegative **interior** margin. Boundary sign does not pay the Green potential; global scalar damping is not a viable repair. [Disc criterion](../../../formal/GaloisForLFunctions/RHTower/XiNewtonSchwarzPickCriticalLine.lean).

### BAG — Deterministic self-return

**Current:** Actual-zeta recurrence throughout the right strip, or the corresponding positive-Haar-mass condition, is an RH receiver. Off-line zeros obstruct the required local return density.

**A:** Make finite-head return/error estimates explicit on chosen zero-free compact targets.

**B:** Prove recurrence at every right-strip point and every tolerance, including possible target-zero neighborhoods. Universality for zero-free targets does not remove those exceptions. [Return receiver](../../../formal/GaloisForLFunctions/RHTower/ZetaStrongRecurrenceReceiver.lean).

### EWU — Even pole-weight uniqueness

**Current:** Attained even blind minima give an exact all-aperture criterion. Full positivity holds in specified high-scale windows and sparse unions, and locally through radius 181/500.

**A:** Certify finite even blind problems and use quantitative cycle recovery only on its stated energy/support class.

**B:** Prove nonnegative minima at every aperture, paying low/mixed modes on the complete even cone. Sparse high-scale positivity and approximate recovery do not provide that sign. [Variational receiver](../../../formal/GaloisForLFunctions/RHTower/EvenSectorBlindVariationalAttainment.lean).

### GTA — Transverse Schur charge

**Current:** Rank-uniform decay of the actual positive quartic Schur charge is RH-equivalent. Finite-prefix convergence and compactness diagnostics are available.

**A:** Calculate finite-rank charges and retain explicit rank dependence in truncation errors.

**B:** Prove arithmetic transverse-energy decay uniformly in rank. Strong convergence at each fixed prefix cannot be substituted. GTA is a live route, not a candidate. [Decay equivalence](../../../formal/GaloisForLFunctions/RHTower/Hedenmalm/HedenmalmThetaSchurQuarticSpectralDecayEquivalence.lean).

### OWU — Odd Weil-weight uniqueness

**Current:** Exact odd/pole-hyperplane and dilation-ray criteria exist. Smooth witnesses distinguish actual Λ from Liouville and a first-prime flip; a radius-23/40 witness also reads primes 2 and 3. These are selective witnesses, not all-test positivity at that radius.

**A:** Extend certified finite-collar accounting, retaining signed autocorrelations and both pole corrections. Locate exactly which finite prime data each aperture reads.

**B:** Prove all-aperture actual-Λ odd sign or the equivalent all-ray condition. Companion forcing and the available conductor horizon have no common sufficient range; zero-ordinate large-value counts do not exclude individual exceptions. [Dilation criterion](../../../formal/GaloisForLFunctions/RHTower/WeilDilationRayCriterion.lean).

### PBM — Pole-regularized prime series

**Current:** Convergence of the fixed signed pole-subtracted coefficients at every real abscissa above 1/2 is an exact RH criterion. Raw positive prime series cannot have this convergence.

**A:** Compute regularized partial sums and explicit tails in already controlled half-planes; translate supplied coefficient estimates into convergence.

**B:** Prove critical-abscissa cancellation for the actual coefficients. Pole subtraction removes a main term, not the remaining arithmetic oscillation. [Regularized criterion](../../../formal/GaloisForLFunctions/RHTower/RegularizedLogZetaAbscissa.lean).

### RB — Robin / Nicolas extremizers

**Current:** Eventual criteria and reduction to colossally abundant integers are established. Fixed exponent/valuation defects give margins and restrictions on large counterexamples.

**A:** Enumerate and certify finite extremal ranges and apply fixed-defect margins with their constants.

**B:** Control the moving remainder on increasingly prime-saturated extremizers or primorials. Necessary divisibility constraints do not contradict their existence. [CA reduction](../../../formal/GaloisForLFunctions/RHTower/RobinColossallyAbundantReduction.lean).

### SRT — Lag localization and atomic visibility

**Current:** Every-width lag bounds, second-order atomic synthesis and canonical index/work laws detect all possible off-line zeros. Widths (log N)^α/N with α>1/4 are RH-complete. Bounded-overlap row costs and covered-measure limitations are explicit.

**A:** Instantiate fixed-width detectors and synthesis errors; compute finite atomic Grams while distinguishing pure Markov, full Weil and pole-hyperplane forms.

**B:** Prove an actual late-lag bound, zero-rate orbit estimate, complete overlap sign or sufficient work ceiling. Detection and per-zero bounds do not supply a collective source upper estimate. [Lag receiver](../../../formal/GaloisForLFunctions/SquareRootThreshold/EveryWidthDecidesTheCriticalLine.lean), [atomic receiver](../../../formal/GaloisForLFunctions/SpacingScaleHarmonicAnalysis/TheSecondOrderSynthesis.lean).

### ACT — One-shift arithmetic criticality

**Current:** For one fixed positive theta shift, a full all-profile variation inequality gives odd Weil positivity and RH. Short-support collars can be absorbed with support-dependent shifts.

**A:** Evaluate the complete signed moment ledger for a prescribed profile/shift and apply the known short-support estimates.

**B:** Find one shift paying **every** support/profile, including exterior primes and signed/polar remainders. A shift chosen after the support does not meet the receiver's quantifiers. [Short-profile scope](../../../formal/GaloisForLFunctions/ArithmeticCriticalityTheory/ShortProfilePoleFreeVariationInequality.lean).

### AIP — Arithmetic incidence allocation

**Current:** Global joint allocation is exactly the odd sign/RH problem. Complete-cell transfer and narrow Hodge/TD are established. High balanced Haar sections have a full rough-Weil floor uniform in upper horizon, with prime, Gamma and both poles paid. Coarse and mixed-scale residuals remain.

**A:** Assemble complete finite incidence matrices with every successor, Gamma and polar contribution; calculate shared spending and existing mixed-entry errors once.

**B:** Prove signed allocation on source-complete cells or an RH-complete overlap family. Independent edge payments overspend shared resources. Beyond-spacing Metzler gauge extension is obstructed, so the full sign needs a different argument. [Allocation criterion](../../../formal/GaloisForLFunctions/ArithmeticIncidencePositivity/GlobalIncidenceAllocationCondition.lean).

### ACS — Arithmetic effectivity

**Current:** Source RR, effectivity, Rosati-height and chirality receivers coexist with complete-cell realization and exact index capture. High Haar sections have a horizon-uniform full-form floor; a proper unbounded cell carrier has a bounded projection. Finite-sieve adjunction and distinct fixed-conductor full-prime quasimodes are available, without complete-source effectivity.

**A:** Transport fixed finite source families into complete smooth cells; calculate actual section/projection/finite-sieve data without assuming positivity.

**B:** Prove full-source quadratic RI with degree-zero subquadratic growth, an actual Rosati-height lower bound, or complete-cell index zero. Counts, positive separated sections and a finite-prime spectrum do not establish any of these. [Effectivity receiver](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/ExactArithmeticSourceEffectivity.lean), [complete transfer](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/CompleteWeilSourceTransfer.lean).

## Route candidates and promotion obstacles

These entries lack an independent source construction or its required landing. An abstract RH receiver inside a candidate does not discharge that gap. Finite calculations in column A are useful preparation, not a promised promotion.

| Candidate | Established mechanism | A — Just work | B — Research / promotion gap |
|---|---|---|---|
| **APF — Arithmetic paired Fredholm** | Actual cycle traces have arithmetic Fourier reconstruction, with one exceptional set for countable families and finite mixtures. | Instantiate fixed cycles, flows and finite combinations with explicit truncation control. | Produce zero-independent divisor exhaustion and trace vanishing. Reconstruction of an off-line coefficient does not annihilate it. [Source](../../../formal/GaloisForLFunctions/RHTower/PaperZetaCycleFourierReconstruction.lean). |
| **BSH — Arithmetic mate curvature** | One-sided framed composition curvature vanishes exactly at critical half-density. | Compute finite curvature/cocycle identities and their calibration. | Construct the pre-divisor section and actual-source mate identity that forces this vanishing at zeros. Neutral radial character cannot be assumed. [Source](../../../formal/GaloisForLFunctions/RHTower/Deninger/DeningerOneSidedFramedMateCurvatureTransgression.lean). |
| **CDC — Constitutive dagger** | Calibrated descending/confluent potentials exist exactly on the critical line. | Calculate finite repair/exchange defects and test proposed descent identities. | Produce one arithmetic potential before divisor restriction and prove descent on every relevant fibre. Merely packaging confluence as a structure field assumes the conclusion. [Source](../../../formal/GaloisForLFunctions/RHTower/ConstitutiveDaggerConfluence.lean). |
| **DR — Dyadic roots** | Every dyadic level extends to the symmetric Littlewood zero-free cusp with fixed normalization. | Glue specified zero-free charts and track roots of unity/monodromy on known domains. | Extend compatibly to the whole strict-right domain. A cusp whose boundary tends to 1 does not reach 1/2; an external fixed-strip theorem would only enlarge that domain. [Source](../../../formal/GaloisForLFunctions/RHTower/XiSymmetricLittlewoodZeroFreeCuspDyadicRoots.lean). |
| **EGC — Pole-safe contour** | Complete copy correction and source extraction; the prescribed ray has a nonzero algebraic Gamma baseline. | Calculate corrected contours and isolate the baseline from the exponentially smaller arithmetic remainder. | Prove expanding outer-contour orientation excluding off-line copies. Enclosed-pole cancellation and false baseline-free decay cannot do it. [Source](../../../formal/GaloisForLFunctions/RHTower/PaperEGCSourceRayBaseline.lean). |
| **EWJ — Euler/Wold jets** | Source-defined three-channel histories converge; compact quotient records their cofinal character. | Compute fixed jets and compare their exact quotient characters. | Prove source admission and norm exhaustion into the RH receiver, controlling transverse gaps across depth. [Source](../../../formal/GaloisForLFunctions/RHTower/PaperEulerWoldDepthHistory.lean). |
| **FEL — Theta likelihood** | Entropy bookkeeping and an unconditional convergent BSY zero-sum identity. | Evaluate predeclared finite histories and the retained contrast terms. | Force cofinal balance from arithmetic independently of the zeros. Adaptive accounting or a positive off-line sum identity is not its vanishing. [Source](../../../formal/GaloisForLFunctions/RHTower/BalazardSaiasYorZeroSum.lean). |
| **HJ — Hurwitz reflection** | Two-seed reflection residual vanishing matches SEC charge and RH; HCF supplies a two-grid bridge. | Compute literal convergent fibres and translate between the established residual coordinates. | Force the actual residual to vanish before divisor-based calibration. An exact defect detector is not a producer. [Source](../../../formal/GaloisForLFunctions/RHTower/PrimeTailSeedHurwitzReflection.lean). |
| **IRK — Rotation-algebra trace** | Full Xi-jet completed relation is invertible exactly off the line; boundary trace/winding is known. | Calculate finite jet inverses, traces and source/cokernel comparison diagrams. | Construct a charged arithmetic projective/Poisson lift with integral analytic count. Completion contracts the off-line resolution and is not identified with the original Poisson source. [Source](../../../formal/GaloisForLFunctions/RHTower/PrimeRotationXiCompletedResolution.lean). |
| **MSC — Möbius–Sonin transport** | A fixed squarefree-discrepancy Hilbert source recovers Mellin moments and arithmetic counts; divisor/conormal transport is available. | Instantiate evaluation jets, finite readouts and existing transport equalities. | Prove source-faithful nonnegative Sonin/Weil energy. Hilbert admission and divisor preservation do not supply sign. [Source](../../../formal/GaloisForLFunctions/RHTower/SquarefreeDiscrepancyHilbertTransport.lean). |
| **PCS — Singular prime co-shift** | Exact shift-plus-defect decomposition; physical Mellin transport; strong finite-prime convergence. | Calculate the retained defect and finite cutoff errors in the correct carrier. | Annihilate the wall by a source-natural mechanism while retaining the forward mode. A unilateral shift with nonzero defect cannot be intertwined isomorphically with invertible dilation. [Source](../../../formal/GaloisForLFunctions/RHTower/PCSChronologicalDilationCarrierObstruction.lean). |
| **PTR — Photonic realization** | Positive lossless products have real zeros; existence of a locally uniform Xi limit is RH-equivalent. | Analyze proposed finite stacks and their exact transfer functions/errors. | Construct a prime-faithful nonlocal port without using unknown Xi zeros. The converse construction from zeros is not independent; the local continuum port has a gap. [Source](../../../formal/GaloisForLFunctions/RHTower/PhotonicLosslessProductPortRH.lean). |
| **RFHM — Support/grade forcing** | Full finite-support/phase/grade Gamma–theta source admission; exact retained/discarded norm law. | Compute coherent defects, phase/depth observables and finite support probabilities. | Find a source law sensitive to arithmetic phase/depth/compound orientation. Two energy probabilities and their entropy forget the inserted prime's log grade; reversible sewing remains nonselective. [Source admission](../../../formal/GaloisForLFunctions/RHTower/GammaThetaFullSupportSource.lean), [information boundary](../../../formal/GaloisForLFunctions/RHTower/PaperRFHMSurvivalInformation.lean). |
| **SC — Stokes/Witt–Krein** | Rigged chambers and almost-everywhere Fourier reconstruction; exact wall recovery occurs only for assigned wall vector zero. | Compute finite cross-fibre coordinates and error terms away from the singular wall. | Construct an arithmetic cross-fibre restriction/index that selects the wall. Almost-everywhere chamber recovery cannot prescribe its missing wall value. [Source](../../../formal/GaloisForLFunctions/RHTower/PaperKreinWallFourierCompletion.lean). |
| **SEC — Adjacent prime seam** | Exact seam-charge/essential-norm and time-one factorial-Fock criteria. | Evaluate finite jets and exact seam charges; translate HJ coordinates. | Prove actual all-order Fock boundedness or exact eventual compactness. Asymptotic smallness of a nonzero seam is insufficient. [Source](../../../formal/GaloisForLFunctions/RHTower/TimeOneGammaJetFockRHCriterion.lean). |
| **W1C — Clifford–Dirac / Lee–Yang** | Ferromagnetic Ising laws converging to the Riemann distribution force RH; specific harmonic mass prescriptions are impossible. | Check finite couplings, characteristic functions and necessary density/field constraints. | Construct source-defined couplings with the required centered limit, or a faithful infinite arithmetic scattering operator. Finite Hermitian-pencil Euler matching is excluded. [Source](../../../formal/GaloisForLFunctions/RHTower/IsingLawConvergenceRH.lean). |
| **WBF — Source certificates** | Abstract genealogy Gram and relative Fredholm recovery; relative completion characterized by certificate-weight summability. | Compute specified certificate streams and relative determinants. | Produce an arithmetic stream and uniform-depth completion landing on actual Xi/Weil data. No such coupling follows from the abstract certificate calculus. [Source](../../../formal/GaloisForLFunctions/HTGeometry/PaperCriticalGenealogyCompletion.lean). |
| **PW-B — PM physical cusp branch** | Native two-response action has a cutoff-independent limit with original causal gates. | Evaluate admitted positive-damping actions and explicit complementary responses. | Remove `XiZeroCopy` indexing and prove the chain from complete-energy ceiling through optical magnitude and ordered cap to all-divisor extinction. Current action formulas do not supply those implications. [Source](../../../formal/GaloisForLFunctions/RHTower/ThetaCusp/ThetaCuspHawkingBMPWNativeTwoResponseAction.lean). |

## Supporting programmes: what they add, what they do not close

| Programme | Available contribution | Unresolved mathematical input |
|---|---|---|
| BVI, arithmetic compensation and orientation dictionaries | Exact pronic/readout decompositions; fixed-row cancellation; VK escape decay; equivalent strip/rate currencies. | Actual complete signed energy at critical rate; moving-scale correlation, not another change of coordinates. |
| AID, ACS complete cells, SSHA | Source-complete approximation, bounded narrow-section projection, finite index capture, RH-complete atomic schedules. | Complete-cell/residual sign or an arithmetic index ceiling. |
| Balanced Haar-cell source | Signed prime compression, coherent Gamma/pole payment and a horizon-uniform full rough-Weil floor above one fixed lower index. | Coarse modes, mixed-scale payment and source-complete positive decomposition. |
| RAPT and arithmetic intersection | Sharp prime/torsion scales, pole-hyperplane gap, Liouville separation, BV/character finite parts, finite-sieve adjunction and fixed-conductor full-prime quasimodes. | Growing-conductor/modal-complement control and full Gamma/pole comparison under source exhaustion. |
| ALG | Actual narrow Hodge/TD, finite-product closure, exact Hessian class, half-line Xi Laguerre law and local-factor/Metzler obstructions. | An arithmetic signed/block construction beyond generic nonnegative closure and a faithful complete-form identification. |
| Arithmetic polarization, CDG, electrostatics | Positive collided form, faithful computation, theta-prefix detectors, field and moment-of-inertia identities. | Upper sign/cap on the computed defect at a sufficient threshold. |
| Arithmetic correlation geometry, signed successor arithmetic | Gauge classification, almost-everywhere cancellation, exact finite moment cones, polynomial charged-cell counts. | Selection of the actual arithmetic gauge and sufficiently uniform signed correlations. A positive-density cell count alone would still not prove full Weil positivity. |
| Pair correlation, IGP and large values | Quantitative simple-critical/distinct proportions, Schur slack and power-saving alignment counts under explicit parameters. | Eliminate exceptional zeros or prove matching-profile signed surplus bounds. A proportion or rare-event estimate does not provide zero exceptions. |
| Effectivity, positive duality, multiplicative positivity and finite-field calibration | Source identification, RR/Hodge equivalences, simple-pole rigidity, finite-field purity and Burgess tools. | An independently proved arithmetic effectivity/height/orientation input. Identities and positive counts alone admit impure models. |
| ALDG, heat and local divisor geometry | Sharp model repair costs, actual finite-head coordinates, asymptotic tail signs. | Actual all-height low-head sign and simultaneous degree/time control. |
| Closed-cycle, finite-incidence and physical sampling tools | Exact finite recovery, source-dependent conditioning and sharp finite-window coercivity. | Uniform source-faithful global sign/admission; injectivity with growing inverse cost is not such a bound. |

## Public mathematical status and literature intake

RH is still listed as unsolved by [Clay](https://www.claymath.org/millennium/Riemann-Hypothesis/). Consequently an unconditional sufficient input to any exact RH receiver above remains a breakthrough target unless an actual proof is supplied. Intermediate project formulations require their own novelty/literature assessment; their local absence is not evidence of worldwide impossibility.

External claims relevant to the research queue:

- A September 2026 [quasi-RH manuscript](https://github.com/openai/math/blob/main/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf) claims zero-freeness for Dirichlet L-functions in \(\Re s>7/8\), including zeta. This report inspected its theorem and scope, not its complete proof. Treat it as **external claimed proof**, not a local Lean result or proof of RH. If adopted, it supplies a fixed first strip; it does not yield all strips approaching 1/2. The corpus's counterexample to a cardinality-only shifted-character bound does not by itself refute a theorem using additional arithmetic structure.
- A September 2026 [ordinary-correlation manuscript](https://github.com/openai/math/blob/main/preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/final.pdf) claims fixed-affine-form Liouville two-point bounds \(C_{\mathrm{forms}}X/(\log X)^c\), and a qualitative corrected Elliott statement. This is not a power saving \(X^{1-\delta}\), nor a bound uniform for growing shifts or moduli. Fixed-form natural-density Chowla must therefore not be labelled “nobody has a solution.” Existing [logarithmic two-point Chowla](https://arxiv.org/abs/1509.05422) is a separate established input. Neither statement automatically pays the moving-source correlations in MC/PM/AIP.

Further distinctions prevent false open-problem claims. Standard [Lorentzian-polynomial theory](https://arxiv.org/abs/1902.03719) already provides powerful Hodge/Hessian tools; applying them to an independently identified arithmetic form is the missing step. The published [de Bruijn–Newman upper bound 0.22](https://arxiv.org/abs/1904.12438) must be compared only after matching heat normalization. [Current simple-zero work](https://arxiv.org/abs/2609.02882) concerns proportions; neither it nor the corpus's positive Schur-slack improvement eliminates all exceptions. Simplicity, Chowla and stronger pair-correlation statements are not automatically consequences of RH.
