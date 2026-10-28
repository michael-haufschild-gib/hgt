# Research routes and their mathematical obstacles

Status: 28 October 2026, corpus commit `d47ab4b5d`. **RH remains open.** The inventory is 31 live routes, 17 standalone candidates and the PW-B candidate branch of PM. Every live route has an exact RH receiver; none has the arithmetic input that receiver needs.

Companions: [summary, open problems and next questions](obstacles-summary.md) · [walls ledger](walls-ledger.md) · [route unification](route-unification-ledger.md) · [frontier map](../rh-current-frontier-map.md) · [scoped obstructions](../rh-killed-routes.md).

## How to read this report

Evidence comes from corpus searches followed by inspection of Lean statements, hypotheses and proof structure. No builds or kernel audits were run. **[S]** marks recent working source: results first committed on 28 October 2026, or with unfinished proofs. The [frontier map](../rh-current-frontier-map.md) carries the authoritative per-item [L]/[S] status. Statements keep their stated scope. Research record: [working log](../../../logs/review-2810-refresh-2026-10-28.log).

Obstacles are split into two classes:

- **A — Just work.** The mathematical ingredients exist: a finite computation with certified error terms, an instantiation of a proved theorem, transport of a supplied bound between proved dictionaries, or formalization of a paper proof. A-items can be large. They never promise that a desired sign is true.
- **B — Open mathematics.** A missing inequality, construction or uniformity. Tags: **[RH]** the statement is equivalent to RH, so nobody has a solution; **[RH+]** it is strictly stronger than RH (for example it also forces simple zeros); **[open]** an intermediate problem with no solution in the corpus or in the literature consulted, which might be solvable without solving RH.

A conditional receiver does not prove its input. A false proposed estimate belongs in neither class; it needs replacing.

## The frontier in seven results

### 1. The complete source is a dyadic multiresolution of itself

Complete logarithmic cells recover every mixed Weil entry of any fixed finite test family, including the Gamma term and both pole moments. Pole-preserving smoothing realizes the finite form on smooth tests, and complete cells capture every finite negative index. [Complete transfer](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/CompleteWeilSourceTransfer.lean), [smooth realization](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/SmoothFiniteCellArithmeticForm.lean), [index capture](../../../formal/GaloisForLFunctions/ArithmeticIndexDescent/TheCompleteCellsCaptureEveryFiniteIndex.lean).

On complete cells the Gamma (Lévy) energy pays every adjacent-pair difference, with all pair averages present [S]:

\[
\sum_{a=1}^{X}\log(a)\,h_a\,(u_a-v_a)^2\;\le\;\mathcal L\Big(\sum_{a=1}^{X}u_a\mathbf 1_{\mathrm{cell}\,2a}+v_a\mathbf 1_{\mathrm{cell}\,2a+1}\Big),\qquad h_a=\operatorname{haarMass}(a).
\]

More generally, the Gamma energy pays \(\log(1/|I|)\operatorname{Var}_I(f)\) on disjoint intervals of width at most one, with no mean-zero condition. On top of that it pays a **mean graph**: for each pair of intervals, the far-end Gamma weight times the squared difference of their actual means [S]. [Complete-cell variance payment](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/CompleteCellVariancePayment.lean), [variance coercivity](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/GammaVarianceCoercivity.lean), [mean graph](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/GammaMeanVarianceCapacity.lean).

Each complete pair splits into a weighted average and a balanced detail. **The average cell is the original cell translated by \(\log 2\)**, and integer prime translations send no average component into a detail; the opposite orientation survives [S]. [Coarse splitting](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/HaarCellCoarseSplitting.lean). Hence complete sections on cells \(2,\dots,2X+1\) equal \(T_{\log 2}\)(complete sections on cells \(1,\dots,X\)) plus balanced details. Since \(W\) is translation invariant, the complete source is a multiresolution whose coarse part is a translated copy of itself.

Balanced details above one fixed lower index \(A\) carry a full rough-Weil floor, uniformly in the upper horizon and for all signed coefficients:

\[
W_{\rm rough}(f_c)\ge\sum_{a}\big((1-1/\sqrt2)\log a+2\theta'(0)-20\big)h_a c_a^2 .
\]

Every finite dimension has a common pole-preserving smoothing with \(W\ge\tfrac12\,\mathrm{mass}\) and restricted Riemann–Roch/ampleness. [Haar floor](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/HaarCellEffectivity.lean), [smooth effectivity](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/HaarCellSmoothEffectivity.lean).

Positive sections have a unique bounded Weil projection with \(W(g-Pg,h-Ph)=W(g,h)-W(Pg,Ph)\); the residual keeps every negative square, and the completed residual index is attained at a finite stage. On the chosen unbounded integer-log carrier the projection costs at most \(2\|T_Wf\|^2\). The carrier is proper, and its complement contains an infinite theta radical equal to the Weil radical. Translation keeps \(W\) fixed while the source-graph norm of every nonzero compact orbit eventually exceeds every exponential. On a fixed window and a fixed translation range, translation is bounded in the graph norm, with constants that are not uniform under exhaustion [S]. [Unbounded carrier](../../../formal/GaloisForLFunctions/ArithmeticIndexDescent/TheUnboundedCellCarrierHasAWeilProjection.lean), [radical](../../../formal/GaloisForLFunctions/SignedArithmeticHodgeTheory/TheSignedComplementRetainsExactlyTheWeilRadical.lean), [translation escape](../../../formal/GaloisForLFunctions/SignedArithmeticHodgeTheory/TranslationPreservesWeilEnergyButEscapesEveryExponentialGraphBound.lean), [bounded-window transport](../../../formal/GaloisForLFunctions/SignedArithmeticHodgeTheory/BoundedWindowsAdmitSourceCompatibleScaleTransport.lean).

**What remains:** the cross-level couplings (the surviving detail-to-average prime orientation, Gamma and pole terms between levels) and the low details \(a<A\), which recur at every dyadic level. Pole products alone are not summable across levels: \(\int T_tf\,e^{\pm u/2}=e^{\pm t/2}\int f e^{\pm u/2}\), so a level-\(j\)/level-\(k\) pole product carries the factor \(2^{(k-j)/2}\). In the full cross entry the prime main term cancels this growth, up to the Chebyshev error of §2. For a twin, whose prime sum does not reproduce the main term \(e^h\) (Liouville gives \(-e^h\)), it does not.

### 2. Ordered mixed entries are centered Chebyshev discrepancies

For real tests \(f\) supported left of \(b\) and \(g\) right of \(b\), and every constant \(c\) [S]:

\[
W(f,g)=-\int_0^\infty\big(e^h-\psi(e^h)-c\big)\,\frac{d}{dh}\Omega_{f,g}(h)\,dh-\Gamma_{\rm tail}(f,g),
\]

where \(\Omega_{f,g}(h)=e^{-h/2}\,\mathrm{corr}_{f,g}(h)\) is the ordered lag weight built from the lag-\(h\) correlation of the pair. The Gamma tail equals a localized mass minus a nonnegative square reserve. The Gamma boundary operator has norm at most \(\pi/2\) from an exact Schur weight; the bound is an identity with a square reserve, and equality holds only at zero, without a uniform gap. Touching ordered cells have bounded Gamma interaction, and an arbitrarily short adjacent cell pays any fixed mass charge [S]. [Chebyshev identity](../../../formal/GaloisForLFunctions/ArithmeticIndexDescent/TheOrderedWeilSourceIsACenteredChebyshevDefect.lean), [Gamma square reserve](../../../formal/GaloisForLFunctions/ArithmeticIndexDescent/TheOrderedWeilSourceRetainsItsGammaSquareReserve.lean), [Schur weight](../../../formal/GaloisForLFunctions/ArithmeticIndexDescent/GammaBoundaryHasAnExactSchurWeight.lean), [exact reserve](../../../formal/GaloisForLFunctions/ArithmeticIndexDescent/TheGammaBoundaryReserveIsAnExactSquare.lean), [no equality case](../../../formal/GaloisForLFunctions/ArithmeticIndexDescent/TheGammaBoundaryBoundHasNoNonzeroEqualityCase.lean), [touching cells](../../../formal/GaloisForLFunctions/ArithmeticIndexDescent/TouchingCellsPayTheFullMixedSource.lean).

Every off-diagonal entry between separated blocks of the complete form is therefore a signed prime-error integral. Local (touching) couplings are paid by Gamma. At separation \(h\), RH-strength control \(\psi(x)-x=O(\sqrt x\log^2x)\) makes the coupling polynomially bounded. The unconditional Vinogradov–Korobov error leaves growth \(e^{h/2}\exp(-c\,h^{3/5}(\log h)^{-1/5})\).

### 3. Atomic families: RH-complete at every root, positive at a fixed fraction of the spacing

Write \(\delta_N=\log(1+1/N)\) and \(f_x=\sum_{n\le N}x_ng(\cdot-\log n)\).

- **Every root [S].** For every smooth profile \(\varphi\) (\(C^\infty\), support in \([-1,1]\), \(\int\varphi=1\)), every order \(q\), and every \(\kappa_N\to\infty\) with \((\kappa_N/N)^q\log\kappa_N\to0\): RH holds iff \(W\ge0\) eventually on all atomic families of width \(1/\kappa_N\). In particular this holds at widths \((\log N)^\alpha/N\) for **every** \(\alpha>0\), superseding the earlier \(\alpha>1/4\). For bounded twists \(|\lambda|\le\Lambda\), negativity at every root is equivalent to failure of Weil positivity. The Liouville twin, \(c\Lambda\) for \(-1\le c<1\), and quadratic mixtures are negative at every root; the Markov form is negative at every root unconditionally. On the pole hyperplane \(\int fe^{-u/2}=0\) the Markov form equals the Weil form, and RH is equivalent to Markov nonnegativity on pole-hyperplane atomic tests at every root. Under RH the pole is the Markov form's only negative square there. [Every root](../../../formal/GaloisForLFunctions/SpacingScaleHarmonicAnalysis/TheOverlapLawAtEveryRoot.lean), [gauge at every root](../../../formal/GaloisForLFunctions/SpacingScaleHarmonicAnalysis/TheGaugeAtEveryRoot.lean), [pole at every root](../../../formal/GaloisForLFunctions/SpacingScaleHarmonicAnalysis/ThePoleAtEveryRoot.lean).
- **Narrow positivity at an explicit fraction [S].** For a \(C^2\) Lipschitz profile on \([0,1]\), eventually \(W\ge0\) on every atomic test at \(w\le K_\star(\varphi)\,\delta_N\), and the atomic intersection Gram is hyperbolic there. Here \(K_\star\) is the minimum of explicit overlap and cross-penalty constants and \(\exp(2\theta'(0)+\kappa_L(\varphi)+\gamma-\varepsilon-2)\). The mechanism: the prime-form Dirichlet defect pays the pole, \(2|AB|\le c_Pe^{w/2}wN\|g\|^2(2|x|^2+D_N(x))\). The Robin–Euler criterion gives the Markov form a negative pole test once its finite-part expression turns negative (\(w\le\delta_N/2\), fixed nonnegative profile). The finite-part component of \(K_\star\) is therefore within a factor \(e^{2+2\varepsilon}\) of the point where this pole-absorbing mechanism must fail. The full Weil form is not shown negative beyond it. [Pole defect pays the pole](../../../formal/GaloisForLFunctions/ArithmeticLorentzianGeometry/ThePoleDefectPaysThePole.lean), [Robin–Euler threshold](../../../formal/GaloisForLFunctions/ArithmeticLorentzianGeometry/TheStabilityRegimeEndsAtTheRobinEulerThreshold.lean).
- **Gauge and coverage boundaries.** For nonnegative profiles positive inside their support, the atomic form is Metzler at overlap ratio \(\rho<1\), and every fixed \(\rho>1\) eventually frustrates every diagonal unimodular gauge; \(\rho=1\) is unsettled. Pure Markov positivity fails at separated widths \(c\delta_N\), \(e/(2\pi)<c<1\). At \(w\le K/N\le1\) the non-ratio Schur rows are bounded by \(2(\log4+4)e^{5/2}K+2e^{3/2}K(m/N)(\log m+1)\). Fixed overlap \(K\) covers measure at most \(K\). [Metzler threshold](../../../formal/GaloisForLFunctions/ArithmeticLorentzianGeometry/TheMetzlerThresholdOfTheOverlapRatioIsOne.lean), [Markov failure](../../../formal/GaloisForLFunctions/SpacingScaleHarmonicAnalysis/TheMarkovFormFailsInsideTheSeparatedRegime.lean), [rows](../../../formal/GaloisForLFunctions/SpacingScaleHarmonicAnalysis/TheRowsAtBoundedOverlap.lean), [coverage](../../../formal/GaloisForLFunctions/ArithmeticLorentzianGeometry/TheOverlapRatioIsTheCoveredMeasure.lean).

**The overlap gap is now exact in kind:** positivity is proved at bounded overlap ratio \(K_\star\), while RH is equivalent to positivity at overlap ratio \((\log N)^\alpha\) for any \(\alpha>0\). In that regime the non-ratio rows grow like \((\log N)^\alpha\), while the Ramanujan-mode margins grow only like \(\log m\).

### 4. Prime form, adjunction and gauge finite parts

- **Prime ceiling and pole-hyperplane gap.** \(P_N\) has sharp ceiling \(\log N-\gamma+o(1)\) and exact nonnegative Dirichlet defect \(D_N\). Some \(g>0\) gives \(P_N(x)\le(\log N-\gamma-g+\varepsilon)\|x\|^2\) eventually on \(\sum x_n/\sqrt n=0\), while the Liouville-twisted form reaches \(\log N-\gamma-o(1)\) on the same hyperplane. For each fixed finite prime set, the valuation chain has gap \(2\log 2\) at large horizons. The all-prime sharp gap is now stated in Lean as a Poincaré inequality, \((2\log2-\varepsilon)\operatorname{Var}_{1/n}(\sqrt n\,x)\le D_N(x)\) eventually. Its proof is incomplete (it still ends in a placeholder), though the two-scale smooth/rough decomposition, fibre splitting and rough-defect variance control are in place [S]. [Gap](../../../formal/GaloisForLFunctions/RenormalizedArithmeticPotentialTheory/ThePrimeFormHasASpectralGapBelowItsPole.lean), [separation](../../../formal/GaloisForLFunctions/RenormalizedArithmeticPotentialTheory/ThePoleHyperplaneSeparatesZetaFromItsLiouvilleTwin.lean), [finite-Q gap](../../../formal/GaloisForLFunctions/RenormalizedArithmeticPotentialTheory/TheValuationChainOfFinitelyManyPrimesHasGapTwoLogTwo.lean), [sharp-gap work](../../../formal/GaloisForLFunctions/RenormalizedArithmeticPotentialTheory/TheSpectralGapOfThePrimeFormIsTwoLogTwo.lean), [uniform tensorization](../../../formal/GaloisForLFunctions/RenormalizedArithmeticPotentialTheory/TheRoughHarmonicMeasureTensorizesUniformly.lean).
- **Adjunction and actual prime modes.** For finite \(Q\), the matched adjunction operator on \(Q\)-supported integers is self-adjoint with simple energies \(E_m=\gamma+\log m+\operatorname{tameDifferent}(m)\) and a compact shifted inverse; the fixed-support horizon defect is its form. Ramanujan profiles \(v_m(n)=c_m(n)/\sqrt{\phi(m)n}\) are quasimodes of \(P_N\) at \(\log N-E_m\) with Gram\(/\log N\to\) identity. Every fixed finite conductor set is realized by injectively chosen actual eigenvalues within any \(\varepsilon\) [S]. A paper-stage card on full-prime spectral exhaustion sits at the fully-proven stage of the pipeline; it is unformalized and outside this review's permitted sources. [Adjunction](../../../formal/GaloisForLFunctions/RenormalizedArithmeticPotentialTheory/TheSieveOperatorHasTheAdjunctionEigenbasis.lean), [quasimodes](../../../formal/GaloisForLFunctions/RenormalizedArithmeticPotentialTheory/TheRamanujanPoleProfilesArePrimeQuasimodes.lean), [spectral packets](../../../formal/GaloisForLFunctions/RenormalizedArithmeticPotentialTheory/TheFullPrimeMatrixRealizesFiniteAdjunctionPackets.lean).
- **Gauge finite parts.** Leading polar matching is nonselective: Euler and finite prime flips have coefficient \(+1\), Liouville \(-1\), nonprincipal real prime-conductor characters \(0\). The finite part is twice the Mertens limit; Liouville has \(2(\gamma+\tau)\), \(\tau\ge(\log 2)/2\), against Euler's \(-2\gamma\), with absolute-profile errors. The \(\chi\)-twisted pole \(\operatorname{Re}\chi(n)n^{-1/2}\) has no divergence and finite part \(2\operatorname{Re}(-L'/L(1,\chi))\) per unit mass, for every modulus and every nontrivial \(\chi\), real or complex [S].

  **Finite-part extremality [S].** Among sign gauges matched to \(\zeta\)'s divergence (coefficient \(+1\)) with convergent Mertens error, \(\zeta\) uniquely maximizes the prime-form finite part. A finite flip of a prime set \(F\) lowers it by \(2\delta_F\), with \(\delta_F\ge2\log p/p\) for each \(p\in F\). Among anti-matched gauges (\(-1\)), Liouville uniquely minimizes it. Because \(W\) contains \(-P\), on uniform step profiles \(\zeta\) is the *hardest* member of its matched family; matched flips fail Weil positivity only through local witnesses.

  [Finite parts](../../../formal/GaloisForLFunctions/RenormalizedArithmeticPotentialTheory/TheFinitePartIsTwiceTheMertensLimit.lean), [Liouville separation](../../../formal/GaloisForLFunctions/RenormalizedArithmeticPotentialTheory/TheFinitePartSeparatesZetaFromItsLiouvilleTwin.lean), [twisted pole](../../../formal/GaloisForLFunctions/RenormalizedArithmeticPotentialTheory/TheTwistedPoleReadsTheLogarithmicDerivative.lean), [flipped primes](../../../formal/GaloisForLFunctions/RenormalizedArithmeticPotentialTheory/TheFinitePartSeesEveryFlippedPrime.lean).
- **Torsion and towers.** The torsion counterterm is \(\varphi\log N+O(1)\), \(\varphi=(1+\sqrt5)/2\). Renormalized torsion positive index lies between polynomial lower bounds and \(N^{4/5+\varepsilon}\); these are not Weil indices. The raw one-prime tower finite part is nonnegative at every depth exactly for \(p\ge47\), and valuation potential pays all smaller primes. [Torsion index](../../../formal/GaloisForLFunctions/ArithmeticIntersectionTheory/ThePositiveSquaresOfTheTorsionFormLiveBelowFourFifths.lean), [tower threshold](../../../formal/GaloisForLFunctions/RenormalizedArithmeticPotentialTheory/TheTowerDeficitChangesSignBetweenFortyThreeAndFortySeven.lean).

### 5. Critical energy separates finite support from RH

Let \(\mathcal W(R)\) be damped source work and \(K(R)=R^2(\mathcal W(2R)-\mathcal W(R))\), \(R\ge4\). Then \(K\uparrow\mathcal E_{\rm crit}\in[0,\infty]\), a canonical nonnegative pair energy that includes off-line/critical exterior interactions. Entrywise nonnegativity of its kernel is not a positive-semidefiniteness claim. Put \(Q_*=1294047/2000\) and \(I_*=Q_*/2\).

| Arithmetic bound | Exact consequence |
|---|---|
| Bounded \(\mathcal W\); bounded integer-log spline index | Finite off-line support |
| \(\Delta\mathcal W\to0\), or eventually \(\Delta\mathcal W\le39/50\), or \(\mathcal E_{\rm crit}<\infty\) | Finite off-line support |
| \(\Delta\mathcal W(R)\le39/50\) for every \(R\ge4\); \(\mathcal W\le2\) cofinally; \(\mathcal E_{\rm crit}\le Q_*\) | RH |

Finite nonempty off-line support gives a finite limit above \(Q_*\); infinite support gives \(\infty\). A finite actual Weil index \(k\) forces \(\mathcal E_{\rm crit}\ge\max\{I_*k,\,50k^2-3k/2\}\). These are lower bounds. No arithmetic upper bound is known. [Canonical energy](../../../formal/GaloisForLFunctions/ArithmeticIndexDescent/TheCriticalSourceRateHasACanonicalEnergy.lean), [classification](../../../formal/GaloisForLFunctions/ArithmeticIndexDescent/TheCriticalRateClassifiesAllOffLineSupport.lean), [quadratic cost](../../../formal/GaloisForLFunctions/ArithmeticIndexDescent/TheSourceBudgetMakesTheIndexCostQuadratic.lean).

### 6. Lorentzian closure has an exact scope

Finite products and nonnegative substitutions of Lorentzian local polynomials are Lorentzian. The Hessians realizable at nonnegative points are exactly the entrywise-nonnegative Lorentzian matrices. Under the stated normalization, Ramanujan prime local factors cannot be inputs, since Lorentzianity forces \(a_1\ge d\sqrt q\) while Ramanujan forces \(a_1\le d\sqrt q\). Ordinary-coefficient Xi Jensen polynomials satisfy Laguerre's inequality on \(s\ge0\) only. Decaying Toeplitz (isometric) ladders are hyperbolic at all depths iff every finite form is nonpositive: a positive block repeats and gives two positive directions [S]. [Exact class](../../../formal/GaloisForLFunctions/ArithmeticLorentzianGeometry/TheClosureProducesExactlyTheLorentzianForms.lean), [local factors](../../../formal/GaloisForLFunctions/ArithmeticLorentzianGeometry/RamanujanAndLorentzianMeetOnlyAtTheWeilBound.lean), [half-line Laguerre](../../../formal/GaloisForLFunctions/ArithmeticLorentzianGeometry/TheJensenPolynomialsOfXiSatisfyLaguerreOnTheHalfLine.lean), [ladders](../../../formal/GaloisForLFunctions/ArithmeticLorentzianGeometry/AnIsometricLadderCarriesNoPositiveSquare.lean).

### 7. Selectivity is localized in the unpaid residual

This is a reading of proof hypotheses, not a separate Lean theorem. Every proved positive family on the complete or atomic source is **twin-blind**: it holds for every bounded twist \(|\lambda|\le\Lambda\) with the same Gamma and pole terms.

- The high-Haar prime bound uses Young's inequality on absolute entries, with "no sign condition imposed".
- The complete-cell Gamma payments do not involve primes.
- The narrow regime's full sign holds for sign twins at the earlier fixed fraction.

The Liouville twin, however, is not Weil-positive and is negative at every root. **Its negative directions must therefore live in the unpaid coarse, low-index or cross-level residual.** Any successful bound on that residual must use a property of \(\Lambda\) that its twins lack. The selective inputs available today are:

- the prime-only pole-hyperplane gap, on which Liouville reaches the ceiling;
- the centered-Chebyshev identity of §2: \(\Lambda\)'s prime sum reproduces the main term \(e^h\) that cancels the pole, while Liouville, scalings and character mixtures do not;
- small-radius OWU witnesses, which separate \(\Lambda\) from Liouville and from the 2-flip.

The prime-form finite part identifies \(\zeta\) uniquely among matched gauges, but as their *maximizer*, so it makes \(\zeta\) the hardest case rather than supplying positivity. Matched finite flips keep the main term and are better than \(\zeta\) on step profiles. They fail Weil positivity only through local witnesses.

## Live routes

Each entry lists the current state, then A (just work) and B (open). The [frontier map](../rh-current-frontier-map.md#live-routes) has full source lists.

### WL — Weil lag / prime-error energy

**Current:** Bounded critical deficit energy, a lower bound on coprime cross-work and a linear cumulative prime-error energy budget are exact RH receivers. Abel-slope saturation at the archimedean genus is equivalent to RH plus simple zeros. Ordered mixed entries of the complete form are centered Chebyshev integrals, so WL's prime error is literally the off-diagonal content of the complete-form routes (§2).

**A:** Evaluate fixed truncations with certified archimedean and high-zero tails; transport lag, count and energy dictionaries with constants; evaluate the ordered Chebyshev integral for specified block pairs.

**B:** The actual signed cross-work or linear prime-error energy bound **[RH]**. Genus saturation is **[RH+]** and must not be used as an RH premise. [Receiver](../../../formal/GaloisForLFunctions/BiScaleUncertainty/WeilLagCriticalDeficitEndpointAndLimitLaw.lean).

### RW — Restricted Weil ground energy

**Current:** RH iff the ground minimum is positive at every finite aperture; it strictly decreases, with an exact shell decomposition. Finite-aperture Gårding bounds allow a nonzero negative index. The literal Gamma boundary operator has norm at most \(\pi/2\) with an exact square reserve and no nonzero equality case [S].

**A:** Certified finite-aperture variational bounds and explicit shell/error ledgers; instantiate the exact Gamma boundary reserve in the shell flux.

**B:** Bound total aperture relaxation by the initial energy, retaining low modes, prime collars and polar terms **[RH]**. Monotonicity and telescoping do not supply it; frozen finite-prime families become negative. [Aperture flow](../../../formal/GaloisForLFunctions/ArithmeticContinuationAndCriticalEnergy/TheApertureFlowNeverStalls.lean).

### FU — Signed prime scheduling

**Current:** An eventual upper bound on the normalized completed Abel moment is equivalent to RH. Narrow translated prime channels have a useful sign; universal nonpositivity fails on dyadic windows.

**A:** Assemble seed, drift, earlier-history, cross-block and endpoint terms for a fixed schedule with existing clock kernels.

**B:** A bound on the joint signed total over a prime-exhaustive schedule **[RH]**. [Receiver](../../../formal/GaloisForLFunctions/RHTower/CCM/CCMFUSuzukiMobiusDivisorOneSided.lean).

### RP — Matched–quantile history floor

**Current:** An eventual linear defect floor is RH-equivalent. Low-LCM payment and exact signed history identities exist.

**A:** Expand fixed histories, instantiate low-LCM estimates and expose the high-LCM/moving-core remainder in the native domain.

**B:** The complete floor with high-LCM pairs, moving core and singular-domain transport controlled together **[RH]**. [Receiver](../../../formal/GaloisForLFunctions/RHTower/SPEQuantileRieszRoutePLinearFloorCriterion.lean).

### PA — Prime–archimedean passivity

**Current:** Exact current-sign, Bernstein-mismatch and signed compact-moment receivers. Every fixed moment order becomes positive after a large enough shift. Certified quadrature enclosures exist for the first theta atom.

**A:** Compute explicit thresholds for specified finite order blocks; extend the certified first-atom quadrature to further atoms.

**B:** An all-order/all-shift sign, high-frequency accretivity, or an every-positive-rate mismatch bound **[RH]**. Order-dependent thresholds do not combine into one. [Signed completion](../../../formal/GaloisForLFunctions/RHTower/PrimeArchSignedCompactCompletionCollapse.lean).

### MC — Möbius cancellation

**Current:** Every strict half-power cancellation bound, or subpower Hilbert energy, is RH-equivalent. Fixed-strip dictionaries are complete:

- \(\Theta\le1-\theta\) is equivalent to the escaped-endpoint rate, the all-test Hecke-defect strip cap and integer-theta reading growth.
- \(\Theta<1\) is equivalent to a uniform power saving in the undamped Vaughan convolution prefix, to a positive Vaughan tail-decay index, and to the Vaughan admission rank boundary.

Vinogradov–Korobov escaped decay gives no fixed power saving. A linear Mertens energy budget forces RH, simple zeros and summable inverse-derivative residues. [Vaughan strip dictionary](../../../formal/GaloisForLFunctions/BezoutValuationIncidence/UniformVaughanPowerBoundsAreFixedStrips.lean).

**A:** Specialize fixed-modulus and below-diagonal estimates; state all rates in one normalization; translate supplied strip bounds through the dictionaries; reconcile the external fixed-strip announcement.

**B:**

- Every strict half-power for the actual moving source, or exclusion of every subcritical oscillating probe **[RH]**.
- The linear Mertens budget **[RH+]**.
- A fixed power saving in any of the Vaughan or escaped dictionaries **[open]**: it is equivalent to a zero-free strip \(\Theta<1\), which is unknown.

[Hilbert criterion](../../../formal/GaloisForLFunctions/RHTower/MobiusHilbertFormEquivalence.lean), [escaped decay](../../../formal/GaloisForLFunctions/BezoutValuationIncidence/UnconditionalEscapedMoebiusDecayAndCrossRouteBridge.lean).

### TT — Theta tails and directed covariance

**Current:** Exact seam, Wold and odd-Weil receivers with the sub-half range explicit; restricted current signs and continuum light-cone positivity.

**A:** Evaluate fixed directed-covariance and reflected-prime terms; apply continuum and short-support identities with endpoints.

**B:** Signed nonlocal covariance at every rapidity and scale, or complete odd/primitive positivity **[RH]**. [Wold receiver](../../../formal/GaloisForLFunctions/RHTower/PaperWoldDirectedCovarianceRH.lean).

### LA — Line anchor / Jensen and heat signs

**Current:** Finite-head/heat receivers and positive complementary tails. Ordinary Xi coefficients are Turán and Lorentzian; the Jensen family satisfies Laguerre on \(s\ge0\). Generic finite-product closure is exact in scope.

**A:** Certify selected finite heads and low degrees; translate coefficient conventions, including factorial normalization; apply heat-tail errors.

**B:** All-height/all-degree head signs, especially low orders and near-double configurations **[RH]**. No source supplies the repairing factors. [Finite-head reduction](../../../formal/GaloisForLFunctions/RHTower/XiSliceHeatFiniteHeadReduction.lean), [half-line Laguerre](../../../formal/GaloisForLFunctions/ArithmeticLorentzianGeometry/TheJensenPolynomialsOfXiSatisfyLaguerreOnTheHalfLine.lean).

### TG — Integer trace below one

**Current:** Winding, cubic transgression and central-gap receivers. Gaussian coprime-divisibility covariance has a sign on indicators.

**A:** Calculate finite projection/transgression data, keeping residual and trace separate.

**B:** A matrix-complete decomposition with nonnegative residual and integer trace below one on every disc, or a zero-rate central-gap bound **[RH]**. [Index estimate](../../../formal/GaloisForLFunctions/RHTower/RestrictedProjectionIndexOperatorNormCriterion.lean).

### HF — Arithmetic Hodge positivity

**Current:** Full Hodge/Weil sign, zero Hecke defect and small enough source work are exact receivers. The complete source is available as a dyadic multiresolution with Gamma-paid details and a horizon-uniform high-detail floor (§1). Its separated mixed entries are Chebyshev integrals (§2). Canonical critical energy has exact finiteness and RH thresholds (§5). Fixed-conductor prime modes are realized by actual eigenvalues (§4).

**A:**

- Form finite complete-cell Grams in multiresolution coordinates: details, translated averages, cross-level blocks.
- Compute the low-detail block \(a<A\) and its level-Toeplitz symbol.
- Transport source-kernel cost bounds.
- Keep distinct-index and multiplicity-weighted energies separate.

**B:**

- Nonnegativity of the complete residual or complete-cell index zero **[RH]**.
- An arithmetic upper bound on source work at an RH threshold **[RH]**.
- Block dominance of the multiresolution with a twin-selective input on the low block **[open]**.
- Finite \(\mathcal E_{\rm crit}\) **[open]**; it would prove finite off-line support.

[Index capture](../../../formal/GaloisForLFunctions/ArithmeticIndexDescent/TheCompleteCellsCaptureEveryFiniteIndex.lean), [work threshold](../../../formal/GaloisForLFunctions/ArithmeticIndexDescent/TheSourceWorkHasAClosedQuantumThreshold.lean).

### CHMD — Causal hyperbolic–modular duality

**Current:** Wave/Doob receivers; the supported maximal graph equals the completed aperture core. The fixed unbounded carrier has a bounded projection and an exact residual; the residual radical equals the Weil radical and contains infinitely many theta states. Translation orbits escape every exponential graph bound while keeping \(W\) fixed [S]. Ordered mixed entries are Chebyshev integrals [S].

**A:** Apply domain/cutoff theorems to fixed sources; compute the signed residual with the primitive defect; instantiate bounded-window scale transport.

**B:** The complete one-sided wave bound or odd Doob/nodal inequality **[RH]**. Projection stationarity measures correction error, not residual sign. [Odd criterion](../../../formal/GaloisForLFunctions/RHTower/CHMDOddSectorCriterion.lean).

### TH — Theta moment positivity

**Current:** All ranks are strictly positive on nonzero nonnegative coefficient vectors over a common small positive time; fixed-rank stable regions are known.

**A:** Compute finite signed blocks with explicit degree/time dependence.

**B:** Positivity for arbitrary signed vectors at every degree under a common time **[RH]**; orthant positivity is not positive semidefiniteness. [Orthant theorem](../../../formal/GaloisForLFunctions/RHTower/XiHeatHankelFormOrthantPositivity.lean).

### RN — Renewal and singular comparison

**Current:** Theta renewal solvers, a compact cone-positive operator, exact determinant resonances and multiplicity bookkeeping.

**A:** Compute finite packet/resolvent data in the admitted topology, with cusp/seam terms.

**B:** Directed boundary-work orientation, or mixed prime-plus-Gamma versus pole **[RH]**. Cone positivity does not imply real spectrum. [Exact spectrum](../../../formal/GaloisForLFunctions/RHTower/ThetaRenewalFredholmSpectrum.lean).

### WD — Ward caps and collision

**Current:** A nonnegative integrated cap vanishes iff RH; finite-head/tail laws and sharp model heat-repair costs are formalized.

**A:** Evaluate cap/head data on fixed compact regions with tail bounds and model extremizers.

**B:** Cap extinction, Euler–Stieltjes saturation, or the all-height coefficient sign as heat tends to zero **[RH]**. [Ward receiver](../../../formal/GaloisForLFunctions/RHTower/XiWardGlobalCapAndFiniteHeadArithmetic.lean).

### LI — Paired Li balances

**Current:** Every-positive-rate lower floors for the prime–Gamma clock are RH-equivalent. The unconditional reciprocal-depth rate \(\le1/431\) is not zero width.

**A:** Compute fixed paired histories, first-crossing and outside-correlation terms.

**B:** A subexponential lower floor for the literal primitive **[RH]**. [Clock growth](../../../formal/GaloisForLFunctions/RHTower/LiEvenCrossActualClockGrowthLaw.lean).

### SZ — Suzuki first variation

**Current:** The compact-L² first variation equals the full Weil form; moving-primary and finite-head limits have scoped transfer theorems.

**A:** Apply those limits to specified families, keeping low and mixed terms visible.

**B:** First-variation sign on an RH-complete family **[RH]**. [Full first variation](../../../formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiCriticalL2FirstVariation.lean).

### PM — Haar approximation / damped admission

**Current:** Global Haar approximation, cofinal signed-damping admission and positive gauge mass for every subcritical escape state are exact receivers. Gauge mass is \(\inf_d d\,K_L(d,d)\). Record-minimum limits have \(K_L(p,p)\ge p^{2\varepsilon-2}\), but this permits zero gauge mass; a zero-cofactor limit forces a continuum of limits. Compact maximal-visible-order laws classify residue concentration. [Record minima](../../../formal/GaloisForLFunctions/ArithmeticDefectRigidity/RecordMinimaForceInfiniteCofactorLimits.lean), [visibility criterion](../../../formal/GaloisForLFunctions/ArithmeticCorrelationGeometry/RHIsTheVisibilityOfEveryEscapeState.lean).

**A:** Calculate fixed compact cofactor Grams; apply energy-transfer/residue formulas with effective pole orders.

**B:** Positive gauge mass for every escape state, or a complete-energy bound as damping tends to zero **[RH]**. Exterior tightness and exclusion of infinite-height escape are **[open]**. [Haar receiver](../../../formal/GaloisForLFunctions/RHTower/FermiNymanHaarApproximationEquivalence.lean).

### JAS — Joint ancestry

**Current:** Level-one prime-product positivity and finite-power square-shell bounds are exact receivers. The Gamma–theta source is admitted at all finite supports, phases and grades; unconditional signs reach a logarithmic prime budget.

**A:** Instantiate finite support/grade formulas; measure the budget gap on chosen shells.

**B:** The half-power prime budget or all-amplitude/every-exponent shell control **[RH]**. [Level-one capstones](../../../formal/GaloisForLFunctions/RHTower/JointAncestryLevelOneCapstones.lean).

### CTF — Chronological / Báez–Duarte approximation

**Current:** The residual is \((1-\Lambda\text{-readout})^2\) plus centered pronic energy; vanishing global error is RH-equivalent.

**A:** Optimize/certify finite rows; report both components with moving-tail errors.

**B:** Bounded rows with complete error tending to zero, or the dual-sampling bound **[RH]**. [Readout criterion](../../../formal/GaloisForLFunctions/BezoutValuationIncidence/VonMangoldtReadoutFormOfTheBaezDuarteCriterion.lean).

### HCF — Gaussian heat trace and two-grid signs

**Current:** Exact archimedean-minus-prime Gaussian traces; positivity on both literal \(\log2\)/\(\log3\) grids with polar cancellation is RH-equivalent; one grid aliases.

**A:** Compute finite degrees/heights on both grids with explicit errors.

**B:** Both grid signs at all degrees and heights, or the one-sided vertical-growth bound **[RH]**. [Two grids](../../../formal/GaloisForLFunctions/RHTower/XiGaussianHeatTwoPrimeSourceSampling.lean).

### XN — Newton invariant discs

**Current:** Line-centered self-map discs covering all zeros give RH; the interior margin has an exact curvature formula.

**A:** Certify specified discs and curvature integrals.

**B:** A covering family with nonnegative interior margin **[RH]**. [Disc criterion](../../../formal/GaloisForLFunctions/RHTower/XiNewtonSchwarzPickCriticalLine.lean).

### BAG — Deterministic self-return

**Current:** Actual-zeta recurrence throughout the right strip, or the corresponding positive-Haar-mass condition, is an RH receiver.

**A:** Make finite-head return/error estimates explicit on zero-free compact targets.

**B:** Recurrence at every right-strip point and tolerance, including possible target-zero neighborhoods **[RH]**. [Return receiver](../../../formal/GaloisForLFunctions/RHTower/ZetaStrongRecurrenceReceiver.lean).

### EWU — Even pole-weight uniqueness

**Current:** Attained even blind minima give an exact all-aperture criterion. Full positivity holds in high-scale windows, sparse unions and locally through radius 181/500.

**A:** Certify finite even blind problems; use cycle recovery only on its stated class.

**B:** Nonnegative minima at every aperture, paying low/mixed modes **[RH]**. [Variational receiver](../../../formal/GaloisForLFunctions/RHTower/EvenSectorBlindVariationalAttainment.lean).

### GTA — Transverse Schur charge

**Current:** Rank-uniform decay of the positive quartic Schur charge is RH-equivalent.

**A:** Finite-rank charges with explicit rank dependence.

**B:** Arithmetic transverse-energy decay uniformly in rank **[RH]**. [Decay equivalence](../../../formal/GaloisForLFunctions/RHTower/Hedenmalm/HedenmalmThetaSchurQuarticSpectralDecayEquivalence.lean).

### OWU — Odd Weil-weight uniqueness

**Current:** Exact odd/pole-hyperplane and dilation-ray criteria. Smooth witnesses separate actual \(\Lambda\) from Liouville and the first-prime flip at radius 181/500, and read primes 2 and 3 at radius 23/40. Twins are negative at every root of the atomic receiver [S]; twisted poles read \(-L'/L(1,\chi)\) [S].

**A:** Extend certified finite-collar accounting with signed autocorrelations and both pole corrections.

**B:** All-aperture actual-\(\Lambda\) odd sign **[RH]**. The conductor/forcing incompatibility is **[open]**. [Dilation criterion](../../../formal/GaloisForLFunctions/RHTower/WeilDilationRayCriterion.lean).

### PBM — Pole-regularized prime series

**Current:** Convergence of the pole-subtracted coefficients at every real abscissa above 1/2 is an exact RH criterion.

**A:** Regularized partial sums and tails in controlled half-planes.

**B:** Critical-abscissa cancellation **[RH]**. [Regularized criterion](../../../formal/GaloisForLFunctions/RHTower/RegularizedLogZetaAbscissa.lean).

### RB — Robin / Nicolas extremizers

**Current:** Eventual criteria, reduction to colossally abundant integers, fixed valuation-defect margins.

**A:** Enumerate and certify finite extremal ranges.

**B:** The moving remainder on increasingly prime-saturated extremizers **[RH]**. [CA reduction](../../../formal/GaloisForLFunctions/RHTower/RobinColossallyAbundantReduction.lean).

### SRT — Lag localization and atomic visibility

**Current:** Every-width lag bounds, orbit/index laws and polynomial-aperture detection. The atomic receiver holds at every root (widths \((\log N)^\alpha/N\), any \(\alpha>0\)), and positivity holds at \(K_\star\delta_N\) (§3). Canonical work separates finite support from RH (§5).

**A:** Instantiate fixed-width detectors and synthesis errors at the new orders; compute atomic Grams at overlap ratios between \(K_\star\) and \((\log N)^\alpha\), keeping Markov, full Weil and pole-hyperplane forms separate.

**B:**

- An actual late-lag bound, zero-rate orbit estimate, or full sign at any unbounded polylog overlap **[RH]**.
- Positivity at a larger fixed overlap ratio than \(K_\star\) **[open]**; it is bounded by the Robin–Euler finite part only for the Markov form.

[Lag receiver](../../../formal/GaloisForLFunctions/SquareRootThreshold/EveryWidthDecidesTheCriticalLine.lean), [every root](../../../formal/GaloisForLFunctions/SpacingScaleHarmonicAnalysis/TheOverlapLawAtEveryRoot.lean).

### ACT — One-shift arithmetic criticality

**Current:** For one fixed theta shift, a full all-profile variation inequality gives odd Weil positivity and RH. Short-support collars can be absorbed with support-dependent shifts.

**A:** Evaluate the signed moment ledger for a prescribed profile/shift.

**B:** One shift paying every support and profile **[RH]**. [Short-profile scope](../../../formal/GaloisForLFunctions/ArithmeticCriticalityTheory/ShortProfilePoleFreeVariationInequality.lean).

### AIP — Arithmetic incidence allocation

**Current:** Global joint allocation is exactly the odd sign/RH problem. Complete-cell transfer, the high-detail floor, complete-cell Gamma payment, the every-root receiver and narrow positivity at \(K_\star\) are established; the beyond-spacing Metzler gauge is obstructed.

**A:** Assemble complete incidence matrices in multiresolution coordinates with every successor, Gamma and polar term; compute shared spending once.

**B:** Signed allocation on source-complete cells or an RH-complete overlap family **[RH]**. A selective allocation of the low/cross-level residual is **[open]**. [Allocation criterion](../../../formal/GaloisForLFunctions/ArithmeticIncidencePositivity/GlobalIncidenceAllocationCondition.lean).

### ACS — Arithmetic effectivity

**Current:** Source RR, effectivity, Rosati-height and chirality receivers coexist with complete-cell realization and index capture. High details have a horizon-uniform full-form floor and finite-dimensional smooth effectivity; Gamma pays every adjacent difference; averages are \(\log2\)-translates. Finite-sieve adjunction and fixed-conductor spectral packets are available.

**A:** Transport fixed source families into complete smooth cells; compute section/projection/finite-sieve data; formalize the paper-stage full-prime spectrum card.

**B:**

- Full-source quadratic RI with degree-zero subquadratic growth, an actual Rosati-height lower bound, or complete-cell index zero **[RH]**.
- Coarse/cross-level payment with a selective low-block input **[open]**.

[Effectivity receiver](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/ExactArithmeticSourceEffectivity.lean).

## Route candidates and promotion obstacles

A candidate lacks an independent source construction or its landing. An abstract receiver inside a candidate does not close that gap. Every promotion gap below is **[open]**, and becomes **[RH]** once it is the final sign.

| Candidate | Established mechanism | A — Just work | B — Promotion gap |
|---|---|---|---|
| **APF — Arithmetic paired Fredholm** | Actual cycle traces have arithmetic Fourier reconstruction. | Instantiate fixed cycles, flows and finite mixtures with truncation control. | Zero-independent divisor exhaustion and trace vanishing. [Source](../../../formal/GaloisForLFunctions/RHTower/PaperZetaCycleFourierReconstruction.lean). |
| **BSH — Arithmetic mate curvature** | Framed composition curvature vanishes exactly at critical half-density. | Finite curvature/cocycle identities and calibration. | Pre-divisor section and actual mate identity forcing the vanishing. [Source](../../../formal/GaloisForLFunctions/RHTower/Deninger/DeningerOneSidedFramedMateCurvatureTransgression.lean). |
| **CDC — Constitutive dagger** | Calibrated confluent potentials exist exactly on the critical line. | Finite repair/exchange defects. | One arithmetic potential descending on every fibre before divisor restriction. [Source](../../../formal/GaloisForLFunctions/RHTower/ConstitutiveDaggerConfluence.lean). |
| **DR — Dyadic roots** | Dyadic levels extend to the Littlewood zero-free cusp. | Glue roots on known zero-free charts. | Compatible extension to the whole strict-right domain. [Source](../../../formal/GaloisForLFunctions/RHTower/XiSymmetricLittlewoodZeroFreeCuspDyadicRoots.lean). |
| **EGC — Pole-safe contour** | Complete copy correction; nonzero Gamma baseline. | Corrected contours; baseline separation. | Outer-contour orientation excluding off-line copies. [Source](../../../formal/GaloisForLFunctions/RHTower/PaperEGCSourceRayBaseline.lean). |
| **EWJ — Euler/Wold jets** | Three-channel histories converge; compact quotient character. | Fixed jets and quotient characters. | Source admission and norm exhaustion across depth. [Source](../../../formal/GaloisForLFunctions/RHTower/PaperEulerWoldDepthHistory.lean). |
| **FEL — Theta likelihood** | Entropy bookkeeping; convergent BSY zero-sum identity. | Predeclared finite histories and contrasts. | Cofinal balance from arithmetic independently of zeros. [Source](../../../formal/GaloisForLFunctions/RHTower/BalazardSaiasYorZeroSum.lean). |
| **HJ — Hurwitz reflection** | Two-seed residual equals SEC charge; HCF two-grid bridge. | Convergent fibres; coordinate translation. | Pre-divisor forcing of residual vanishing. [Source](../../../formal/GaloisForLFunctions/RHTower/PrimeTailSeedHurwitzReflection.lean). |
| **IRK — Rotation-algebra trace** | Completed Xi-jet relation invertible exactly off the line. | Finite jet inverses and traces. | Charged arithmetic Poisson lift with integral analytic count. [Source](../../../formal/GaloisForLFunctions/RHTower/PrimeRotationXiCompletedResolution.lean). |
| **MSC — Möbius–Sonin transport** | Squarefree-discrepancy Hilbert source recovers moments; divisor transport. | Evaluation jets and readouts. | Source-faithful nonnegative Sonin/Weil energy. [Source](../../../formal/GaloisForLFunctions/RHTower/SquarefreeDiscrepancyHilbertTransport.lean). |
| **PCS — Singular prime co-shift** | Exact shift-plus-defect decomposition; strong finite-prime convergence. | Retained defect and cutoff errors. | Wall annihilation retaining the forward mode. [Source](../../../formal/GaloisForLFunctions/RHTower/PCSChronologicalDilationCarrierObstruction.lean). |
| **PTR — Photonic realization** | Lossless products real-rooted; Xi-limit criterion. | Finite stacks and transfer functions. | Prime-faithful nonlocal port built without Xi zeros. [Source](../../../formal/GaloisForLFunctions/RHTower/PhotonicLosslessProductPortRH.lean). |
| **RFHM — Support/grade forcing** | Full support/phase/grade admission; norm law. | Coherent defects and grade observables. | A source law sensitive to arithmetic phase/depth orientation. [Source](../../../formal/GaloisForLFunctions/RHTower/PaperRFHMSurvivalInformation.lean). |
| **SC — Stokes/Witt–Krein** | Rigged chambers; a.e. Fourier reconstruction. | Finite cross-fibre coordinates. | Arithmetic cross-fibre index selecting the wall. [Source](../../../formal/GaloisForLFunctions/RHTower/PaperKreinWallFourierCompletion.lean). |
| **SEC — Adjacent prime seam** | Seam-charge/essential-norm and factorial-Fock criteria. | Finite jets and seam charges. | All-order Fock boundedness or eventual compactness. [Source](../../../formal/GaloisForLFunctions/RHTower/TimeOneGammaJetFockRHCriterion.lean). |
| **W1C — Clifford–Dirac / Lee–Yang** | Ferromagnetic Ising limits to Riemann's law force RH. | Finite couplings and density constraints. | Source-defined centred couplings or faithful scattering operator. [Source](../../../formal/GaloisForLFunctions/RHTower/IsingLawConvergenceRH.lean). |
| **WBF — Source certificates** | Abstract genealogy Gram and relative Fredholm recovery. | Certificate streams and determinants. | Arithmetic stream with uniform-depth landing on Xi/Weil data. [Source](../../../formal/GaloisForLFunctions/HTGeometry/PaperCriticalGenealogyCompletion.lean). |
| **PW-B — PM cusp branch** | Native two-response action with cutoff-independent limit. | Admitted positive-damping actions. | Remove zero indexing; prove ceiling→optical→cap→extinction chain. [Source](../../../formal/GaloisForLFunctions/RHTower/ThetaCusp/ThetaCuspHawkingBMPWNativeTwoResponseAction.lean). |

## Supporting programmes

| Programme | Contribution | Unresolved input |
|---|---|---|
| ACS complete cells, Haar multiresolution | Mixed-entry transfer; Gamma payment of details; \(\log2\) self-similarity; high-detail floor; smooth effectivity | Cross-level and low-detail payment with a selective input |
| AID, SAHT | Bounded projection, finite index attainment, Chebyshev identity of ordered entries, exact Gamma boundary reserve, translation escape, canonical critical energy | Residual sign; arithmetic upper bound on \(\mathcal E_{\rm crit}\) |
| SSHA, ALG | RH-complete atomic receiver at every root; \(K_\star\) positivity; Metzler threshold; Robin–Euler instability; Lorentzian closure scope; isometric ladders | Full sign at unbounded polylog overlap; non-ratio lag signs |
| RAPT, AIT | Prime ceiling and pole gap; finite-\(Q\) gap \(2\log2\); adjunction spectrum and actual spectral packets; gauge finite parts incl. \(-L'/L(1,\chi)\); torsion bounds | All-prime sharp gap; growing-conductor control; Gamma/pole coupling |
| BVI, ArithmeticCompensation, SignedSuccessor | Readout/pronic decompositions; escaped VK decay; Vaughan and theta-prefix strip dictionaries | RH-strength moving-scale cancellation; no fixed power saving known |
| ACP, ADR, ACG | Escape-state classification, gauge-mass criterion, record-minimum diagonals, prime-error/genus laws, Stepanov count | Visibility (positive gauge mass) of every escape state; actual cancellation |
| AES, CDG, PL, RBG | Field/energy laws, theta-prefix detectors, collided polarization, renormalized survival | Upper sign or cap on the computed defect |
| APD, MPG, SBWF, AE | Positive-measure rigidity, successor/Kronecker spectra, boundary forcing capacity, finite-field calibration (incl. odd hyperelliptic RH) | An independently proved arithmetic positivity/orientation input |
| Pair correlation, IGP, large values | Simple-critical proportion \(\ge0.67250071-\varepsilon\); Schur slack; large-value counts | Elimination of exceptional zeros |

## External mathematical status

RH is listed as unsolved by [Clay](https://www.claymath.org/millennium/Riemann-Hypothesis/), so a sufficient input to any receiver above is a breakthrough target unless an actual proof is supplied. Two external claims bear on the queue. Both are carried over from the previous review's theorem-scope inspection; their proofs are not validated here.

- A September 2026 [quasi-RH manuscript](https://github.com/openai/math/blob/main/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf) claims Dirichlet zero-freeness for \(\operatorname{Re}s>7/8\), including \(\zeta\). If accepted, it supplies a fixed strip \(\Theta\le7/8\) to the MC/BVI dictionaries, not the critical endpoint.
- A September 2026 [ordinary-correlation manuscript](https://github.com/openai/math/blob/main/preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/final.pdf) claims fixed-form Liouville two-point bounds \(X/(\log X)^c\). This is not a power saving and not uniform in growing shifts or moduli.

Published [Lorentzian-polynomial theory](https://arxiv.org/abs/1902.03719), the [de Bruijn–Newman bound 0.22](https://arxiv.org/abs/1904.12438) and [simple-zero proportion results](https://arxiv.org/abs/2609.02882) are separate inputs. None supplies all-degree real-rootedness or zero exceptions.
