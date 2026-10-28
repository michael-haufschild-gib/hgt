# Research routes and mathematical obstacles

Status: 28 October 2026. **RH remains open. The inventory is 31 live routes, 17 standalone candidates and the PW-B candidate branch of PM.** Most live routes already have an exact receiver. Their missing input is an arithmetic estimate or sign, not another equivalence.

Companions: [summary and priorities](obstacles-summary.md), [walls](walls-ledger.md), [route unification](route-unification-ledger.md), [current frontier map](../rh-current-frontier-map.md), [scoped obstructions](../rh-killed-routes.md).

## Evidence and classification

This report uses corpus searches followed by inspection of Lean statements, hypotheses and proof context across established routes, candidates and current supporting frameworks. It does not infer status from modification dates or module titles. Source references below identify mathematical evidence, not a fresh kernel audit. No builds or compilations were run. Working or unintegrated developments retain that qualification. Search records and findings are in the [research log](../../../logs/review-2810-research.log), with [declaration evidence](../../../logs/review-2810-source-evidence.jsonl) and [filtered search results](../../../logs/review-2810-search/). Only the six requested inherited Markdown reports were consulted.

Two categories organize each route:

- **A — Just work:** a specified finite calculation, application of an existing theorem, explicit error accounting, or transport whose mathematical ingredients are already available. This can be substantial work. It does not promise that a requested positivity certificate exists.
- **B — Research:** the missing estimate, construction or uniformity principle. An RH-equivalent conclusion is an open mathematical problem. A project-specific intermediate question is labelled unresolved, rather than asserting that nobody worldwide has ever studied or solved its exact formulation.

A false proposed estimate belongs in neither queue: it needs replacement. A proved conditional receiver is not an unconditional proof of its input. Likewise, a published theorem missing from the corpus is a literature/formalization gap, not a new open problem. External announcements need a separate status; their existence prevents an unqualified claim that “nobody has a solution.”

## The present mathematical frontier

### 1. Complete approximation is available; complete positivity is not

Complete logarithmic cells retain every relevant prime translation, the Gamma contribution, mass and both exponential pole moments. For each fixed compact smooth test family, one refinement recovers **every mixed Weil entry**, not just diagonal energies. Pole-preserving smoothing realizes the finite arithmetic form on original smooth tests. These results close the fixed-support transfer problem. They do not prove the finite forms positive. [Complete source transfer](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/CompleteWeilSourceTransfer.lean), [smooth realization](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/SmoothFiniteCellArithmeticForm.lean).

Narrow positive sections now have a unique bounded Weil-orthogonal projection in the closed source graph. Its complement satisfies

\[
W(g-Pg,h-Ph)=W(g,h)-W(Pg,Ph).
\]

Every negative square survives in this complement. For each finite probe family, the completed residual index is attained at a finite refinement; complete cells capture every finite actual Weil index. Thus the unresolved object can be stated precisely: **the signed complementary form, or an upper index bound on source-complete cells**. Projection existence and finite mixed-entry recovery are no longer the missing lemmas. [Projection](../../../formal/GaloisForLFunctions/ArithmeticIndexDescent/TheClosedSectionHasABoundedWeilProjection.lean), [finite attainment](../../../formal/GaloisForLFunctions/ArithmeticIndexDescent/TheCompletedIndexIsReachedAtAFiniteStage.lean), [index capture](../../../formal/GaloisForLFunctions/ArithmeticIndexDescent/TheCompleteCellsCaptureEveryFiniteIndex.lean).

Two attempted exhaustions do not supply the sign. At fixed atom count, shrinking widths removes vanishing energy. Recentered high arithmetic bands have increasing coercivity, but their unit-energy balls pair to zero with each fixed compact source. Nested positive sections can therefore remain mathematically useful without exhausting the source. [Shrinking cells](../../../formal/GaloisForLFunctions/ArithmeticIndexDescent/ShrinkingCellsRemoveVanishingEnergy.lean), [moving-band decoupling](../../../formal/GaloisForLFunctions/ArithmeticIndexDescent/MovingArithmeticBandsDecoupleFromFixedTests.lean).

Working source also provides a concrete signed block input. Balanced adjacent-cell Haar sections cancel translated prime pairings except at odd-boundary incidences `(2a+1)m=2b+1`; even multipliers vanish. For arbitrary real coefficients their actual prime energy obeys

\[
P_{\mathrm{Haar}}(c;X)\le
\sum_{a=1}^{X}\left(16+\frac{\log(2a+1)}{\sqrt2}\right)h_a c_a^2,
\qquad h_a=\operatorname{haarMass}(a).
\]

The logarithmic coefficient is strictly below one. This is a prime-only inequality on a restricted balanced block space: full archimedean/smoothing cost, both pole moments, coarse components and mixed-scale payment remain to be established. Ordinary mean-zero balance is not polar neutrality. [Haar compression](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/HaarCellPrimeCompression.lean), [signed prime bound](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/HaarCellPrimeBound.lean).

### 2. Overlap has several different boundaries

Write \(\delta_N=\log(1+1/N)\) and \(w\) for atom width. At a fixed sufficiently small fraction of \(\delta_N\), archimedean self-energy pays prime interactions and the pole. Actual zeta intersection Grams satisfy Hodge hyperbolicity, weighted trickle-down and link inequalities there. This is a genuine local closure. The corresponding narrow full-form positivity also holds for sign twins, so it does not select zeta globally. [Actual narrow Hodge theorem](../../../formal/GaloisForLFunctions/ArithmeticLorentzianGeometry/TheHodgeIndexHoldsAtAFixedFractionOfTheSpacing.lean), [polar payment](../../../formal/GaloisForLFunctions/ArithmeticLorentzianGeometry/TheTiltedMarginPaysThePolarDispersion.lean).

For nonnegative Lipschitz smooth profiles supported on \([0,1]\) and positive inside, the natural atomic form is Metzler for \(w=\rho\delta_N\), \(0<\rho<1\). For every fixed \(\rho>1\), sufficiently large atom families contain a frustrated sign triangle: **no diagonal unimodular gauge makes the atom block Metzler**. The theorem does not settle \(\rho=1\), and does not disprove full Weil positivity. An overlap programme requiring this gauge at every width is nevertheless impossible. [Metzler threshold](../../../formal/GaloisForLFunctions/ArithmeticLorentzianGeometry/TheMetzlerThresholdOfTheOverlapRatioIsOne.lean).

Pure Markov positivity is a different question. For every \(e/(2\pi)<c<1\), some smooth nonnegative plateau has negative Markov energy on the pole coefficients \(n^{-1/2}\) at width \(c\delta_N\). Complete overlap families also have negative Markov directions unconditionally. The **full Weil form**, or Markov form restricted to the exact pole hyperplane, remains the relevant RH target. [Separated Markov failure](../../../formal/GaloisForLFunctions/SpacingScaleHarmonicAnalysis/TheMarkovFormFailsInsideTheSeparatedRegime.lean), [pole-hyperplane criterion](../../../formal/GaloisForLFunctions/SpacingScaleHarmonicAnalysis/ThePoleIsTheOnlyNegativeSquareBeyondTheThreshold.lean).

Full atomic synthesis is already RH-complete on shrinking-width schedules: \(w_N=N^{-\theta}\), \(0<\theta<1\), and \(w_N=(\log N)^\alpha/N\), \(\alpha>1/2\). More generally, inverse widths \(\kappa_N\to\infty\) with \((\kappa_N/N)^2\log\kappa_N\to0\) suffice. Eventual positivity for **all real coefficient vectors** on each such family is equivalent to RH. These are sufficient synthesis conditions, not a sharp theorem at \(\alpha=1/2\). Bounded-overlap improvement is a meaningful intermediate target; it is not, by itself, the complete RH bridge. [Critical exponent](../../../formal/GaloisForLFunctions/SpacingScaleHarmonicAnalysis/TheCriticalExponent.lean).

Atomic Fourier–Dirichlet factorization and a bound for each zero's summand give useful scale information. They do not establish a strict Fourier bandlimit or a Nyquist sampling theorem for zeta's zeros. Nor does a per-zero upper bound control the sum over all zeros. [Weight of one zero](../../../formal/GaloisForLFunctions/SpacingScaleHarmonicAnalysis/TheWeightOfOneZero.lean).

### 3. Finite-prime renormalization has an actual spectral theory

For the prime-only form \(P_N\), the sharp ceiling is \(\log N-\gamma+o(1)\). Its defect is an exact nonnegative Dirichlet energy. The torsion form has a different leading counterterm: \(\varphi\log N+O(1)\), \(\varphi=(1+\sqrt5)/2\). Working source also gives the extremal Rayleigh edges of \(\alpha\operatorname{diag}(\log n)+P_N\): \(\kappa_\pm\log N+O_\alpha(1)\), where \(\kappa^2=\alpha\kappa+1\). This asserts the edges, not that every interior spectral value occurs. Here the source name `atomicWeilForm` denotes the **prime form**, not complete Weil energy. [Prime ceiling](../../../formal/GaloisForLFunctions/RenormalizedArithmeticPotentialTheory/ThePoleIsTheTopOfThePrimeForm.lean), [Dirichlet defect](../../../formal/GaloisForLFunctions/RenormalizedArithmeticPotentialTheory/TheDeficitOfThePrimeFormIsADirichletEnergy.lean), [golden counterterm](../../../formal/GaloisForLFunctions/RenormalizedArithmeticPotentialTheory/TheTorsionCountertermIsTheGoldenRatio.lean), [working fixed-point family](../../../formal/GaloisForLFunctions/RenormalizedArithmeticPotentialTheory/TheSelfIntersectionFamilyObeysAFixedPointLaw.lean).

For every fixed prime, the valuation potential pays the tower deficit, including small primes. For fixed finite class families the corresponding asymptotic is uniform over their coefficient vectors. For each finite prime set \(Q\), the matched adjunction operator acts on the actual \(Q\)-supported-integer \(\ell^2\) space, is self-adjoint on its maximal logarithmic domain, and has a complete product-Blaschke eigenbasis with simple eigenvalues

\[
\gamma+\log m+\operatorname{tameDifferent}(m)
=\gamma+2\log m-\operatorname{selfIntersection}(m).
\]

Its shifted inverse is compact. A fixed finite-support sieve-horizon defect converges to its quadratic form. The remaining issue is **compatibility and estimates as prime sets, class depth, horizons and signed source families grow together**, including the full Gamma and pole terms. This operator is not identified with a spectral realization of \(\xi\). [Tower payment](../../../formal/GaloisForLFunctions/RenormalizedArithmeticPotentialTheory/TheArchimedeanPlacePaysTheTowerDeficit.lean), [adjunction basis](../../../formal/GaloisForLFunctions/RenormalizedArithmeticPotentialTheory/TheSieveOperatorHasTheAdjunctionEigenbasis.lean), [source landing](../../../formal/GaloisForLFunctions/RenormalizedArithmeticPotentialTheory/TheSieveHorizonDefectIsTheAdjunctionOperator.lean), [compact resolvent](../../../formal/GaloisForLFunctions/RenormalizedArithmeticPotentialTheory/TheAdjunctionResolventIsCompact.lean).

Leading polar matching alone remains nonselective: Euler and finite-prime flips have coefficient \(+1\), Liouville \(-1\), and extended nonprincipal real prime-conductor characters \(0\). Two-horizon sieve formulas are uniform in the two horizons with \(Q\) fixed; that is not uniformity in \(Q\). [Character matching](../../../formal/GaloisForLFunctions/RenormalizedArithmeticPotentialTheory/CharactersAreInvisibleToPolarMatching.lean), [two horizons](../../../formal/GaloisForLFunctions/RenormalizedArithmeticPotentialTheory/TheFiniteSieveUnitGramHasTwoHorizons.lean).

Working source makes the distinction between **valuation classes and unit residue classes** exact. For fixed modulus \(q\), the latter have rank-one leading counterterm \((q/\phi(q))\ell^2\), with an absolute signed-profile Gram error. For a unit-class function \(f\), the leading coefficient is \((\sum_{a\in(\mathbb Z/q)^\times}f(a))^2/(q\phi(q))\). Thus every nonprincipal character, real or complex, loses the quadratic logarithmic divergence. This does not bound the remainder by actual L² mass uniformly in profiles or in \(q\), and does not prove its sign. [Residue-class counterterm](../../../formal/GaloisForLFunctions/RenormalizedArithmeticPotentialTheory/TheHorizonCountertermIsBlindToResidueClasses.lean), [class-function law](../../../formal/GaloisForLFunctions/RenormalizedArithmeticPotentialTheory/TheHorizonSeesOnlyTheMeanOfAClassFunction.lean).

### 4. Finiteness and absence of exceptions have distinct exact thresholds

Let \(\mathcal W(R)\) be the damped arithmetic source work and \(\Delta\mathcal W(R)=\mathcal W(2R)-\mathcal W(R)\), \(R\ge4\). Current source gives:

| Arithmetic bound | Exact consequence |
|---|---|
| Bounded \(\mathcal W\) | Finite off-line support; equivalently bounded integer-log spline negative index. |
| \(\Delta\mathcal W(R)\to0\), or eventually \(\Delta\mathcal W(R)\le39/50\) | Finite off-line support. |
| \(\Delta\mathcal W(R)\le39/50\) for **every** \(R\ge4\) | RH. |
| \(R^2\Delta\mathcal W(R)\le48\) cofinally | RH. |
| \(\mathcal W(R)\le2\) cofinally | RH. |

Every off-line quartet costs more than \(39/50\) at its height. Any exception eventually forces the quadratically scaled increment above \(48\); infinitely many exceptions force it to infinity. Thus vanishing unscaled increments cannot eliminate a finite exceptional set. No sufficient arithmetic upper bound in this table has been produced. [Finite stratum](../../../formal/GaloisForLFunctions/ArithmeticIndexDescent/TheWorkAndIndexHaveTheSameFiniteStratum.lean), [vanishing increments](../../../formal/GaloisForLFunctions/ArithmeticIndexDescent/VanishingScaleIncrementsCharacterizeFiniteSupport.lean), [strict quantum](../../../formal/GaloisForLFunctions/ArithmeticIndexDescent/EveryOffLineQuartetCostsAStrictScaleQuantum.lean), [quadratic increments](../../../formal/GaloisForLFunctions/ArithmeticIndexDescent/TheQuadraticScaleWorkDetectsEveryException.lean).

Working source sharpens this to an exact trichotomy for \(R^2\Delta\mathcal W(R)\): identically zero under RH; convergence to a finite \(L>48\) for finite nonempty off-line support; divergence to \(+\infty\) for infinite support. Eventual boundedness, or existence of a finite limit, is therefore equivalent to finite support. The finite limit is the signed source moment \((3/2)\sum_{\mathrm{off\ copies}}\gamma_\rho^2 d_\rho F_\rho\); individual summands are not asserted positive. Every finite Weil negative index \(k\) also forces the quadratic increment eventually above each \(b<24k\). These are classification and lower-payment laws, not arithmetic upper bounds. [Trichotomy](../../../formal/GaloisForLFunctions/ArithmeticIndexDescent/TheCriticalRateClassifiesAllOffLineSupport.lean), [index payment](../../../formal/GaloisForLFunctions/ArithmeticIndexDescent/TheCriticalRatePaysEveryNegativeSquare.lean).

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

**Current:** Complementary tails and head-to-full transfer are controlled. Ordinary even Taylor coefficients satisfy the Turán/Lorentzian layer. Working generic theory includes mixed-Hessian hyperbolicity, Alexandrov–Fenchel inequalities and nonnegative substitution closure; none is all-degree Jensen real-rootedness or an identification of the overlapping Weil form.

**A:** Certify selected finite heads and low-degree inequalities; translate coefficient conventions carefully, including factorial normalization; apply existing heat-tail errors.

**B:** Establish the remaining actual all-height/all-degree head signs, especially low orders and near-double configurations. No source supplies all required repairing factors. [Finite-head reduction](../../../formal/GaloisForLFunctions/RHTower/XiSliceHeatFiniteHeadReduction.lean), [Lorentzian scope](../../../formal/GaloisForLFunctions/ArithmeticLorentzianGeometry/TheHessianOfALorentzianPolynomialTricklesDown.lean), [mixed Hessians](../../../formal/GaloisForLFunctions/ArithmeticLorentzianGeometry/TheMixedHessiansOfALorentzianPolynomialAreHyperbolic.lean), [substitution closure](../../../formal/GaloisForLFunctions/ArithmeticLorentzianGeometry/TheLorentzianClassIsClosedUnderNonnegativeSubstitution.lean).

### TG — Integer trace below one

**Current:** Winding, cubic transgression and central-gap receivers are explicit. Gaussian coprime-divisibility covariance has a sign on its stated indicator class.

**A:** Calculate finite projection/transgression data and retain the residual and trace separately.

**B:** Produce a matrix-complete decomposition with nonnegative residual and integer trace below one on every required disc, or a zero-rate central-gap bound. Indicator covariance does not control arbitrary signed Euler-inverted combinations. [Index estimate](../../../formal/GaloisForLFunctions/RHTower/RestrictedProjectionIndexOperatorNormCriterion.lean).

### HF — Arithmetic Hodge positivity

**Current:** Complete Weil positivity, zero collided-form Hecke defect, and several subquantum work conditions are exact receivers. Complete-cell transfer, narrow Hodge/TD and closed-section residual constructions now give concrete finite and completed carriers.

**A:** Form actual finite mixed Grams, their projections and residuals; transport existing source-kernel cost bounds; keep distinct-index and multiplicity-weighted energies separate.

**B:** Prove complete-cell/complementary positivity, or an arithmetic upper bound at a sufficient work/defect threshold. Neither positive collided mass nor a computable defect gives this sign. This is a central meeting point for U1 and U2, not a closed route. [Index capture](../../../formal/GaloisForLFunctions/ArithmeticIndexDescent/TheCompleteCellsCaptureEveryFiniteIndex.lean), [work threshold](../../../formal/GaloisForLFunctions/ArithmeticIndexDescent/TheSourceWorkHasAClosedQuantumThreshold.lean).

### CHMD — Causal hyperbolic–modular duality

**Current:** Completed graph domains, sharp-window convergence and bounded narrow-section projection are available. Exact wave and odd-Doob receivers remain.

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

**Current:** Every-width lag bounds, full atomic synthesis and exact index/work laws detect all possible off-line zeros. Sufficient shrinking-width families are already RH-complete.

**A:** Instantiate fixed-width detectors and synthesis errors; compute finite atomic Grams while distinguishing pure Markov, full Weil and pole-hyperplane forms.

**B:** Prove an actual late-lag bound, zero-rate orbit estimate, complete overlap sign or sufficient work ceiling. Detection and per-zero bounds do not supply a collective source upper estimate. [Lag receiver](../../../formal/GaloisForLFunctions/SquareRootThreshold/EveryWidthDecidesTheCriticalLine.lean), [atomic receiver](../../../formal/GaloisForLFunctions/SpacingScaleHarmonicAnalysis/TheCriticalExponent.lean).

### ACT — One-shift arithmetic criticality

**Current:** For one fixed positive theta shift, a full all-profile variation inequality gives odd Weil positivity and RH. Short-support collars can be absorbed with support-dependent shifts.

**A:** Evaluate the complete signed moment ledger for a prescribed profile/shift and apply the known short-support estimates.

**B:** Find one shift paying **every** support/profile, including exterior primes and signed/polar remainders. A shift chosen after the support does not meet the receiver's quantifiers. [Short-profile scope](../../../formal/GaloisForLFunctions/ArithmeticCriticalityTheory/ShortProfilePoleFreeVariationInequality.lean).

### AIP — Arithmetic incidence allocation

**Current:** Global joint allocation is exactly the odd sign/RH problem. Local shared-surplus rules, complete-cell transfer and actual narrow-spacing Hodge/TD are established.

**A:** Assemble complete finite incidence matrices with every successor, Gamma and polar contribution; calculate shared spending and existing mixed-entry errors once.

**B:** Prove signed allocation on source-complete cells or an RH-complete overlap family. Independent edge payments overspend shared resources. Beyond-spacing Metzler gauge extension is obstructed, so the full sign needs a different argument. [Allocation criterion](../../../formal/GaloisForLFunctions/ArithmeticIncidencePositivity/GlobalIncidenceAllocationCondition.lean).

### ACS — Arithmetic effectivity

**Current:** Source RR, effectivity, Rosati-height and chirality receivers coexist with complete-cell realization and exact index capture. Finite-sieve adjunction now gives a concrete arithmetic spectral input with limited scope.

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
| Balanced Haar-cell source | Exact odd-boundary prime compression and signed prime bound with logarithmic coefficient 1/√2, in working source. | Full Gamma/Lévy/pole payment, smoothing and coarse/mixed-scale completion. |
| RAPT and arithmetic intersection | Sharp prime/torsion scales, covariant class counterterms, finite-prime adjunction and exact source finite parts. | Simultaneous source-faithful prime/class exhaustion with Gamma/pole payment. |
| ALG | Actual narrow Hodge/TD, polar-dispersion payment, precise Metzler obstruction and generic Lorentzian Hessian theory. | A sign mechanism beyond the frustrated diagonal-gauge regime. Local hyperbolicity is not additive. |
| Arithmetic polarization, CDG, electrostatics | Positive collided form, faithful computation, theta-prefix detectors, field and moment-of-inertia identities. | Upper sign/cap on the computed defect at a sufficient threshold. |
| Arithmetic correlation geometry, signed successor arithmetic | Gauge classification, almost-everywhere cancellation, exact finite moment cones, polynomial charged-cell counts. | Selection of the actual arithmetic gauge and sufficiently uniform signed correlations. A positive-density cell count alone would still not prove full Weil positivity. |
| Pair correlation, IGP and large values | Quantitative simple-critical/distinct proportions, Schur slack and power-saving alignment counts under explicit parameters. | Eliminate exceptional zeros or prove matching-profile signed surplus bounds. A proportion or rare-event estimate does not provide zero exceptions. |
| Effectivity, positive duality, multiplicative positivity and finite-field calibration | Source identification, RR/Hodge equivalences, simple-pole rigidity, finite-field purity and Burgess tools. | An independently proved arithmetic effectivity/height/orientation input. Identities and positive counts alone admit impure models. |
| ALDG, heat and local divisor geometry | Sharp model repair costs, actual finite-head coordinates, asymptotic tail signs. | Actual all-height low-head sign and simultaneous degree/time control. |
| Closed-cycle, finite-incidence and physical sampling tools | Exact finite recovery, source-dependent conditioning and sharp finite-window coercivity. | Uniform source-faithful global sign/admission; injectivity with growing inverse cost is not such a bound. |

## Public mathematical status and literature intake

RH is still listed as unsolved by [Clay](https://www.claymath.org/millennium/Riemann-Hypothesis/). Consequently an unconditional sufficient input to any exact RH receiver above remains a breakthrough target unless an actual proof is supplied. Intermediate project formulations require their own novelty/literature assessment; their local absence is not evidence of worldwide impossibility.

Two current announcements materially affect the wording of the research queue:

- A September 2026 [quasi-RH manuscript](https://github.com/openai/math/blob/main/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf) claims zero-freeness for Dirichlet L-functions in \(\Re s>7/8\), including zeta. This report inspected its theorem and scope, not its complete proof. Treat it as **external claimed proof**, not a local Lean result or proof of RH. If adopted, it supplies a fixed first strip; it does not yield all strips approaching 1/2. The corpus's counterexample to a cardinality-only shifted-character bound does not by itself refute a theorem using additional arithmetic structure.
- A September 2026 [ordinary-correlation manuscript](https://github.com/openai/math/blob/main/preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/final.pdf) claims fixed-affine-form Liouville two-point bounds \(C_{\mathrm{forms}}X/(\log X)^c\), and a qualitative corrected Elliott statement. This is not a power saving \(X^{1-\delta}\), nor a bound uniform for growing shifts or moduli. Fixed-form natural-density Chowla must therefore not be labelled “nobody has a solution.” Existing [logarithmic two-point Chowla](https://arxiv.org/abs/1509.05422) is a separate established input. Neither statement automatically pays the moving-source correlations in MC/PM/AIP.

Further distinctions prevent false open-problem claims. Standard [Lorentzian-polynomial theory](https://arxiv.org/abs/1902.03719) already provides powerful Hodge/Hessian tools; applying them to an independently identified arithmetic form is the missing step. The published [de Bruijn–Newman upper bound 0.22](https://arxiv.org/abs/1904.12438) must be compared only after matching heat normalization. [Current simple-zero work](https://arxiv.org/abs/2609.02882) concerns proportions; neither it nor the corpus's positive Schur-slack improvement eliminates all exceptions. Simplicity, Chowla and stronger pair-correlation statements are not automatically consequences of RH.
