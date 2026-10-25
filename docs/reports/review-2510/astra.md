# RH research synthesis: arithmetic correlation, boundary control, and relative amplification

**Assessment.** The best opportunity is to derive a new inequality from the interaction between additive incidence and multiplicative arithmetic, retaining its signed boundary terms. Signed near-coincident prime pairs provide the clearest concrete entry point. A source-defined theory of mixed correspondences and relative tensor operations offers a more ambitious way to turn such information into individual-zero exclusion.

I do not see a completed new proof mechanism in the material. I do see a narrower, better specified research opening than “find more positivity” or “use higher rank.” The three questions I recommend are:

1. **Can the actual signed coalescent prime-pair surplus be bounded beyond the diagonal threshold, with enough localization to address exceptional heights?**
2. **Can source-prescribed successor–dilation correlations impose a new constraint on the full arithmetic form or its escaping states, with every boundary cost retained?**
3. **Can an arithmetic relative tensor operation amplify an off-line defect faster than its source-side loss grows?**

The first has explicit intermediate numerical targets. The second asks for the missing arithmetic compatibility law. The third asks for an amplification mechanism capable of converting partial control into a full result. Arithmetic surface effectivity is a possible construction supporting the second and third, rather than a fourth unrelated programme.

This report uses the six requested reports, all 22 distinct requested programme READMEs, and the Lean corpus search tool. The duplicated MultiplicativePositivityGeometry entry was read once. ArithmeticKunnethTheory contained three Lean files by the final directory reading; all were read. No other Markdown sources, web searches, or builds were used. “Established” follows the ledgers' scope and the inspected declarations; the working Künneth sources are distinguished from an independently checked integration claim. Search records and research notes are in [the log](../../../logs/astra-rh-synthesis-2026-10-25.txt).

## 1. What the research has already changed

The main achievement is no longer merely a collection of RH equivalents. The corpus has separated several tasks that used to look interchangeable:

- identifying the arithmetic source;
- faithfully detecting its possible off-line divisor;
- producing a sign or growth bound from arithmetic;
- transferring that bound through the required limits.

There is substantial progress on the first two and many exact transfer theorems for the fourth. The third remains the central missing input. Some transfers also expose a further uniformity problem: a true estimate in the wrong norm, at fixed aperture, or after normalization need not control the RH receiver.

The [route-unification ledger](route-unification-ledger.md) organizes the endpoints as critical cancellation, full signed Weil positivity, and faithful realization/forcing. That unification is useful, but it does not identify their constructions. A source estimate for one route must still cross its actual comparison theorem; an abstract equivalence cannot pay the comparison error.

### 1.1 The strongest established structure

| Programme cluster | Mathematical contribution | Remaining mathematical input |
|---|---|---|
| Arithmetic positivity, BiScaleUncertainty, SquareRootThreshold | Exact source/zero identities, depth-sensitive witnesses, aperture and rate laws, positive windows and averaged bounds | Signed source control on the scales and heights needed by those witnesses |
| ArithmeticCriticalityTheory, ArithmeticIncidencePositivity, ScaleSignedIncidenceCriticality, ArithmeticCompensationTheory | Full reflected-prime/polar accounting, critical-deficit formulas, local payment, exact compensation and width dictionaries | Joint payment of the complete signed form, with one shared reserve |
| TransHorizonIncidenceMechanics, BezoutValuationIncidence, ArithmeticContinuationAndCriticalEnergy | Actual centered receiver, half-damping admission, signed continuation laws, restricted arithmetic cancellation | Absolute complete-energy control at cofinally small positive damping |
| SignedArithmeticEnergyIncidence, SignedSuccessorArithmetic | Frustration/path calculus, bounded endpoint transport, sharp successor laws and arithmetic endpoint distinctions | Actual source-specific cancellation across growing scales, rather than universal bounds for arbitrary rows |
| ArithmeticOrientationTheory, ArithmeticOrientationGeometry | Exact orientation/index/rate receivers, generic spline orbits, finite-curve calibrations, theta Riemann–Roch on the base | An independent arithmetic orientation or upper defect bound |
| ArithmeticCastelnuovoSeveri | Exact full-source Riemann–Roch, genuine Meyer principals, maximal positive blind ideal, explicit effectivity boundaries | Bézout/ampleness on the same full source cone, or an independent full-source floor |
| ArithmeticLocalDivisorGeometry | Sharp repair and heat thresholds, actual finite-head coordinates, exact masking costs | Actual divisor/cofactor supply that gives the required all-height coefficient sign |
| ArithmeticDefectRigidity, BiarithmeticGeometry | Actual cofactor limits, dilation modules, origin costs, finite affine actions, payment graph domains, torsion | Source constraints excluding escape while preserving the relevant topology and boundary |
| MultiplicativePositivityGeometry, ArithmeticPositiveDuality, StripBochnerWeilForcing | Sharp boundary forcing/capacity, positive-measure source rigidity, exact duality receivers and coefficient barriers | Interior signed control; boundary positivity and source uniqueness do not provide it |
| ArithmeticKunnethTheory, current source declarations | Total-support response bound, exact diagonal product moments, collapse of external-product positivity to point-count positivity | A genuinely additional arithmetic tensor/intersection law |

This is a substantial foundation. In particular, “construct a source,” “find a detector,” “prove local positivity,” and “add a tensor product” are now too imprecise to serve as research objectives.

### 1.2 Four distinctions that should govern the next research programme

**Source rigidity is not spectral positivity.** Positive-measure theta rigidity identifies the ordinary integer/prime-power source under its precise moment and theta-law hypotheses. It rules out a broad class of impostors. It does not prove the sign of the resulting archimedean-minus-prime Weil form. The completed-functional-equation version also retains substantive strip and decay assumptions; bare FE is not the proved hypothesis. The distinction between the already positive prime measure and the RH-equivalent positive spectral measure is explicit in [PositivityOnBothSidesOfTheExplicitFormula](../../../formal/GaloisForLFunctions/ArithmeticPositiveDuality/PositivityOnBothSidesOfTheExplicitFormula.lean).

**A positive restricted geometry need not approach the missing directions.** The greatest sharp-stable positive Meyer convolution ideal is precisely the ideal whose Mellin values vanish at off-line zeros. It retains all critical jets and supports restricted Hodge/RR/Bézout/ampleness. Its equality with the full source is equivalent to RH, without a simplicity requirement. The theorem `isGreatest_meyerSharpPositiveIdeal` makes this an exact boundary, not an intuition. Natural Fréchet closedness and density for critical-jet observations occur in different topologies; they cannot be combined to prove exhaustion. See [the maximal ideal](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/MaximalBlindIdealOfTheMeyerSource.lean) and [its topology](../../../formal/GaloisForLFunctions/ArithmeticPositiveDuality/TheBlindIdealIsClosedOnlyWhereOffLineZerosAreSeen.lean).

**Leading cancellation is not bounded remainder.** The Möbius/Vaughan/cofactor programmes prove strong relative cancellation, including anti-alignment of divergent pieces and precise limiting Grams. Those statements can coexist with an unbounded absolute residual. The geometric language is useful only if it retains that residual's original scale. Likewise, a paid ideal's ambient Wiener closure can contain unpaid elements; the graph norm carries information that the ambient norm loses.

**The currencies are different.** Width, distinct-zero Hodge defect, multiplicity-weighted Weil energy, squared-multiplicity packet energy, and heat thresholds are not interchangeable. The actual distinct-right-zero count is even, and fewer than two right zeros implies RH. A bound merely proving finiteness does not. A faithful positive full-jet degree can additionally demand simple zeros, whereas ordinary trace positivity does not. Research should target the weakest sufficient invariant, not inadvertently solve RH plus simplicity. See `riemannHypothesis_iff_encard_rightZeros_lt_two` in [TheIndexExit](../../../formal/GaloisForLFunctions/ArithmeticOrientationGeometry/TheIndexExit.lean).

## 2. What the walls say—and what they do not say

The [walls ledger](walls-ledger.md), [hard obstacles](hard-obstacles.md), and [killed-routes catalogue](../rh-killed-routes.md) support three central obligations.

| Wall | Question exposed by the obstruction | What would count as overcoming it |
|---|---|---|
| **1: arithmetic estimates** | What relation among the actual signed arithmetic terms makes the complete remainder small or nonnegative? | A source-specific signed inequality in an RH-relevant scale; a fixed-strip improvement already counts as a major intermediate result |
| **3: information, norms, shared resources** | Does that relation survive increasing aperture, changing origin, small damping, and joint assembly? | A theorem with the right quantifier order, boundary terms, norm, and non-reused reserve |
| **14: faithful realization** | What arithmetic construction produces the desired orientation instead of defining it through the unknown divisor? | A source-defined carrier or operation with an independently proved sign law and a faithful comparison to the existing receiver |

These are not impossibility theorems for all analysis, all positivity, or all multiplication-based arguments. Most no-gos classify a stated observation, norm, normalization, or producer class. A signed estimate using the existing objects could still succeed without inventing a new field. Conversely, inventing a richer category will not help unless it supplies such an estimate or a new forcing law.

Several tempting extensions are already constrained more sharply than the early question in [what-forces-blindness](what-forces-blindness.md) suggests:

- Increasing finite harmonic degree has an exact Fejér barrier. Coupled height channels have genuine boundary-capacity and shrinking-collar theorems, but no fixed interior strip.
- A free positive-definite affine extension adds nothing: positive definiteness on a subgroup extends by zero to the whole group. The successor coordinates must be prescribed by arithmetic before they can constrain anything.
- Taking scalar powers multiplies the defect exponent and its old bound together. Increasing tensor order at fixed total support adds no independent depth exponent.
- Positive external Adams products and positive symmetric-power zeta coefficients do not force purity. The newest Künneth declaration proves that these requirements are equivalent to nonnegative point counts, and the golden datum satisfies them while failing Hodge index.
- Exact arithmetic source Riemann–Roch is already available. The unresolved statement is compatible Bézout/ampleness or sign on that same source cone. “Prove RR” alone is now an outdated target.

The third Künneth file is especially useful: `kunneth_positivity_tfae` and `goldenDatum_kunneth_positive_not_pure` in [KunnethPositivityIsPointCountPositivity](../../../formal/GaloisForLFunctions/ArithmeticKunnethTheory/KunnethPositivityIsPointCountPositivity.lean) rule out interpreting more positive point-count constructions as the missing correspondence positivity.

One further scope distinction matters for prospective index arguments. The inspected `indexIncrement_eq` and `absolute_inequality_fails` in [WeilIndexConservation](../../../formal/GaloisForLFunctions/RHTower/WeilIndexConservation.lean) concern defined insertion/removal counts. They do not themselves construct an entire completed deformation or identify its analytic Weil index. The newest frontier states this separation explicitly. Pole bookkeeping is useful, but it supplies no intrinsic upper bound for ζ's unknown defect.

## 3. Three research questions, ranked

### Question 1. Can actual signed near-coincident prime pairs beat the available absolute bounds?

**Priority: first concrete attack.** This is the clearest place where the corpus has isolated a genuinely arithmetic remainder, supplied its surrounding analysis, and given intermediate outcomes weaker than RH.

At bandwidth $4/3$, write $X=\exp(L(T))\asymp T^{4/3}$. The smooth coalescent statistic is exactly

\[
\mathcal S_{u,\eta}(T)
=\frac{\operatorname{coalSum}
 (\Omega_{u,T},g_T,X,T^{-1+\eta})}{(a(T)L(T))^2}.
\]

It retains the signed cosine-transform weight on pairs with

\[
0<|\log(n/m)|\le T^{-1+\eta}.
\]

Here $N_0^*(T,2T)$ counts distinct critical-line zeros, while $N(T,2T)$ counts all nontrivial zeros with multiplicity in that window. The established certificate has the form

\[
N_0^*(T,2T)\ge
\left(\frac{29}{36}-\varepsilon\right)N(T,2T)
-\mathcal S_{u,\eta}(T).
\]

For $0<\eta<1/3$, proper prime powers contribute

\[
O(T^{2/3+\eta}\log T)=o(N(T,2T)).
\]

Thus the remaining problem can be restricted to distinct odd primes, with even additive separation. This is an actual prime-pair problem, not a missing prime-power bookkeeping step. See the definition in [SmoothWeightedCertificateAtFourThirds](../../../formal/GaloisForLFunctions/TransThresholdPairCorrelation/SmoothWeightedCertificateAtFourThirds.lean) and `coalescentSurplusAtMost_iff_primeCoalescentSurplusAtMost` in [CoalescentPrimeReductionAndParitySieve](../../../formal/GaloisForLFunctions/TransThresholdPairCorrelation/CoalescentPrimeReductionAndParitySieve.lean).

**Precise first target.** Prove an eventual upper bound

\[
\mathcal S_{u,\eta}(T)\le(\beta+\varepsilon)N(T,2T)
\]

for admissible profiles that also supply the certificate. The profile and coalescent exponent must be chosen before taking $T\to\infty$, with the tolerance dependence recorded. They cannot be optimized retrospectively at each height. The normalization by $(aL)^2$ has already occurred; the remaining comparison scale is $N(T,2T)$.

| Budget proved for the actual statistic | Certified consequence |
|---|---|
| $\beta<5/36$ | Proportion exceeding $2/3$ |
| $\beta\le577/4500$ | At least $254/375$, up to arbitrarily small error |
| $\beta\le1/18$ | At least $3/4$, up to arbitrarily small error |

These transfers are in [CoalescentSurplusAndTransThresholdProportionLaws](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/CoalescentSurplusAndTransThresholdProportionLaws.lean). The table records this certificate's output, not a comparison between every distinct zero-counting statistic in the corpus.

**Where a new mechanism could enter.** The signed Ramanujan/singular-series model has cancellations unavailable after replacing the kernel by its absolute value. The missing step is a weighted discrepancy estimate between actual prime pairs and that model in the particular oscillatory statistic. Seek cancellation after summing the signed lobes and the relevant shifts together. A uniform asymptotic for every individual prime gap is stronger than the immediate target requires; a bound for this complete weighted sum could suffice.

The task is therefore not “improve the sieve constant” in isolation. It is to show that the arithmetic discrepancy pairs weakly enough with this signed kernel, with the endpoint and divisor errors retained. A successful first result could be a source-specific saving on a growing range of shifts that remains visible after the final normalization. Merely showing that an absolute upper envelope grows more slowly than another divergent envelope is insufficient.

There is a useful caution here: the unsigned factor-two model already gives $49/72$, so unsigned methods are not categorically incapable of improving the existing certificate. The stronger $3/4$ target distinguishes the signed mechanism in the stated calibration. The research should measure the actual surviving budget rather than attach significance to the word “signed.”

**The further bridge to RH.** A better proportion, even a density-one result, leaves exceptional zeros possible. The next objective would be a localized version matched to an off-line witness, or a quantitative theorem showing that a negative witness persists on more heights than the arithmetic exceptional set can contain.

The averaged Weil results make this direction credible but do not supply that bridge. `exists_frequencyAverage_quadrature_fullZeroForm_ge_subpower` gives a subpower negative floor for $A\le\alpha\log\Gamma$, every $0\le\alpha<2/3$, with an explicit profile-norm remainder. A separate theorem gives a positive logarithmic main term for some smaller aperture constant $\kappa_0>0$. These are different conclusions. Neither selects an individual zero ordinate. See [ZeroDensityFilteredWeilPositivityAndCoercivity](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/ZeroDensityFilteredWeilPositivityAndCoercivity.lean).

The useful localization question is: **can the estimate track the norm, width, and negative margin of the detecting profile as its center and aperture vary?** A measure estimate for bad heights is useful only if it beats the persistence scale of that particular witness. Finite-prime phase recurrence already rules out the naive alternative of an eventual height-uniform power saving for the raw prime symbol.

**Success criterion:** an unconditional bound for the actual weighted residual with a numerical surplus consequence, followed by a separately quantified localization theorem. **Failure criterion:** all cancellation disappears when actual primes replace the model, or the claimed gain is consumed by profile/endpoint costs.

### Question 2. Can prescribed additive–multiplicative compatibility force a new source inequality?

**Priority: the main structural question.** This asks where information absent from the established multiplicative observations might enter.

There are now two precise reasons to prescribe the mixed arithmetic data:

1. Every sharp-stable positive convolution ideal lies inside the off-line-blind Meyer ideal.
2. Every positive-definite subgroup function has a positive-definite extension by zero. Passing from dilations to an affine group with free successor coordinates therefore imposes no new condition.

The second fact is `exists_isPosDefOnGroup_extension_iff`; the actual rational-dilation specialization is an RH equivalence. See [AffinePositivityIsInducedFromTheDilations](../../../formal/GaloisForLFunctions/ArithmeticPositiveDuality/AffinePositivityIsInducedFromTheDilations.lean).

The possible opening is **a mixed functional whose successor and dilation values are fixed by the same arithmetic source, together with an independently proved compatibility estimate**. Examples of the underlying data are divisibility and $n\mapsto n+h$, near-equalities of products, or signed prefix/cofactor correlations. Merely adjoining noncommuting symbols does not produce such an estimate.

**A concrete construction problem.** Start at finite integer horizon with actual arithmetic coefficients and the affine maps $n\mapsto an+b$, for integers $a\ge1$ and $b\ge0$. Keep the relations

\[
D_aU=U^aD_a
\]

and every escaped-cell term. The existing finite-horizon calculus already proves that the change in a signed pairing is exactly the pairing carried through the boundary. In its cell normalization,

\[
\langle A_{a,b}v,A_{a,b}w\rangle_N
+\sum_{\substack{0\le j\le N\\aj+b>N}}v_j\overline{w_j}
=\langle v,w\rangle_N,
\]

with the real version formalized by `horizonPairing_affine_add_boundary` in [HorizonBoundaryCalculus](../../../formal/GaloisForLFunctions/BiarithmeticGeometry/HorizonBoundaryCalculus.lean). A pronic or other weighted realization must carry its own exact weighted comparison; the displayed cell identity does not supply it automatically.

Seek a mixed boundary identity whose arithmetic specialization controls one of the actual residuals in Question 1, the centered small-damping receiver, or a full-source Weil lower floor. The new result must include the comparison to that target. A physical Gram matrix is positive for every input and can remain unrelated to the signed Weil form.

**Two useful formulations of the missing law.**

- On the Weil/Meyer side: can an explicitly constructed arithmetic operation enlarge a known positive family, with controlled mixed pairings, until it becomes detecting? The hard step is positivity of the enlarged span. Separate positive orbits do not provide it.
- On the cofactor side: can mixed source identities exclude every putative unbounded-energy limit? Existing dilation contraction, horizon order, antipodality, and paid-ideal annihilation are necessary constraints. A classification that merely relocates possible ζ-zero characters is not an exclusion theorem.

These are alternative tests of the same proposed source law, not a claim that a comparison between the two carriers is already available.

**Try a strict error margin before exact positivity.** A useful lesson comes from the working [PositivityMargin](../../../formal/GaloisForLFunctions/MultiplicativePositivityGeometry/PositivityMargin.lean) source: in its boundary-weight model, a coefficient floor $w_x(n)\ge-\epsilon\Lambda(n)n^{-1-x}$ yields capacity $2\sum m\le k+\epsilon$. Integer orders, no off-origin poles, and $k=1$ exclude boundary zeros whenever $\epsilon<1$; that threshold is sharp. This is boundary forcing, not interior RH control. It nevertheless suggests a precise construction question: can a mixed arithmetic law bound a faithful interior defect below its first nonzero discrete value? The even distinct-right-zero index supplies such a threshold at two. Neither the required upper bound nor a bridge from the boundary margin to that index is known here. Small norm error alone cannot be substituted for an index bound.

**The first milestone must precede full positivity.** Derive a finite-horizon mixed identity and a genuine arithmetic inequality for its complete boundary correction. It should distinguish data currently identified by multiplicative magnitudes or complete-period covariances. Then prove the gain survives the actual growing horizon in the target norm. This would be meaningful progress even if it yields only a restricted class or a fixed positive damping interval.

The successor scale is a serious constraint. Fixed words disappear on actual escape; even moving shifts can disappear after normalization. The inspected theorem `normalized_successor_tendsto_origin_trace` identifies subenergy displacement limits with their origin trace, and nonvanishing raw displacement requires $k^2/E$ to exceed every fixed bound frequently on escape. A proposal must reach a scale outside the applicable disappearance theorem and pay the new origin/tail cost. See [MovingSuccessorLimitsAreOriginTraces](../../../formal/GaloisForLFunctions/ArithmeticDefectRigidity/MovingSuccessorLimitsAreOriginTraces.lean).

**How this relates to effectivity.** Exact arithmetic source RR is already proved; the source reserve equals the original defect. Its Bézout condition is exactly nonnegativity of that reserve. Positive majorants give Bézout but spend RR. The useful geometric target is therefore a genuine arithmetic construction of sections or correspondences whose composition supplies the missing same-cone inequality. Boolean membership, finite ranks insensitive to weights, or a newly defined positive norm do not do so. See `exactArithmeticSourceCone_riemannRoch` and `exactArithmeticSourceCone_bezout_iff_source_nonneg` in [ExactArithmeticSourceEffectivity](../../../formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/ExactArithmeticSourceEffectivity.lean).

**Success criterion:** a source-prescribed mixed law with a nontrivial, surviving target estimate. **Failure criterion:** free mixed coefficients, automatic Gram positivity, character-normalization freedom, or boundary terms discarded in the limit.

This is a promising place to search, not a theorem that every RH proof must use successor arithmetic. A sufficiently strong direct signed estimate could bypass this construction.

### Question 3. Is there a genuinely relative arithmetic amplification with sublinear loss?

**Priority: the most ambitious mechanism.** The relevant distinction is between multiplying observations and constructing a new operation whose arithmetic cost has a different scaling law.

Three existing boundaries must be faced simultaneously:

1. For product responses supported on $\sum_j|x_j|\le S$,
   \[
   |\mathcal R(\mathbf z)|\le e^{\delta S}\|\Phi\|_1,
   \qquad |\Re z_j|\le\delta.
   \]
   Tensor order is absent. On the repeated diagonal, the response pushes forward under $x\mapsto\sum_jx_j$ to a one-variable response.
2. A length-$X$ Dirichlet polynomial raised to order $k$ has length $X^k$. The proved sufficient exact-diagonal regime is $2rX^k\le1$. Outside it, nonnegative coefficients and a nonnegative window give a nonnegative off-diagonal contribution, not automatic cancellation.
3. External Adams products and symmetric-power coefficient positivity are already satisfied by the impure golden datum.

These are the three current [ArithmeticKunnethTheory](../../../formal/GaloisForLFunctions/ArithmeticKunnethTheory/) sources. Their scope leaves signed mixed-correlation estimates and genuinely relative constructions open. It does not justify a universal no-go for tensor methods.

**The proposed mechanism.** Find coefficient objects over one arithmetic base, with a relative operation that increases the response to an off-line defect while keeping the base contribution independently controlled. The base need not literally have zero-free spectrum. What matters is that its contribution, boundary, and complexity do not reproduce the same defect exponent once per tensor factor.

A useful performance specification is the following. This is a **research target**, not a constructed observable or an established arithmetic theorem. For each integer $k\ge1$, construct a source observable $\mathcal R_k(R)$ such that a zero of depth $\delta>0$ forces

\[
\limsup_{R\to\infty}\frac{\log(1+|\mathcal R_k(R)|)}R\ge k\delta,
\]

while arithmetic independently proves

\[
\limsup_{R\to\infty}\frac{\log(1+|\mathcal R_k(R)|)}R\le b_k,
\qquad \frac{b_k}{k}\longrightarrow0.
\]

The detector and estimate would imply $k\delta\le b_k$ for every $k$, excluding positive depth. Ordinary powers give $b_k=kb_1$ and make no progress. The missing mathematics is the construction and the improved source bound, not this final comparison.

The two limits are essential. Take $R\to\infty$ for each fixed $k$, then $k\to\infty$. Constants depending rapidly on $k$ are harmless only if the estimate and detection hold on the required unbounded $R$-range. If the construction permits only $R=R(k)$, all constants and remainder terms must instead be controlled jointly. “Fixed base” is not a substitute for this calculation.

**Where it could come from.** A relative trace formula, effective intersection theory, or signed connected-correlation decomposition could separate the repeated local coefficient operation from the global base loss. Exact product coincidences are the familiar multiplicative diagonal; the unresolved near-coincidences are precisely where additive arithmetic and boundary geometry enter. Questions 1 and 2 are therefore possible ingredients of this mechanism.

“Connected” here must mean an exact subtraction of specified diagonal, pole, and factorized terms. It must not mean discarding inconvenient terms or defining a residual whose desired bound is assumed. Likewise, tensor compatibility must act on the arithmetic source before spectral interpretation, not only on a zero algebra built from the unknown divisor.

**First milestone.** Construct and calculate the two-factor relative operation, including its trace, support, pole/Gamma term, and boundary. Show that its useful estimate is not determined solely by total support or products of the original counts. Test it on the golden datum: either a proved geometric hypothesis fails there, or the proposed selector has not yet distinguished purity. An order-two inequality does not establish $b_k=o(k)$, but it can reveal whether a different loss law exists at all.

**Success criterion:** a source operation with a proved new loss law and a faithful detector. **Failure criterion:** an external product in disguise, positive point counts alone, or a source cost growing linearly with the same tensor exponent.

## 4. The field these questions suggest

I would call the proposed field **arithmetic correlation geometry**.

Its central problem would be:

> How do additive relations among integers constrain signed multiplicative correlations, and how can those constraints become global spectral bounds without losing their boundary information?

This is a proposal for organizing and extending the existing programmes. It is not a claim that a completed field exists, that the name is historically new, or that no current analytic technique could answer these questions.

### 4.1 Point of view

Study arithmetic through **relations with weights and boundaries**, rather than through isolated prime factors or an already completed spectral object.

The elementary relations include

\[
ab=cd,\qquad ab-cd=h,\qquad n\mapsto an+b,
\qquad d\mid n,\qquad \gcd(n,n+1)=1.
\]

The first is visible to multiplicative moment methods. The second and third expose the additional arithmetic needed when the observation crosses the diagonal threshold. The weights—Möbius signs, von Mangoldt masses, phases, damping, and the archimedean completion—must remain part of the object.

The intended geometry is not obtained by declaring all these relations effective. It would explain which signed combinations have controlled boundary and why their complete arithmetic trace has a useful sign or growth rate.

### 4.2 Objects and language

**Finite arithmetic presentations.** Start with finite intervals or finite divisor configurations, weighted incidence maps, and partial affine correspondences. These give concrete matrices and exact identities before any limit. Residue phases and prime-power multiplicities remain labelled.

**Boundary-bearing coefficient spaces.** Attach the escaped cells, origin traces, pole terms, and cofactor tails to the presentation. A map should specify its action on both the interior and boundary. The absorbing finite successor is an instructive model: invariance without a boundary correction forces a constant observable.

**Completions with a specified reading.** A completion is chosen to preserve the quantity of interest: full Weil form, pronic energy, Mellin jets, or a relative trace. There need not be one universal Hilbert space. Payment graph domains provide an existing example of the right principle: the norm must remember both input and output.

**Metrized sections and arithmetic degrees.** Section spaces should carry genuine growth and weights, not just support ranks. The box-defect formula already separates integer degree, logarithmic torsion, and continuous polar evolution. A proposed Euler characteristic must preserve those distinctions; an ordinary integer dimension difference cannot equal a generally nonintegral arithmetic defect.

**Relative coefficient operations.** Tensor order, base complexity, and total analytic support are distinct parameters. Products over different bases and coefficient operations over one base should be different constructions in the language, with different accounting theorems.

**Signed defect and index objects.** Track the exact primitive form and its negative directions, with the chosen multiplicity convention. A form's sign, an integer index, and a norm estimate should be related by explicit theorems, never identified by terminology.

The essential numerical parameters are aperture, height, additive shift, arithmetic cutoff, damping, and tensor order. Every limit theorem should display which are fixed and which grow. Several existing walls are precisely failures caused by identifying two of these parameters too early.

### 4.3 Foundational principles

These should be requirements on constructions and theorems, not extra assumptions imposed on ζ.

1. **Arithmetic determination.** All operations and mixed coefficients are defined from the actual integer/prime/theta source. Zeros can diagnose the construction afterward; their unknown location cannot define its positive part.

2. **Exact signed accounting.** Diagonal, mixed, pole, Gamma, origin, and tail terms belong to one identity. An absolute-value estimate is an explicit relaxation with a recorded cost. A reserve is allocated once.

3. **Functorial boundary control.** Composition carries boundary defects through a proved law. Gluing must not silently reset the origin, periodize a prefix, or replace a signed boundary by its average.

4. **Faithful transport of the needed invariant.** The comparison preserves the full target pairing or gives a sufficient one-sided estimate with a controlled error. Preserving coefficients or divisors alone is insufficient; preserving a positive auxiliary norm alone is insufficient.

5. **Quantitative passage to infinity.** Finite identities become useful only with the required uniformity. Ambient density, strong convergence, or normalized anti-alignment cannot substitute for convergence in the relevant energy or graph norm.

6. **Positivity must have an arithmetic proof.** A useful positive cone comes from a counting, intersection, variational, or correlation theorem whose hypotheses are independently satisfied. Defining the cone by the target sign creates a receiver.

7. **Relative amplification must earn its gain.** Prove how base loss, conductor/complexity, coefficient rank, support, and boundary scale under the operation. A tensor symbol does not establish a sublinear loss law.

8. **Keep the weakest sufficient endpoint.** Do not introduce simple-zero faithfulness, a uniform positive spectral gap, or pointwise monotonicity when nonnegative full energy or a zero-rate floor suffices. Some stronger targets are already false.

### 4.4 Main research topics

**A. Signed near-incidence estimates.** Develop weighted sums over $ab-cd=h$, prime pairs, and divisor successor relations in which cancellation is proved for the complete kernel. The first benchmark is the actual coalescent surplus, with its stated $N(T,2T)$ normalization.

**B. Arithmetic compatibility of mixed moments.** Determine which joint additive/multiplicative arrays arise from the literal source. Existing phase-recovery theorems show that data can be reconstructed without controlling its energy. The new topic is quantitative compatibility strong enough to constrain that energy.

**C. Boundary and escape classification.** Classify source-specific limits with their origin, tail, and paid-ideal data intact. The purpose is to find a constraint violated by every escaping state, not merely to realize or name its spectrum. A complete classification that remains compatible with possible off-line zeros is informative but not a closure.

**D. Arithmetic sections with metric and torsion.** Construct section growth on the original scaling pairing and investigate composition, restriction, and duality. Exact RR is already a foothold. The new theorem must supply compatible Bézout/ampleness, or a weaker quantitative floor, from the same construction.

**E. Relative tensor/intersection calculus.** Separate coefficient amplification from external support growth. Compute the two-factor case before extrapolating. Distinguish effective zero-cycle counts from positivity of correspondences; the golden Künneth example makes this distinction mandatory.

**F. Defect-sensitive localization.** Translate averaged estimates into bounds adapted to detecting profiles, retaining derivative norms, negative margins, zero clustering, and remote-ordinate errors. Establish exactly when a possible isolated defect cannot hide in the allowed exceptional set.

**G. Signed continuation and renormalization.** Seek integrated, horizon-uniform continuation laws rather than everywhere-positive damping work. The existing countermodels show that positive-part control can be stronger than necessary. A field that only admits monotone or termwise positive evolution would discard viable mechanisms.

### 4.5 Criteria the field must meet

Its usefulness should be judged by results on the existing arithmetic objects, not the size of its formalism.

| Required test | Reason |
|---|---|
| Derive a new inequality for the actual source | Source identification and exact reformulations are already abundant |
| Recover the correct Gamma/pole terms and all prime powers | Omissions can change positivity or make a false model look selective |
| Explain why the golden impure datum fails the new geometric hypothesis | Positive Euler, Adams, and symmetric-power data already survive there |
| Detect relevant phase/parity distinctions | Magnitudes and complete-period quadratic observations can identify sources with different admission |
| Preserve energy at the required horizon/origin/damping limit | The critical information can live entirely in the boundary or closure defect |
| Provide an intermediate theorem weaker than RH | Otherwise the programme has only renamed its endpoint |
| Exhibit a quantitative path from that theorem to an individual-defect receiver | Better density or restricted positivity alone leaves exceptions |

Countermodels must be used with their actual scope. The golden curve is not a counterexample to Riemann's exact degree-one theta law. A shifted ζ pair changes poles and coefficient growth. A positive correction density is not automatically a completed Euler system. A good theory should distinguish these cases rather than demand that one toy model preserve every arithmetic invariant.

## 5. Research choices implied by this assessment

The proposed focus is **one concrete signed statistic, one source-compatibility construction, and one amplification law**. This supplies three different chances of progress while keeping them mathematically connected.

I would not make the next principal objective another finite positive aperture, another free positive carrier, a sharper finite harmonic certificate with unchanged growth payment, or a new equivalent index formula. Those remain useful supporting tools when they pay a specified part of one of the three questions. They do not by themselves cross the established boundaries.

Likewise, classifying cofactor spectra, improving source rigidity, and refining finite section geometry remain worthwhile, but each needs an explicit next implication. Does the classification exclude an actual escape state? Does the rigidity theorem supply an estimate? Does the section construction control the original mixed defect? If not, it has clarified the problem without yet reducing the central uncertainty.

The strongest opportunity exposed by the combined research is the passage from **multiplicative equalities to signed near-equalities, and from separate positive observations to prescribed joint arithmetic relations**. Relative geometry is attractive because it might make that passage systematic and amplifiable. The first evidence that it works should be a concrete arithmetic inequality whose gain survives all the way to an existing receiver.
