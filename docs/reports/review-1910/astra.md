# Research-program review — 19 October 2026

**The main deficit is an arithmetic estimate, not another representation of RH.** The four programs have developed substantial mathematics: exact decompositions, finite-source classification, sharp instability results, arithmetic sampling identities and useful counterexamples. They have not yet produced a bound on a complete signed quantity, with the source and quantifiers required by a closing theorem.

My recommendations are to concentrate the existing programs on two explicit receivers, redirect several current research targets, and **not start a fifth broad theory program now**. A narrower investigation of arithmetic concentration in the bad directions of the actual energy forms could justify a fifth program later. Its novelty would have to be an arithmetic theorem, not a new name for positivity, observability or cancellation.

This review also corrects the [obstacles report](../hard-obstacles-summary-1810.md). Several of its claims were mathematically wrong or overstated; others had fallen behind the Lean corpus. Those errors change what should be researched next.

## 1. What the evidence supports

The initial repository document review was restricted to the six requested files: the [route ledger](../rh-current-frontier-map.md), the [obstacles report](../hard-obstacles-summary-1810.md), and the READMEs for [Arithmetic Positivity Theory](../../../formal/GaloisForLFunctions/arithmetic-positivity-theory/README.md), [BiScale Uncertainty](../../../formal/GaloisForLFunctions/BiScaleUncertainty/README.md), [Trans-Horizon Incidence Mechanics](../../../formal/GaloisForLFunctions/TransHorizonIncidenceMechanics/README.md) and [Bézout–Valuation Incidence](../../../formal/GaloisForLFunctions/BezoutValuationIncidence/README.md). The requested follow-up also reviews [Argon's report](argon.md); §11 records the resulting corrections and executable work. Claims were compared with corpus-search results and Lean statements/proofs. The assessment covers all 27 live routes and 18 candidates at the level of their stated open dependencies; it is not a fresh compilation of every route.

Three distinctions govern the conclusions:

| Kind of result | What it establishes | What it does not establish |
|---|---|---|
| Identity or recovery theorem | The arithmetic data and a transformed object determine each other under stated hypotheses. | A favorable sign or bound for that object. |
| Structural or quantitative theorem | A conditioning law, sharp obstruction, restricted estimate or admissible limit. | That the actual arithmetic source satisfies the remaining hypotheses. |
| Closing arithmetic estimate | The literal source satisfies the complete inequality with every required parameter controlled. | This is the missing achievement. |

The existing work is not worthless. It has narrowed the problem and ruled out attractive shortcuts. But the evidence does not support measuring distance to RH by module count, number of equivalent criteria, or number of finite families recovered. Nor does it support the original claim that six identified obstacles are six irreducible gaps in all mathematics.

### Corrections with immediate consequences

1. **Nyman–Beurling used the wrong measure.** With \(\rho_k(x)=\{1/(kx)\}\), the standard space is \(L^2((0,\infty),dx)\). Under \(u=1/x\), the origin tail becomes an integral against \(du/u^2\). The former combination of the same fractional parts with \(dx/x^2\) becomes an unweighted integral of a periodic function and usually diverges. The corrected criterion is classical, not a new obstacle. [Báez–Duarte](https://arxiv.org/abs/math/0202141).
2. **Selberg tapering changes the head.** For \(c_{N,d}=\mu(d)\log(N/d)/\log N\), the divisor sum at \(2\le k\le N\) is \(\Lambda(k)/\log N\), not zero. Literal Möbius cancellation cannot be transferred unchanged to this row.
3. **The damping requirement was overstated.** The PM/BVI receiver permits a different finite horizon bound at each member of an arbitrarily small sequence of positive dampings. It does not require a single bound as damping tends to zero. The quoted Euler product also had order \(\varepsilon^{-2}\), not \(\varepsilon^{-1}\).
4. **CHMD threshold control is not compactness.** The infinite-dimensional threshold radical prevents compactness of the full resolvent. Finite multiplicity at each eigenvalue above the threshold does not imply a finite-dimensional entire band. Source mass does not descend through the signed radical quotient.
5. **The arithmetic bridges have advanced.** BVI already has cofinal sublinear discrepancy and strict negative renormalized defects on fixed polynomial windows. THIM already connects valuation clocks with prime-chain energies. Recommending those connections as a new discipline would duplicate existing work.
6. **One new BiScale classification excludes the actual Möbius support.** Its nonzero highest-dyadic anchor is identically zero for squarefree-supported coefficients when \(N\ge4\). Section 4 gives the exact argument and the resulting research direction.

The corrected obstacles report contains the formulas, qualifications and supporting Lean links. These corrections remove invalid targets; they do not close a proof route.

## 2. Which mathematical tools are missing?

### 2.1 Arithmetic cancellation in the complete weighted form

The central unmet need is a way to retain enough cancellation among signs, depths, endpoints and inherited histories in a source-dependent quadratic or bilinear expression. Knowing the diagonal, magnitudes, local frequencies or a positive component is insufficient when the omitted cross terms determine the outcome.

This is especially visible in BVI. For the actual truncated Möbius sieve, the corpus proves
\[
s_{N,\mu}(k)=-\mu(k)\quad(N<k\le2N),
\]
and hence
\[
s_{N,\mu}(k)s_{N,\mu}(k+1)=\mu(k)\mu(k+1)
\quad(N<k,\ k+1\le2N).
\]
Thus even the first trans-horizon band already contains a fixed-shift signed Möbius correlation. Recovering its magnitude patterns solves a different problem. See `sieveSeq_moebiusReal_mul_succ_first_octave` in [QuotientDualOctaveReciprocityAndValuationSwitching.lean](../../../formal/GaloisForLFunctions/BezoutValuationIncidence/QuotientDualOctaveReciprocityAndValuationSwitching.lean).

This identifies a recognizable number-theoretic difficulty; it does not prove that a full Chowla theorem is necessary for RH or for the proposed energy estimate. A one-sided weighted aggregate may need much less than every individual signed correlation. Research should target that aggregate before taking on a stronger famous conjecture.

**Current-literature qualification.** The September 24, 2026 preprint [Ordinary two-point correlations of multiplicative functions](https://github.com/openai/math/blob/main/preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/final.pdf) claims ordinary two-point cancellation: a logarithmic saving for fixed Liouville affine forms, and qualitative Möbius cancellation for fixed affine forms. Its introduction explicitly disclaims uniformity for coefficients growing with the cutoff; §18.3 supplies no quantitative rate for products containing Möbius. I inspected those statements, not the full proof or its formalization. Thus this report neither declares the ordinary binary problem definitively open nor treats the claim as independently verified. Even if accepted, its stated conclusions alone do not give the moving-kernel, summable-energy estimate needed here. Verification and applicability assessment should precede reinventing this fixed-form result.

There is already powerful mathematics nearby. The following sources describe useful tools, but none supplies the particular closing estimate merely by citation:

| Existing tool | What it supplies | Transfer still needing proof here |
|---|---|---|
| [Matomäki–Radziwiłł short-interval theory](https://arxiv.org/abs/1501.04585) | Cancellation/mean-value control for multiplicative functions in almost all short intervals. | The actual moving weights, exceptional intervals and endpoint costs of the complete energy. |
| [Matomäki–Radziwiłł–Tao averaged Chowla](https://arxiv.org/abs/1503.05121) | Cancellation averaged over growing shift families, for fixed correlation order. | The required weighted, scale-dependent aggregate and a sufficiently strong rate. |
| [Tao's logarithmically averaged two-point theorem](https://arxiv.org/abs/1509.05422) | Logarithmically weighted two-point cancellation through entropy decrement and related tools. | An unweighted fixed-shift conclusion does not follow just by removing the weight. The native pronic weights need a real calculation. |
| [Green–Tao Möbius–nilsequence orthogonality](https://arxiv.org/abs/0807.1736) | Strong logarithmic savings against controlled nilsequence families. | Complexity and norms of the arithmetic tests generated by the energy can grow with the cutoff. |
| [Matomäki–Shao–Tao–Teräväinen higher uniformity](https://arxiv.org/abs/2204.03754) | Short-interval nilsequence/Gowers estimates in specified length and complexity regimes. | A reduction of the actual cofactor kernel to those regimes, with all losses paid. |

The corpus already contains an [averaged-Chowla interface](../../../formal/GaloisForLFunctions/RHTower/Sieve/AveragedChowlaInterface.lean). Its relevant cancellation property is a premise of the transfer theorem. A name in Lean is not evidence that the external analytic theorem, with the needed uniformity, has been proved there.

**What is missing in the repository:** a proved application of arithmetic cancellation to a complete receiver quantity. **What may require new mathematics:** control of an adaptive, growing family of these tests at a strength current correlation estimates do not deliver. This audit cannot establish that no existing combination of methods can do it.

### 2.2 Estimates that survive growth of the test family

Several successful results have the form
\[
\forall\text{ fixed finite pattern }b,\qquad Q_N(b)\longrightarrow Q_\infty(b).
\]
The intended application instead chooses a pattern \(b_N\), increasing support, increasing aperture, or increasing moment order. Pointwise convergence does not justify that substitution. Even an existential diagonal choice growing arbitrarily slowly may be useless if a receiver demands a specified relation between the scales.

The missing tool is a quantitative estimate in the receiving norm, with dependence on support size, frequency, amplitude, aperture and damping displayed. Sometimes an operator bound will work. Where universal operator bounds fail, the estimate must use the actual source subclass or bound its component in the badly conditioned directions.

This is not an absence of compactness theory from mathematics. The challenge is proving tightness and continuity for the particular arithmetic form. Origin concentration, polar mass, translation and increasing oscillation must be controlled in that form's topology. An unweighted \(L^2\) approximation does not automatically control its prime and polar contributions.

### 2.3 An arithmetic sign principle for the complete odd form

CHMD/RW/OWU need an inequality on the actual source, not another spectral dictionary. A precise existing formulation is
\[
\mathcal E_{\rm arch}(v)+\mathcal E_{\rm prime}(v)
\ \ge\ \mathcal M_{\rm cosh}(v^2)
\]
for every admissible odd compactly supported \(C^2\) test. The exact definitions occur in `riemannHypothesis_iff_forall_odd_phiDoob_dirichlet_poincare`, in [WeilPhiDoobArchimedeanJumpAndHalfLineFolding.lean](../../../formal/GaloisForLFunctions/RHTower/WeilPhiDoobArchimedeanJumpAndHalfLineFolding.lean). This is RH-equivalent.

Positive jump terms, an even ground state and a self-adjoint resolvent do not automatically control sign-changing odd states. Passing to \(|v|\) changes parity. Quotienting a null space removes degeneracy but does not remove negative directions; the corpus even proves `not_sourceMass_descends` in [CHMDQuotientParityAndCoercivity.lean](../../../formal/GaloisForLFunctions/RHTower/CHMDQuotientParityAndCoercivity.lean).

A useful new tool would bound the actual low-prime/polar potential against the jump energy on this constrained source domain, or identify a source-derived nodal inequality that pays the primitive projection defect. Calling that inequality “arithmetic curvature” or defining a square root after assuming positivity would add no mathematics.

### 2.4 Other routes retain genuinely different difficulties

The entire portfolio does not reduce, by currently proved implications, to one BVI estimate. BAG needs a centered tail bound conditioned on finite-head return heights. TH/HCF need control of unbounded degree, with compatible parameters. Several geometric candidates need a construction from primes and archimedean data before introducing the Xi zero divisor, followed by a proved identification with the receiving object. Robin/Nicolas needs a sign at prime-saturated extremal integers.

These are separate research obligations. A universal “bridge between discrete and continuous mathematics” is too vague to answer them. Existing arithmetic spectral work already connects primes, trace formulas and positivity; [Connes's trace-formula program](https://arxiv.org/abs/math/9811068) and [Suzuki's screw-function criterion](https://arxiv.org/abs/2209.04658) are relevant precedents. Any proposed new program must explain the additional theorem it would provide.

## 3. Arithmetic Positivity Theory: research the complete critical form

### What has already been achieved

The current Lean frontier is ahead of a simple “derive a critical affine model” agenda. [FactorialCriticalAffineComparison.lean](../../../formal/GaloisForLFunctions/arithmetic-positivity-theory/FactorialCriticalAffineComparison.lean) already proves a whole-source weighted error bound
\[
\int_1^\infty |F_b(v)-A_b(v)|^2\frac{dv}{v^2}
\le \frac{C}{140}\sum_n\frac{|b_n|^2}{n+1}.
\]
In particular, support above \(m\) gives an error at most \(C\|b\|_2^2/[140(m+1)]\), without a restriction on the number of coefficients. Re-proving a finite-pattern version would be a regression.

The critical translated prime channel also has an exact limiting representation. For every fixed finite real pattern \(b\),
\[
P_\infty(b)=\frac4{\pi^4}\int_0^1 K(t)
\left|\sum_j b_j e^{2\pi ijt}\right|^2dt,
\]
with a continuous symmetric real kernel \(K\). See [FactorialCriticalTranslatedPrimeLimit.lean](../../../formal/GaloisForLFunctions/arithmetic-positivity-theory/FactorialCriticalTranslatedPrimeLimit.lean) and [FactorialCriticalPrimeContinuousKernel.lean](../../../formal/GaloisForLFunctions/arithmetic-positivity-theory/FactorialCriticalPrimeContinuousKernel.lean).

The charge feeding this kernel is unusually explicit. [FactorialCriticalPrimeCumulativeCharge.lean](../../../formal/GaloisForLFunctions/arithmetic-positivity-theory/FactorialCriticalPrimeCumulativeCharge.lean) proves that its cumulative cubic-weighted charge is negative at the initial nonzero stages and positive from stage five onward. That is valuable information. It is not yet a sign theorem for the periodized kernel, and a prime-channel sign is not a complete Weil-form sign: in the usual Weil decomposition the prime channel is subtracted.

### Next target A1: settle the limiting kernel as a diagnostic

Determine rigorous lower and upper bounds for \(K\), ideally its sign and extremal values. If it changes sign, construct finite coefficient patterns witnessing the corresponding signs of \(P_\infty\). Use the exact charge expansion and a proved tail bound; numerical samples alone cannot certify a continuous kernel's minimum.

**Why this comes next:** the object is already explicit, so this is a finite mathematical question with a clear outcome. It reveals which directions the critical model rewards or penalizes. It is a structural result, not an RH closure. Stop expanding this calculation once the signature and usable bounds are known; further decimal precision has little research value here.

### Next target A2: lift approximation to the complete form

Let \(P_n\) be the already defined translated prime energy. A concrete intermediate quantity is
\[
\eta(n,J)=\sup_{\substack{\operatorname{supp}b\subseteq\{0,\ldots,J\}\\
\sum_j b_j^2=1}} |P_n(b)-P_\infty(b)|.
\]
For each fixed \(J\), convergence follows from convergence of the finitely many matrix entries. That consequence alone is not the desired research advance. Seek an explicit bound for growing \(J\), and then a corresponding comparison for the **complete** Gamma/prime/polar form, including all cross terms. The admissible growth rate should be chosen from a receiving approximation or separation argument, rather than chosen only to make convergence easy.

The uniform affine estimate above is an ingredient, not a substitute for this step. Identify where the prime sum or polar functional requires stronger control, and prove that control or construct a failure sequence. A failure sequence would be useful if it identifies the exact missing norm or escaping profile.

### Next target A3: prove that the family can detect a negative direction

Before treating positivity of another factorial family as RH progress, prove one of these alternatives:

- its span approximates the required test domain in a topology controlling the complete form; or
- every hypothetical negative direction produces a negative member of the family, by an independently justified separation argument.

High-scale restricted positivity is already known and is RH-nonselective. More examples of it do not address this requirement. APT's next substantial contribution should therefore combine **full-form control and a useful family**, not just one of them.

**Stop condition:** if the family cannot reach or separate the unresolved odd/polar directions, classify that limitation and keep its kernel theorem as a standalone result. Do not present its unconditional positivity as movement toward the unrestricted sign criterion.

## 4. BiScale Uncertainty: move to the actual source support and receiving norm

### An applicability gap worth fixing first

[SieveLocalVisibilityClassification.lean](../../../formal/GaloisForLFunctions/BiScaleUncertainty/SieveLocalVisibilityClassification.lean) classifies the sharp local recovery exponent on the highest-dyadic stratum: exponent \(1\) when the specified first-order visibility holds, otherwise \(1/3\). Its hypothesis includes
\[
Y_{N,b}(q_N)\ne0,\qquad q_N=2^{\lfloor\log_2N\rfloor},
\quad
Y_{N,b}(q)=\sum_{\substack{1\le d\le N\\q\mid d}}\frac{b_d}{d}.
\]

For any squarefree-supported \(b\), every nonsquarefree \(q\) has \(Y_{N,b}(q)=0\): each multiple of \(q\) is nonsquarefree. For \(N\ge4\), \(q_N\) is divisible by four. Therefore
\[
Y_{N,b}(q_N)=0\quad(N\ge4)
\]
for literal Möbius rows, power-damped Möbius rows, and Möbius rows multiplied by a taper. This elementary deduction is now formalized in [SieveArithmeticSourceAnchors.lean](../../../formal/GaloisForLFunctions/BiScaleUncertainty/SieveArithmeticSourceAnchors.lean); its status is an applicability audit, not a claimed new research theorem.

The existing classification is valid on its stated stratum. It cannot be invoked for these arithmetic rows. Source recovery with nearby arbitrary perturbations and recovery within the squarefree-supported class are also different problems; the latter excludes many of the perturbations that determine the former exponent.

### Next target U1: classify local recovery on the relevant support class

Start with the squarefree stratum and the actual transformed support generated by BVI's cofactor operations. Determine the correct phase ambiguities, visible modes and local exponents there. Keep actual integer translation as the equivalence relation where that is what the receiver respects; an arbitrary coordinate sign change need not be a physical symmetry.

State two versions separately: perturbations constrained to the source class, and unrestricted perturbations about that source. Quantify dependence on nonzero coordinate sizes. An anchor that is nonzero at each finite cutoff can still approach zero too fast to yield useful stability.

The same module proves the precise terminal-prime alternative: for prime
\(N/2<p\le N\) and \(c(d)=\mu(d)w(d)\),
\(Y_{N,c}(p)=-w(p)/p\), nonzero exactly when \(w(p)\ne0\).
For a Barban–Vehov row of cutoff \(X\), nonvanishing is equivalent to \(p<X\).
Thus the proposed prime anchor needs a taper check, and replacing the anchor
does not prove the new visibility classification.

**Success:** a theorem whose hypotheses can be checked for a named arithmetic row and whose constants have explicit cutoff dependence. **Insufficient:** another complete classification on a convenient stratum disjoint from those rows.

### Next target U2: replace recoverability by an energy estimate

The receiving task does not need every coefficient recovered with the best possible exponent. It needs control of a particular form. Let \(d_N\) denote the observation discrepancy and \(\mathcal E_N\) the chosen receiving energy. Seek a bound of the form
\[
|\mathcal E_N(c)-\mathcal E_N(b)|
\le A_N\,d_N(c,b)^\alpha+R_N,
\]
on a stated bounded source class, with the observation normalization, coefficient budget and remainder specified. A theorem is useful only when the actual approximation makes the right side small in the required scale regime. Audit the constant in the actual recovery theorem: the \((N!)^6\) factors in the current classification occur in sharpness-witness moment bounds. Its `normalized_local_cubic` recovery proof uses \(2+2\sum_{q\le N}\varphi(q)\) when the reference anchor has magnitude at least \(2\). This corrects Argon's attribution without supplying short-horizon recovery or applicability to squarefree sources.

First try this for one concrete BVI/PM energy or APT critical-form block. Do not invent an abstract norm and postpone its relation to the receiver. It may be easier and stronger for the application to estimate the energy directly than to reconstruct the whole source.

### Next target U3: classify the escapes that defeat finite observations

[FullGridEnergyCycleAmbiguity.lean](../../../formal/GaloisForLFunctions/BiScaleUncertainty/FullGridEnergyCycleAmbiguity.lean) already constructs ambiguity with a bounded singular-energy budget and all integer-log grid observations together with any fixed finite cycle degree. The conclusion is not “take a larger fixed collection of the same moments.”

Study whether a growing degree/window resolves the relevant ambiguity with acceptable cost, or whether an additional source constraint removes the escaping packets. A useful classification would explicitly distinguish translation, concentration at the origin, separated polar packets and growing oscillation, then show which profiles the actual arithmetic source can generate.

**Stop condition:** if excluding an escape is merely the desired RH sign restated, mark it as the unresolved arithmetic premise. The uncertainty theorem should expose that premise rather than hide it in an admissibility definition.

## 5. Trans-Horizon Incidence Mechanics: spend the transfers on a source estimate

### What the sharp bounds already say

The universal inverse physical Fermi constant is not bounded independently of the horizon. [FermiPhysicalOptimalConstants.lean](../../../formal/GaloisForLFunctions/TransHorizonIncidenceMechanics/FermiPhysicalOptimalConstants.lean) identifies its asymptotic growth as
\[
\frac4{\pi^2}(\log_2 N)^2,
\]
both for arbitrary coefficients and for nonnegative coefficients. Positivity of coefficients alone does not remove the loss.

But this does not obstruct every arithmetic source. For Möbius-twisted rows \(c(d)=\mu(d)w(d)\), [FermiValuationSamplingAndPronicObservability.lean](../../../formal/GaloisForLFunctions/TransHorizonIncidenceMechanics/FermiValuationSamplingAndPronicObservability.lean) already gives
\[
Q_{N,S}(c)\le P_{N,S}(c)\le4Q_{N,S}(c)
\]
for the literal selected and paired pronic energies, uniformly in horizon and finite cell set. The larger four-free class also has this control. Therefore “prove uniform Fermi observability for Möbius weights” is already answered. The unresolved issue is bounding the selected energy and transporting the *complete* target through subsequent operations.

The latest working-tree files sharpen a different support boundary. [FermiDyadicAntichainSupportRepresentation.lean](../../../formal/GaloisForLFunctions/TransHorizonIncidenceMechanics/FermiDyadicAntichainSupportRepresentation.lean) gives an \(8e^{6M}\) physical bound for admissible dyadic antichains when the allowed odd primes have reciprocal capacity at most \(M\). [FermiDivergentCapacityAntichainPackets.lean](../../../formal/GaloisForLFunctions/TransHorizonIncidenceMechanics/FermiDivergentCapacityAntichainPackets.lean) constructs nonnegative admissible packets with \(P\ge(L-1)/2\) and \(0<Q<5/6\) when that capacity is unbounded. These are substantive positive and negative support results, not a reason to launch another universal-observability project. They were source-inspected here, not rebuilt as a separate checkpoint.

The subsequently inspected [FermiDyadicAntichainPrimeCapacityClassification.lean](../../../formal/GaloisForLFunctions/TransHorizonIncidenceMechanics/FermiDyadicAntichainPrimeCapacityClassification.lean) packages both directions into an exact classification by summability of the allowed odd-prime reciprocals, for signed and nonnegative packets. At this review's lint check, several of these newest modules were still unreachable from the umbrella; their working-tree status must be kept distinct from an imported checkpoint.

### Next target T1: identify the exact class preserved by the complete calculation

Take one concrete PM/BVI decomposition and track its coefficients through cofactor restriction, birth-time shifts, centering and boundary extraction. For each operation, determine whether the resulting row stays squarefree/four-free, becomes an admissible antichain, or leaves those classes. This is a mathematical closure question about the actual operators, not a generic bridge exercise.

Where the favorable class survives, apply the existing constant-four estimate. Where it fails, isolate the offending component and estimate its receiving energy or construct a counterexample. Do not apply the bounded-prime-capacity theorem to all primes: their reciprocal capacity is unbounded. Do not infer failure for Möbius rows from a different class's bad packets either.

**Deliverable:** a source-specialized inequality for the entire transformed quantity, with an explicit defect term whose arithmetic size is the next stated question. An exact transfer that simply puts the same uncontrolled energy on the right is a dictionary, not an estimate.

### Next target T2: bound selected energy, means and boundary leakage together

The existing [NaturalCutoffMultiDepthCofactorAndConditionalTailBridge.lean](../../../formal/GaloisForLFunctions/BezoutValuationIncidence/NaturalCutoffMultiDepthCofactorAndConditionalTailBridge.lean) gives the exact decomposition
\[
V_\varepsilon(Q)=H_\varepsilon(Q,H)
+(H+1)m_\varepsilon(Q,H)^2
+T_\varepsilon(Q,H),
\]
where the terms are the natural-cutoff head energy, head mean and conditional tail variance. The tail variance is nonnegative. Merely making the head fluctuation small does not control the mean term or the tail.

THIM should turn its sampling and support information into a joint bound for these terms on the actual coefficient trajectory. Optimize the cutoff only after displaying its cost in every term. A source-specific bound may succeed where the operator norm over arbitrary coefficient packets cannot.

### Next target T3: a separate, narrowly stated odd-sector pilot

For the CHMD/OWU connection, select the low-prime diagonal potential remaining after exact collar cancellation. Determine its best relative bound against the *actual* odd jump energy, retaining support radius and rapidity. A bound below the needed threshold would be meaningful; a proof that the proposed local comparison fails would expose the compensating global term required next.

This pilot must pay reflected-prime and primitive-projection defects. Existing conditional absorption with `coshSinhPolarRatio ≤ θ ≤ 1` still leaves a source pairing. Calling that conditional estimate a positivity producer would be circular. Similarly, a detected off-line chain excess needs an independent ceiling for the same energy before it can exclude a zero.

**Stop condition:** stop adding transforms once the remaining inequality is unchanged under the transform. Continue only if a new coordinate system yields a provable estimate, a sharper necessary hypothesis, or a counterexample with a useful replacement theorem.

## 6. Bézout–Valuation Incidence: prioritize signed cofactor coupling

### Use the exact receiver, including its weaker damping quantifiers

Write \(I_\varepsilon(n)=\texttt{pmBezoutInteriorPrefix}\ \varepsilon\ n\). The existing theorem `riemannHypothesis_of_pmBezoutInteriorPronicEnergy_bounded` accepts
\[
\boxed{
\forall\delta>0\ \exists\varepsilon\in(0,\delta)\ \exists B_\varepsilon<\infty\
\ \forall T\ge1:\quad
\sum_{n=1}^{T}\frac{I_\varepsilon(n)^2}{n(n+1)}\le B_\varepsilon .
}
\]
See [PronicPotentialSelfCancellationAndInteriorGradientConservation.lean](../../../formal/GaloisForLFunctions/BezoutValuationIncidence/PronicPotentialSelfCancellationAndInteriorGradientConservation.lean). This is a closing target, not a newly discovered intermediate theorem. It allows arbitrarily large constants as \(\varepsilon\downarrow0\). Even a sequence of positive dampings tending to zero is enough if every corresponding horizon supremum is finite.

**The baseline already includes \(\varepsilon=1/2\).**
[PMPowerDampedMobiusEndpoint.lean](../../../formal/GaloisForLFunctions/RHTower/PMPowerDampedMobiusEndpoint.lean)
and [PMPowerDampedMobiusDiscreteEnergy.lean](../../../formal/GaloisForLFunctions/RHTower/PMPowerDampedMobiusDiscreteEnergy.lean)
prove actual source admission and a horizon-uniform discrete-energy bound for
every \(\varepsilon\ge1/2\). The follow-up adds
`exists_pmBezoutInteriorPronicEnergy_budget_of_half_le`, using the existing
inequality \(\mathcal I_\varepsilon(T)\le2E_\varepsilon(T)+1/2\).
The unknown source/interior range is \(0<\varepsilon<1/2\). A uniform natural-cutoff
Ramanujan variance bound in \(Q\) is a different sufficient condition: the
source endpoint does not prove that approximation sequence uniformly bounded.

The actual cofactor coordinates must also be kept straight:
\(Y_\varepsilon(q)=\operatorname{Re}\sum_{m\ge1}\mu(qm)(qm)^{-1-\varepsilon}\),
and \(Y_\varepsilon(pr)=-Y_\varepsilon(r)/(p^{1+\varepsilon}-1)\) for
\(\varepsilon>0\), prime \(p\), and \(p\nmid r\). They are not
\(\mu(q)q^{-\varepsilon}\). The [BVI README](../../../formal/GaloisForLFunctions/BezoutValuationIncidence/README.md)
now states the restricted head identity and the separate head/mean/tail costs.

The corpus also proves in [UniformRenormalizedInteriorEnergyRemainder.lean](../../../formal/GaloisForLFunctions/BezoutValuationIncidence/UniformRenormalizedInteriorEnergyRemainder.lean) that a strict contraction of its complete compensated interior expression is equivalent, at fixed positive damping, to bounded actual energy. That equivalence prevents “find a strict contraction” from being counted as an independent weakening of the problem.

### Next target B1: expand the unsolved signed term into usable correlation kernels

Start from the exact complete compensated budget, retain its counterterm, and group the literal coefficients by gcd, cofactor scale and birth interval. Determine the resulting signed kernels before applying absolute values. The objective is to expose a class to which a proved number-theoretic estimate can be applied, while keeping the diagonal, shared-start covariance, conditional means and endpoints explicit.

The new arithmetic question should name an actual kernel and a scale range. “The remainder is pseudorandom,” “successors are independent,” or “the martingale has negative drift” is not a hypothesis-free result. In this deterministic setting a martingale label does not itself provide a probabilistic filtration or conditional expectation law.

A useful first comparison is with the averaged-Chowla and short-interval estimates in §2: calculate exactly which part of the kernel they control, what loss survives, and which part lies outside their hypotheses. This can either yield a genuine estimate or show precisely where a stronger correlation theorem is needed. Either outcome is more informative than another magnitude law without a signed consumer.

### Next target B2: test summability, not just cofinal negativity

For the same literal interior prefix, define the nonnegative dyadic block budget
\[
\mathcal B_{\varepsilon,j}
=\sum_{2^j\le n<2^{j+1}}
\frac{I_\varepsilon(n)^2}{n(n+1)}.
\]
Bounded total energy is exactly summability of these block budgets. A pointwise-in-scale \(o(1)\) bound does not ensure summability. Negative renormalized defects on fixed polynomial windows do not automatically control this different nonnegative series.

Use the signed-kernel analysis to seek a summable majorant for arbitrarily small fixed positive dampings. If only a nonsummable bound is obtained, state its cumulative growth explicitly and compare it with the best already available bound. An explicit decay law would be stronger than the receiver requires; do not silently make a convenient geometric decay rate a necessary condition.

This is the main research experiment. A successful bound would close PM through an existing theorem. Failure to obtain it should be recorded as failure of the tested mechanism, not as a new no-go for all trans-horizon analysis.

### Next target B3: use a smaller signed benchmark before a full joint law

The cofinal magnitude laws and gradient bounds are already substantial. [CofinalMobiusJointMagnitudeLaw.lean](../../../formal/GaloisForLFunctions/BezoutValuationIncidence/CofinalMobiusJointMagnitudeLaw.lean), [CofinalMobiusMagnitudeObservablesAndGradient.lean](../../../formal/GaloisForLFunctions/BezoutValuationIncidence/CofinalMobiusMagnitudeObservablesAndGradient.lean), and [UniformCofinalMobiusPrefixDiscrepancy.lean](../../../formal/GaloisForLFunctions/BezoutValuationIncidence/UniformCofinalMobiusPrefixDiscrepancy.lean) should be treated as inputs, not as unfinished tasks. The first-band two-prime occupancy bound in [MobiusFirstBandTwoPrimeBound.lean](../../../formal/GaloisForLFunctions/BezoutValuationIncidence/MobiusFirstBandTwoPrimeBound.lean) is also a magnitude statement; it does not resolve adjacent Möbius signs.

Before attempting an entire signed finite-dimensional process law, identify the minimum signed aggregate needed by B1. Its weights might permit shift averaging or logarithmic averaging even when a fixed-shift theorem is unavailable. Prove that compatibility; do not assume it.

For comparison, the corpus already has the explicit alternative target
\[
\forall\eta>0\ \exists C_\eta:\quad
\sum_{\substack{1\le m<n\\m+n\le N}}\mu(m)\mu(n)
\le C_\eta(N+1)^{1+\eta},
\]
whose Lean version implies RH after paying the linear diagonal. See [MobiusAdditiveTriangleChowlaFrontier.lean](../../../formal/GaloisForLFunctions/RHTower/MobiusAdditiveTriangleChowlaFrontier.lean). This is an existing difficult receiver, not a new proposal to solve by assuming Chowla. It is useful for judging the strength of any advertised “signed correlation” advance.

**Stop condition:** if a proposed extension computes only additional unsigned statistics, require an explicit inequality converting them to the signed budget before assigning it RH priority. It can still be valuable independent research.

## 7. Is a fifth program justified?

**Not as another umbrella for arithmetic geometry, clocks, incidence, positivity or spectral realization.** Those subjects are already represented. The current bottleneck is not an empty namespace. A fifth broad program would most likely add another set of reductions with the same arithmetic premise.

There is, however, a specific research question that deserves a joint pilot: **can the actual arithmetic source be proved to avoid the bad directions of the complete energy operators, quantitatively as the scales grow?** Call the pilot *arithmetic concentration and signed energy*. Keep it inside the existing programs until it produces a distinct theorem.

### What the pilot would try to do

For a specified finite-cutoff positive observation problem, let \(P_N\) be the full Gram form on a justified nondegenerate domain and \(Q_N\) the observed Gram form on that same domain. Any quotient must first be shown to preserve both forms. Set
\[
A_N=P_N^{-1/2}Q_NP_N^{-1/2},\qquad x_N=P_N^{1/2}c_N,
\]
where \(c_N\) is a literal arithmetic coefficient vector, not an arbitrary vector chosen after seeing the spectrum. If \(\Pi_{N,<a}\) is the spectral projection of \(A_N\) below \(a>0\), then
\[
\|\Pi_{N,<a}x_N\|^2\le\theta\|x_N\|^2,\quad\theta<1
\quad\Longrightarrow\quad
Q_N(c_N)\ge a(1-\theta)P_N(c_N).
\]
This implication is elementary spectral theory. **The research content would be proving the left-hand bound from arithmetic**, with useful dependence on all cutoffs. Universal bad vectors do not disprove it, and favorable computations for \(c_N\) do not prove it.

For raw Möbius Fermi sampling, the existing constant-four theorem already does the job. The pilot must therefore choose a genuinely unresolved object: for example the cofactor/centering operation that exits that favorable source class, or a controlled finite approximation to the complete signed remainder. It must justify any passage from finite matrices to the required infinite energy. The construction above concerns positive observation forms; it is not by itself a positivity proof for an indefinite Weil form.

The central questions would be:

1. Which bad modes have explicit arithmetic descriptions, rather than descriptions through unknown Xi zeros?
2. Do those descriptions reduce the source projection to a known correlation problem with controlled complexity?
3. Can existing cancellation estimates bound it in a growing range that is useful after summing scales?
4. If not, what precise new weighted correlation estimate is needed, and is it weaker than a known RH-equivalent target?
5. Does the estimate survive the actual means, boundaries and prime/polar subtraction, or only the auxiliary positive form?

### What would justify a separate program

A distinct program would be justified by a source-specific theorem beyond the current support classifications, together with a proved transfer that improves a complete budget. A sharp counterexample plus a replacement hypothesis that the actual source satisfies could also qualify. The output should explain why standard sieve, harmonic-analysis or correlation machinery does not already give the result in its stated regime.

It would **not** be justified by the spectral decomposition above, a renamed RH-equivalent coercivity conjecture, a zero-indexed Hilbert space, or a proof of injectivity without a usable constant. These are already familiar kinds of construction. This review does not claim that nobody has studied arithmetic concentration, inverse theorems or spectral nonconcentration; that novelty claim would require a much deeper literature audit around a precise theorem.

The potential new mathematics is the interaction between an arithmetic source and a growing family of hard test directions. That is a research question with falsifiable intermediate outcomes. It is not evidence that inventing an entirely new mathematical discipline is necessary for RH.

## 8. Consequences for the whole route portfolio

These tables account for every route in the requested ledger. They identify the first unpaid mathematical obligation, not a claim that all obligations are equivalent. The program recommendations above primarily serve the Möbius/approximation group and the complete Weil-form group. The other routes need a specific independent producer before they justify a comparable expansion of infrastructure.

### All 27 live routes

| Route | Unpaid obligation that should determine the next research task |
|---|---|
| WL | A source-derived one-sided critical prime-lag or integrated Chebyshev-deficit bound. More sampling identities do not produce it. |
| RW | All-aperture sign of the complete Gamma/prime/polar form. Use APT family tests and the odd-sector pilot where their hypotheses match. |
| FU | Pay the signed scheduling drift, seed, previous action, covariance and endpoints over the whole history. |
| RP | A complete-history floor including moving-core, high-LCM and singular-domain costs. |
| PA | Sign of the full arithmetic current or complete moment problem, including the complement of favorable saddle bands. |
| MC | A global signed bilinear estimate with principal counterterm and high-product remainder treated together. Primary BVI application. |
| TT | Nonlocal covariance/full odd or primitive positivity at every required rapidity and test scale. |
| LA | An all-height arithmetic separator, especially for near-double off-line pairs and remaining low-order cases. |
| TG | A matrix-complete residual-energy decomposition and an all-disc sub-unit bound, or its stated independent gap alternative. |
| HF | Complete positivity on the unresolved blind/odd source domain. Arithmetic cup/trace geometry is a separate construction obligation. |
| CHMD | An actual-source nodal/jump/potential estimate excluding the unresolved odd states above threshold. Primary positivity application. |
| TH | All-degree positivity with one compatible heat parameter. Fixed-degree eventual signs do not suffice. |
| RN | Prime-plus-Gamma versus pole control with global seam/cusp gluing and correct boundary orientation. |
| WD | A global source contraction/cap estimate paying every zero-block owner and absorber cost. |
| LI | The literal primitive's finite lower bound, or the stated eventual prime–Gamma inequality with outside correlations retained. |
| SZ | A source Wronskian law and controlled cusp-preserving passage to unshifted Xi, including the infinite moving head. |
| PM | Complete pronic/interior energy bounded in the horizon at arbitrarily small fixed positive dampings. Primary closing receiver. |
| JAS | Source sign on enough exceptional shells, all-amplitude shell positivity, or the stated subpower Riesz bound. |
| CTF | Actual rows with the required global norm and approximation control, or vanishing discrete Báez–Duarte distance. Primary alternative receiver. |
| HCF | Both literal grid forms controlled at unbounded polynomial degree, or a proved stated entropy/chirp alternative. |
| XN | Source construction of invariant discs covering every zero, with interior curvature potential paid. |
| BAG | Centered tails controlled on the same finite-head return heights across the required disc. Keep as an independent conditional-analysis pilot. |
| EWU | Complete even blind minimum at every aperture; restricted factorial positivity does not settle it. |
| GTA | Uniform transverse-energy decay proved from the source, independently of the zero divisor. |
| OWU | Actual odd positivity with reflected-prime, cosh-pole and negative-sinh-moment costs included. |
| PBM | Critical-abscissa cancellation for the fixed regularized prime/log-zeta coefficients, or the ledger's stronger alternative package. |
| RB | The required square-root-scale remainder sign on increasingly prime-saturated extremal integers or primorials. |

PM's PW-B sub-branch is still a candidate inside that live route: it needs a pre-divisor source formulation and a complete small-damping ceiling, plus the remaining optical/cap/extinction implications. FZZ-P progress cannot be assigned to PW-B without those bridges.

### All 18 candidates

| Candidate | Admission requirement before further RH-oriented expansion |
|---|---|
| APF | Zero-independent exhaustion/vanishing of all trace coefficients; reconstructing off-line terms is not their elimination. |
| BSH | An arithmetic section and mate identity constructed before using the Xi divisor. |
| BVI | The complete signed trans-horizon estimate in §6; the candidate status is appropriate until a closing source bound exists. |
| CDC | A source-defined potential on the closed error fibres that couples the parameter to Xi without assuming the desired wall. |
| DR | Global continuation/monodromy and source convergence, beyond compatible finite covers. |
| EGC | An outer expanding-contour sign/covariance argument; inner cancellations and raw ray decay do not pay the Gamma floor. |
| EWJ | Zero-independent admission and norm exhaustion of the full jet system. |
| FEL | A source-derived cofinal zero-to-contrast balance; posterior accounting alone does not select the line. |
| HJ | A source producer before the divisor, instead of parity/heat witnesses already indexed by Xi zeros. |
| IRK | A global arithmetic lift with integral analytic count and the correct defect. |
| MSC | A source-faithful transfer from squarefree observation to a complete nonnegative receiving energy. |
| PCS | An arithmetic wall-class annihilation preserving the forward mode and the nonzero shift defect. |
| PTR | A prime-faithful continuum construction preserving the divisor, or an independent zero-loss theorem overcoming its current gap. |
| RFHM | A source-defined phase/depth law that supplies orientation beyond reversible forward creation. |
| SC | A source-fixed indefinite cross-fibre restriction/index that selects the wall. |
| SEC | Pre-divisor arithmetic eventual compactness or depth-uniform jet control. |
| W1C | Concrete arithmetic couplings with the required centered limit and interaction-driven edge behavior, not a generic Lee–Yang analogy. |
| WBF | An arithmetic certificate stream and depth-uniform completion with a proved Xi/Weil landing. |

“Defer expansion” is not “retire the route.” A route should be retired only after its stated mechanism fails and the strongest positive survivor has been extracted. Several current counterexamples already have valuable survivors: support-dependent observability, sharp finite recovery, exact residual decompositions and restricted positive cones.

## 9. Recommended next research cycle

Run two coordinated mathematical investigations, with one small independent reserve:

| Investigation | Responsibilities | Evidence required to count it as progress |
|---|---|---|
| Complete damped Möbius energy | BVI identifies and estimates the signed kernel; THIM pays transfers/means/boundaries; BiScale handles only observation errors the argument actually uses. | A new bound for the literal complete budget, with exact damping and horizon quantifiers. |
| Complete critical/odd Weil form | APT settles the critical kernel and full-form comparison; BiScale controls changing families; THIM tests the specific low-prime/nodal estimate. | A usable full-form estimate or a sharp obstruction plus an arithmetic replacement hypothesis. |
| Conditional recurrence reserve | BAG studies one centered tail under one explicit return conditioning. | A conditional estimate stronger than the unconditional bound divided by the return density, or a rigorous boundary explaining why that approach fails. |

The investigations need not close RH in one cycle. They must move a numerical bound, a provable admissible regime, or a source hypothesis. The following questions should accompany every proposed result:

1. What literal arithmetic object is being bounded, and where is it defined?
2. Which closing theorem could consume the result, with what still missing?
3. Which parameters are fixed, growing, or chosen after other parameters?
4. Does the proof use source signs, or only magnitudes and finite algebra?
5. What counterexample tests the proposed scope, and what survives if it fails?

A result earns RH priority when it removes an assumption, improves a relevant estimate, admits the actual source to a needed domain, or proves a controlled limit required by a receiver. An identity with the same unpaid estimate on both sides is useful infrastructure; it should be recorded as such. This change in research selection is more urgent than adding a fifth program.

## 10. Verification and limits of this review

The documented corpus command was used directly, including module-filtered searches for critical APT results, BiScale visibility, THIM Fermi estimates and BVI cofinal laws, plus a deep search for signed Möbius correlation mechanisms. Representative invocations were:

```sh
scripts/formal_tools.py research "critical" --module arithmetic-positivity-theory --no-refresh --json
scripts/formal_tools.py research "visibility phase" --module BiScaleUncertainty --no-refresh --json
scripts/formal_tools.py research "Fermi" --module TransHorizonIncidenceMechanics --no-refresh --json
scripts/formal_tools.py research "cofinal" --module BezoutValuationIncidence --no-refresh --json
scripts/formal_tools.py research "signed shifted Mobius correlations logarithmic cancellation growing coefficients" --mode deep --budget-seconds 60 --no-refresh --json
```

Declaration results, candidate lemmas and source arguments were inspected, then important claims were checked against Lean source. The initial searches reported `partial: false`; the follow-up squarefree/prime-anchor deep search also completed. The follow-up clock-kernel deep search reported `partial: true` after its budget expired; its available hits were inspected and the relevant formulas checked directly in Lean source. The index contained substantial pending/stale compiler metadata. Complete retrieval is not complete verification. Current working-tree additions were inspected where they materially changed a recommendation, including the latest support-capacity and local-visibility files.

A temporary Lean import probe successfully checked the actual PM receiver, first-octave adjacent-product identity, CHMD source-mass obstruction and APT prime-limit declaration. Axiom probes for the receiver, adjacent-product identity, source-mass obstruction and continuous-kernel representation reported only `propext`, `Classical.choice` and `Quot.sound`. These checks used available compiled imports; they do not certify a clean rebuild of the concurrently changing repository.

The original temporary squarefree-support proof has now been promoted into the repository and extended with the terminal-prime/taper facts. The requested follow-up also adds the exact mass/edge correlation module and the BVI interior-energy endpoint theorem. Both new modules and the modified BVI implementation module compiled successfully with `lake env lean -o …`. Their statements were first checked in temporary Lean files; no proof holes or new axioms were introduced in the source. The four program READMEs, ledger and obstacles report were corrected as described in §11.

A follow-up temporary probe checked **all 12 new public theorems** with `#print axioms`: each depends only on `propext`, `Classical.choice` and `Quot.sound`. The same probe compiled concrete boundary checks: the Barban–Vehov prime anchor vanishes at `(N,X,p)=(7,7,7)`, survives at `(7,7,5)`, and the interior budget includes damping exactly `1/2`. Both the BVI and BiScale umbrellas compiled successfully. The BiScale check required rebuilding three pre-existing missing dependency artifacts (including the clock graph’s BV-admission dependency) and fixing the duplicate helper name described in §11. The renamed helper’s source compiled; a joint-import probe confirmed both previously conflicting lemmas coexist and the renamed proof uses only the same standard axioms.

The required `scripts/formal_tools.py lint` now **passes**, with existing large-file warnings. The first review had reported six unreachable THIM modules; their umbrella imports had already been added by other work before this follow-up. The new BiScale modules are also reachable from their umbrella. This is a lint and targeted-compilation result, not a clean rebuild of every route or every transitive dependency.

Document checks confirmed that all 121 local links across the seven edited documents resolve, display-math/code delimiters are balanced, and whitespace checks pass. The original route-table audit covered exactly the ledger's 45 route labels; the follow-up did not change those route tables.

Primary literature was used to check classical criteria and the scope of relevant analytic methods. Recent preprint claims were distinguished from independently verified inputs. This was an applicability review, not a comprehensive proof audit of the literature and not a certificate that a proposed research direction is unprecedented. The review establishes no new RH-closing estimate; its concrete contributions are corrected targets, an independently checked source-stratum mismatch, and a research agenda tied to the actual remaining arithmetic inequalities.


## 11. Follow-up: comparison with Argon and executable changes

**Argon changes several details and the immediate work list, but not the main
recommendation.** Its strongest contribution is identifying corrections that
had not been propagated into the program READMEs. It reinforces the need to
select research by an independently proved arithmetic estimate. It does not
establish that ordinary spectral theory is inadequate, that the visibility
theorem is vacuous on its own domain, or that the quoted large-sieve exponents
apply to the PM receiver. I have preserved Argon's report as an independent
review and recorded the disagreements here.

### What changes in this report

1. **Make the existing endpoint explicit.** The actual PM source-energy bound
   already covers every $\varepsilon\ge1/2$. I should have stated that baseline
   alongside the receiver. Its transfer to the interior energy is routine and
   is now in Lean. A bound below $1/2$ is a substantial arithmetic problem, not
   an implementation task. The stronger uniform-in-$Q$ natural-cutoff variance
   premise must be discussed separately.
2. **Correct the literal PM coordinates.** The BVI README had identified a
   divisor coefficient with a Selberg/Ramanujan coordinate and consequently
   gave the wrong prime-step factor. The corrected factor is
   $-(p^{1+\varepsilon}-1)^{-1}$ under the coprimality hypothesis. The finite
   head identity retains its range restrictions and head/mean/tail terms.
3. **Qualify both the proposed anchor and the cited constants.** A terminal
   prime works only if its coefficient is nonzero. A Barban–Vehov taper kills
   the cutoff endpoint and all primes beyond it. The existing $(N!)^6$ bounds
   occur in sharpness-counterexample estimates, not the normalized local cubic
   recovery constant. Both distinctions are now stated in §4 and the README.
4. **Use the actual clock-kernel parameters.** A common center, cutoff and
   nontranslation-invariant measures survive the prime-ratio lag substitution.
   Exact integrated readouts are routine; a lag-only reduction or a useful
   signed estimate would require another theorem.

The fifth-program recommendation is unchanged: first work inside the four
existing programs on a specified arithmetic inequality. The concentration pilot
in §7 remains a possible focused investigation, with its source and success
criterion stated. Neither review proves that a new named theory is necessary,
nor that a particular organization of future work is mathematically mandatory.

### Completed work

| Item | Concrete result |
|---|---|
| THIM documentation | Replaced the invalid Nyman measure and tail-only closure claim; restored the prime guard in the clock formula; removed the obsolete subhorizon-only account of BVI and claims that transfer identities defeat the open obstacles. Distinguished source-domain mass from a quotient norm, and existing Chebyshev transport from the remaining absorption bound. |
| BVI documentation | Corrected the PM coordinate, prime factor and restricted recursion; corrected damping quantifiers; documented the established endpoint and the separate natural-cutoff variance premise. |
| BiScale documentation | Stated the actual source-stratum exclusion, exact taper condition, scope of the constants, and parameters retained by the new kernel readouts. |
| APT documentation | Distinguished established subcritical/critical affine tools and kernel representations from the open complete-form sign and growing-pattern estimates. Recorded the existing exact kernel-weight mass theorem. |
| Ledger and obstacles report | Removed the uniform-as-damping-vanishes requirement; added the source/interior endpoint baseline, actual PM weights, and permanent links to the source-anchor proofs. |
| Source-anchor Lean module | [SieveArithmeticSourceAnchors.lean](../../../formal/GaloisForLFunctions/BiScaleUncertainty/SieveArithmeticSourceAnchors.lean) proves six results: nonsquarefree coordinate vanishing, highest-dyadic vanishing, its Möbius-taper specialization, the weighted terminal-prime formula, its nonvanishing criterion, and the exact Barban–Vehov criterion. It reuses the existing single-multiple prime-coordinate theorem. |
| Interior endpoint Lean theorem | [PronicPotentialSelfCancellationAndInteriorGradientConservation.lean](../../../formal/GaloisForLFunctions/BezoutValuationIncidence/PronicPotentialSelfCancellationAndInteriorGradientConservation.lean) now exposes `exists_pmBezoutInteriorPronicEnergy_budget_of_half_le`. No new analytic assumption was introduced. |
| Clock correlation Lean module | [PrimeGraphClockCorrelationKernels.lean](../../../formal/GaloisForLFunctions/BiScaleUncertainty/PrimeGraphClockCorrelationKernels.lean) defines the center-and-lag mass/edge kernels and proves the vertex/edge readouts, both inner-product formulas, and the complete signed source-pair formula. Both new modules are imported by the BiScale umbrella. |
| Umbrella integration fix | The full BiScale import check exposed two distinct lemmas named `RHTower.abs_arg_le_of_re_pos`. Renamed the Jordan-bound helper in [JointAncestryExplicitSectorBlindBand.lean](../../../formal/GaloisForLFunctions/RHTower/JointAncestryExplicitSectorBlindBand.lean) to `abs_arg_le_pi_div_two_mul_im_div_re` and updated its sole call site. The inequality and proof are unchanged; the separate zeta-mass lemma keeps its existing name. |

For the last item, write
$$F_{k,t}(x)=\chi_k(x)A(t-x),\qquad
K_M(k,t,\ell)=\int F_{k,t+\ell}(x)F_{k,t}(x)\,d\mu(x),$$
$$K_E(k,t,\ell)=\int
  [F_{k,t+\ell}(e_L)-F_{k,t+\ell}(e_R)]
  [F_{k,t}(e_L)-F_{k,t}(e_R)]\,d\kappa(e).$$
Here $A$ is the literal critical Abel profile, $\mu$ the actual mass measure,
and $\kappa$ the complete edge measure. For $N,p,q>0$,
$t=\log(N/q)$ and $\ell=\log(q/p)$, the proved formulas are
$$\langle a_p^{\rm mass},a_q^{\rm mass}\rangle
=\frac{N}{pq}K_M(k,t,\ell),\qquad
\langle a_p^{\rm edge},a_q^{\rm edge}\rangle
=\frac{N}{pq}K_E(k,t,\ell),$$
$$\operatorname{sourcePair}(a_p,a_q)
=\frac{N}{pq}\bigl(K_E(k,t,\ell)-K_M(k,t,\ell)\bigr).$$
These are exact explicit integral representations. They do not evaluate the
integrals in closed form or establish the sign of their difference.
The sign question must retain the receiver's source restrictions:
`constantLift_energy` in
[CHMDDoobSourceGraph.lean](../../../formal/GaloisForLFunctions/RHTower/CHMDDoobSourceGraph.lean)
gives energy $-c^2/2$ for constant profiles. Positivity on the full source graph
is false; the odd or other constrained domain is part of the research target.

### Action items that remain research, or were already done

| Argon proposal | Disposition after the source audit |
|---|---|
| Prove a PM budget on $(1/3,1/2]$ | The source-energy endpoint $1/2$ was already proved and is now exposed at the interior interface. Extending below it, or establishing the natural-cutoff variance version, remains research. A cited Kloosterman/large-sieve exponent is not a proof of its applicability to this receiver. |
| Replace the dyadic visibility classification by a prime anchor | Elementary applicability facts are now proved. The phase ambiguities, local inverse exponent and horizon-dependent stability theorem still require research. |
| Replace factorial full-period constants by polynomial-horizon bounds | Corrected the attribution of the factorial constants first. Changing the observation horizon still requires a new theorem; it is not a constant simplification. |
| Integrate low-prime collar sums by parts against a Chebyshev discrepancy | The exact transport already exists in `CollectiveLowPrimeChebyshevTransportAndSinhAbsorption.lean`. The all-radius bound strong enough for absorption is the unresolved step. |
| Remove or bypass the Fermi $(\log_2N)^2$ loss | It is sharp for the current universal observation model. Constant-$4$ Möbius-twisted sampling and the antichain prime-capacity classification already give restricted positive alternatives. Admitting the actual target source to a useful class, or changing the sampled cells, is a separate research task. |
| Resolve the critical APT prime-kernel sign and assemble the full form | The kernel and mass identities exist. A sign estimate, the complete archimedean/prime/polar comparison, and control for growing patterns remain open; none is supplied by the documentation update. |
| Replace the four-term eigenvector criterion by a genuine estimate | The criterion is an exact balance/conditional receiver. Its usefulness depends on proving the premise independently. The short algebraic proof is not an error to “fix”; generic Cauchy–Schwarz upper bounds do not supply the required lower bound. |

No open estimate has been replaced by an assumption disguised as a new theorem.
The completed Lean additions make existing arithmetic facts and exact readouts
available to the next research step; they do not claim to close an RH route.
