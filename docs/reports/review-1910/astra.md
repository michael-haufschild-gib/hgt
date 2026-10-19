# Review of the RH research program

**Status: 19 October 2026.** The mission is a proof of RH whose decisive arithmetic input is constructed independently of the desired zero location and whose deductions can be checked in Lean.

## 1. Where the program stands

The four programs have built substantial mathematical infrastructure: exact source identities, admissible completions, observability classifications, sharp counterexamples, and bridges between arithmetic and spectral formulations. They have not supplied the complete arithmetic sign or cancellation estimate needed to close a proof route. More infrastructure is worthwhile only when it removes a specific obstacle to producing such an estimate.

The central gap is **a bound for the actual arithmetic source, in the complete receiving form, with the required growing-parameter control**. It is not a general absence of Fourier analysis, Dirichlet forms, ground-state transforms, sieve decompositions, or compactness theory. Some missing transfers are substantial research problems; some proposed “new tools” already exist, either in mathematics or in this corpus.

| Program | Established capability | Unpaid obligation | Recommended focus |
|---|---|---|---|
| Arithmetic Positivity Theory (APT) | Critical affine comparisons, translated prime limits, harmonic kernel representations and exact kernel-weight mass. | Sign and approximation control for a complete, sufficiently rich arithmetic test family. | Complete critical forms, quantitative approximation and detection of negative directions. |
| BiScale Uncertainty | Sharp recovery/conditioning laws, source-support obstructions, and literal mass/edge correlation kernels. | Recover or approximate the actual source in a norm controlling the receiving energy, without losing the needed uniformity. | Relevant support strata and source-specific tightness. |
| Trans-Horizon Incidence Mechanics (THIM) | Exact horizon transfers, sharp sampling losses, restricted inverse bounds, collar identities and Chebyshev transport. | Pay means, endpoints, reflected interactions and the negative mass term together. | Complete signed estimates and compensated odd-sector coercivity. |
| Bézout–Valuation Incidence (BVI) | Exact cofactor/pronic identities, the interior-energy RH receiver, the damping endpoint, a Vaughan Type-I/II dictionary and classical discrepancy transfers. | Signed cancellation strong enough to bound the complete pronic energy at arbitrarily small positive dampings. | The actual weighted remainder, beyond coefficient-energy and prefix bounds. |

Two proof projects should organize most work:

1. **Complete damped Möbius energy:** BVI produces the arithmetic estimate; THIM handles transfers and boundary terms; BiScale supplies only the approximation or observation control actually required.
2. **Complete critical/odd Weil form:** APT supplies arithmetic test families and full-form comparisons; THIM studies the unresolved compensated coercivity; BiScale controls changes of scale and limits.

These are useful organizing targets, not a theorem that every route has the same mathematical difficulty. Conditional zeta recurrence, all-degree positivity and arithmetic geometric realization retain distinct obligations.

### 1.1 The Möbius receiver: exact strength and baseline

Write

$$
 I_\varepsilon(n)=\operatorname{pmBezoutInteriorPrefix}(\varepsilon,n),\qquad
 E_\varepsilon(T)=\sum_{n=1}^{T}\frac{I_\varepsilon(n)^2}{n(n+1)}.
$$

The formal receiver is

$$
 \left[\forall\delta>0\;\exists\varepsilon\in(0,\delta)\;
 \exists B_\varepsilon\;\forall T\ge1,\quad E_\varepsilon(T)\le B_\varepsilon\right]
 \Longrightarrow \mathrm{RH}.
$$

The constant may depend on damping and may diverge as damping tends to zero. A common bound for all small dampings is unnecessary. The corpus already proves horizon-uniform bounds for **every fixed $\varepsilon\ge\tfrac12$, including the endpoint**, for both the actual discrete source energy and the interior pronic energy. A natural-cutoff Ramanujan variance bound uniform in its additional cutoff is a different, sufficient premise; the established source-energy endpoint should not be advertised as proving that stronger premise. See [`PronicPotentialSelfCancellationAndInteriorGradientConservation.lean`](../../../formal/GaloisForLFunctions/BezoutValuationIncidence/PronicPotentialSelfCancellationAndInteriorGradientConservation.lean), especially `exists_pmBezoutInteriorPronicEnergy_budget_of_half_le` and `riemannHypothesis_of_pmBezoutInteriorPronicEnergy_bounded`.

**One fixed damping bound does not directly yield the often-claimed zero-free half-plane.** The Mellin identity is

$$
 \mathcal M F_\varepsilon(s)
 =\frac{(1-2^{1-s})\zeta(s)}{s\zeta(s+\varepsilon)}
$$

on its initial strip. Source admission gives analyticity for $\Re s>\tfrac12$, and a cleared identity extends into the right critical strip. For $0<\varepsilon\le\tfrac12$, the actual proved conclusion is

$$
 \zeta(\rho)=0,\qquad \tfrac12+\varepsilon<\Re\rho<1
 \quad\Longrightarrow\quad \zeta(\rho-\varepsilon)=0.
$$

This is **zero translation**, not nonvanishing: a denominator zero can be cancelled by a numerator zero. The RH proof chooses admitted dampings arbitrarily close to zero and contradicts isolation of zeros. Consequently, identifying one fixed sub-half damping budget with a “quasi-RH” zero-free half-plane requires an additional argument. The source already makes this distinction explicit in `pmPowerDamped_zero_translation` and `riemannHypothesis_of_pmPowerDamped_cofinal_admission` in [`PMPowerDampedMobiusCriterion.lean`](../../../formal/GaloisForLFunctions/RHTower/PMPowerDampedMobiusCriterion.lean).

A first bound at a specified $0<\varepsilon<\tfrac12$ is a meaningful intermediate target. It must be reported with its actual consequences, rather than labelled either a full RH proof or an already-proved zero-free region. A converse from a zero-free region to source admission also needs growth/integrability control; holomorphy alone does not establish the required $L^2$ bound.

### 1.2 The positivity receiver: domain and subtraction matter

The relevant target is positivity on the specified odd or constrained source domain. Positivity on the full source graph is false: `constantLift_energy` gives energy $-c^2/2$ for a constant source. An even-sector calibration therefore needs the correct spectral shift and normalization.

The corpus already has a complete graph space retaining both mass and every arithmetic edge. Its norm controls

$$
 \|v\|_{\mathrm{mass}}^2+\|Dv\|_{\mathrm{edge}}^2,
$$

whereas the signed source energy subtracts mass from edge energy. Constructing another “Weil Sobolev norm” with these ingredients is not the missing discovery. The missing estimate is that the actual odd arithmetic sector has enough edge energy to pay the mass subtraction. See [`CHMDDoobSourceGraph.lean`](../../../formal/GaloisForLFunctions/RHTower/CHMDDoobSourceGraph.lean) and the exact odd-sector equivalences in [`CHMDOddSectorCriterion.lean`](../../../formal/GaloisForLFunctions/RHTower/CHMDOddSectorCriterion.lean).

Source mass does not descend to the signed radical quotient; see [`CHMDQuotientParityAndCoercivity.lean`](../../../formal/GaloisForLFunctions/RHTower/CHMDQuotientParityAndCoercivity.lean). The infinite family of threshold modes also rules out compactness of the full resolvent. Removing the exact critical band preserves signed pairings, but does not prove positivity of the remaining form; see [`CHMDCriticalBandReduction.lean`](../../../formal/GaloisForLFunctions/RHTower/CHMDCriticalBandReduction.lean). Arguments using a quotient norm or compactness must address the actual domain and remaining spectrum.

### 1.3 What should count as progress

A research chain should pass three tests:

- **Arithmetic input:** identify where the literal Möbius, von Mangoldt, theta or zeta source enters an estimate stronger than the generic bound.
- **Discrimination:** identify which hypothesis rules out an explicit off-line or wrong-sign model. A useful countermodel must satisfy the hypotheses actually being tested.
- **Completion:** state the cutoffs, test degree, aperture, height, damping and exceptional-set dependence needed to reach the receiver.

These tests apply to the complete argument. A universal lemma need not distinguish Möbius from Liouville to be useful. Nor does a counterexample to one coarse observable prove that every signed construction in BVI or THIM is subject to an identical sieve-parity obstruction. An equivalence with RH identifies the destination; it does not supply the arithmetic mechanism that reaches it.

## 2. Which mathematical tools are missing?

### 2.1 A usable arithmetic cancellation estimate for the complete weighted object

The main cancellation target is not an isolated correlation $\sum_{n\le X}\mu(n)\mu(n+h)$. It is a coupled sum with cofactor restrictions, moving cutoffs, principal counterterms, endpoints and weights dictated by the receiving energy. An estimate must survive summation over that family.

Existing analytic number theory supplies serious tools. What remains unproved here is their sufficiently strong transfer to the literal objects:

| Existing mathematics | Available strength | Transfer still required |
|---|---|---|
| [Matomäki–Radziwiłł short-interval theory](https://arxiv.org/abs/1501.04585) | Multiplicative-function control in almost all short intervals. | Moving weights, exceptional intervals and boundary costs in the complete energy. |
| [Matomäki–Radziwiłł–Tao averaged correlations](https://arxiv.org/abs/1503.05121) | Cancellation averaged over shift families. | The actual weighted family, coefficient ranges and a summable quantitative loss. |
| [Tao's logarithmically averaged two-point theorem](https://arxiv.org/abs/1509.05422) | Logarithmically weighted cancellation. | A valid comparison with the native pronic weights and cutoff geometry. |
| [Green–Tao Möbius–nilsequence orthogonality](https://arxiv.org/abs/0807.1736) and [higher uniformity in short intervals](https://arxiv.org/abs/2204.03754) | Cancellation against structured tests in specified complexity and length regimes. | A reduction of the actual tests to those regimes, with growing complexity paid for. |
| Vaughan decompositions and coefficient-energy estimates | Exact separation of arithmetic sums into pieces amenable to different estimates. | A signed saving for the relevant pieces and their complete remainder. A decomposition alone is not that saving. |

Even a qualitative ordinary two-point theorem for each fixed pair of affine forms would not supply growing-coefficient uniformity or the rate needed here. The [September 2026 ordinary-correlation preprint](https://github.com/openai/math/blob/main/preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/final.pdf) should be treated as a claimed result requiring a separate applicability audit, not as an automatic solution of the weighted energy problem. This review does not certify that preprint's proof.

The immediate research question is therefore: **which existing estimate can be applied to one exact remainder, and what precise loss prevents its sum from closing?** Only after answering that can we identify a new cancellation theorem that mathematics genuinely needs for this route.

### 2.2 Stability and tightness in the norm the proof actually consumes

Finite recovery, fixed-pattern asymptotics and pointwise convergence do not automatically pass to a growing family in the source graph. Needed tools include:

- quantified approximation of the full form, with aperture and coefficient complexity visible;
- source-specific bounds excluding escape through increasing prime indices, concentration, translation or frequency;
- control of exceptional intervals and boundary leakage in the same energy budget;
- an admissible limit preserving every polar constraint and reflected interaction.

Concentration–compactness and profile decompositions are possible methods. Their applicability is an open task, not a ready-made conclusion that every bounded archimedean-energy sequence has finitely many profiles and a remainder invisible to the prime form. Archimedean energy alone need not control the singular prime observations. Start with one actual family and the existing graph norm.

### 2.3 A sign principle for the compensated odd arithmetic form

Nonlocal ground-state representations and Allegretto–Piepenbrink theory already exist: see [Frank–Seiringer](https://arxiv.org/abs/0803.0503) and [Frank–Lenz–Wingert](https://arxiv.org/abs/1012.5050). The unresolved issue is whether an applicable representation or coercivity theorem can be built for this specific arithmetic form.

There is a concrete obstacle to importing the positive-jump theory directly. The corpus proves that odd half-line folding produces a negative reflected-prime measure mutually singular with the positive archimedean and same-side prime measure. On

$$
 B=\{(x,\log 2-x):0<x<\tfrac12\log2\},
$$

the positive jump measure has zero mass and the negative reflected measure has strictly positive mass. `negative_component_survives_positive_gauge` proves that every strictly positive scalar reweighting retains this obstruction, even after adding an absolutely continuous correction or a diagonal measure. See [`CHMDReflectedPrimeSingularPart.lean`](../../../formal/GaloisForLFunctions/RHTower/CHMDReflectedPrimeSingularPart.lean).

The positive survivor is equally important: the negative reflected difference term and its collar diagonal combine into a strictly positive crossing energy for nonzero odd compact tests. The full source identity retains this compensated term and the remaining cosh-mass subtraction. Thus the task is **quantitative control of the compensated form**, or a genuinely different nonlocal representation. It is not routine construction of a positive scalar ground state for the original folded jump kernel. The obstruction does not prove that the complete Weil form is negative or forbid every possible factorization.

### 2.4 What cannot yet be claimed about mathematics as a whole

The evidence supports missing estimates and construction principles for these routes. It does not establish that RH necessarily requires one particular new theory, that all existing methods face one identical barrier, or that “arithmetic criticality” is an undeveloped field. A novelty claim needs a specific theorem statement and a literature comparison.

The most plausible new mathematics would connect arithmetic restrictions to global signed coercivity or to quantitative cancellation for a growing family. Its value would be demonstrated by a new bound, a sharper detection law, or an obstruction with a useful replacement hypothesis—not by another name for the RH-equivalent positivity statement.

## 3. Arithmetic Positivity Theory

### Current position

Critical affine approximation and translated prime limits are already present. The harmonic kernel has a representation, and [`FactorialCriticalPrimeKernelMass.lean`](../../../formal/GaloisForLFunctions/arithmetic-positivity-theory/FactorialCriticalPrimeKernelMass.lean) gives the exact positive kernel-weight mass

$$
 \frac{\pi^2}{12}\sum_{j\in S}b_j^2.
$$

This is a statement about the positive weight. It does not settle the sign of the complete charged prime form, much less the prime–Gamma–polar balance. “Construct the critical kernel” and “compute its total weight” are therefore obsolete next milestones.

### Research next

**A1. Determine the sign and sharp bounds of the complete limiting quadratic form.** Keep every subtraction and mixed coefficient. Either prove a lower bound with explicit dependence on pattern size and coefficients, or exhibit a finite coefficient vector with negative value. Both outcomes inform which family is worth extending. A positive weight integral alone is not evidence for the required sign.

**A2. Prove full-form approximation with explicit costs.** Choose one admissible family and control its prime, Gamma and polar errors together in the existing receiving norm. The estimate must say how its constants grow with support, aperture and coefficient complexity. Fixed-pattern convergence is a baseline; the new result is the joint regime needed for density or an expanding test family.

**A3. Establish that the family can detect the obstruction.** Before a large positivity campaign, test the family on specified off-line configurations. A family that stays nonnegative on an obstruction model cannot close the route by its own positivity alone. The Square-Root Threshold models in §7 give concrete tests, but they do not reproduce all arithmetic axioms of zeta.

A useful diagnostic is the reflection defect. For a reflection-invariant zero configuration, multiplicities $m_\rho$, transform values $F_\rho$, and sufficient absolute convergence, set

$$
 Z_F=\sum_\rho m_\rho|F_\rho|^2,\qquad
 W_F=\sum_\rho m_\rho F_\rho\overline{F_{1-\overline\rho}}.
$$

Then

$$
 Z_F-\Re W_F
 =\tfrac12\sum_\rho m_\rho
   |F_\rho-F_{1-\overline\rho}|^2.
$$

This separates the diagonal budget from the reflection defect. The algebra does not bound the defect arithmetically; $Z_F$ itself is defined using zeros. A useful theorem must produce a source-derived bound with the right margin. This expression should not be confused with a two-zero pair-correlation statistic merely because both involve zeros.

**Progress criterion:** a complete-form estimate for a family that demonstrably detects a relevant obstruction, with enough parameter control to enlarge that family. Another fixed-pattern representation without those properties does not move the closing frontier.

## 4. BiScale Uncertainty

### Current position

The local visibility classification has a genuine source-stratum limitation. For squarefree-supported coefficients, the highest-dyadic Selberg coordinate vanishes once $N\ge4$; the nonzero-anchor branch therefore excludes the actual Möbius and Möbius-tapered sources in that range. This does not make the entire classification vacuous.

The elementary arithmetic anchor facts are established in [`SieveArithmeticSourceAnchors.lean`](../../../formal/GaloisForLFunctions/BiScaleUncertainty/SieveArithmeticSourceAnchors.lean). For a terminal prime $N/2<p\le N$,

$$
 Y_{N,\mu w}(p)=-\frac{w(p)}p,
$$

so it is nonzero exactly when $w(p)\ne0$. For the Barban–Vehov taper with cutoff $X$, the condition is $p<X$. A prime exists in the relevant interval in the usual Bertrand range, but that alone does not ensure a nonzero tapered anchor or good conditioning.

The factorial-size bounds belong to particular sharpness witnesses, not to every local recovery constant. On the normalized cubic branch with anchor magnitude at least 2, the recovery constant is $2+2\sum_{q=1}^{N}\varphi(q)$; see `normalized_local_cubic` in [`SieveLocalVisibilityClassification.lean`](../../../formal/GaloisForLFunctions/BiScaleUncertainty/SieveLocalVisibilityClassification.lean). The normalization and observation model still matter. Correct attribution is necessary before proposing a polynomial improvement.

Literal clock correlations also exist. [`PrimeGraphClockCorrelationKernels.lean`](../../../formal/GaloisForLFunctions/BiScaleUncertainty/PrimeGraphClockCorrelationKernels.lean) identifies mass and edge inner products with kernels $K_M,K_E$, and the signed source pairing with

$$
 \frac{N}{pq}\left[K_E(k,t,\ell)-K_M(k,t,\ell)\right],\qquad
 t=\log(N/q),\quad \ell=\log(q/p).
$$

The cutoff $k$ and center $t$ remain. This is not a lag-only kernel, and the identity supplies neither its sign nor a uniform spectral bound.

### Research next

**U1. Classify recovery on the actual support stratum.** Replace the unusable anchor by terminal-prime or mixed-coordinate observations, then determine the remaining phase ambiguities, inverse exponent and conditioning constants. Keep taper zeros, shrinking anchor size and the observation horizon explicit. The established prime-coordinate formula is the starting point; a new recovery theorem is not a rename of the dyadic result.

**U2. Estimate error in the complete receiving energy.** Connect observation error to mass-plus-edge norm or directly to the full quadratic form. Recovery of coefficients is insufficient if the stability loss grows faster than the analytic saving. A useful result supplies a bound of the form

$$
 |\mathcal E(c)-\mathcal E(b)|
 \le C\,\operatorname{ObsErr}(b,c)^\alpha
$$

on a precisely specified source class, with $C$, the horizon and every normalization controlled in the intended limit.

**U3. Prove tightness for one arithmetic family.** Identify which escapes are possible for the actual Möbius/BV or prime-clock family in the existing source graph. Prove a compactness statement only after controlling the singular prime part, or construct an escaping sequence and state the extra hypothesis that excludes it. Do not assume a finite-profile theorem or a remainder with vanishing Weil energy in advance.

**Progress criterion:** a usable energy-error or tightness bound on an actual source family. Greater observability by itself does not supply arithmetic cancellation.

## 5. Trans-Horizon Incidence Mechanics

### Current position

The sharp losses and several positive alternatives are already known. The universal selected Fermi trace has an unavoidable logarithmic-square inverse loss in its present observation model. Möbius-twisted sampling has a constant-4 inverse estimate, and the antichain theory identifies a prime-capacity boundary. These results tell us which restrictions or observation changes might help; they do not establish that the full target energy is controlled by a favorable restricted observation.

The odd-source side already includes divisor-chain decompositions, reflected-collar compensation, secondary odd-profile identities and integration against a Chebyshev discrepancy. The Stieltjes/partial-summation transport in [`CollectiveLowPrimeChebyshevTransportAndSinhAbsorption.lean`](../../../formal/GaloisForLFunctions/TransHorizonIncidenceMechanics/CollectiveLowPrimeChebyshevTransportAndSinhAbsorption.lean) is an existing tool, not a missing first step.

### Research next

**T1. Identify a source class preserved by the whole argument.** If a constant-4 inverse estimate or antichain capacity bound is used, prove that the arithmetic construction and every needed truncation, shift or limit remain in its class. Track the mean and the omitted cells. A theorem for selected gradients does not automatically control an uncentered primitive or its full history.

**T2. Prove one complete horizon estimate.** Combine selected energy, means, endpoints and moving-cutoff errors before taking a limit. For a Nyman–Beurling landing, the usual $\{1/(kx)\}$ coordinates use $dx$ on $(0,1)$, or $du/u^2$ after inversion. A tail estimate or a bounded sequence of norms alone does not prove approximation: the target limit and the bulk/origin contribution must also be identified.

**T3. Audit the feasibility of the actual absorption coefficient.** With $\Theta=\operatorname{riemannKernelReal}$, the available bound uses

$$
 r(a,M,R)=\frac{2M\cosh(R/2)}{\Theta(R)\sinh(a/2)},\qquad
 M\ge\sup_{u\in[a-R,a+R]}|\Theta'(u)|.
$$

To make this useful as an absorption with coefficient at most one, one needs $r(a,M,R)\le\theta\le1$. The theorem supplies a conditional inequality; it does not produce such parameters uniformly in $R$. Its admissibility condition also restricts $0<a<\tfrac12\log2$. The derivative bound concerns $\Theta$, not the amplitude of the chosen test, so rescaling the test does not make $M$ arbitrarily small.

For fixed admissible $a$ and a legitimate positive lower bound on $M$, decay of $\Theta(R)$ makes this crude ratio grow without bound. The next task is to quantify the feasible region and determine whether a sharper integrated estimate can replace the endpoint supremum. Until then, “uniform all-radius absorption” is an unpaid premise. A failure of this particular ratio would retire that sufficient bound, not the entire odd-sector route.

**T4. Study compensated coercivity, not a scalar positive-jump replacement.** Use the exact positive survivor in §2.3: crossing energy plus its original collar compensation. Investigate a nonlocal comparison, an enlarged state space, or a genuinely sharper arithmetic potential bound that retains the negative reflected measure. A positive scalar gauge cannot remove that singular component. Harnack-type positivity propagation, if available, would still need a quantitative global estimate to pay the mass subtraction.

**Progress criterion:** an actual source bound with every transferred cost included, or a sharp obstruction that identifies a different admissible coercivity mechanism. Another exact transfer with an unproved absorption premise does not close the gap.

## 6. Bézout–Valuation Incidence

### Current position

The strongest available receiver is the complete interior energy in §1.1. Its decomposition and the $\varepsilon=\tfrac12$ endpoint are established. Logarithmic self-cancellation of selected terms does not by itself bound the residual complete energy.

The actual Ramanujan/cofactor coordinate is, for positive indices and damping,

$$
 Y_\varepsilon(q)
 =\Re\sum_{m\ge1}\mu(qm)(qm)^{-1-\varepsilon}.
$$

It is not $\mu(q)q^{-\varepsilon}$. For prime $p$ and $p\nmid r$,

$$
 Y_\varepsilon(pr)
 =-\frac{Y_\varepsilon(r)}{p^{1+\varepsilon}-1}.
$$

The exponent, denominator and coprimality restriction are essential when estimating growing cofactor packets; see [`PMPowerDampedMobiusRamanujanWeights.lean`](../../../formal/GaloisForLFunctions/RHTower/PMPowerDampedMobiusRamanujanWeights.lean). Strong bounds uniform in a separate Ramanujan truncation must not be silently identified with source admission.

There is also a concrete classical bridge. In [`VaughanTypeIIShortAndAllHorizonMobiusL2Energy.lean`](../../../formal/GaloisForLFunctions/BezoutValuationIncidence/VaughanTypeIIShortAndAllHorizonMobiusL2Energy.lean), for $k\ge1$,

$$
 \operatorname{typeIIShort}_N(k)
 =\mathbf1_{k=1}-\operatorname{sieveSeq}_{N,\mu}(k).
$$

For positive $N,M$, the literal prefix square energy is exactly one plus the Type-II short-side coefficient energy. The module supplies an all-horizon unsigned bound

$$
 \sum_{k=1}^{M}\operatorname{sieveSeq}_{N,\mu}(k)^2
 \le M\,\operatorname{invSum}(M)^3,
$$

and a log-free linear-window bound

$$
 \sum_{m=1}^{L}|\operatorname{typeIIShort}_V(m)|^2
 \le B^2(L-V)_+,
 \qquad V,B\ge1,\quad L\le(B+1)V.
$$

The exact two-cutoff identity

$$
 \mu=\mu_U+\mu_V-\zeta*\mu_U*\mu_V
       +(\mu-\mu_U)*(1-\zeta*\mu_V)
$$

is formalized, together with its application to the trans-horizon quotient windows. Here $\zeta$ denotes the constant-one arithmetic function under Dirichlet convolution. Thus neither “there is no classical interface” nor “the program only has subhorizon identities” describes the current state. The interface still does not provide a signed saving for the complete damped energy.

Classical signed estimates also reach the native source. [`VinogradovKorobovCofinalMobiusDiscrepancy.lean`](../../../formal/GaloisForLFunctions/BezoutValuationIncidence/VinogradovKorobovCofinalMobiusDiscrepancy.lean) transfers the corpus's Vinogradov–Korobov Mertens bound to quotient windows and the literal source prefix, retaining the sum over the horizon-band parameter. It also transfers a short-interval mean-square theorem to the first trans-horizon octave, with its original parameter restrictions. These are substantive calibration transfers. They do not establish a bound for the complete damped pronic energy or a new critical power saving.

### Research next

**B1. Derive the exact weighted remainder from the receiver.** Start from $E_\varepsilon(T)$, expand the unresolved signed term, and map it into the existing Type-I/II dictionary. Retain all cofactor restrictions, logarithmic weights, moving endpoints and cross terms. The completed quotient-window decomposition is not yet a decomposition of every term in the pronic receiver. Do not assume in advance that everything reduces to one bilinear sum plus an $O_\varepsilon(1)$ remainder.

**B2. Obtain a source-specific signed estimate in one explicit range.** Apply established analytic estimates where their hypotheses actually fit. Record coefficient norms and all dependence on the cutoffs. Compare the result with the unsigned all-horizon baseline above. A first useful theorem could be a saving on a nontrivial block family or a calibrated estimate showing exactly which range remains beyond existing tools.

**B3. Test summability in the complete budget.** Insert the proposed saving back into the original weighted sum. Cofinal negativity, cancellation of a leading logarithm, or a favorable finite-band estimate is insufficient if the accumulated remainder still diverges. The closing target remains horizon-uniform boundedness at a cofinal sequence of positive dampings. A bound at one specified sub-half damping is an intermediate milestone with the zero-translation consequence already described.

**B4. Make any parity obstruction precise.** Specify which observations a proposed pair of models shares: diagonal Selberg data, finitely many correlations, or particular unsigned energies. Do not demand identical complete weighted Gram data and different values of the very quadratic form determined by those data. A useful obstruction identifies the missing signed observable and gives a replacement hypothesis. General claims that every BVI identity is inherently parity-blind go beyond the established results.

Use the classical calibration transfers as baselines and reusable input. Further progress should quantify the improvement they permit in the original energy budget; reproving the prime number theorem inside every program is unnecessary. A function-field comparison can test the mechanism, but is not a mandatory property of every valid approach to the classical zeta function.

**Progress criterion:** a new quantitative estimate for the literal signed remainder, with losses small enough to improve the actual receiver. More decompositions without such an estimate should have lower priority.

## 7. Is another research program justified?

**A narrow Square-Root Threshold program is justified as a study of detection and estimation costs. A broad new “Arithmetic Criticality Theory” is not yet justified as a separate program.** The former already has a concrete model theorem; the latter needs to confront the existing reflected-prime obstruction before claiming a new positive-ground-state mechanism.

### 7.1 Square-Root Threshold: separate universal obstructions from model-dependent costs

The useful question is:

> How much aperture, height localization and arithmetic information are required to detect an off-line configuration, and can the corresponding complete arithmetic form be estimated at that cost?

Two formal examples show why there is no single detection scale justified by the present evidence.

For the full reflected off-line lattice with spacing $2\pi/L$ and depth $0<\delta\le\tfrac12$,

$$
 W[f,f]\ge0\text{ for every }C^2\text{ test supported in }[-a,a]
 \quad\Longleftrightarrow\quad a\le L/2.
$$

The threshold is independent of depth. This is `offLineLattice_weil_positive_iff` in [`ZeroLatticeDepthNyquistLaw.lean`](../../../formal/GaloisForLFunctions/RHTower/ZeroLatticeDepthNyquistLaw.lean).

For a **doubled on-line lattice plus one reflected off-line pair** at height $\gamma_0$, the exact answer is different. For $0<a\le L/2$,

$$
 W[f,f]\ge0\text{ for every such test}
 \quad\Longleftrightarrow\quad
 \frac{\sinh(2\delta a)}{\delta}\le2L+2a.
$$

At $a=L/2$, this becomes $\sinh(\delta L)\le3\delta L$. For large $\delta L$, detection can occur at logarithmic-in-$L$ aperture rather than at $L/2$. The sharp equivalence and explicit logarithmic sufficient bounds are in [`IsolatedOffLinePairVisibilityLaw.lean`](../../../formal/GaloisForLFunctions/SquareRootThreshold/IsolatedOffLinePairVisibilityLaw.lean).

These are exact statements about specified `ZeroConfig` models, not claims that either configuration is the zero set of an Euler product with all zeta's arithmetic properties. The second model prevents extrapolating the dense-lattice threshold to every isolated off-line zero.

A related analytic scale comes from the classical mean-value estimate

$$
 \int_0^T\left|\sum_{n\le N}b_n n^{-it}\right|^2dt
 =T\sum_{n\le N}|b_n|^2+O\!\left(\sum_{n\le N}n|b_n|^2\right).
$$

The generic relative error is $O(N/T)$. For tests supported in $[-a,a]$, the autocorrelation can see prime powers up to $e^{2a}$; matching lattice spacing to the average zeta spacing suggests $L$ of order $\log T$. These comparisons explain interest in $a\approx\tfrac12\log T$, but do not prove a universal RH barrier or a pointwise positivity theorem. The mean-value statement follows from [Montgomery–Vaughan, *Hilbert's Inequality*, Corollary 3](https://personal.science.psu.edu/rcv4/personal/Publications/s2-8-1-73.pdf); its application to the complete arithmetic form remains a separate task.

### 7.2 Concrete next questions for this program

1. **Visibility beyond the two solved models.** Establish bounds for finite clusters and perturbed lattices with explicit dependence on depth, multiplicity, separation and local density. Distinguish a single pair from a coherently repeated off-line configuration. Preserve sharp positive survivors when proving a lower limit on resolution.
2. **Height-localized arithmetic formula.** For one chosen test family, retain the complete Gamma, prime and pole terms under modulation. State precisely which coefficients and prime lengths the localization creates. Determine whether a classical mean-value estimate supplies a useful margin for that family.
3. **From averaged estimates to useful positivity.** Prove a quantitative tail and exceptional-set theorem before claiming positivity in almost every height window. Zero-density bounds alone do not control arbitrarily shallow off-line zeros or the tails of a transform of a compactly supported test. Even an almost-everywhere result would leave the exceptional windows required for RH.
4. **Matched obstruction models.** List the exact arithmetic constraints imposed on a model and prove them. A configuration satisfying a density bound is not automatically a counterexample to all methods using the functional equation, Gamma factor, pole and Euler product together.

A useful output is an explicit tradeoff: which configurations a test detects, the arithmetic length it requires, and the strongest available estimate at that length. Another identity without that tradeoff would not justify expanding the program.

### 7.3 Where the criticality proposal belongs

Keep a bounded feasibility project inside THIM, coordinated with APT. Its first question is whether a nonlocal representation or quantitative comparison can exploit the **compensated** reflected-prime energy while retaining the original mass subtraction. Positive scalar reweighting of the folded jump measure is already obstructed. Standard ground-state representation theorems cannot be invoked before verifying their kernel, domain and positivity hypotheses.

If the project produces a new coercivity theorem that applies to the actual arithmetic form and has useful consequences short of RH, it may justify a separate program. Merely proving “positivity is equivalent to existence of an appropriate supersolution,” with positivity hidden in the hypotheses or the construction, would supply another receiver. The needed advance is a way to construct or estimate that object from arithmetic.

## 8. Consequences for the whole route portfolio

The [route ledger](../rh-current-frontier-map.md) remains the detailed inventory. The following obligations keep all 27 live routes and 18 candidates visible; grouping priorities around two proof projects does not discharge any of them.

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


## 9. Priorities and decision rules

The next cycle should aim for a small number of discriminating results, with infrastructure work tied to those results.

| Priority | Deliverable | What makes it consequential |
|---|---|---|
| BVI + THIM | One exact decomposition of the unresolved complete damped remainder, followed by a signed estimate in a stated parameter range. | The estimate improves the literal receiver after all weights and endpoints are restored. |
| APT + BiScale | A complete-form estimate for one expanding, demonstrably detecting test family. | Approximation error is controlled in the receiving norm and does not erase the positivity margin. |
| THIM | A feasibility boundary for the cosh/sinh absorption bound, and a precise compensated-coercivity replacement if needed. | It separates a useful source estimate from a conditional inequality with unattainable parameters. |
| Square-Root Threshold | A visibility law beyond the two solved models, coupled to the arithmetic estimation cost. | It identifies an achievable intermediate result or a sharp, explicitly scoped obstruction. |
| BiScale | A prime-anchor stability theorem or source-specific tightness theorem actually consumed by one of the above arguments. | It controls the required full energy with quantified losses. |
| BAG reserve | One centered-tail estimate under one explicit finite-head return conditioning. | It beats the naive unconditional estimate divided by the return density, or proves a sharp limitation with a useful survivor. |

Use three stopping rules:

1. **No arithmetic producer:** if a proposed theorem only transports the same unproved bound into another notation, defer it unless the new notation admits a specified estimate unavailable before.
2. **Wrong domain or quantifiers:** reject an argument whose anchor excludes the source, whose norm ignores prime edges, whose positivity includes known negative constant directions, or whose limits leave a required parameter uncontrolled.
3. **No useful survivor:** when an approach fails, extract its sharp boundary, classification or replacement hypothesis before retirement. Existing compensated crossing positivity, restricted inverse bounds and visibility laws are examples of substantive survivors.

The program needs fewer independent reformulations and more attempts to prove a complete arithmetic estimate in a deliberately chosen range. A successful intermediate theorem need not prove RH. It should improve a measurable quantity—energy growth, admissible damping, detection aperture, approximation loss or conditional tail size—and state exactly how that improvement can enter a proof route.

### Evidence and scope

This assessment uses the [frontier map](../rh-current-frontier-map.md), the [hard-obstacles report](../hard-obstacles-summary-1810.md), the four named program READMEs, the [Argon](argon.md), [Opus](opus.md) and [Fable](fable.md) reviews, and the Lean sources linked above. The reviews contribute proposals; the status claims are checked against theorem statements and their hypotheses. Corpus searches include partial and source-only indexed results, so search ranking or missing hits are not treated as proof of existence or absence.

The isolated-pair visibility module, Vaughan bridge and Vinogradov–Korobov calibration module cited here pass Lean in the current toolchain. The zero-translation/cofinal-admission results and reflected-prime obstruction/positive-survivor results have been checked to depend only on the standard axioms `propext`, `Classical.choice` and `Quot.sound`. This is targeted verification of the claims driving the assessment, not a fresh certification of the entire corpus. Research recommendations, proposed transfers and heuristic scale comparisons are distinguished from those established results throughout.
