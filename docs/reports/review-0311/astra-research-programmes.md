**Astra — three research programmes for new arithmetic tools toward RH**

The three proposed fields are **signed arithmetic quadrature**, **arithmetic excursion theory**, and **factorization transport geometry**. Their common problem is controlling a deterministic signed arithmetic source while preserving the relations between its parts. Their missing tools differ: compensation across a moving boundary; forced returns of a history-dependent quantity; and cancellation whose combinatorial complexity adapts to factorization.

The corpus already contains foundations for all three. Creating a field would mean supplying reusable construction and estimation theorems beyond those foundations. An RH-equivalent condition, a new name for an error term, or an abstract theorem assuming the desired estimate does not supply that field.

This develops the priorities in [the hostile route review](astra-routes-review.md). **Scope:** local corpus research; no web research or Lean execution. “Proved” means the cited Lean source contains the result, not a fresh compilation or transitive-axiom audit. New deductions below are labelled; proposed objects, laws and research questions are not claimed as formalized results. Field names are proposals, with no claim of worldwide novelty or that existing mathematics cannot eventually supply the tools.

| Programme | Question that defines the proposed field | Actual missing output |
|---|---|---|
| Signed arithmetic quadrature | Which arithmetic structure of the hyperbola bounds the long-modulus remainder, and with it the Möbius mean tail, below half damping? | A horizon-uniform pronic bound for the long-modulus remainder at one sub-half damping; equivalently, for the Möbius mean tail alone. |
| Arithmetic excursion theory | What prevents a signed arithmetic history from staying on the wrong side of a linear barrier throughout a power-length window? | One controlled sample in every sufficiently large power window, on one fixed side (equivalent to RH; with a loss \(M^c\), \(c<\tfrac12\), a fixed strip). |
| Factorization transport geometry | What complexity and displacement are necessary to move opposite arithmetic signs without losing cancellation in the residue? | A source-constructed transport or cluster decomposition whose signed residual has an independently proved estimate; a cost bound alone is equivalent to the Laplace receiver. |

**Strength calibration.** The first quantitative milestone of every programme is a fixed zero-free strip, that is, quasi-RH: Q1 at any \(a<\tfrac12\) (programme 1), the graded bound Hc at any \(c<\tfrac12\) (programme 2), and the Laplace bound \(O(x^{-b})\) at any \(b<1\) (programme 3, by the same Mellin argument as T). The unconditional state of all three is the Vinogradov–Korobov saving. Milestones short of a strip are structural: exact identities, classifications and sharp obstructions on explicit families.

These programmes respect exclusion B: no Weil-form positivity, positive spectral realization, or self-adjointness is proposed as the decisive mechanism. Scalar norms, finite weighted averages and nonnegative transport costs are ordinary estimates on the signed source. A construction that changes its decisive input to an RH-equivalent positive form would leave this scope. The receivers themselves are proved theorems with their own mechanisms: programme 1 lands through Mellin–Plancherel in \(L^2\) of the dilation group, programme 2 through a positive Green inverse (a Landau-type one-sided theorem), programme 3 through Mellin analyticity. Using a proved receiver is within scope; the open estimate must be a signed arithmetic bound. In particular a one-sided bound \(\sigma F(M)\le CM\) produced by writing \(CM-\sigma F(M)\) as a positive form would leave it.

**1. Signed arithmetic quadrature**

**Proved starting point.** For damping \(\varepsilon>0\), write

\[
A_\varepsilon(n)=\sum_{d\le n}\mu(d)d^{-\varepsilon}\lfloor n/d\rfloor
 -\frac{n}{\zeta(1+\varepsilon)},\qquad
E_T(\varepsilon)=\sum_{n=1}^{T}\frac{A_\varepsilon(n)^2}{n(n+1)}.
\]

Admission at \(\varepsilon\) means \(\sup_T E_T(\varepsilon)<\infty\). Half damping is admitted unconditionally. Admission at positive dampings accumulating at zero is equivalent to RH. The exact infimum of admitted dampings is \(\Theta-\tfrac12\), where \(\Theta\) is the supremum of the real parts of nontrivial zeros. For a single damping: \(\varepsilon>\Theta-\tfrac12\) is admitted, and admission at \(\varepsilon\) gives \(\Theta\le\tfrac12+\varepsilon\). Unconditionally, at every fixed \(0<a<\tfrac12\) and \(c\ge a\), \(E_T(a)-E_T(c)\le C\,T^{1-2a}e^{-\kappa\sigma(T)/270}\) eventually (the Vinogradov–Korobov saving), and along the band \(a\ge\tfrac12-\kappa\sigma(T)/(480\log T)\) the continuation budgets are bounded uniformly in T. Admission at a fixed \(a<\tfrac12\) asks to remove the factor \(T^{1-2a}\). [SignedAveragedContinuationAndTheZeroWidthBand.lean](../../../formal/GaloisForLFunctions/ArithmeticContinuationAndCriticalEnergy/SignedAveragedContinuationAndTheZeroWidthBand.lean).

At \(D_n=\lfloor\sqrt n\rfloor\), the source splits exactly as

\[
\begin{aligned}
A_\varepsilon(n)&=S_\varepsilon(n)+L_\varepsilon(n),\\
S_\varepsilon(n)&=\sum_{d\le D_n}\mu(d)d^{-\varepsilon}
                 (\lfloor n/d\rfloor-n/d),\\
L_\varepsilon(n)&=\sum_{D_n<d\le n}\mu(d)d^{-\varepsilon}
                 (\lfloor n/d\rfloor-n/d)
             -n\sum_{d>n}\frac{\mu(d)}{d^{1+\varepsilon}}.
\end{aligned}
\]

For \(0<\varepsilon<1\), the short part already satisfies

\[
\sup_T\sum_{n\le T}\frac{S_\varepsilon(n)^2}{n(n+1)}
\le\left(1+\frac1{1-\varepsilon}\right)^2\left(1+\frac1\varepsilon\right).
\]

Thus bounded pronic energy of L is exactly the remaining obligation; the equivalence follows from the triangle inequality and this bound. The harmonic tail past n is part of L. [LongModulusExactDecomposition.lean](../../../formal/GaloisForLFunctions/ArithmeticContinuationAndCriticalEnergy/LongModulusExactDecomposition.lean), [LongModulusShortEnergy.lean](../../../formal/GaloisForLFunctions/ArithmeticContinuationAndCriticalEnergy/LongModulusShortEnergy.lean).

There are two useful source descriptions. First, define the integrable step function

\[
f_{\varepsilon,n,D}(u)=
\begin{cases}
\displaystyle\sum_{D<d\le\lfloor n/u\rfloor}\mu(d)d^{-\varepsilon},&u>0,\\
0,&u\le0.
\end{cases}
\]

Then the long term is exactly its integer-sampling error:

\[
L_\varepsilon(n)=\sum_{j\ge1}f_{\varepsilon,n,D_n}(j)
                  -\int_{\mathbb R}f_{\varepsilon,n,D_n}(u)\,du.
\]

This includes the region near \(u=0\), which carries the infinite mean tail. [LongModulusQuadratureSampling.lean](../../../formal/GaloisForLFunctions/ArithmeticContinuationAndCriticalEnergy/LongModulusQuadratureSampling.lean).

Second, the centered prefix has increments

\[
A_\varepsilon(n)-A_\varepsilon(n-1)
 =c_\varepsilon(n)-\zeta(1+\varepsilon)^{-1},\qquad
c_\varepsilon(n)=\sum_{d\mid n}\mu(d)d^{-\varepsilon}
 =\prod_{p\mid n}(1-p^{-\varepsilon})\quad(n\ge1).
\]

The prefix identity is in [PMPowerDampedMobiusDiscreteEnergy.lean](../../../formal/GaloisForLFunctions/RHTower/PMPowerDampedMobiusDiscreteEnergy.lean); the product formula is used explicitly in [AllHorizonRadicalSawtoothAndDefectReduction.lean](../../../formal/GaloisForLFunctions/TransHorizonIncidenceMechanics/AllHorizonRadicalSawtoothAndDefectReduction.lean). The increment formula is an immediate deduction. The field must relate this multiplicative local structure to additive accumulation across integer horizons. Merely knowing \(0\le c_\varepsilon(n)\le1\) cannot supply that relation.

**The tail alone carries the threshold.** Write the tail as

\[
\tau_\varepsilon(n)=n\sum_{d>n}\frac{\mu(d)}{d^{1+\varepsilon}}.
\]

For \(\varepsilon>\Theta-\tfrac12\), partial summation from \(M(x)\ll x^{\beta}\) with \(\Theta<\beta<\tfrac12+\varepsilon\) gives \(\tau_\varepsilon(n)\ll n^{\beta-\varepsilon}\), \(\beta-\varepsilon<\tfrac12\), hence bounded pronic energy; the corpus records the square-root form \(N\bigl(\sum_{d>N}\mu(d)d^{-1-\varepsilon}\bigr)^2\le C\) on the same range. Conversely

\[
\int_1^\infty\tau_\varepsilon(x)x^{-s-1}\,dx=\frac{1/\zeta(s+\varepsilon)-1/\zeta(1+\varepsilon)}{1-s},
\]

which has a pole at \(\rho-\varepsilon\) for every zero \(\rho\); bounded pronic energy places this transform in the Hardy space of \(\Re s>\tfrac12\), so \(\Theta\le\tfrac12+\varepsilon\). **This two-sided threshold for the tail is a deduction here, not a formalized theorem.** Consequently, at every damping off \(\Theta-\tfrac12\), the long-modulus remainder L, the tail \(\tau_\varepsilon\) and the long sawtooth are bounded together, or L and the tail are unbounded together. For the literal source no compensation between sawtooth and tail is needed or available at the level of admission: the decisive estimate is a weighted mean-square bound for the Möbius tail. [PrefixStabilityAndCriticalWienerClosureOfMoebiusRows.lean](../../../formal/GaloisForLFunctions/TransHorizonIncidenceMechanics/PrefixStabilityAndCriticalWienerClosureOfMoebiusRows.lean).

**Point of view.** Treat the hyperbola \(du=n\), its integer sampling and its mean tail as one arithmetic object, as a method for bounding the tail. Changing n moves every quotient boundary; changing damping inserts logarithmic weights. The hyperbola representation earns its place only if its quotient structure bounds the tail through information that partial summation from \(M(x)\) does not see; above the threshold every piece is bounded, below it the remainder and the tail diverge together.

The research is therefore a calculus of **arithmetic cells** for the tail. A cell records a quotient range, its literal Möbius coefficients, its cofactor relations, and the boundary contribution required when it is merged or split. The new theorem must estimate the cell sums for the actual coefficients.

| Objects and language | Required meaning |
|---|---|
| Hyperbola cell | Integers d sharing a specified value or range of \(\lfloor n/d\rfloor\), with weights retained. |
| Compensated cell | A signed cell sum together with its assigned mean contribution; neither may be silently discarded. |
| Boundary transfer | The exact signed change when n, D or damping changes. |
| Pronic size | \(\|v\|_T^2=\sum_{n\le T}v(n)^2/[n(n+1)]\); the norm the existing receiver consumes. |
| Damping work | \(W_T=\sum_{n\le T}A_\varepsilon(n)\partial_\varepsilon A_\varepsilon(n)/[n(n+1)]\), with \(E'_T=2W_T\). |
| Arithmetic selectivity | An estimate uses information distinguishing the literal source from coefficient majorants and other sources with different admission behaviour. |

**Foundational principles.** These are requirements on the proposed theory, not extra axioms to assume.

1. **Conservation under decomposition.** Every rearrangement retains the full mean tail and every cutoff boundary. Establish finite identities first and justify the infinite tails separately.
2. **Joint estimation where it matters.** For the literal source, boundedness of the tail alone is equivalent to admission off the threshold (deduction above), so splitting L into sawtooth and tail costs nothing at that level. Joint estimation is essential for other decompositions, for modified sources and for the oscillating probes, whose tails never cancel.
3. **Uniformity in the observation horizon.** Constants may depend arbitrarily badly on a fixed positive damping or compact damping interval. They may not grow with T.
4. **Source sensitivity.** Floor identities that hold for every coefficient sequence are useful algebra, but the decisive estimate must use additional arithmetic structure.
5. **Direction matters.** Continuing toward smaller damping can increase energy. A forward dissipation statement does not automatically control the backward problem.

**Open mathematical questions.**

**Q1 — What arithmetic law bounds the long-modulus remainder below half damping?** The first decisive numerical target is

\[
\exists a\in(0,\tfrac12)\ \exists C_a<\infty\ \forall T,
\qquad\sum_{n\le T}\frac{L_a(n)^2}{n(n+1)}\le C_a.
\tag{Q1}
\]

This gives \(\Theta\le\tfrac12+a<1\), and conversely \(\Theta<\tfrac12+a\) gives (Q1): Q1 for some \(a<\tfrac12\) is equivalent to quasi-RH \(\Theta<1\). Off the threshold, Q1 at a is equivalent to the same bound for the tail \(\tau_a\) alone. It is a breakthrough target, not a small preliminary lemma. The tool-building problem before it is to discover a source identity or correlation estimate that makes this bound accessible.

A concrete investigation is to partition moduli by quotient and coprime cofactor, then retain the mixed products in the squared quadrature. Which mixed terms can be expressed exactly through the tail, and which remaining terms have a summable estimate? A proposed decomposition should identify a strict subproblem whose estimate is not merely Q1, or the tail bound, written again.

**Q2 — Can the source control accumulated backward work without controlling the tangent norm?** The existing continuation variable is

\[
r_T(\varepsilon)=-\frac{2W_T(\varepsilon)}{1+E_T(\varepsilon)}
                 =-\partial_\varepsilon\log(1+E_T(\varepsilon)).
\]

For an admitted c, a horizon-uniform upper bound on \(\int_a^c r_T\) transports admission to a. But

\[
\int_a^c r_T=\log\frac{1+E_T(a)}{1+E_T(c)},
\]

so the integrated bound is already equivalent to admission at a. A new field must derive it from cell-level arithmetic. Introducing a “budget” equal to this logarithm is circular. Pointwise bounds on \(r_T\) and tangent-norm bounds are stronger than necessary. [TheDampingContinuationCriterion.lean](../../../formal/GaloisForLFunctions/ArithmeticContinuationAndCriticalEnergy/TheDampingContinuationCriterion.lean), [TheAveragedBudgetIsExactlyAdmission.lean](../../../formal/GaloisForLFunctions/ArithmeticContinuationAndCriticalEnergy/TheAveragedBudgetIsExactlyAdmission.lean).

The specific question is whether finite cell transfers produce independently estimable boundary terms and a summable accumulated defect after integration in damping. If they do not, classify which transfers generate an unavoidable horizon loss.

**Q3 — Which information is sufficient, and which summaries destroy it?** Compare the exact source with its absolute majorant, radical-based summaries, oscillating coefficient probes, the parity twin and sparse prime flips.

- *Oscillating probes* \(c_{\varepsilon,t}(d)=d^{-\varepsilon}\cos(t\log d)\) are a different source. Their tail drift has unbounded pronic norm for every \(0<\varepsilon\le\tfrac12\) and every t, unconditionally; a probe is admitted iff \(\zeta(1-\varepsilon+it)=0\), so an admitted probe exists only if RH fails, and then its sawtooth is unbounded too. They calibrate sources whose tail has no cancellation, not the Möbius source, whose tail is bounded exactly above the threshold. [OscillatingProbeSourceEstimatesEnergyGapAndCollarLimitations.lean](../../../formal/GaloisForLFunctions/TransHorizonIncidenceMechanics/OscillatingProbeSourceEstimatesEnergyGapAndCollarLimitations.lean).
- *The parity twin* is a nonnegative squarefree weight whose Ramanujan amplitudes \(|W(e)|\) equal those of the damped Möbius weight at every modulus, while its weighted pronic energy grows at least like \(c\log T\) at every damping of the Vinogradov–Korobov band. An estimate that sees the Ramanujan coordinates only through their absolute values cannot prove Q1. [ParityTwinOfTheDampedMoebiusWeight.lean](../../../formal/GaloisForLFunctions/TransHorizonIncidenceMechanics/ParityTwinOfTheDampedMoebiusWeight.lean), [SignedAveragedContinuationAndTheZeroWidthBand.lean](../../../formal/GaloisForLFunctions/ArithmeticContinuationAndCriticalEnergy/SignedAveragedContinuationAndTheZeroWidthBand.lean).
- *Sparse prime flips* (§5) are invisible to the receiver at damping a when \(\sum_{p\in S}p^{-1/2-a}<\infty\) (proved for unimodular completely multiplicative signs) and destroy admission at a when the flipped set has counting exponent above \(\tfrac12+a\). An estimate at damping a must read \(\mu(p)=-1\) on every prime set of counting exponent above \(\tfrac12+a\). [SparsePrimeFlipsPreserveTheReceiver.lean](../../../formal/GaloisForLFunctions/TransHorizonIncidenceMechanics/SparsePrimeFlipsPreserveTheReceiver.lean).

The desired classification says which finite incidence data preserve the compensation estimate and which do not. Any failure should expose the missing correlation, not just declare “more cancellation needed.”

**Q4 — Can a local arithmetic estimate propagate through damping?** After obtaining one sub-half damping, determine whether its proof is stable under inserting \(\log d\), as differentiation requires. A bound at one damping does not imply a continuation law. Seek a source-controlled interval of extension, allowing its constants to deteriorate toward zero. A sequence of admitted dampings tending to zero suffices; a uniform bound all the way to zero is unnecessary.

**Research programme and milestones.**

| Stage | Research topic and concrete deliverable | What would count as progress |
|---|---|---|
| A1 | Exact quotient-cell decomposition of the tail, including arbitrary cutoffs | A decomposition exposing an arithmetic correlation genuinely smaller than the tail; the long/short identity and the tail threshold alone are already owned. |
| A2 | Classification of boundary errors under cell merger and damping differentiation | A proved error estimate or sharp obstruction on an explicit arithmetic family, beyond a generic norm inequality. |
| A3 | Sub-half quadrature at one explicit a | Q1 with a constant independent of T, hence a fixed zero-free strip (quasi-RH). |
| A4 | Source-derived continuation between admitted dampings | An extension law with its horizon dependence eliminated by proved arithmetic estimates. |
| A5 | Admission cofinal at zero | RH through the existing receiver; no additional spectral construction needed. |

**What would make this a field beyond the RH application?** A classification of compensated quadrature for arithmetic rows with convergent harmonic means; explicit laws for its change under dilation, convolution and prime-factor modification; and a theory identifying which integer-boundary defects obstruct those laws. Such results would explain when multiplicative structure controls additive sampling error, including cases where cancellation fails. The existing abstract continuation calculus supplies the final propagation step; these arithmetic transformation laws are the proposed new content.

**Try to kill the programme early.** Apply any candidate estimate to the unsigned source; if the proof never used signs, it faces the corpus's half-damping barrier. Check moving cutoffs rather than fixed n. Check the order of limits: finite-horizon energy has a controlled limit at zero damping, yet the corpus permits an unbounded interior bump escaping to large T if RH fails. Reject a “continuation proof” that only controls endpoints. Run the estimate on the parity twin and on a sparse prime flip of counting exponent above \(\tfrac12+a\): it must fail on both. The surviving result from a failed cell estimate should be a sharp loss, an exact uncancelled boundary term, or a classification of coefficients for which compensation does hold. [ACCE's obstruction inventory](../../../formal/GaloisForLFunctions/ArithmeticContinuationAndCriticalEnergy/README.md).

**2. Arithmetic excursion theory**

**Proved starting point.** Let

\[
\begin{aligned}
D(N)&=\sum_{m\le N}\log m-\sum_{d\le N}\lfloor N/d\rfloor+2\gamma N,\\
F(M)&=\sum_{1\le k<M}(\sqrt{k+1}-\sqrt k)
                  \sum_{d\le k}\mu(d)D(\lfloor k/d\rfloor).
\end{aligned}
\]

The corpus proves \(|D(N)|\le24\sqrt N\), but Möbius inversion restores the full Chebyshev error:

\[
F(M)=\sum_{1\le k<M}(\sqrt{k+1}-\sqrt k)(\psi(k)-k+2\gamma).
\]

Thus a bound for D alone is already available; the missing estimate concerns its **signed inversion and accumulated readout**. [CCMFUSuzukiMobiusDivisorAbelProducer.lean](../../../formal/GaloisForLFunctions/RHTower/CCM/CCMFUSuzukiMobiusDivisorAbelProducer.lean).

For either fixed choice \(\sigma\in\{1,-1\}\), the following is an RH criterion:

\[
\exists\delta>0,\ C\in\mathbb R,\ N_0\quad
\forall N\ge N_0\quad
\exists M\ge2:\quad
N-N^{1-\delta}\le M\le N,\qquad \sigma F(M)\le CM.
\tag{H}
\]

One may restrict to \(0<\delta<1\) by widening windows. Upper and lower versions are separate criteria. There is no requirement to control both sides or every M. For every fixed integer \(m\ge1\), a uniform one-sided bound along all \(M=j^m\) also suffices. Arbitrarily many isolated good samples, with no gap bound, are not the stated criterion. [MobiusDivisorOneSidedPowerGapBootstrap.lean](../../../formal/GaloisForLFunctions/RHTower/MobiusDivisorOneSidedPowerGapBootstrap.lean), [MobiusDivisorLowerStripPowerGapBootstrap.lean](../../../formal/GaloisForLFunctions/RHTower/MobiusDivisorLowerStripPowerGapBootstrap.lean).

There is a graded version already in Lean: on any set with backward gaps \(O(N^{1-\delta})\),

\[
\sigma F(M)/M\le C(1+M^c),\quad C\ge0
\quad\Longrightarrow\quad
|\Re\rho-\tfrac12|\le\max(0,c).
\tag{Hc}
\]

The exponent scale runs from \(c=\tfrac12\), which holds unconditionally by Chebyshev's bound \(|\psi(k)-k|\le k\), through every \(c<\tfrac12\), a fixed zero-free strip (quasi-RH), to \(c\le0\), which is RH. The exponent is the meaningful progress measure; the sampling exponent need only remain positive.

**Point of view.** Study the duration and shape of arithmetic excursions. An upper excursion is a run of integers on which \(F(M)>CM\); a lower excursion uses \(-F\). The missing theorem would prevent every sufficiently large power window from being entirely occupied by one chosen kind of excursion.

This is deterministic, history-dependent mathematics. A random model, an average over multiplicative characters, or a density-one theorem does not control the duration of an exceptional excursion in the actual sequence.

**The excursion scale is multiplicative.** Integrating the explicit formula against \(t^{-1/2}\) gives

\[
\frac{F(M)}{M}=-\sum_\rho\frac{M^{\rho-1/2}}{2\rho(\rho+\frac12)}+O(M^{-1/2}),
\]

an absolutely convergent sum; under RH it is a bounded almost-periodic function of \(\log M\). The term of a zero \(\rho_0=\beta_0+i\gamma_0\) has size \(M^{\beta_0-1/2}\) and changes phase on the scale \(\Delta\log M\asymp1/\gamma_0\), while a power window has \(\Delta\log M\le N^{-\delta}\). An excursion driven by an off-line zero therefore occupies whole power windows, and the power-gap bootstrap converts one good sample per window into a bound at every M. **This is a deduction here.** Excursion duration is set by the zero ordinates, not by a sub-power arithmetic clock: the programme must show that excursions above \(CM\) do not occur, and the excursion language reads the one-sided bound rather than weakening it.

The corpus supplies a more informative state than F alone. With its literal completed-source history, write

\[
H_M(j)=P(j)-(j+1)B(M)+D_*(M),\qquad
\mathcal H(M)=\sum_{j<M-3}\frac{H_M(j)}{\sqrt{j+1}}.
\]

Here P is `completedSourceObserverJetPrefixPotential`, B is `completedSourceObserverJetMass`, and \(D_*\) is `completedSourceObserverJetDrift`; \(D_*\) differs from the divisor defect D above. The exact two-point version is

\[
H_M(j)=D_*(M)-D_*(j+2)
 -(j+1)\bigl(B(M)-B(j+2)\bigr).
\]

Moreover,

\[
F(M)-\tfrac38\mathcal H(M)=o(M).
\]

All three statements are in [ObserverJetSignedCurvatureAndPrefixTelescoping.lean](../../../formal/GaloisForLFunctions/RHTower/ObserverJetSignedCurvatureAndPrefixTelescoping.lean). The last error is harmless for an eventual linear one-sided bound, after enlarging C.

An immediate algebraic deduction exposes the joint state:

\[
\mathcal H(M)=Q(M)-B(M)V(M)+D_*(M)U(M),
\]

where \(Q=\sum P(j)/\sqrt{j+1}\), \(V=\sum\sqrt{j+1}\), and \(U=\sum1/\sqrt{j+1}\), over the same range. The field should control this **coupled combination**. Bounding its three contributions separately can be much stronger and can erase the intended cancellation.

| Objects and language | Required meaning |
|---|---|
| Arithmetic memory state | The actual prefix, mass and drift fields, with their exact finite update identities. |
| Signed history | The full sum \(\mathcal H\); replacing summands by positive parts defines a different, stronger target. |
| Barrier and excursion | A level \(\sigma F(M)\le CM\), and a contiguous interval failing it. |
| Return set | \(G_{C,\sigma}=\{M\ge2:\sigma F(M)/M\le C\}\), equipped with a quantitative backward-gap bound. |
| Selection rule | An arithmetic construction producing a good M in each window, with a proof of its estimate. |
| Selection obstruction | A finite identity or certificate explaining why a proposed class of rules cannot control a window. |

**Foundational principles.** Preserve the sign inside the history sum. Treat mass and drift jointly. Distinguish a fixed polynomial sampling schedule from an adaptive choice inside each window. Make every claimed return quantitative. Allow the harmless \(o(M)\) change of readout already proved, but establish an explicit transfer for any other change of state.

**Open mathematical questions.**

**Q1 — What finite arithmetic event forces an excursion to end?** The receiver already proves that H suffices. The new content must explain why a long run above the barrier is incompatible with an independently controlled feature of the prime-free divisor source or its exact history.

The first investigation should retain the exact increment

\[
F(M+1)-F(M)=(\sqrt{M+1}-\sqrt M)(\psi(M)-M+2\gamma)
\]

and express it through the divisor source and the joint history state. Can a persistent excursion force a definite cost in a finite cofactor or boundary quantity whose total is bounded for arithmetic reasons? The cost cannot be defined to be the excursion itself. A negative derivative at scattered points is also insufficient: its accumulated effect must overcome the starting height.

**Q2 — Can one construct a local averaging rule that certifies a return?** For the integer window \(I_N=[N-N^{1-\delta},N]\cap\{2,3,\ldots\}\), a sufficient construction would give

\[
w_N(M)\ge0,\qquad\sum_{M\in I_N}w_N(M)=1,\qquad
\sum_{M\in I_N}w_N(M)\frac{\sigma F(M)}M\le C.
\tag{S}
\]

The passage from S to a good sample is elementary. The research question is whether quotient geometry or the joint mass–drift identity supplies such weights and a source estimate. Choosing a minimizer of F and declaring its value bounded is H again. Signed averaging weights do not imply a good sample without an additional argument controlling their negative part.

A useful intermediate result would classify which moment constraints on a proposed local averaging rule are feasible, and identify the arithmetic obstruction when they are not. It would explain what state information a selector must retain.

**Q3 — Can the prefix and terminal layers cancel in a useful joint law?** The corpus bounds the prefix contribution from P and B at the scale \(J^{3/2}\), so choosing \(J\le M^{2/3}\) pays those terms at linear scale. The drift contribution remains. Unit-step telescoping gives precise terminal identities. The open task is to combine these facts into a signed estimate at selected apertures, without requiring independent control of every terminal value of \(\psi-n\).

There is a concrete false shortcut here. The positive cubic two-zone criterion `riemannHypothesis_of_twoZone_cubic_positive` assumes

\[
\psi(m+1)-(m+1)\le K N
\quad\text{for }N^2+2\le m<N^3,
\]

for every large N; its negative counterpart `riemannHypothesis_of_twoZone_cubic_negative` bounds \(-[\psi(m)-m]\le KN\) on the same m-interval. Choosing \(N=\lfloor n^{1/3}\rfloor+1\) puts n, and n−1, inside that interval for all sufficiently large n. Either assumption would therefore give a global one-sided \(O(n^{1/3})\) bound for \(\psi(n)-n\). Both contradict the corpus's unconditional \(\Omega_\pm(\sqrt x)\) oscillation theorem. Passing from real x to integer n changes the error by at most one. **This incompatibility is a deduction here, not a formalized no-go.** Both criteria are valid implications with unsatisfiable hypotheses; they are not research targets. [ObserverJetSignedCurvatureAndPrefixTelescoping.lean](../../../formal/GaloisForLFunctions/RHTower/ObserverJetSignedCurvatureAndPrefixTelescoping.lean), [ChebyshevSchmidtOmega.lean](../../../formal/GaloisForLFunctions/RHTower/ChebyshevSchmidtOmega.lean).

The positive survivor is sharper: large pointwise oscillations must remain allowed; the sought law controls their **signed accumulation and excursion duration**. This is a reason to develop the new field, not to strengthen pointwise estimates further.

**Q4 — What is the minimum arithmetic memory needed for a selector?** Determine whether a finite collection of prefix statistics can force S, or whether cofactor histories across growing scales are indispensable. The corpus has exact prime-merger identities where late primes improve or worsen a merger according to a retained singleton's sign. It also has complete quotient-window orders whose three endpoint energies need bounds. These are examples of available arithmetic update information, not an established selector for F. [MobiusDivisorNonemptyEnergy.lean](../../../formal/GaloisForLFunctions/RHTower/MobiusDivisorNonemptyEnergy.lean), [MobiusDivisorQuotientWindowOrder.lean](../../../formal/GaloisForLFunctions/RHTower/MobiusDivisorQuotientWindowOrder.lean).

Before importing those orders, prove an exact map from their retained fields to the F/history quantity and bound the endpoint terms. Changing the prime-processing order does not change the final arithmetic source by itself.

**Research programme and milestones.**

| Stage | Research topic and concrete deliverable | What would count as progress |
|---|---|---|
| B1 | Joint mass–drift updates across an aperture window | An exact finite excursion identity that retains the cancellation lost by positive-history bounds. |
| B2 | Arithmetic selection and obstruction duality | A constructed family of window rules with proved estimates on a nontrivial source class, or a sharp classification of what defeats them. |
| B3 | Graded sparse bound | Hc for an explicit \(c<1/2\), with fixed \(\delta>0\), hence an actual zero-free strip (quasi-RH). |
| B4 | Remove the power loss | A linear one-sided sampled bound, or a family of proved graded bounds with \(c\downarrow0\); the existing receivers then give RH. |

**What would make this a field beyond the RH application?** Quantitative return theorems for deterministic arithmetic histories, with explicit bounds on excursion duration and on the memory required to predict or certify a return. Its general results would distinguish source classes by their exact update laws. Density, recurrence and cancellation would have separate quantitative meanings, and examples with long exceptional excursions would be part of the classification. The elementary averaging step in S is already available; the proposed new content is the arithmetic construction that makes S true.

**Try to kill the programme early.** Test a selector against the proved positive and negative Chebyshev excursions. Test its largest uncovered interval, not just the density of samples. Check whether it controls the original history or its positive part. Inspect every “bounded drift” premise for an RH-strength or impossible pointwise condition. Run the selector on the history built from a sparse prime flip of counting exponent \(\sigma_0>\tfrac12\) (§5): its Dirichlet series has a real singularity at \(\sigma_0\), so at least one of its two one-sided bounds fails, while the divisor source D is unchanged. If a finite-state selector fails, retain the pair of indistinguishable states or the missing cofactor statistic as a lower bound on the memory a successful theory needs.

**3. Factorization transport geometry**

**Proved starting point.** The arithmetic object is the signed measure

\[
\nu_N=\sum_{n\le N}\mu(n)\delta_n,
\]

or its exponentially weighted version. Pairing a positive atom u with a negative atom v costs at most

\[
|e^{-xu}-e^{-xv}|
\le x|u-v|e^{-x\min(u,v)},\qquad x\ge0.
\]

The corpus already proves this cost, Hall selection consumers, sign-reversing prime replacements, and fractional-transport identities. It also proves that unrestricted fractional transport merely attains the original signed imbalance. Existence of a transport is therefore not the cancellation theorem. [MobiusBoundaryOppositeSignTransport.lean](../../../formal/GaloisForLFunctions/RHTower/MobiusBoundaryOppositeSignTransport.lean).

The relevant RH receiver is

\[
\forall\eta>0,\qquad
\left|\sum_{n\ge1}\mu(n)e^{-nx}\right|
=O_\eta(x^{-1/2-\eta})\quad(x\downarrow0).
\tag{T}
\]

This is already equivalent to RH. Exact half-power decay without the arbitrarily small loss is a stronger target and is unnecessary. [MobiusMertensLittlewoodConsequences.lean](../../../formal/GaloisForLFunctions/RHTower/MobiusMertensLittlewoodConsequences.lean).

**The obstruction is structural.** A common-spectator replacement has

\[
n=u a,\qquad m=v a,\qquad u\ne v.
\]

If u uses at most k source primes, each at most y, then

\[
n\le y^k|n-m|.
\tag{R}
\]

The corpus amplifies R into a mass obstruction: for every fixed k, products of \(12(k+1)\) distinct primes in \((Y,2Y]\), at boundary \(N=(2Y)^{12(k+1)}\), are isolated from such replacements of displacement at most \(N^{2/3}\). Their Gibbs mass exceeds every constant multiple of \(N^{2/3}\). Thus every fixed-arity, spectator-preserving local scheme paying unmatched mass absolutely is ruled out, including its half-power-local versions. [MobiusBoundaryFixedArityLocalHallMassNoGo.lean](../../../formal/GaloisForLFunctions/RHTower/MobiusBoundaryFixedArityLocalHallMassNoGo.lean). The opposite-sign transport module proves the friable form for the \(\{1\leftrightarrow2,1\leftrightarrow4\}\) replacement graph: a y-friable endpoint \(n>y^4H\) has no neighbour within displacement H, so every uniformly sublinear H leaves a macroscopic isolated set. [MobiusBoundaryOppositeSignTransport.lean](../../../formal/GaloisForLFunctions/RHTower/MobiusBoundaryOppositeSignTransport.lean).

There are two further constraints. First, row normalization does not create cancellation: signed normalizer flux can equal twice the original imbalance. The weighted inverse-load flux is exactly the current minus its isolated and displacement terms. [RouteESignedNormalizerFluxCircularity.lean](../../../formal/GaloisForLFunctions/RHTower/RouteESignedNormalizerFluxCircularity.lean), [RouteESignedInverseLoadFlux.lean](../../../formal/GaloisForLFunctions/RHTower/RouteESignedInverseLoadFlux.lean).

Second, the corpus rules out a different attempted escape through bounded-density binary singleton histories: vanishing curvature defect and exact scalar cancellation force component density to diverge. It extracts the finite lower bound

\[
C\ge-\frac{M-2}{2}\log D
\]

when the singleton bias must fit defect D. This is a theorem about that specific history model, not every multi-atom construction. [RouteEComponentHistorySparseDensityNoGo.lean](../../../formal/GaloisForLFunctions/RHTower/RouteEComponentHistorySparseDensityNoGo.lean).

**Point of view.** Arithmetic transport has two geometries: distance between integer values and distance between their prime-factor descriptions. A small change in factorization need not give a small change in integer value. A useful theory must quantify both, and track the signed residue instead of requiring every unmatched atom to be negligible in absolute mass.

A natural proposed invariant is **replacement depth at radius H**. For squarefree n and \(H\ge1\), define

\[
\tau_H(n)=\min\left\{|S|:\ S\subseteq\operatorname{PrimeFactors}(n),
                         \ \prod_{p\in S}p\ge n/H\right\}.
\]

The full prime set makes the minimum well-defined. Any nontrivial spectator-preserving replacement within distance H must replace at least \(\tau_H(n)\) source primes: its spectator is an integer step size, so \(|m-n|\ge a=n/u\). **This is an elementary deduction and a proposed organizing invariant, not a claimed new Lean result.**

For n composed of r comparably sized primes and \(H\approx\sqrt n\), this requires replacing approximately half the factors. Therefore “let arity grow slowly” is not an answer. Arity must adapt to the actual factor profile and the available displacement budget. This is the positive geometric content extracted from the local no-go.

| Objects and language | Required meaning |
|---|---|
| Factor profile | Actual prime factors, their sizes, parity, and common cofactors; not just \(\mu(n)\). |
| Replacement depth | \(\tau_H(n)\), or a refined profile recording which factor subsets permit the desired radius. |
| Arithmetic transport | An explicit conservative assignment between actual opposite-sign atoms, with capacities and multiplicities. |
| Signed residue | The remaining signed measure, retained as an object with arithmetic structure. |
| Physical cost | The change in the actual receiver's test function, not merely the number of graph edges. |
| Cancellation cluster | A finite signed collection of actual atoms whose combined readout is estimated before absolute values. |
| Complexity–cost frontier | Feasible tradeoffs among replacement depth, displacement, congestion, residual size and cancellation order. |

**Foundational principles.** Conserve every coefficient. Pay repeated use of a target through an explicit capacity constraint. Distinguish abundance of both signs from Hall expansion for every source family. Record physical displacement through every composed move. Permit signed cancellation in the residue, but require an independent source estimate for it. A graph identity that merely reconstructs the starting sum is bookkeeping.

**Open mathematical questions.**

**Q1 — What is the sharp tradeoff between replacement depth and cheap opposite-sign access?** R and \(\tau_H\) give necessary conditions. Which are sufficient on explicit factor-profile classes? Can one produce opposite-sign target reservoirs with enough capacity after replacing a substantial fraction of factors? How much congestion is forced when many source vertices share those reservoirs?

The corpus already proves abundant capacity of both signs in appropriate near-square-root windows, including capacity to receive prime sources. That does not solve the composite-family Hall problem. [RouteEMarkerHallLawAll.lean](../../../formal/GaloisForLFunctions/RHTower/Sieve/RouteEMarkerHallLawAll.lean). The next theorem should treat a named composite factor-profile class with an explicit admissible graph and all-family expansion or a sharp obstruction.

**Q2 — Can nonlocal moves be rare enough, or cancel strongly enough, to remain affordable?** At \(x=1/N\), on values comparable to N, one macroscopic displacement costs order one under the existing absolute edge estimate. Approximately N such moves cannot produce a half-power bound. A successful nonlocal scheme must reduce their number, their aggregate weighted cost, or the loss from taking absolute values separately.

For ordinary pair transport, a sufficient target is an exact decomposition

\[
\sum_{n\ge1}\mu(n)e^{-nx}
 =\sum_{(u,v)\in\mathcal P_x}(e^{-xu}-e^{-xv})+r(x)
\]

with, for every \(\eta>0\),

\[
\sum_{(u,v)\in\mathcal P_x}x|u-v|e^{-x\min(u,v)}+|r(x)|
 \le C_\eta x^{-1/2-\eta}.
\tag{C}
\]

The decomposition must include multiplicities, unmatched atoms and the truncation tail. The tail is not intrinsically difficult: truncating at \(R(x)=\lceil2x^{-1}\log(1/x)\rceil\) for small x makes its absolute exponential sum \(O(x)\). This is an elementary geometric-series deduction. The difficult part is the actual arithmetic transport inside the truncation.

C is equivalent to T. The triangle inequality and the edge cost give T from C; conversely T gives C with \(\mathcal P_x=\varnothing\) and \(r=\sum\mu(n)e^{-nx}\). A transport has content only through how its residual is estimated.

**Matching cost is never the bottleneck.** For any pairing whatever, arithmetic or not, with displacements at most h, the cost is at most \(xh\sum_{(u,v)}e^{-x\min(u,v)}\le h\,x/(1-e^{-x})\approx h\), which is inside the budget for \(h\le x^{-1/2-\eta}\). The difficulty sits entirely in the signed residual: with value-local pairs it is the sum of window imbalances \(\sum_{n\in I}\mu(n)\), whose absolute total the square-root model puts near \(N/\sqrt h\gg N^{1/2+\eta}\) (a heuristic, not a theorem). The residual must be estimated with its signs for every transport; the fixed-arity and friable obstructions say that arithmetic move sets do not even make it sparse. **These are deductions here.** A cluster method has content exactly when it gives the residual an arithmetic structure with an independent estimate.

**Q3 — Can a signed residual be simplified without losing its arithmetic law?** Suppose a first transport leaves residue \(\sigma_1\). Can it be decomposed again so that the number or complexity of unresolved factor profiles decreases, while all displacement and normalization errors remain controlled? An invariant must demonstrate this progress. Repeatedly naming the unresolved current “inverse-load flux” fails the exact circularity tests already in Lean.

This is the core question for a multiscale theory: does the residue acquire simpler arithmetic structure, or merely fewer labels for the same hard sum? A useful theorem would classify residues of a particular source-derived transport and prove a quantitative simplification law, even before achieving RH strength.

**Q4 — Do actual prime-product atoms admit useful higher-order cancellation clusters?** Pairing uses cancellation of total mass. A proposed extension groups actual signed atoms into clusters with vanishing moments

\[
\sum_i a_i(n_i-c)^j=0\qquad(0\le j<r),
\]

and uses the Taylor remainder of \(e^{-xn}\) to reduce the cluster's physical cost. The analytic Taylor estimate is standard; the missing mathematics is constructing enough such clusters from the actual arithmetic source, with controlled multiplicities, diameters and leftover signed mass.

Exact high-order moments may be too rigid. An alternative is to retain and estimate every lower-moment defect. These are competing research branches, not established constructions. A cluster proposal must be tested against the fixed-arity obstruction and, if it uses singleton histories, the component-density obstruction. Increasing the number of formal labels alone does not evade either theorem.

**Research programme and milestones.**

| Stage | Research topic and concrete deliverable | What would count as progress |
|---|---|---|
| C1 | Factor-profile complexity | Sharp lower and upper bounds for cheap opposite-sign access, beginning with the families that kill fixed arity. |
| C2 | Composite capacity and congestion | An actual adaptive graph with proved family expansion and cost bounds, or a stronger impossibility theorem with an explicit survivor. |
| C3 | Residue classification | A source-derived transformation whose residual has a proved simpler structure; include every normalization term. |
| C4 | Pair or cluster cancellation estimate | A quantitative improvement with a proved receiver consequence, not just a finite matching or abundant local signs. |
| C5 | Bounds at every strict half exponent | T, through a residual estimate produced by C3–C4; RH through the existing Laplace receiver. |

**What would make this a field beyond the RH application?** A geometry of factorization changes with sharp laws relating arithmetic complexity, integer displacement and congestion. Its theorems would classify which signed multiplicative measures admit low-cost decompositions for specified families of test functions. Replacement-depth lower bounds and constructive matching or cluster laws would be equally central. Hall's theorem and Taylor's theorem are available; source-faithful constructions satisfying their quantitative demands are the proposed new content.

**Try to kill the programme early.** Apply the proposed rule to products of many comparable primes. Measure arity relative to \(\tau_H\), not a fixed numerical cutoff. Test shared-neighbor congestion. Track every residual's sign. Test the zero-weight-variation limit, where normalizer flux identities expose tautologies particularly clearly. Run the construction on a sparse prime flip (§5): it has the same squarefree support, absolute values, factor profiles and local sign abundance, and its Laplace sum is not \(O(x^{-b})\) for any \(b<\sigma_0\). If the desired transport is impossible, extract the precise complexity or cost lower bound and use it to redesign the permitted moves.

**4. How these fields should interact**

There is an exact shared language: the Möbius measure \(\nu=\sum_{d\ge1}\mu(d)\delta_d\), evaluated against different arithmetic test functions.

\[
\begin{aligned}
L_\varepsilon(n)&=\langle\nu,k_{\varepsilon,n}\rangle,&
k_{\varepsilon,n}(d)&=\mathbf1_{d>\lfloor\sqrt n\rfloor}
 d^{-\varepsilon}(\lfloor n/d\rfloor-n/d),\\
F(M)&=\langle\nu,g_M\rangle,&
g_M(d)&=\sum_{d\le k<M}(\sqrt{k+1}-\sqrt k)D(\lfloor k/d\rfloor),\\
\mathcal L(x)&=\langle\nu,e^{-x\cdot}\rangle.
\end{aligned}
\]

These are direct rewritings of the source formulas, not new bounds. They explain a productive interaction: a transport construction can be tested against the **specific** kernel needed by quadrature or sparse history.

For example, a proposed transport cost for the first route is

\[
c_{\varepsilon,T}(u,v)=
\left(\sum_{n\le T}\frac{|k_{\varepsilon,n}(u)-k_{\varepsilon,n}(v)|^2}{n(n+1)}\right)^{1/2}.
\]

A coefficient-preserving finite pairing gives a triangle-inequality bound by the sum of these costs plus the norm of its residual. The empty pairing attains this bound with the original norm, so the bound is equivalent to Q1; the open issue is whether actual arithmetic pairings or clusters leave a residual whose norm has an independent estimate. The exponential cost from route 3 does not automatically control these discontinuous floor kernels. Nor does a bound at one damping automatically supply the one-sided F samples of route 2.

The shared research topic is therefore **which arithmetic transports are cheap for which readouts**. Prove the transfer identities and estimates before sharing a claimed breakthrough between programmes. A unified vocabulary can help; an unproved universal cancellation principle cannot.

**5. Criteria for a field that earns its name**

Each programme should produce all of the following:

1. **Independent arithmetic constructions.** Its selector, compensation rule or transport must be defined from the source, rather than from the desired zero location or an unproved bound.
2. **General theorems with discriminating hypotheses.** Identify a class of arithmetic sources and explain both successful and failing members. Do not assert a universal theorem contradicted by majorants or twins.
3. **An obstruction theory with positive content.** Failure yields a sharp exponent, memory requirement, missing correlation, factor-profile invariant or complexity law.
4. **Intermediate mathematical outputs.** A new source estimate, a sharp transport classification, or a fixed zero-free strip counts. Another equivalence with RH does not move the source frontier.
5. **Exact handling of scale.** State which constants are uniform in T, M, x, damping, arity and sampling gaps. Quantifier changes are mathematical changes.
6. **A construction-to-receiver proof.** Trace the actual estimate into an already proved RH or strip theorem, with all residuals and boundaries present.
7. **Calibration against sparse prime flips and the parity twin.** For a set S of primes put \(\mu_S(n)=\mu(n)(-1)^{\omega_S(n)}\), \(\omega_S(n)=\#\{p\in S:p\mid n\}\), so that \(\sum\mu_S(n)n^{-s}=\zeta(s)^{-1}\prod_{p\in S}(1+p^{-s})/(1-p^{-s})\). Choose S greedily with \(\sum_{p\in S,\,p\le x}\log p\sim x^{\sigma_0}\), \(\tfrac12<\sigma_0<1\); S has relative density zero among the primes. As \(\sigma\downarrow\sigma_0\) the product tends to \(+\infty\) while \(1/\zeta(\sigma)\) stays finite and negative, so the Dirichlet series of \(\mu_S\) is singular at the real point \(\sigma_0\) and \(\sum_{n\le x}\mu_S(n)\ne O(x^{\sigma_0-\delta})\) for every \(\delta>0\). Hence the \(\mu_S\)-analogues of Q1 at \(a<\sigma_0-\tfrac12\) and of T at \(b<\sigma_0\) fail, and at least one of the two one-sided versions of H fails. \(\mu_S\) shares multiplicativity, squarefree support, \(|\mu_S|=\mu^2\), the value \(-1\) on almost all primes, the hyperbola and floor identities, the divisor source D and local sign abundance. **This is a deduction here.** A decisive estimate must use \(\mu(p)=-1\) on every sparse prime set of counting exponent above the target, and, in programme 1, the signs of the Ramanujan coordinates (parity twin).
8. **Formal proof obligations.** Any future claimed theorem needs a complete paper argument followed by Lean formalization. This document proposes programmes and questions; it does not declare their open estimates proved.

The most consequential conjectural picture is that **arithmetic cancellation is constrained by the zero-width threshold of the Möbius tail, the multiplicative scale of excursions and the factorization complexity of signed residuals**. The corpus provides exact identities and lower bounds for all three, while exposing why several simpler estimates fail: separate sawtooth and tail bounds lose nothing for the literal source, power-window sampling gains nothing over the bootstrap, and transport cost bounds are equivalent to the receiver. The proposed fields would turn those constraints into constructive laws. Their first task is to discover and prove one such law for the literal source that survives the stated countertests.
