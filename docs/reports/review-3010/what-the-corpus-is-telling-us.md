# What the corpus is telling us

The corpus gives good reasons to stop treating a reconstruction of the finite-field proof as the default architecture. It does **not** identify a different architecture that already solves RH. Its strongest recurring evidence is more specific: arithmetic information often survives in a signed comparison, an output norm, a mixed term or a scale-dependent response that disappears in the attractive positive object built from it.

That is my interpretation, not a theorem classifying possible proofs. The distinction matters: several existing reports turn exclusions of specified constructions into exclusions of entire kinds of mathematics. Those stronger exclusions are not what the inspected Lean statements prove.

The productive question is therefore: **which operation discards information that an actual arithmetic identity still controls?** The corpus contains answers—and successful repairs—more concrete than another proposed geometry of the zeros.

Evidence comes from corpus searches, programme surveys, direct inspection of statements and proof mechanisms, and the selected kernel audits described in the companion [mathematical fact log](corpus-facts.md). The reports were treated as leads. This is a broad investigation with targeted proof audits, not an audit of every declaration. No external mathematical source was used. F-numbers below identify facts in that log; proposed connections are explicitly questions, not new proved results.

**1. Some representations lose the arithmetic before any difficult estimate begins.**

The sharpest example is the proposed union of Weil correlation and integer successor in one positive affine state. Suppose a positive-definite function on `Aff(ℚ)` restricts on dilations to the actual Weil spline correlation. Then its value on translation by **every nonzero rational** is one constant. Literal integer successor, which distinguishes integers from nonintegral rationals, cannot occur there. The proof first obtains RH from the positive extension, then uses the resulting atomic archimedean spectrum to force translation blindness. Thus even the desired RH-positive extension would not retain that successor information. [F06; `weil_successor_blind`](../../../formal/GaloisForLFunctions/ArithmeticPositiveDuality/WeilsCorrelationCarriesNoSuccessor.lean).

The stronger spectral theorem explains why. Integer successor forces dilation coefficients to decay along

\[
u_N=(N+1+b)/(N+1+a),\qquad a\ne b.
\]

These rationals tend to 1 in the real topology while their reduced numerator–denominator product grows. Archimedean characters tend to 1 along them; the arithmetic Hecke bound forces the coefficient to zero. Averaging an arbitrarily large finite Gram system then shows that the dilation spectral measure assigns zero mass to the entire archimedean Kronecker line. This is an incompatibility between two exact requirements, not a failure to optimize a constant.

The conclusion is narrow but consequential. A construction retaining literal successor and Weil correlation must change the relation between them; it cannot merely improve this positive affine extension. The theorem does not prohibit every operator realization, correspondence, indefinite form or nonlinear construction. It tells us exactly which proposed identification cannot work.

Three other inspected mechanisms make the same warning concrete:

| Construction | Information discarded | What the corpus retains instead |
|---|---|---|
| Closure of the critical payment domain in the input norm | Square summability of partial sums; the closure remembers only total evaluation | The complete cofactor graph, including its output energy |
| One scalar normalization of forcing and receiver | Receiver vanishes if forcing stays bounded | Their exact Gram distance at receiver scale |
| Restriction to a simultaneous Sonin/Euler carrier | The entire cleared source current vanishes, although the carrier is nonzero | The complementary boundary quotient and its actual Fourier chart |

These are source theorems, not objections based on analogy. See [critical closure](../../../formal/GaloisForLFunctions/BiarithmeticGeometry/CriticalCoefficientDomain.lean), [scale separation](../../../formal/GaloisForLFunctions/ArithmeticDefectRigidity/ForcingScaleSeparation.lean) and [the Euler-current radical](../../../formal/GaloisForLFunctions/RHTower/CCM/CCMEulerMovingCarrierRadical.lean) (F19, F24–F25).

For actual source graphs, closedness of the input image is **equivalent** to a uniform output-energy estimate. A completion cannot manufacture that estimate. For the Möbius source, forcing-normalized Gram determinants tend to zero while the forcing–cofactor squared distance divided by receiver energy is exactly one. The arithmetic can lie below the scale on which the positive limiting object is observed.

There is also a useful check against overinterpreting this observation. Adding the fixed receiver, residual and forcing covariances does not provide new limiting coordinates: after subtracting the forcing power, their entire escaping table is `sign(b) sign(c) K(j,k)`, with signs `(1,−1,0)`. The existing cofactor Hilbert module already contains it. A larger notation for the same fixed limit supplies no additional constraint. [F25; signed Gram classification](../../../formal/GaloisForLFunctions/ArithmeticDefectRigidity/TheSignedCofactorGramHasNoExtraCoordinates.lean).

**Interpretation.** Before searching for a universal positive space, establish that its norm, quotient and limiting operation preserve the arithmetic relation to be used. The corpus repeatedly proves that a natural-looking construction does not. Preserving information is necessary; it is not yet a bound on that information.

**2. RH-equivalent endpoints can demand different amounts of arithmetic structure.**

The corpus makes an unusually useful distinction between counting and complete tower positivity. Write

\[
\operatorname{Count}(a):\quad \sum_{n\le x}a(n)-x=O(\sqrt{x}\log^2x).
\]

At `a = Λ`, this is equivalent to RH. At the same source, positivity of every compact smooth generator on one prime tower is also equivalent to RH. But as properties of variable sources they differ sharply:

- Counting is unchanged by perturbations whose partial sums are `O(√x log²x)`.
- Complete tower index zero forces every coefficient `a(n)=Λ(n)` for `n≥2`, as well as RH.
- In particular, `Count(Λ+1/n)` is equivalent to RH, while `Λ+1/n` is never tower positive.

These are exact theorems, including the last counterexample. [F07; `TowerPositivityIsPrecisionExact`](../../../formal/GaloisForLFunctions/ArithmeticOfSquareRootPrecision/TowerPositivityIsPrecisionExact.lean).

**Why it matters.** A requirement necessary for a universal positivity theorem is not automatically necessary for an argument proving the weaker counting endpoint. The project can accidentally demand recovery of every coefficient when its intended conclusion only needs a precision class. Equivalence at the actual source does not transport every robustness or selection requirement across a family of sources.

Likewise, `TheDecidingInputTheorem` rules out specified perturbation-stable predicates as sufficient for counting over all sources. Its error-law counterexamples show that those estimates alone are insufficient. They do not show that analytic estimates combined with exact source identities can never decide the question, or that every proof must be phrased as a ring-level counting geometry.

**Research consequence.** Select the endpoint before selecting the counterexample battery. Preserve exactly the source distinctions that endpoint requires. This permits less ambitious intermediate objects than a complete, coefficient-exact positive realization without reducing the strength of the final statement about ζ.

**3. The strongest positive advances keep interactions that separate bounds discard.**

The prime-comb example shows why a sharp estimate can still estimate the wrong quantity. On an explicit smooth odd normalized family, both comb energy and the cross-prime aggregate are asymptotic to `4 exp(2r)`. Yet the first-power charge divided by comb mass tends to zero. The normalized comb converges to translation by 2; its pairing with the original profile tends to that profile's autocorrelation at 2, which vanishes by support. The large norm is real. The adverse pairing is small for a geometric reason the norm majorant cannot express. [F04; `ThePrimeCombIsATranslation`](../../../formal/GaloisForLFunctions/ArithmeticCompensationTheory/ThePrimeCombIsATranslation.lean).

The shell-completed conductor energy provides a second, arithmetic example. Its divisor sum has Möbius signs. Interchanging that finite sum with convergent Fourier tails turns the Möbius cancellation into an exact coprimality indicator:

\[
E_m(c)=\frac{2}{M\varphi(m)}
\sum_{\substack{a\ge1\\(a,m)=1}}\frac ma
\int_{ac/m}^{\infty}|\widehat\phi(2\pi t)|^2\,dt\ \ge0,
\qquad M=\int\phi^2.
\]

The sum becomes positive **after** the arithmetic cancellation. Bounding the divisor terms separately would obscure this mechanism. For every fixed conductor, however, this energy tends to zero as overlap grows. The identity supplies sign; a finite-source comparison must still be paid against the shrinking reserve. [F09; `TheShellsRepayEveryConductor`](../../../formal/GaloisForLFunctions/RenormalizedArithmeticPotentialTheory/TheShellsRepayEveryConductor.lean).

Two other exact mechanisms expose useful interaction terms:

- For positive definite preceding Hankel heads, the successor Schur complement of two summed sources equals the sum of their successor complements **plus a nonnegative minimizer-discrepancy variance**. Equality holds precisely when their minimizers coincide. Separate minimization discards a real reserve. [F13; `SuccessorMixture`](../../../formal/GaloisForLFunctions/CompletedArithmeticForms/SuccessorMixture.lean).
- The complete Weil prefix already has a dimension-independent inverse bound: `bᵀA⁻¹b ≤ 20‖b‖²`, uniformly in both horizons and every admissible overlap `cM≤N`. Its Schur complement retains the literal complete mixed block: `yᵀCy−(By)ᵀA⁻¹(By)`. The unresolved sign is a coupled question about `B` and `C`, not the absence of a prefix inverse estimate. [F23; `WeilPrefixPayment`](../../../formal/GaloisForLFunctions/CompletedArithmeticForms/WeilPrefixPayment.lean).

These results do not prove that every lost mixed term is favorable. They show where successful proofs have obtained information unavailable to separate size estimates. They suggest asking for the sign or geometry of a specific interaction before asking for a stronger universal norm bound.

**4. Changing coordinates helps only when the required form survives.**

The first theta atom supplies a decisive control experiment. The exact invertible clock

\[
u=\operatorname{arsinh}(t/\sqrt q)
\]

turns its reflected source into `C exp(−4t²)(B−24t²)`. At every nonnegative source center, all clocked signed Hankel heads are positive definite. At that very center, some physical signed head fails positive semidefiniteness. Exact substitution and exact inverse substitution do not preserve the target cone. [F11; `HyperbolicClock`](../../../formal/GaloisForLFunctions/CompletedArithmeticForms/HyperbolicClock.lean).

The Hermite construction succeeds in a more demanding sense. It is an actual congruence of the complete quadratic form. Gaussian contraction controls the first atom, the transformed infinite theta remainder has a linear dimension cost, and the combined estimate returns to the original signed coefficient directions:

\[
|v^T(H_N(x)-G_N)v|
\le \frac{C(N)}{q(x)}\,v^TG_Nv,
\qquad q(x)\ge16(N+2)^2,
\]

with quadratic rank numerator `C(N)`. This includes mixed directions and the full native theta source. It is an actual improvement in the comparison estimate, not just a new positive model. Its condition still depends on rank. [F12; `NativeQuadraticRank`](../../../formal/GaloisForLFunctions/CompletedArithmeticForms/NativeQuadraticRank.lean).

**What if the theta tail is tiny?** Fixed-rank smallness is insufficient near the first atom's moving failing rank. The clock counterexample and the rank-dependent comparison prevent dismissing the rest of the source by its scalar size. The relevant question is its contribution in the complete source's near-degenerate directions, including the successor minimizer. Conversely, the mixture variance theorem assumes positivity of preceding heads; it cannot be used past a failing head without another argument.

This gives a concrete direction independent of constructing a finite-field surface: compare the actual source in its own quadratic norm, with an exact transport law and explicit rank range. The remaining task is to connect those ranges through the central region and growing rank. The available tail theorem alone does not do so.

**5. A universal scalar margin can fail to select even when joint responses succeed.**

Among finite prime flips, the maximal original selective gap does not identify the untwisted source. Nevertheless, two lower bounds do: maximal original gap together with at least the untwisted response to the fixed dyadic toggle holds exactly for the empty flip set.

The proof identifies the information missing from the first reading. A maximal original gap excludes flipping 2. The dyadic gap has an interior secular root, so adding any remaining flipped prime strictly decreases it. The second reading moves the problem away from the first reading's maximal plateau. [F15; `OneDyadicProbeSelectsTheFinitePrimeSource`](../../../formal/GaloisForLFunctions/ArithmeticCountingPositivity/OneDyadicProbeSelectsTheFinitePrimeSource.lean).

This is genuine finite-family selection, but it is not robust at fixed absolute precision. Arbitrarily remote prime flips retain the maximal original gap and have arbitrarily small dyadic-response loss; the quantitative bound is of order `1/p`. Exact identifiability, stable identifiability and an arithmetic proof of the required readings are three different questions.

The infinite-prime classification goes further than a generic warning about limits. At every regular energy threshold, exact eigenvalue counts prove that the counted conductor lines exhaust the **whole actual spectral sublevel**. Euler density zero is equivalent to the constraint mass escaping every bounded energy window. The missing mass has been located, not merely suspected. [F16; `PrimeCountsDetermineEveryBoundedSpectralMass`](../../../formal/GaloisForLFunctions/ArithmeticCountingPositivity/PrimeCountsDetermineEveryBoundedSpectralMass.lean).

**Interpretation.** Source selection may require a response to a controlled change, or a scale-dependent family of readings, rather than a better single invariant. But the finite two-probe theorem does not establish selection for arbitrary sources, and pointwise convergence cannot replace control of escaping mass. These are precise limits on what this successful mechanism currently buys.

**6. Several purported universal obstructions are narrower than the reports say.**

The most consequential example is the claim that an arithmetic depth-sensitive observable cannot exist, leaving a positivity family as the only possible form of progress. The inspected holomorphic-carrier theorem does not establish that classification.

Its exact hypotheses concern holomorphic linear carriers, or separately holomorphic sesquilinear carriers, vanishing on **every** critical configuration. Its approximate version fixes bounds on the critical line and a second vertical line; three-lines interpolation then makes the response to sufficiently shallow quartets smaller than a fixed quantum. The entire calibration theorem similarly identifies an entire weight whose values on **all real points** are prescribed to be `|F|²`. These statements exclude their stipulated classes. They do not cover all nonlinear constructions from an arithmetic source, singular limits, or estimates tailored to the actual divisor. [F08; `HolomorphicCarriersCannotBeQuantized`](../../../formal/GaloisForLFunctions/RHTower/HolomorphicCarriersCannotBeQuantized.lean).

The corpus already supplies a counterexample to the broader dismissal of arithmetic evaluation. Prescribed finite theta prefixes and regularized positive curvature recover the collided metric and depth moments. One stage works uniformly over normalized tests, motions `|τ|≤n/2`, and combined aperture `a+j|L|≤2log(n+1)`. After division by `4^j`, the error is `O(n⁻²)+O(log n/n)`. No RH or zero-separation premise occurs in the capstone. [F17; `PolynomialThetaMetric`](../../../formal/GaloisForLFunctions/ConjugateDiagonalGeometry/PolynomialThetaMetric.lean).

The mechanism is nonlinear: regularized curvature involves the amplitude, its derivative and the denominator `(|A|²+η)²`; Green testing then recovers the divisor. It is outside the holomorphic linear-carrier class. It computes the collided trace, **not** a bound comparing it with the reflection pairing, and not automatically the integer horizontal-collision charge. These distinctions leave a hard problem; they do not justify saying there is no arithmetic source formula for depth-sensitive data.

Other corrections follow from the same insistence on quantifiers:

| Strong reading | What the inspected theorem supports |
|---|---|
| Every deciding method must be a particular arithmetic geometry | Specified predicates stable under specified perturbations cannot imply the count for all weights |
| Exponential conductor confinement is unavoidable for negative directions | Exponential conductor scale is necessary for **all bounded-defect vectors**; the test vectors are not proved negative for the complete form |
| A positive nonlinear model gives the physical positivity | False for the exact invertible first-atom clock |
| Self-dual positive rigidity transfers automatically to the zero divisor | The tent theorem needs positivity, gap and self-duality on the same measure |
| Enlarging a fixed limiting Gram representation necessarily adds constraints | The receiver/residual/forcing table adds no coordinates after the stated normalization |

The positive self-dual measure theorem is particularly instructive. Its proof succeeds because the unshifted tent identity saturates a nonnegative integral: the origin already accounts for all of it. The remaining sinc-square integral must vanish, forcing integer support; translated tents force equal masses. This is an exact rigidity mechanism, but the theorem cannot transfer positivity between two different measures merely because an explicit formula relates them. [F20; `PositiveSelfDualMeasuresWithAGapAreDiracCombs`](../../../formal/GaloisForLFunctions/ArithmeticPositiveDuality/PositiveSelfDualMeasuresWithAGapAreDiracCombs.lean).

**7. The mature Weil route has real progress and a precisely located remaining comparison.**

Abandoning it because it resembles Weil would disregard the strongest complete finite-source results inspected. For the explicit tilted unit spline, **every fixed positive overlap** eventually gives a positive definite full actual Weil matrix, with a floor independent of the horizon. This already crosses the separated-atom and entrywise-sign boundaries. The proof combines actual norm quasimodes, a defect reserve and a common conductor floor. [F14; full fixed-overlap positivity](../../../formal/GaloisForLFunctions/CriticalArithmeticCorrelationTheory/TheCompleteWeilFormIsPositiveAtEveryFixedOverlap.lean).

But the order of quantifiers remains decisive:

| Proved | Required by the cited RH comparison |
|---|---|
| For each fixed overlap `c`, one eventual horizon works for every coefficient vector | Control along an overlap growing sufficiently fast with the horizon |
| At `c_N=(log N)^α`, `0<α<1/40`, every fixed finite conductor family is eventually positive for all its coefficients | The whole space along, for example, `c_N=2(log N)^α`, `α>1/4` |
| For each fixed overlap, finitely many conductor readings control the complete inverse tail | Quantitative control of that family, its errors and the inverse as overlap grows |

The first line does not provide the schedule needed in the second column. The second has **both** a growth-range gap and an exhaustion gap. The third is stronger than individual mode convergence, but still has overlap-dependent quantifiers. [F21, F23; growing packets](../../../formal/GaloisForLFunctions/CompletedArithmeticForms/WeilGrowingPackets.lean), [RH overlap criterion](../../../formal/GaloisForLFunctions/RenormalizedArithmeticPotentialTheory/LogarithmicOverlapOfTheCompleteWeilMatrixIsTheRiemannHypothesis.lean).

The existing polynomial estimate reads schematically

\[
W_{c,N}(x)\ge a c^{-7}D_N(x)-C c^9\|x\|^2,
\qquad N\ge Hc^8.
\]

Hence a nonpositive unit direction has defect at most `C'c^16`. Inspection of the proof shows exactly where this power comes from: separate absolute payments for the non-ratio form and pole moments, each using a defect fraction proportional to `c⁻⁷` and a cost proportional to `c²` divided by that fraction. Sixteen is the exponent of this estimate, not a proved optimum for actual negative directions. [F22; polynomial reserve proof](../../../formal/GaloisForLFunctions/CriticalArithmeticCorrelationTheory/TheCompleteWeilReserveHasPolynomialOverlapCost.lean).

There is a genuine neighboring obstruction: binary conductor `2^k` has adjunction energy only `γ+(k+1)log2`, so arbitrary bounded-defect unit vectors cannot be captured below an exponential conductor scale. Those are actual vectors, not formal models. The hypothesis that they are nonpositive for the complete signed form is absent. This leaves room for stronger confinement using that sign, but does not prove such confinement. [F10; binary cutoff obstruction](../../../formal/GaloisForLFunctions/RenormalizedArithmeticPotentialTheory/PrimeDefectConfinementMustRetainLowEnergyConductors.lean).

The specific research question is therefore about the joint complete source on its potentially adverse directions. Another scalar defect estimate on arbitrary vectors may repeat a known obstruction. Another positive fixed packet may repeat a known theorem. Neither is a substitute for the missing joint comparison.

**8. Where to look without choosing the answer in advance.**

The following are research questions supported by inspected mechanisms. They are not claims of a new proof route, nor claims that no related module exists elsewhere in the corpus.

**A. Nonlinear source readings and actual local dynamics.** This is the most substantial alternative to the reports' forced return to a holomorphic carrier or a Weil positivity family. CDG already computes depth-sensitive traces from arithmetic prefixes. Independently, actual heat-zero dynamics prove

\[
E_w(b)-E_w(a)+2\int_a^b N_w(t)\,dt
\le C_w\log X\int_a^b E_{\rm outer}(t)\,dt,
\quad b\log X\le1.
\]

Here `N_w` is the full multiplicity-weighted nonreal count. The estimate passes through collisions and includes time zero. Continuous truncated counts, bounded convergence and actual exterior-force estimates remove the need to assume a simple separated zero configuration. [F18; `HeatLocalizedEnergyDissipation`](../../../formal/GaloisForLFunctions/RHTower/Heat/HeatLocalizedEnergyDissipation.lean).

The first question is whether a common finite arithmetic source can represent this energy and its exterior flux **uniformly in the admissible heat interval**, with compatible regulator, height and cutoff errors. The CDG theorem is not already that bridge: it concerns its own unheated source readings and test norm. Establishing compatibility would identify exactly which arithmetic term governs the dissipative balance. A source-side estimate improving that balance would be substantive even before an extinction theorem. Simply restating extinction, or deriving the existing inequality again from zero locations, would not be progress.

**B. Complete quadratic comparisons at the moving difficult directions.** The Gaussian/Hermite theorem is evidence that the comparison norm can change the attainable rank range. The mixture identity identifies a reserve created by disagreement of minimizers. The prefix theorem already pays a complete inverse uniformly. These mechanisms justify examining the actual Schur coupling or successor minimizer before estimating constituent entries.

For theta, the first question is quantitative control of the complete source's successor test near the rank–center transition, including the contribution of the remaining atoms. For the atomic Weil form, it is control of the actual coupled expression `C−B* A⁻¹B` beyond the known prefix regime. The two problems have different sources and profiles; theorems cannot be transferred between them without an exact comparison. A useful result must improve a range or a bound for the literal source. A new coordinate model or the formal Schur identity alone is already insufficient.

**C. Source selection at the precision the endpoint actually needs.** The finite two-probe law proves that a plateau in one invariant can be resolved by a controlled perturbation. The infinite-pattern theorem proves that bounded spectral windows may nevertheless miss all mass. Investigate which joint responses are stable in the counting precision class, and what arithmetic identities control their resolution as conductors grow.

This question deliberately separates exact source reconstruction from the counting endpoint. A first useful result would be a quantitative selection or approximation statement for a strictly larger source family in its declared norm, with the escaped mass accounted for. Exact classification of a finite family is not a uniform arithmetic estimate; fixed tolerance cannot exclude remote flips. The existing theorems specify these failure modes rather than foreclosing the question.

**D. Preserve source boundary data before completing a representation.** The cofactor graph and Euler boundary quotient provide actual mathematical objects retaining data lost by simpler closures and compatible carriers. Their use should begin with a source-specific estimate on that retained data. The closed-range equivalence shows where an estimate is still owed; the signed Gram classification shows that merely adding fixed coordinates will not pay it. A useful first result would control a growing family or a prelimit remainder not determined by the already classified fixed limit.

These directions can be pursued alongside the mature shell comparison. They should not be collapsed into a single conjectural geometric object. Their common lesson is methodological and mathematical: preserve the relevant interaction, prove the transport law, then obtain an estimate with the quantifiers the endpoint uses.

**9. What would change this assessment.**

A convincing new result would do at least one of the following: produce a source-side bound for the nonlinear depth reading or heat flux; extend complete relative theta control into a previously unpaid rank–center region; control the mixed shell form on growing adverse directions; prove stable selection in the appropriate precision class; or show that one of these proposed intermediate statements fails and extract its exact surviving boundary.

A new RH equivalence, another positive model without a transport identity, another fixed packet, or a larger fixed limiting Gram table would not address the distinctions established above. Nor would a no-go for one such construction justify closing a broader route.

The corpus has not told us what the final proof must look like. It has told us, with unusual precision, where several plausible representations forget the actual problem—and has demonstrated that retaining complete signed and relative information can cross boundaries that scalar or entrywise reasoning made look final. That is the strongest basis I found for changing the research direction without substituting a new predetermined answer.
