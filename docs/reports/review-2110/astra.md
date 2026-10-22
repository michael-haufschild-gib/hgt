**RH after the walls: arithmetic continuation and critical energy**  
Research assessment, 22 October 2026.

**Answer.** I see opportunities for new *producer estimates inside existing routes*, but no established mechanism that circumvents the identified walls and proves RH. The strongest opportunity I found is to study **one-sided continuation of the complete signed Möbius energy in the damping parameter**, starting from the proved half-damping bound. Its target differs materially from bounding an undamped derivative, controlling each prime insertion, or estimating separate positive sectors. It survives the inspected no-go theorems. Its decisive arithmetic estimate remains unproved.

A second opportunity is **quantitative propagation of the arithmetic cancellation already proved between complementary denominator sectors**. A third, useful independently of an RH proof, is **compensated comparison of zero width with ground-energy growth**, retaining the positive zero contributions discarded by the current local-count argument. These are research directions, not claimed new routes with completed producers.

The field I would try to develop is **arithmetic continuation and critical energy**: a theory of when exact arithmetic identities prevent critical energy from escaping as damping decreases, aperture grows, or cutoffs are removed. Its distinguishing problem is quantitative control of complete signed interactions for one specified arithmetic source. The corpus already contains much of its algebra and many sharp counterexamples. Its missing substance would be continuation and compensation theorems, not another vocabulary for the receiver.

**Evidence and scope.** During the initial report phase, the four requested ledgers were read across the research team, followed by targeted corpus searches and inspection of actual Lean statements and proofs. No additional existing Markdown files were opened; initial corpus results included indexed prose, after which search output was restricted to Lean modules or filtered to Lean hits. No builds were run in that phase. The subsequent Opportunity 1 investigation, separately requested with targeted Lean audits, is recorded below. Main log: [astra-research.log](../../../logs/astra-research.log); initial detailed audits: [routes](../../../logs/astra-route-opportunities.txt), [kills](../../../logs/astra-killed-audit.txt), [unification](../../../logs/astra-unification-audit.txt). Saved initial search results are `logs/astra-search-*.json`.

Evidence labels below distinguish **corpus result** (source inspected; no fresh compiler audit), **paper deduction** (argument supplied here), and **research target** (unproved). The ledgers' committed/working-tree labels are provenance claims, not compilation performed in this investigation. Hybrid/deep retrieval repeatedly reported incomplete semantic stages; lexical searches and source inspection supplied usable evidence. Failure to find a theorem is not a proof that it is absent. This is an internal research assessment, not a worldwide literature or priority audit.

**What the walls actually permit.** Several distinctions matter before choosing a direction.

| Established obstruction | What it excludes | What it leaves open |
|---|---|---|
| Width dictionaries | Counting a change of receiver coordinates as an improved arithmetic bound | A new estimate deriving that bound from the actual source |
| Finite-aperture indistinguishability | Deciding arbitrary configurations from one bounded aperture | One arithmetic argument valid at every aperture, with justified uniformity |
| Half-damping parity barrier | Receiver control from magnitudes, unsigned majorants, or the specified invariant data | Signed estimates restricted to the actual Möbius source |
| Coherent-block Type-II obstruction | Uniform bounds on the forbidden arbitrary-coefficient classes | A smaller arithmetic coefficient class with independently proved cancellation |
| Carrier size/torsion laws | The specified finite-rank, trace-class, finite-deficiency or integral-Frobenius constructions | A sufficiently large, nonintegral, source-derived realization with a proved domain and trace identity |

These are not loopholes in the theorems. They are distinctions between a theorem's hypotheses and an extrapolation beyond them.

In particular, “the Weil cone is the point Λ” must be read carefully. The actual theorem states

\[
\operatorname{WeilPositiveFull}(\lambda)
\iff \mathrm{RH}\ \land\ \forall n\ge2,\ \lambda(n)=\Lambda(n).
\]

Thus, modulo the unused first two coefficients, the cone has **at most** one point; it is empty if RH fails. This is uniqueness, not unconditional positivity of Λ. See `weilPositiveFull_iff_riemannHypothesis_and_eq_vonMangoldt` in [WeilConeUniquenessUnconditional.lean](../../../formal/GaloisForLFunctions/RHTower/WeilConeUniquenessUnconditional.lean).

An RH-equivalent conclusion is also not automatically a circular proof target. Every successful proof will establish something implying RH. Circularity arises when an equivalent unproved statement enters as an input, or when a supposed independent certificate already assumes the desired sign. An arithmetic proof of Weil positivity need not begin by constructing a self-adjoint operator; the existence of a spectral interpretation does not disqualify a direct inequality proof.

Nor must every useful observable change sign under reflection. Squared transverse depth is reflection-even and still detects departure from the axis. The requirement is **depth sensitivity with a proved vanishing or sign law**, not reflection-oddness as a universal axiom.

Finally, the ledgers do not establish that mathematics as a whole lacks the necessary tools. They establish many precise failures of surveyed methods. A proposed new field earns that description by producing new theorems that overcome those failures.

**The present frontier is stronger than a collection of RH criteria.** Four assets deserve to drive the next questions.

First, the signed receiver damping rate already equals the zero width. With \(\Delta=\Theta-\tfrac12\), the corpus proves admission for every \(\varepsilon>\Delta\),

\[
\operatorname{receiverDampingRate}=\Delta,
\qquad
\mathrm{RH}\iff
\forall\delta>0\ \exists\varepsilon\in(0,\delta)\ \exists B_\varepsilon\ \forall T,
\ E_T(\varepsilon)\le B_\varepsilon.
\]

The constant may depend on damping. No uniform bound as \(\varepsilon\downarrow0\) is required. The rate is the infimum of the **accumulation points** of admitted dampings, not merely their infimum. This source theorem supersedes older language in parts of the unification ledger that separates the damping threshold from width. Admission at a *single* damping still has its separate zero-translation interpretation; it is not the same assertion as the accumulation threshold. See `receiverDampingRate_eq_zetaZeroAbscissa_sub_half`, `riemannHypothesis_iff_cofinal_budget`, and `Ioi_zero_subset_receiverDampings_of_riemannHypothesis` in [AdmissionBelowHalfDampingAboveTheZeroWidth.lean](../../../formal/GaloisForLFunctions/RHTower/AdmissionBelowHalfDampingAboveTheZeroWidth.lean).

Second, genuine arithmetic cancellation is already proved. For fixed \(0<\varepsilon<1/2\), a large-prime denominator sector and its literal complement satisfy

\[
\frac{E_{\mathrm{complete}}}{E_{\mathrm{sector}}}\longrightarrow0,
\qquad
\frac{E_{\mathrm{complement}}}{E_{\mathrm{sector}}}\longrightarrow1,
\qquad
\frac{\langle\mathrm{sector},\mathrm{complement}\rangle}
 {E_{\mathrm{sector}}}\longrightarrow-1.
\]

This is actual-source anti-alignment, not a random-model prediction. But the available complete-head estimate is only \(o(P^{1-2\varepsilon}/\log^2P)\), not a horizon-uniform constant. See the three ratio theorems in [PMRamanujanComplementaryCancellation.lean](../../../formal/GaloisForLFunctions/RHTower/PMRamanujanComplementaryCancellation.lean).

Third, information recovery is stronger than energy control. All logarithmic pronic moments determine a damped source on \(n\ge2\), whereas all stationary translated moments can agree for rows with different receiver behavior. Source identification therefore cannot be substituted for a quantitative bound. See `eq_add_unitMass_of_logMoments_eq` and `exists_logMoment_ne` in [LogarithmicMomentsAreACompleteReceiverInvariant.lean](../../../formal/GaloisForLFunctions/TransHorizonIncidenceMechanics/LogarithmicMomentsAreACompleteReceiverInvariant.lean), and [FermiRowsAgreeInEveryTranslatedMomentAndSplitTheReceiver.lean](../../../formal/GaloisForLFunctions/TransHorizonIncidenceMechanics/FermiRowsAgreeInEveryTranslatedMomentAndSplitTheReceiver.lean).

Fourth, the exact theta–Gamma–pole source already determines its admissible signed arithmetic coefficients uniquely, even from agreement on an unbounded set of integer observations. This is an unusually strong source-selection theorem. It still supplies no energy sign. See `unique_frequently_signed_arithmetic_source` and `signed_arithmetic_source_rigidity` in [CHMDSignedEulerPoissonRigidity.lean](../../../formal/GaloisForLFunctions/RHTower/CHMDSignedEulerPoissonRigidity.lean).

Together these results suggest a precise change of question: **how does exact arithmetic identity produce a quantitative bound on complete signed energy under continuation?** More source reconstruction, more complete-period moments, or another receiver equivalence does not answer it.

### Opportunity 1: backward damping continuation.
This is my first choice for a focused investigation. It refines PM/BVI rather than adding another route to the ledger.

For \(\varepsilon>0\), define the literal arithmetic quantities

\[
\begin{aligned}
c_\varepsilon(d)&=\mu(d)d^{-\varepsilon},
&r_\varepsilon&=\zeta(1+\varepsilon)^{-1},\\
A_\varepsilon(n)&=\sum_{d\le n}c_\varepsilon(d)\lfloor n/d\rfloor-nr_\varepsilon,
&E_T(\varepsilon)&=\sum_{n=1}^{T}\frac{A_\varepsilon(n)^2}{n(n+1)}.
\end{aligned}
\]

These match the corpus's centered divisor prefix and discrete energy. Every \(\varepsilon\ge1/2\) is admitted, including the endpoint: \(\sup_T E_T(1/2)<\infty\). See [PMPowerDampedMobiusDiscreteEnergy.lean](../../../formal/GaloisForLFunctions/RHTower/PMPowerDampedMobiusDiscreteEnergy.lean) and `Ici_half_subset_receiverDampings` in [ReceiverDampingsAccumulateAboveTheZeros.lean](../../../formal/GaloisForLFunctions/RHTower/ReceiverDampingsAccumulateAboveTheZeros.lean).

**Corpus result.** The damping tangent is already explicit:

\[
\partial_\varepsilon A_\varepsilon(n)=B_\varepsilon(n),\qquad
B_\varepsilon(n)=\sum_{k\le n}\Lambda_\varepsilon(k)-nr'_\varepsilon,
\quad
\Lambda_\varepsilon(k)=-\sum_{d\mid k}\mu(d)d^{-\varepsilon}\log d.
\]

`hasDerivAt_pmPowerDampedCenteredDivisorPrefix` proves this. The existing tangent receiver assumes a horizon-uniform norm bound on \(B_\varepsilon\) integrable near zero. It does not prove that bound. See [DampedChebyshevTangentFormOfTheReceiver.lean](../../../formal/GaloisForLFunctions/BezoutValuationIncidence/DampedChebyshevTangentFormOfTheReceiver.lean).

**Proposed research target.** For every \(0<a<1/2\), find a nonnegative function \(b_a\), integrable on \([a,1/2]\), such that for every horizon \(T\), almost everywhere on that interval,

\[
\boxed{
-2\sum_{n\le T}\frac{A_\varepsilon(n)B_\varepsilon(n)}{n(n+1)}
\ \le\ b_a(\varepsilon)\bigl(1+E_T(\varepsilon)\bigr).
}
\tag{C}
\]

The same \(b_a\) must work for every \(T\). Dependence on \(a\), including arbitrarily bad growth as \(a\downarrow0\), is allowed. The left side is the complete signed work against the damping tangent. It is not \(\|B_\varepsilon\|_T\), not the sum of absolute cross terms, and not an energy component after deleting the pole correction.

**Paper deduction: (C) suffices for RH.** Finite sums give

\[
E'_T(\varepsilon)=2\sum_{n\le T}
\frac{A_\varepsilon(n)B_\varepsilon(n)}{n(n+1)}.
\]

Divide (C) by \(1+E_T\) and integrate from \(a\) to \(1/2\):

\[
1+E_T(a)
\le \bigl(1+E_T(1/2)\bigr)
\exp\!\left(\int_a^{1/2}b_a(\varepsilon)\,d\varepsilon\right).
\]

Writing \(B_{1/2}=\sup_T E_T(1/2)<\infty\), the right side is at most \((1+B_{1/2})\exp(\int_a^{1/2}b_a)\), independent of \(T\). Thus every \(a>0\) below half damping is admitted. The existing cofinal-budget theorem gives RH. This elementary continuation implication is proved on paper here; it was not formalized or compiled in this task. **No proof of (C) is claimed.**

This changes the analytic demand in two useful ways. It starts at a known finite-energy state, rather than trying to enter the critical norm from the singular zero-damping tangent. It also asks only for the energy-increasing part of the derivative when moving backward. Large tangential motion can be harmless if it does not increase energy. The corpus's failure of an undamped \(L^2\) tangent and of uniformly bounded difference quotients at zero does not refute this demand on each compact positive-damping interval. See [PMPowerDampedMobiusDerivativeBoundary.lean](../../../formal/GaloisForLFunctions/RHTower/PMPowerDampedMobiusDerivativeBoundary.lean).

There is a less restrictive variant if linear control proves too strong. Replace \(1+E\) by a positive continuous nondecreasing function \(\Phi(E)\) satisfying

\[
\int_0^\infty\frac{du}{\Phi(u)}=\infty.
\]

Integrating \(-E'_T/\Phi(E_T)\le b_a\) again prevents energy from becoming unbounded over a finite damping interval. This allows some growth faster than linear. A coefficient growing with \(T\) does not give the required uniform continuation; a finite reciprocal integral does not by itself guarantee continuation over the whole interval. The missing theorem remains arithmetic control of the signed pairing.

**Where a producer would have to enter.** Dirichlet convolution gives

\[
\partial_\varepsilon c_\varepsilon
=c_\varepsilon*(\Lambda(n)n^{-\varepsilon}).
\]

For \(x>0\), using sums over positive integers, define the *real-centered extension*
\(\mathcal A_\varepsilon(x)=\sum_{d\le x}c_\varepsilon(d)\lfloor x/d\rfloor-xr_\varepsilon\).
Its corresponding paper identity is

\[
\partial_\varepsilon\mathcal A_\varepsilon(x)
=\sum_{k\ge1}\Lambda(k)k^{-\varepsilon}
\mathcal A_\varepsilon(x/k).
\tag{F}
\]

For fixed \(x\) and \(\varepsilon\ge a>0\), the part \(k>x\) is an absolutely convergent tail, because \(\mathcal A_\varepsilon(x/k)=-xr_\varepsilon/k\). It contributes
\(-xr_\varepsilon\sum_{k>x}\Lambda(k)k^{-1-\varepsilon}\). Together with the finite part this supplies the full centering derivative. Replacing \(\mathcal A(x)\) with \(A(\lfloor x\rfloor)\) introduces a fractional-part correction; they must not be silently identified.

The underlying logarithmic Möbius identity is already in [DeningerVonMangoldtMoebiusConvolution.lean](../../../formal/GaloisForLFunctions/RHTower/DeningerVonMangoldtMoebiusConvolution.lean). The corpus also has a different, logarithmic-in-cutoff covariance balance, with kernel \(\Lambda(d)(1-d^{-\varepsilon})\), in [PMPowerDampedMobiusLogConvolution.lean](../../../formal/GaloisForLFunctions/RHTower/PMPowerDampedMobiusLogConvolution.lean). Neither identity supplies (C).

An absolute dilation estimate encounters the critical coefficient sum \(\sum_k\Lambda(k)k^{-\varepsilon-1/2}\), so it cannot justify the proposed continuation below half damping. The prospective input must be a **lower bound on the signed numerical range along the literal arithmetic source**, perhaps after an explicitly controlled correction to the energy. It must retain the full Mangoldt forcing and all mixed terms. An abstract operator inequality assumed on that source would merely move the obligation.

The first worthwhile attack is therefore concrete: express \(\langle A_\varepsilon,B_\varepsilon\rangle_T\) using the owned divisor, Vaughan and logarithmic covariance identities; identify a joint cancellation that controls its negative part uniformly in \(T\). Any proposed auxiliary energy must be comparable to the original energy with constants independent of \(T\), and its correction must be paid explicitly.

**Why this passes the scope audit.** It reads signs, keeps the physical origin and every horizon, uses the actual arithmetic row, and requires no finite spectral carrier. It seeks to prove the missing bound in Wall 1, rather than violating Wall 3 or Wall 14. Targeted searches found the derivative and tangent-norm receivers but no identical continuation estimate. That supports investigating this formulation; it does not certify global novelty or suggest that its sign is easy.


### Opportunity 3: propagate complete-sector compensation.
The existing complementary-sector theorem gives more evidence of a real arithmetic mechanism than a generic appeal to randomness. Its missing ingredient is a rate and a compatible iteration.

Write a complete truncated source as \(H_P=S_P+C_P\). Its energy is

\[
\|H_P\|^2=\|S_P\|^2+\|C_P\|^2+2\Re\langle S_P,C_P\rangle.
\]

The corpus proves cancellation at leading order. The next question is whether the *residual after all three terms have been combined* obeys a useful recurrence as \(P\) grows. One possible sufficient structure would be a source-derived inequality

\[
F_{j+1}\le q_jF_j+r_j,
\qquad
\sup_J\left[
F_0\prod_{i<J}q_i+
\sum_{j<J}r_j\prod_{j<i<J}q_i\right]<\infty,
\tag{R}
\]

where \(F_j,q_j,r_j\ge0\), and \(F_j\) controls the **complete** receiver energy with the required horizon and cutoff uniformity. The second condition makes the iteration explicit; neither it nor the needed arithmetic recurrence is currently supplied by the ratio theorem.

This is not a license to choose disjoint sectors and add their energies. Different sector decompositions can overlap, and cross terms between stages may restore the entire lost cost. A useful theorem must specify the partitions, physical horizon, centering and all transition cross terms. It must not turn the proved good-row quantifiers \(\exists E\,\forall T\,\forall^\infty N\) into \(\exists E\,\forall N\,\forall T\).

The first meaningful advance would be a quantitative residual estimate that improves the currently proved power rate and survives a second scale transition. Re-proving a ratio tending to zero, or obtaining cancellation only after a complete-period average, would not establish that advance. This direction could supply the arithmetic estimate behind (C), but no such implication is asserted yet.

### Opportunity 3: compensate the width-to-ground-energy comparison

This is a narrower, valuable benchmark for the proposed field. It should be pursued as a bridge theorem, not advertised as RH progress by itself.

The present source proves ground-energy rate equality with width under a uniform bound on squared off-line depths in unit-height windows. A bound on the *number* of off-line copies is sufficient but stronger. Neither is proved necessary. Unconditionally, the available depth-square bound retains \(\log|T|\). See `OffLineDepthLocallyBounded`, `sum_sq_im_xiSpectralPoint_window_le` and `polarGroundEnergyRate_eq_zetaZeroWidth_of_offLineDepthLocallyBounded` in [TheWidthIsTheGroundEnergyRateWhenOffLineZerosDoNotCluster.lean](../../../formal/GaloisForLFunctions/SquareRootThreshold/TheWidthIsTheGroundEnergyRateWhenOffLineZerosDoNotCluster.lean).

There is an identifiable loss in that proof. On the smooth interior core, put

\[
a_q=\widehat u(-z_q),\qquad b_q=\widehat u(-\overline{z_q}),
\]

using the transform convention of the source and \(q\) ranging over zero copies, already counting multiplicity. Then

\[
Q_A(u)=\sum_q\Re(a_q\overline{b_q})
=\frac14\sum_q\bigl(|a_q+b_q|^2-|a_q-b_q|^2\bigr).
\]

The exact zero-form identity is in [CCMParityQuartetZeroSum.lean](../../../formal/GaloisForLFunctions/RHTower/CCMParityQuartetZeroSum.lean). The current lower bound uses \(\Re(a\bar b)\ge-|a-b|^2/4\), discarding the positive term. On-line zeros contribute only to the positive part.

**Research target.** After justifying separate summability on the smooth core, define \(E_\pm(u)=\tfrac14\sum_q|a_q\pm b_q|^2\). Can one derive, from the actual prime–Gamma–pole source, for every \(\sigma>\Delta\) a constant \(C_\sigma\ge0\), independent of \(A>0\) and of the smooth source \(u\) compactly supported inside \((-A,A)\), such that

\[
E_-(u)\le E_+(u)+C_\sigma e^{2\sigma A}\|u\|_2^2
\quad\text{for every }\sigma>\Delta,
\tag{G}
\]

without assuming bounded local off-line depth mass? Then extend the floor through the actual form completion.

(G) is the desired signed floor rewritten, not an independent input. The prospective mechanism is to estimate positive and negative sampling contributions *jointly*, instead of paying every negative contribution separately by local counting. It would close the reverse ground-rate inequality and give rate equality. It would **not** show that the common rate vanishes. Strict slack \(\sigma>\Delta\) matters: current bounds at the exact width contain polynomial factors in aperture.

Positive-background compensation already occurs in the synthetic [DilutedOffLineLatticeHidingLaw.lean](../../../formal/GaloisForLFunctions/SquareRootThreshold/DilutedOffLineLatticeHidingLaw.lean). Thus retaining the positive part is not itself a novel theorem. The new content must be a uniform source-specific comparison, or a genuinely weaker structural hypothesis verified independently for the arithmetic source. Nor may the argument subtract two divergent completed energies; the smooth-core identity and the passage to the form domain require separate justification.

## Directions I would not count as new opportunities. 
Bare first-contact noncrossing, generic Schur complements, source reconstruction, or another spectral realization at finite aperture are already extensively developed. The corpus locates first contact in a completion-boundary kernel and has finite movable-source coordinates; this does not prove that the kernel is impossible. See [CCMFirstContactSourceKernel.lean](../../../formal/GaloisForLFunctions/RHTower/CCMFirstContactSourceKernel.lean) and [SuzukiTaMovableReducingExceptionalBlock.lean](../../../formal/GaloisForLFunctions/RHTower/SuzukiTaMovableReducingExceptionalBlock.lean).

I would also reject the shortcut “hidden off-line configurations crystallize; zeta is noncrystalline; therefore RH.” The inspected rigidity theorem concerns fixed-period, fixed-depth synthetic profiles under a scaling limit. The actual anti-crystal statement uses eventual strict ordering of zero copies, which already excludes reflected off-line pairs with the same ordinate. The hypotheses needed for the proposed combination are not available. See [ProfileRigidityAtTheSquareRootThreshold.lean](../../../formal/GaloisForLFunctions/SquareRootThreshold/ProfileRigidityAtTheSquareRootThreshold.lean) and [ZetaZeroAntiCrystalLaw.lean](../../../formal/GaloisForLFunctions/RHTower/ZetaZeroAntiCrystalLaw.lean).

Finally, there is no reason yet to prioritize a new infinite-dimensional carrier over the signed-energy work. Avoiding the finite-carrier no-go is only an admission condition. One would still need source construction, a domain, a renormalized trace/determinant identity, and positivity independent of the target divisor. Naming an infinite or nonintegral object supplies none of these.

## New field - research programme
**What the proposed field would study.** Arithmetic continuation and critical energy would organize the surviving questions around the following object:

\[
\text{exact arithmetic source}
\quad+\quad
\text{complete signed response}
\quad+\quad
\text{scale/damping evolution}
\quad+\quad
\text{a specified critical norm}.
\]

Its central question would be: **which independently verifiable arithmetic relations prevent critical energy from accumulating under repeated extension?** This differs from determining the source, proving convergence at each finite cutoff, or finding a positive representation after assuming admissibility.

Its objects would include:

- Signed arithmetic weights and their divisor responses, with the exact mean or pole subtraction included. Möbius, Liouville and Mangoldt sources should remain distinct until a proved transport identifies their relevant energy.
- Families indexed jointly by physical horizon, coefficient cutoff, damping and aperture. None of these parameters may disappear through an unstated order of limits.
- Complete quadratic forms and their mixed bilinear terms. A decomposition is useful only with its interaction terms and correction terms attached.
- Prime dilations and additive translations acting on the same source. The interaction with the physical origin matters: stationary translated moments alone are insufficient.
- Closed form domains and source-defined embeddings between them, including the possibility of boundary concentration, loss of mass or loss of pole data.
- Countermodel families sharing selected observables with the arithmetic source. They identify exactly which information an estimate uses.

Its language should make distinctions currently easy to blur explicit:

| Term | Meaning that must accompany it |
|---|---|
| Admission | Finiteness of a named complete norm, with its quantified parameters |
| Continuation | Propagation of admission through a parameter interval with a stated bound |
| Compensation | A bound on a combined signed expression, not smallness of its separate terms |
| Observation | A specified map from source to data, together with its indistinguishability class |
| Stability | A quantitative estimate in the norm required by the receiver |
| Completion | A specified topology and a theorem showing which source, pole and sign data survive |
| Selectivity | A proved reason the estimate holds for the actual source and fails for an explicit excluded model |

These definitions are not proposed new mathematical axioms. They specify what a theorem must say. The available algebraic identities—such as \(\mu*1=\delta_1\), \(\Lambda*1=\log\), the exact tangent law and the explicit formula—are starting facts. Global positivity, small-damping admission, purity and zero width must remain conclusions.

**Foundational principles and acceptance criteria.** I would require the following of work in this program.

1. **Exact source before closure.** Every coefficient, prime power, Gamma term and pole term must be fixed before claiming an estimate. A favorable source selected from the zeros is not an arithmetic construction.
2. **Keep signs until their cancellation is paid.** Absolute values are allowed where their loss is proved acceptable. The default object is the complete signed pairing, not a sum of separate upper bounds.
3. **Uniformity is part of the theorem.** State \(\forall\varepsilon\,\exists C_\varepsilon\,\forall T\) explicitly when that is what is needed. A horizon-dependent damping band or a complete-period limit is a different result.
4. **Distinguish recovery from control.** An injective observation map, even a complete invariant, requires a stability estimate before it can bound critical energy. Exact recovery by analytic continuation alone supplies no such estimate.
5. **Preserve the required norm.** An \(H^1\) estimate cannot silently pay an \(L^2\)-normalized ground floor. Pointwise convergence cannot replace convergence in the receiver's energy.
6. **Test selectivity against the known adversaries.** Shifted zeta pairs, altered prime weights, parity partners and coherent blocks must fail a named hypothesis, not be dismissed after the proof.
7. **Pay both ends of a limit.** The origin, infinity, fractional-part terms and polar constraints belong to the same accounting. A missing boundary term can contain the whole obstruction.
8. **Separate endpoint success from bridge success.** A better dictionary, a larger certified aperture or equality of two unknown rates is useful, but it is not a smaller zero width.
9. **Require a positive survivor from failure.** If continuation fails, extract a sharp growth law, obstruction measure, structural classification or weaker valid estimate. Do not retire a mechanism with only another negative slogan.

No principle here asserts that arithmetic must exhibit the needed cancellation. That assertion is the research problem.

**Research questions and first deliverables.** A field should offer tractable work before its RH endpoint.

| Question | Concrete first deliverable | RH-level destination |
|---|---|---|
| Can complete energy continue through decreasing damping? | Exact finite-horizon signed-work identity; classify which terms obstruct a bound independent of horizon | Prove (C), or its non-linear continuation variant, on every compact positive-damping interval |
| Can proved anti-alignment be propagated? | Quantitative complementary-sector residual surviving two compatible scale transitions | A complete recurrence such as (R), with every cross term paid |
| Can positive spectral mass pay negative depth mass? | A compensated sampling theorem under an independently checkable hypothesis permitting unbounded local depth-square mass | Establish (G); then seek a separate arithmetic mechanism forcing zero rate |
| Which observations control energy stably? | Quantitative recovery with error amplification and required observation order stated | Energy bounds from signed, origin-sensitive arithmetic observations |
| Which completion defects can survive exact source laws? | Classify pole/origin defects for a specified actual source transport | Rule out the exact boundary defect preventing an all-aperture sign |
| Can pointwise constructions reach the needed cone? | Prove the remaining affine-slice estimate at a larger finite aperture | An all-aperture transfer with source-specific control of every new prime atom |

For the last row there is already a precise intermediate problem. Even-window positivity splits into nonnegativity of Markov energy on zero-cosh-moment tests and the bound \(\mathrm{MarkovEnergy}\ge-2\) on unit-cosh-moment tests. The second affine slice cannot be discarded after proving the polar sector. See [TheBlindMinimumIsTheEvenPolarGroundEnergyBelowTheFirstPrime.lean](../../../formal/GaloisForLFunctions/SquareRootThreshold/TheBlindMinimumIsTheEvenPolarGroundEnergyBelowTheFirstPrime.lean). Extending that certificate is measurable progress, although finite aperture still cannot decide RH.

For observation stability, the first test is particularly sharp: any proposed theorem depending only on stationary translated moments is already excluded. A theorem using finitely many logarithmic moments must state how its constants and remainder depend on the number of moments, the damping and the horizon. “All moments determine the row” cannot be used as a bounded inverse theorem.

For compensation, the corpus already demonstrates why separate budgets can mislead: finite coherent repair can cancel all integer atoms at bounded archimedean cost even when atomwise budgets diverge. But that repair family has a positive energy floor, so bounded repair cost does not mean vanishing defect. See [WeilWorkExposingRayCoherentCompletion.lean](../../../formal/GaloisForLFunctions/RHTower/WeilWorkExposingRayCoherentCompletion.lean). The program must improve rates and preserve the right complete energy, not merely rediscover that cancellation exists.

## Recommended sequence.
Begin with the damping pairing, because its source, finite-horizon derivative and RH receiver are already precise. Derive the complete arithmetic identity and test it against the owned no-gos before introducing any new operator. Next, investigate whether the complementary-sector cancellation controls that pairing quantitatively. Pursue the compensated ground-rate comparison as an independent benchmark with a useful non-RH outcome. Keep first-contact and singular-carrier constructions available only when a specific new arithmetic regularity or sign estimate appears.

Success would be a theorem that propagates an independently established arithmetic bound beyond the point where present estimates lose its signs, uniformity or norm. At present I can identify that missing theorem more precisely, and explain why several familiar obstructions do not refute it. I cannot supply its proof, or conclude that any proposed mechanism closes RH.

## Follow-up: Opportunity 1, worked arithmetic audit

**Verdict so far.** The signed continuation target survives, but no unconditional producer has been proved. Its all-positive-damping version is equivalent to RH. The investigation does produce an exact arithmetic evolution, a centered compact semigroup in a weaker norm, and several sharply scoped obstructions. None should be counted as continuation in the critical norm. The in-progress [research card](../../drafts/pipeline/1-in-progress/astra-opportunity1-signed-damping-continuation.md) and [threshold](../../../logs/astra-opportunity1-threshold.txt), [arithmetic](../../../logs/astra-opportunity1-arithmetic.txt), and [literature](../../../logs/astra-opportunity1-literature.txt) logs preserve the proofs and search history.

Throughout this follow-up, \(t>0\) denotes damping, not physical position. Write
\[
f_t(n)=\sum_{d\mid n}\mu(d)d^{-t},\quad
S_t(n)=\sum_{k\le n}f_t(k),\quad
u_t(n)=S_t(n)/n,\quad v_t(n)=A_t(n)/n.
\]
The critical energy is \(E_T(t)=\sum_{n\le T}w_nv_t(n)^2\), with \(w_n=n/(n+1)\). Thus its sequence weight is comparable to counting measure; it is much stronger than convergence to zero or a harmonic occupation norm.

### 1. Exact continuation threshold

**Paper deduction.** Let \(C(a)\) denote the proposed inequality on \([a,1/2]\). Then
\[
a>\Delta\ \Longrightarrow\ C(a)\ \Longrightarrow\ a\ge\Delta,
\qquad \Delta=\Theta-\tfrac12.
\]
The endpoint \(a=\Delta>0\) is not decided by this argument. In particular, all positive-\(a\) instances of (C) are equivalent to RH.

The reverse implication follows from the original backward integration and the corpus's admission-accumulation theorem. For the forward implication, the literal complex-damped prefix is holomorphic with values in the pronic Hilbert space on \(\Re z>\Delta\). Here is the required justification, beyond scalar holomorphy. On compact damping sets in that half-plane, the corpus's reciprocal-zeta and numerator estimates give a uniform square-integrable majorant for the Mellin quotient on the critical line. Fixed Paley–Wiener inversion therefore gives a Hilbert-holomorphic Fermi source. Its identity with the literal arithmetic source follows from the absolutely convergent Mellin identity on a sufficiently right line and uniqueness. A bounded backward dyadic inverse recovers the centered source; a fixed weighted cell-average operator, **with the fractional-part correction retained**, recovers the discrete prefix. Banach-valued Cauchy estimates then bound every damping derivative on compact intervals above \(\Delta\).

Consequently \(M_a=\sup_{t\in[a,1/2]}\|B_t\|_{\rm pronic}<\infty\) when \(a>\Delta\), and
\[
-E'_T(t)\le2M_a\sqrt{E_T(t)}\le M_a(1+E_T(t)).
\]
This proves the stated threshold, not a zero-width estimate. The key existing inputs are [the Hardy quotient bounds](../../../formal/GaloisForLFunctions/RHTower/TheDampedMoebiusMellinQuotientIsHardyRightOfTheZeroAbscissa.lean), [the complex-source Mellin identity](../../../formal/GaloisForLFunctions/RHTower/PMPowerDampedMobiusComplexBoundary.lean), and [bounded dyadic inversion](../../../formal/GaloisForLFunctions/RHTower/PMPowerDampedMobiusCenteredEnergy.lean). The Hilbert-holomorphic synthesis has a paper proof; it has not been formalized in this investigation.

The parent analytic family, unconditional half-damping admission, and cofinal-admission receiver already appear in Burnol's work. Compact-parameter derivative control follows by analytic-family estimates; it is not an independent arithmetic producer. Burnol also distinguishes a square-integrable boundary expression from identification with the literal source. [Burnol, §4](https://arxiv.org/pdf/math/0202166)

### 2. An exact arithmetic Markov evolution

The product formula gives \(f_t(n)=\prod_{p\mid n}(1-p^{-t})\ge0\). Combining differentiation with the logarithmic convolution law yields
\[
f'_t(n)+f_t(n)\log n
 =\sum_{d\mid n}\Lambda(d)f_t(n/d).
\]
Finite summation by parts therefore gives
\[
S'_t(n)=\sum_{d\le n}\Lambda(d)S_t(\lfloor n/d\rfloor)
 +\sum_{1\le k<n}S_t(k)\log\frac{k+1}{k}
 -S_t(n)\log n.
\tag{M}
\]
Define the downward generator, for \(1\le k<n\), by
\[
L_{nk}=\frac{k}{n}\left(
 \sum_{\substack{2\le d\le n\\\lfloor n/d\rfloor=k}}\Lambda(d)
 +\log\frac{k+1}{k}\right),\qquad L_{nn}=-\log n.
\]
All off-diagonal rates are nonnegative. The identities
\[
\sum_{d\le n}\Lambda(d)\lfloor n/d\rfloor=\log(n!),\qquad
\sum_{k<n}k\log\frac{k+1}{k}=n\log n-\log(n!)
\]
prove zero row sums. Thus \(u'_t=Lu_t\), while
\[
v'_t=Lv_t-r'_t\mathbf1.
\tag{MC}
\]
The generator is independent of damping. State 1 is absorbing; the initial raw mean is \(u_0(n)=1/n\).

For any finite horizon, its exact energy balance is
\[
E'_T=
\sum_{k\le T}\left(\sum_{n=k+1}^Tw_nL_{nk}-w_k\log k\right)v_t(k)^2
-\sum_{n\le T}w_n\sum_{k<n}L_{nk}(v_t(k)-v_t(n))^2
-2r'_t\sum_{n\le T}w_nv_t(n).
\tag{MF}
\]
The middle term is forward dissipation. Backward continuation must pay it together with the signed flux and density term. These are not three separately bounded budgets. For a nonzero finitely supported sequence, both the uncentered flux and jump-energy sums grow linearly with \(T\), although their difference cancels exactly outside its support. Indeed PNT gives \(L_{nk}\to1/(k+1)\) for fixed \(k\). Dropping this cancellation manufactures a divergence.

The underlying divisor chain has recent precedent: Alexeev and coauthors study the downward von Mangoldt process, with rates \(\Lambda(q)\) from \(n\) to \(n/q\), and a continuous zeta process. Our normalized-prefix generator is its Cesàro conjugate. Their occupation estimates do not supply the critical signed-energy bound here. [Alexeev et al., §1 and §10.2](https://arxiv.org/pdf/2605.00301)

### 3. Transition kernel, entrance law, and the paid tail

**Paper deduction.** The transition probabilities of \(L\) are
\[
K_t(n,k)=\frac{k}{n}\left[
 k^{-t}S_t(\lfloor n/k\rfloor)
 -(k+1)^{-t}S_t(\lfloor n/(k+1)\rfloor)\right],\quad k\le n.
\tag{K}
\]
For each finite truncation, let \(F_{nd}=\lfloor n/d\rfloor\) and \(D_{nn}=n\). Finite Abel summation proves
\(DLD^{-1}=F\operatorname{diag}(-\log d)F^{-1}\), which gives the semigroup identity and formula (K). Positivity follows from increasing \(S_t\) and decreasing \(k^{-t}\). Telescoping reduces row sums to
\(n^{-1}\sum_{k\le n}k^{-t}S_t(\lfloor n/k\rfloor)=1\), using the exact convolution \(f_t*(k^{-t})=1\).

Absolute convergence of the density series gives the entrance law
\[
K_t(n,k)\longrightarrow
\pi_t(k)=r_tk\bigl(k^{-1-t}-(k+1)^{-1-t}\bigr).
\]
It has total mass 1; hence coordinate convergence upgrades to total variation. Semigroup consistency gives \(\pi_tK_s=\pi_{t+s}\), and \(\pi_t(1/k)=r_t\).

This exposes a sharp failure of total variation as a receiver estimate. A chain started at \(n\) never exceeds \(n\), while
\[
\pi_t(k>n)
=r_t\left((n+1)^{-t}+\sum_{k\ge n+2}k^{-1-t}\right)
\ge r_t(n+1)^{-t}.
\]
Thus an unsigned total-variation majorant is not square summable when \(0<t\le1/2\). But the **actual observable** has the exact omitted tail
\[
\sum_{k>n}\frac{\pi_t(k)}k=r_t(n+1)^{-1-t}.
\tag{T}
\]
This tail and its damping derivative have uniformly finite critical energy on every compact positive-damping interval. The tail is paid. The remaining interior signed discrepancy is not. Conditioning the entrance law on \(k\le n\) changes its normalization and can reintroduce the slower tail; it is not a harmless replacement.

### 4. What the centered semigroup does—and does not—prove

Set \(R_t=K_t-\mathbf1\otimes\pi_t\). Entrance consistency gives \(R_tR_s=R_{t+s}\), and
\[
v_t=R_th,\qquad h(n)=1/n.
\]
For \(t>0\), total-variation convergence shows that \(R_t\) maps bounded sequences into \(c_0\), the sequences tending to zero. On \(c_0\), it is a strongly continuous semigroup, bounded by 2 in supremum norm. On real sequences it contracts the equivalent oscillation norm. Strong continuity follows first for finite support from bounded jump rates into each finite set, then by density. It is not strongly continuous on all bounded sequences: \(R_t\mathbf1=0\).

Every \(R_t:c_0\to c_0\), \(t>0\), is compact. Truncating its output rows gives finite-rank operators, with error bounded by
\(\sup_{n>N}\|K_t(n,\cdot)-\pi_t\|_1\to0\).
Its nonzero spectrum on complex \(c_0\) is exactly
\[
\{d^{-t}:d\ge2\}.
\]
The explicit eigenvectors are
\[
g_d(n)=\frac{\lfloor n/d\rfloor}{n}-\frac1d
       =-\frac{\{n/d\}}n,\qquad R_tg_d=d^{-t}g_d.
\tag{G}
\]
To exclude other nonzero eigenvalues, use compactness and an eigenvector \(f\). Subtract \(f(1)\); the first nonzero coordinate of the resulting triangular eigen-equation forces \(\lambda=d^{-t}\). The case \(\lambda=1\) would make the original sequence constant and hence zero in \(c_0\).

These sampled Nyman–Beurling profiles are already present in the corpus's [fractional-part expansion](../../../formal/GaloisForLFunctions/RHTower/PMPowerDampedMobiusNymanSeries.lean). For \(d\ge2\), their norms satisfy
\[
\|g_d\|_\infty=1/d,\qquad
\|g_d\|_{\ell^2(w)}^2\asymp1/d.
\]
The second estimate follows by splitting at \(n=d\): the head contains \(d-1\) constant values \(-1/d\), and the tail is bounded by \(\sum_{n\ge d}n^{-2}\). Consequently
\[
v_t=\sum_{d\ge2}\mu(d)d^{-t}g_d
\]
converges absolutely in \(c_0\) for all \(t>0\), whereas the unsigned Hilbert triangle estimate stops at \(t>1/2\).

This supplies a precise generic no-go: no finite backward logarithmic-energy coefficient can work uniformly on the whole linear span of the \(g_d\). Their backward quadratic growth rates are \(2\log d\), unbounded. For the affine bound \(b(1+E)\), scale each mode to the same positive energy at the damping being tested; the unscaled profiles alone do not refute that bound. Changing to another fixed positive quadratic norm preserves the eigenrates. The same normalization defeats a generic Osgood bound. It does **not** defeat a bound restricted to the single Möbius orbit.

There is also no bounded imaginary-time extension of these eigenmultipliers on \(c_0\). The normalized vectors \(e_d=dg_d\) have norm 1 and converge coordinatewise to the constant \(-1\). For any bounded linear operator \(T:c_0\to\ell^\infty\), each output coordinate is an \(\ell^1\) functional, so \((Te_d)(n)\) converges by dominated convergence. If \(Tg_d=d^{-i\tau}g_d\), that coordinate equals \(-d^{-i\tau}\) for \(d>n\), which has no limit when \(\tau\ne0\). This is a \(c_0\) obstruction, not a substitute for a Hilbert-space theorem.

The interior nevertheless has a stronger positive result: \(R_z\) is compact and operator-holomorphic on complex \(c_0\) for every \(\Re z>0\). Here the same formulas define a complex kernel and entrance functional. Fix \(0<a<1\) below the real parts on a compact parameter set. Since
\[
|f_z(m)|\le\sum_{d\mid m}d^{-a},\qquad |S_z(N)|\le\zeta(1+a)N,
\]
splitting the kernel difference into a power difference and a prefix increment gives
\[
\sup_n\sum_{k>K}|K_z(n,k)|
\le\zeta(1+a)\left(
 |z|\sum_{k>K}k^{-a-1}+\frac1{a(K+1)^a}\right).
\]
The second term follows by summing the prefix increments over \(m\le n/(K+1)\) and exchanging \(m=d\ell\). Uniform tails and locally uniform coordinate limits yield locally uniform convergence of centered rows in total variation. Rectangular finite-rank truncations therefore converge locally in operator norm, proving both compactness and holomorphy. These bounds deteriorate as \(a\downarrow0\); no bounded-sector estimate at zero is asserted. Interior analyticity in \(c_0\) still supplies no critical Hilbert bound.

The compact semigroup, spectrum and domain statements above are paper results, not newly compiled Lean theorems. Standard incidence conjugation and Markov oscillation methods have established parent theories. Bounded searches did not establish priority for this exact arithmetic package. [Lorek–Szekli](https://link.springer.com/article/10.1007/s11134-012-9284-z), [Gaubert–Qu](https://arxiv.org/abs/1302.5226)

### 5. Exact scalar cancellation isolates the remaining covariance

There is a stronger source-specific fact than stochastic positivity. Define
\(\ell(v)=\sum_{n\ge1}v(n)/(n+1)\) on its absolute-convergence domain. The kernel identity
\[
\sum_{n\ge1}\frac{\{n/d\}}{n(n+1)}=\frac{\log d}{d}
\]
comes from a finite harmonic-sum telescope. Absolute Fubini in the Möbius expansion then gives
\[
\ell(v_t)=\sum_{n\ge1}\frac{A_t(n)}{n(n+1)}=r'_t.
\tag{H}
\]
The first-pronic-moment theorem is already in [DampedMoebiusFirstMomentAndChebyshevTangentBridge.lean](../../../formal/GaloisForLFunctions/TransHorizonIncidenceMechanics/DampedMoebiusFirstMomentAndChebyshevTangentBridge.lean). Thus (MC) is the homogeneous boundary-subtracted evolution \(v'_t=(L-\mathbf1\otimes\ell)v_t\), not an unidentified external forcing. On finite support this is also the \(c_0\) generator. No assertion that finite support is a generator core is needed.

Differentiating the absolutely convergent coefficient series gives the further paper identity
\[
\sum_{n\ge1}\frac{B_t(n)}{n(n+1)}=r''_t,
\]
with absolute majorant \(\sum_d(\log d)^2/d^{1+a}\) uniform for \(t\ge a>0\). Therefore
\[
E'_T(t)=2\sum_{n\le T}\frac{B_t(n)}{n(n+1)}
 +2\sum_{n\le T}\frac{(A_t(n)-1)B_t(n)}{n(n+1)}.
\tag{W}
\]
The first term is paid uniformly on compact damping intervals. The second is the precise unpaid covariance.

This is not an information-theoretic failure of all scalar traces. The corpus already proves that the entire logarithmic-moment hierarchy determines a damped coefficient sequence at every \(d\ge2\); the remaining unit mass is invisible to the receiver. For the actual orbit these moments are, up to the derivative signs, the hierarchy \(r_t^{(m+1)}\). Thus every receiver parity pair is separated by some moment. What is missing is a quantitative reconstruction estimate in critical energy, with constants that pay (W). Uniqueness by analytic continuation supplies no such stability estimate. See [LogarithmicMomentsAreACompleteReceiverInvariant.lean](../../../formal/GaloisForLFunctions/TransHorizonIncidenceMechanics/LogarithmicMomentsAreACompleteReceiverInvariant.lean), especially eq_add_unitMass_of_logMoments_eq and exists_logMoment_ne.

At zero damping, the continuous finite-coordinate limits are \(A_0(n)=1\) and \(B_0(n)=\psi(n)-n\). Existing absolute harmonic cancellation proves
\[
\sum_{n\ge1}\frac{\psi(n)-n}{n(n+1)}=-2\gamma.
\]
Hence the **iterated** limit of finite-horizon signed work is
\[
\lim_{T\to\infty}\lim_{t\downarrow0}E'_T(t)=-4\gamma.
\tag{Z}
\]
This is not differentiation of the infinite energy. The source theorem is `hasSum_completedPrimePolarGammaHarmonicCharge_zero` in [CCMFUSuzukiCompletedRieszGraphEnergy.lean](../../../formal/GaloisForLFunctions/RHTower/CCMFUSuzukiCompletedRieszGraphEnergy.lean).

The distinction is substantive: for \(D_T(t)=\sum_{n\le T}(A_t(n)-1)^2/[n(n+1)]\), the corpus proves
\[
D_T(t)/t^2\longrightarrow
\sum_{n\le T}\frac{(\psi(n)-n)^2}{n(n+1)},
\]
and the right-hand horizons are unbounded. Finite signed first work coexists with singular residual curvature. See `tendsto_dual_residual_div_sq` in [DampedChebyshevTangentFormOfTheReceiver.lean](../../../formal/GaloisForLFunctions/BezoutValuationIncidence/DampedChebyshevTangentFormOfTheReceiver.lean).

There is a sharper unconditional boundary statement. Put \(D(t)=\sup_TD_T(t)\), allowing \(+\infty\). For every critical-line zero \(\rho\) of multiplicity \(m\ge1\), and every \(c>0\),
\[
\liminf_{t\downarrow0}\frac{D(t)}t
\ge
\frac{2c\bigl[1-(c/(c+1))^m\bigr]^2}{|\rho|^2}.
\tag{Cusp}
\]
In particular, \(c=1\) gives a lower bound at least
\(\kappa_\rho=1/(2|\rho|^2)>0\). Thus the residual has at least linear energy growth, stronger than the failure of a uniform quadratic tangent bound.

Here is a proof that does not assume admission. For each damping with \(D(t)<\infty\), the exact step residual
\[
q_t(x)=S_t(\lfloor x\rfloor)-r_t\lfloor x\rfloor-1,\qquad x\ge1,
\]
has squared norm \(D(t)\) in \(L^2(dx/x^2)\). Its Mellin transform is holomorphic for \(\Re s>1/2\), and continuation from \(\Re s>1\) gives
\[
F_t(s)=\frac{\zeta(s)\bigl(\zeta(s+t)^{-1}-r_t\bigr)-1}{s}.
\]
The floor correction is retained: its transform is \(r_t\zeta(s)/s\).
Cauchy–Schwarz gives
\[
D(t)\ge(2\Re s-1)|F_t(s)|^2.
\]
Evaluate at \(s=\rho+ct\). Local factorization at the isolated zero gives
\[
F_t(\rho+ct)\longrightarrow
\frac{(c/(c+1))^m-1}{\rho}.
\]
For sufficiently small positive \(t\), the denominator zero at \(\rho\) has been shifted away from this evaluation point. Dividing by \(t\) proves (Cusp). When \(D(t)=+\infty\), the lower bound is automatic; continuation was needed only separately at the finite-energy dampings. No interval of admission was assumed.

This object is classical: \(F_t=H_t-1/s\) for the explicit damped Hardy-space family in [Bagchi's 2005 survey, proof of Theorem 2](https://www.isibang.ac.in/~statmath/eprints/2005/isibc200535.pdf). The lower bound above is a deduction from local zero factorization and Hardy evaluation, not a claim of a new proof mechanism or established novelty.

The trace discrepancy can now be quantified. Absolute convergence of (H) gives, in extended values,
\[
D(t)=E(t)-2r'_t+1,\qquad E(t)=\sup_TE_T(t).
\]
The reciprocal-zeta expansion gives \(r'_t=1-2\gamma t+O(t^2)\). Hence
\[
\liminf_{t\downarrow0}\frac{E(t)-1}{t}
\ge-4\gamma+\kappa_\rho>-4\gamma.
\]
Thus (Z) cannot equal a finite right derivative of the full energy. Moreover, the finite-horizon identity \(D'_T=2\sum_{n\le T}(A_t(n)-1)B_t(n)/[n(n+1)]\) implies
\[
\limsup_{t\downarrow0}\sup_T
\sum_{n\le T}\frac{(A_t(n)-1)B_t(n)}{n(n+1)}
\ge\kappa_\rho/2.
\]
Otherwise integrating a smaller uniform upper bound from zero would contradict (Cusp). Each fixed-horizon covariance tends to zero, so positive work escapes to growing horizons. Its sign matters: this is a positive-work lower bound at zero, not a failure of the negative-work estimate (C) on compact positive-damping intervals. These sharper boundary statements are paper results awaiting formalization.

### 6. Two additional shortcuts fail precisely

**Interpolation from the admitted zero-damping source fails at its boundary.** The corpus proves `exists_pmComplexDampedFermiSource_imaginary_memLp_iff_zero`: every sufficiently small nonzero imaginary damping is inadmissible. Discrete critical admission would imply Fermi admission by the fractional correction and bounded dyadic difference, so the same obstruction applies to the discrete source. The real points (0) and (1/2) do not supply the vertical boundary bounds required by three-lines interpolation. Multiplying by a nonvanishing Gaussian does not turn infinite Hilbert norms into finite ones. [Complex boundary theorem](../../../formal/GaloisForLFunctions/RHTower/PMPowerDampedMobiusComplexBoundary.lean)

**A generic subpower Möbius-block bound already contains RH.** For
\(G_{D,M}=\sum_{D<d\le M}\mu(d)g_d\), \(D\le M\le2D\), its first \(D\) coordinates equal \(-\sum_{D<d\le M}\mu(d)/d\). Consequently
\[
\|G_{D,M}\|_{\ell^2(w)}^2
\ge\frac D2\left|\sum_{D<d\le M}\frac{\mu(d)}d\right|^2.
\]
A bound \(\|G_{D,M}\|\le C_\delta D^\delta\) for all partial blocks and every \(\delta>0\) would therefore give half-power Mertens bounds by Abel summation, then RH. This does not make block cancellation circular as a conclusion; it forbids treating that estimate as a routine input.

Exact dilation conservation also does not finish the work:
\[
\sum_{j\ge1}j^{-t}\mathcal A_t(x/j)=-\{x\}.
\]
It follows absolutely from \(f_t*(j^{-t})=1\) and \(r_t\zeta(1+t)=1\). Applying it to the interior transition discrepancy returns the original fractional-part source. It identifies the cancellation required; it does not bound it in the critical norm.

The stronger owned block theorems were also checked. Their improvement is real: for each fixed \(\delta>0\), sufficiently large \(Q\) permits uniform estimates over all eligible growing prime packets and coefficients, with primes above a logarithmic threshold. The dual estimate also retains all sign choices. However, cubic and quartic errors remain; no rate permits choosing \(\delta=\delta(Q)\); and the estimate has neither all composite/cofactor interactions nor the differentiated damping weights needed in (W). Its normalization is the large-sieve packet scale, which can exceed complete energy by an unbounded factor. See [the Möbius Type-II improvement](../../../formal/GaloisForLFunctions/BezoutValuationIncidence/MoebiusBlockBeatsTheTypeTwoBarrier.lean) and [the actual-row dual bound](../../../formal/GaloisForLFunctions/BezoutValuationIncidence/DualNormOfTheActualRowsBeatsTheLargeSieve.lean).

The complementary-sector proof likewise uses more than a qualitative Mertens estimate. For fixed \(0<t<1/2\), its remainder-energy argument gives a constant term plus \(O_t(P^{(1-2t)/2})+O_t(P^{1-2t}/\log^8P)\); the finite denominator approximation also contributes \(O_t(P^{1-3t})\). These still allow positive-power growth. Their pointwise damping asymptotics cannot be differentiated without new uniform estimates. Finally, the owned short-window power-saving statement is equivalent to \(\Theta<1\); its proof transfers an assumed saving \(\delta\) at window exponent \(\alpha\) to zero abscissa at most \(\max(1-\delta/2,\alpha)\). It does not prove that saving. [Complementary cancellation](../../../formal/GaloisForLFunctions/RHTower/PMRamanujanComplementaryCancellation.lean), [short-window equivalence](../../../formal/GaloisForLFunctions/BezoutValuationIncidence/ShortWindowMoebiusSavingIsTheQuasiRiemannHypothesis.lean)

### 7. A quantitative survivor if the width were positive

**Paper deduction, not yet formalized.** Put
\[
g(t)=\limsup_{T\to\infty}\frac{\log(1+E_T(t))}{\log T}.
\]
Then
\[
g(t)\le2\max(\Delta-t,0),
\]
with equality outside the countable set of positive horizontal translations between two zeta zeros at the same ordinate. No equality is asserted at the exceptional translations.

For the upper bound, move the Hardy line to any
\(\max(1/2,\Theta-t)<\sigma<1\). This admits the centered source in
\(L^2(dx/x^{2\sigma+1})\). The backward dyadic inverse has norm at most
\((2^{1-\sigma}-1)^{-1}\); the discrete correction gives
\(E_T(t)\le C_\sigma(T+1)^{2\sigma-1}\). Let \(\sigma\) decrease to the indicated boundary. For the lower bound, an uncancelled zero \(\rho\) gives a genuine Mellin pole at \(\rho-t\). Any smaller energy-growth exponent would, by weighted summation and Cauchy–Schwarz, make the literal Mellin transform holomorphic through that pole. Countability isolates possible numerator-denominator cancellation.

Thus, if \(0<a<\Delta\), the unavoidable accumulated positive logarithmic work obeys
\[
\limsup_{T\to\infty}\frac1{\log T}
 \int_a^{1/2}\left[-\frac{E'_T(t)}{1+E_T(t)}\right]_+dt
\ge2(\Delta-a).
\]
Indeed the integral dominates
\(\log(1+E_T(c))-\log(1+E_T(1/2))\) for every \(c\in(a,\Delta)\); use a nonexceptional \(c\), then let \(c\downarrow a\). This is a subsequential lower bound, not an asymptotic equality or a claim for every large horizon.

### 8. Remaining obligation and formal status

The original opportunity is **not retired and not proved**. The strongest remaining target is a source-derived lower bound for the complete covariance in (W), or an explicitly comparable corrected energy with all correction work paid. It must exploit actual Möbius interactions; total variation, generic semigroup contraction, scalar traces and zero-width analytic regularity do not provide it.

The finite generator and exact energy balance are now formalized in [DampingWorkAsArithmeticMarkovBoundaryFlux.lean](../../../formal/GaloisForLFunctions/BezoutValuationIncidence/DampingWorkAsArithmeticMarkovBoundaryFlux.lean). The final targeted Lean audit exited 0 without warnings, and the module is wired into the BVI umbrella. The main result, hasDerivAt_pmPowerDampedDivisorDiscreteEnergy_markov, proves the derivative of the original energy equals the full signed flux minus nonnegative jump energy minus the exact density work. Its flux is expressed as finite jump sums; displayed incoming-column form (MF) is the paper reindexing of that identity. The module also proves the literal source ODE, centering law and rate conservation.

The iterated zero-damping signed-work trace is formalized in [ZeroDampingSignedWorkHasFiniteHarmonicTrace.lean](../../../formal/GaloisForLFunctions/BezoutValuationIncidence/ZeroDampingSignedWorkHasFiniteHarmonicTrace.lean). Its final targeted Lean audit exited 0 without warnings, and the module is wired into the umbrella. It proves absolute convergence to \(-4\gamma\) after taking damping to zero at each fixed horizon; it does not interchange the limits.

The finite transition kernel and entrance distribution are undergoing separate targeted formalization. The infinite-dimensional semigroup, analytic-family synthesis and energy-exponent laws above remain paper results. No full or umbrella build is being run. These auxiliary results do not close (C).
