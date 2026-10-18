# Foundational research programme

**Status:** research specification, 2026-10-18. No new theorem is claimed proved by this document.

Read [README.md](README.md) for motivation, notation, established foundations, and the distinction between local progress and RH-equivalent endpoints. This programme starts with an explicit source estimate, then asks which parts of its mechanism can be generalized.

## Research question and standard of evidence

Which independently verifiable features of an exact arithmetic source control the sign, mixed couplings, and stability of its complete spectral energy?

An answer must connect hypotheses on the source to an energy estimate. An abstract theorem assuming the desired positive metric, invariant cone, or critical cancellation does not supply that connection. Negative results also count when they identify a sharp boundary or a useful replacement hypothesis.

Use these status labels throughout the work:

| Label | Meaning |
|---|---|
| Existing corpus result | A declaration or recorded proof already exists. Recheck its precise hypotheses and current build before depending on it. |
| Classical input | A theorem from established mathematics, with an exact source and applicability check. |
| Derived consequence awaiting verification | An apparent consequence of existing results whose full argument and formal compatibility still need checking. |
| Proposed estimate / `[OPEN CORE]` | The mathematical work to be done. It may be true, false, already known, or weaker than the eventual application needs. |
| RH-equivalent endpoint | A final universal premise already known to imply and follow from RH in the route ledger. It cannot serve as an independent foundational assumption. |

The first success criterion is a complete local result below RH. The long-term success criterion is a mechanism that scales to independently verified global hypotheses. Do not conflate them.

## Ordered work packages

The identifiers below are proposed task identifiers, not Lean declaration names. Open a dedicated pipeline card when beginning each substantial mathematical task.

| Task | Dependencies | Deliverable and completion gate |
|---|---|---|
| APT-01: audit the starting point | None | A premise ledger for WL, RW, and the factorial pilot; every assumption classified and linked to an exact source. |
| APT-02: fix the source–energy dictionary | APT-01 | Exact domains, normalizations, reflection, multiplicities, and physical/spectral compatibility; reuse existing comparison machinery. |
| APT-03: calibrate mechanisms against controls | APT-01; refine with APT-02 | Known positive examples and obstructed examples, with an explicit list of retained and broken hypotheses. |
| APT-04: prove or refute the local sampling budget | APT-02; APT-03 guides falsification | A quantitative estimate for the actual factorial correction tail, or a sharp reason it fails and a replacement estimate. |
| APT-05: close the compact ramp application | Successful APT-04 or a substitute mixed estimate | Full energy convergence, eventual ramp margin, and the exact two-dimensional Gram conclusion. |
| APT-06: extract a source-level stability theorem | APT-03 and completed local results | A reusable theorem with independently checkable arithmetic hypotheses and nontrivial examples. |
| APT-07: address all directions and all scales | APT-06 plus new arithmetic input | A justified extension mechanism; identify the remaining RH-hard premise explicitly. |
| APT-08: evaluate a geometric realization | APT-01–03; independent longer-term track | A genuinely constructed arithmetic object or a useful partial construction, with positivity and spectral correspondence separately audited. |

Start APT-01 and APT-02 before creating new abstractions. APT-03 can develop alongside them. The first attempted new estimate should be APT-04. APT-07 and APT-08 are research directions, not scheduled promises of a solution.

## APT-01: audit premises and reuse prior work

Produce a small dependency table for each intended theorem:

1. What is the literal source, including gamma factors, poles, endpoint corrections, and support conditions?
2. Which identity transfers the physical expression to the spectral form?
3. Which quantitative estimate is still missing, with every quantifier written out?
4. Which inputs are unconditional, conditional, classical but unformalized, or merely proposed?
5. Does the conclusion improve a family-level result, or does it already quantify over the full RH criterion?

Audit these existing assets first:

- [WL receiver](../../../formal/GaloisForLFunctions/RHTower/ChebyshevDeficitPrimitiveOneSidedRH.lean) and [RW capacity identity](../../../formal/GaloisForLFunctions/RHTower/WeilMarkovPoleCapacity.lean).
- [Hilbert comparison](../../../formal/GaloisForLFunctions/RHTower/XiWeilLineConjHilbert.lean) and [spectral square summability](../../../formal/GaloisForLFunctions/RHTower/XiCompactSpectralSampling.lean).
- [Current factorial ramp card](../../drafts/pipeline/1-in-progress/factorial-ramp-diagonal-margin-2026-10-18.md) and [completed tail-growth card](../../drafts/pipeline/3-formalized/factorial-muntz-tail-archimedean-growth-2026-10-18.md).
- [Arithmetic Schur programme](../../drafts/pipeline/1-in-progress/arithmetic-schur-renormalization-law.md) and [geometric purity programme](../../drafts/pipeline/1-in-progress/deninger-closed-generator-hodge-weil-purity-universality-law.md).

**Completion gate:** no research task is described as “prove positivity” without a specific source, domain, quantitative target, and dependency boundary. Existing conditional receivers are not counted as new arithmetic progress.

## APT-02: fix the dictionary before adding abstractions

Use the normalization

\[
F_f(s)=\int_{\mathbb R}f(x)e^{(s-1/2)x}\,dx,
\qquad
\mathcal Z(f)=\sum_\rho m_\rho|F_f(\rho)|^2,
\]

and, on the proved domain,

\[
\mathcal W(f,g)
=\sum_\rho m_\rho F_f(\rho)\overline{F_g(1-\overline\rho)}.
\]

The zero sum counts multiplicities once: either sum distinct zeros with weights \(m_\rho\), or sum zero copies with no extra weight. Do not mix conventions. Use the known critical strip, not an assumed critical-line support.

Identify the evaluation map into \(\ell^2\), the reflection involution, and the existing theorem `norm_xiWeilPolarization_le`. Record exactly how each physical source is admitted and how its readout matches that theorem. The resulting comparison is

\[
|\mathcal W(f,g)|\le\sqrt{\mathcal Z(f)\mathcal Z(g)}.
\]

This inequality is already available. The work is compatibility and quantitative source control. In particular, \(\mathcal Z\) depends on the actual zero divisor; it is not automatically a practical arithmetic certificate. Bounds for it must come from independently established source estimates and unconditional information about the zeros.

Also record the finite arithmetic identity underlying the pilot. If \(w(k)=0\) for \(k>K\) and \(M\ge K\), then

\[
\sum_{m=1}^{M}\Lambda(m)\sum_{j=1}^{K}w(jm)
=\sum_{k=1}^{K}\log k\,w(k).
\]

It follows from \(\sum_{d\mid k}\Lambda(d)=\log k\), with the finite support conditions doing essential work. Reuse [ClampedPrimeLogResummation.lean](../../../formal/GaloisForLFunctions/BiScaleUncertainty/ClampedPrimeLogResummation.lean); audit the particular weight and normalization instead of proving a duplicate identity.

**Completion gate:** each equality is valid on the actual source class, including noncompact tails, and no omitted limit or boundary term is being called a convention.

## APT-03: calibrate against positive and obstructed examples

Before trusting a proposed structural principle, require it to distinguish examples whose behavior is already understood.

| Control | What it checks |
|---|---|
| A finite-dimensional positive block with explicit coupling | The Schur condition and proposed stability constants reproduce the exact sign threshold. This is an algebraic check, not evidence for arithmetic novelty. |
| Existing restricted Weil positivity and the factorial corrected family | The mechanism reproduces an established positive case without importing a stronger hypothesis. |
| A symmetry-preserving off-line zero model | Functional-equation symmetry alone is not misidentified as arithmetic positivity. State which Euler, pole, growth, and completion properties the model does or does not have. |
| The actual factorial polar and Gram terms | A genuine negative contribution cannot be absorbed into an error of smaller order. |
| Controlled changes to coefficients or archimedean data | The mechanism notices changes that alter the complete energy, rather than using only a common abstract operator description. |

Use the [off-line functional-equation models](../../../formal/GaloisForLFunctions/RHTower/EntireFunctionalEquationOffLine.lean), [compact orbit inertia](../../../formal/GaloisForLFunctions/RHTower/WeilCompactOrbitInertia.lean), and [polar/Gram obstruction](../../../formal/GaloisForLFunctions/BiScaleUncertainty/FactorialPolarGramScaleSeparation.lean) as existing controls. Do not claim they disprove positivity for a stronger arithmetic class whose hypotheses they do not satisfy.

Numerical work may locate a bad scale, a negative residual, or an incorrect asymptotic. A finite positive scan proves neither a uniform estimate nor a universal sign assertion. To refute a proposed bound rigorously, supply an analytic counterexample or certified error control where computation is essential.

**Completion gate:** every candidate mechanism comes with at least one serious attempted falsification and an explanation of what arithmetic feature makes its positive examples different.

## First pilot: the actual factorial correction tail

### APT-04: isolate the new estimate

Use the sources already defined by the factorial programme. Write \(N=n+1\), let \(r_n\) be its compact ramp, let \(G_n\) be its canonical boundary-corrected source, and let \(\eta_k\) be its normalized mollifier. Set

\[
H_{n,k}=\eta_k*G_n,
\qquad
U_{n,k}=\eta_k*(G_n-r_n),
\qquad
r_{n,k}=H_{n,k}-U_{n,k}=\eta_k*r_n.
\]

These are descriptive mathematical names for existing sources, not declarations that new Lean definitions already exist. Reconcile any reflection or indexing convention with the source files before using the identities. Reflection preserves the relevant ramp autocorrelation and diagonal, but mixed identities must still be checked in a consistent convention.

Existing inputs and their exact roles:

| Input | Status and use |
|---|---|
| \(F_{G_n}(\rho)=c_n/\rho\), where \(c_n=1/(2\sqrt N)\) | Existing corrected-source readout at nontrivial zeros; makes the corrected part small. |
| \(F_{H_{n,k}}(\rho)=F_{\eta_k}(\rho)c_n/\rho\) and \(\lvert F_{\eta_k}(\rho)\rvert\le e\) | Existing smoothing/readout facts, uniform in the smoothing parameter and zero height. |
| \(\sum_\rho m_\rho/\lvert\rho\rvert^2<\infty\) | Existing zero-side summability input; no RH assumption. |
| \(\operatorname{Re}\mathcal W(U_{n,k},U_{n,k})\ge c\log N/N\) | Existing eventual tail growth: sufficiently large \(n\), then sufficiently large \(k\), with a positive absolute constant. |
| Exact ramp diagonal and Gram decomposition | Existing identities; the remaining ramp margin is not yet supplied by them. |

Inspect [FactorialMuntzWeilSmoothing.lean](../../../formal/GaloisForLFunctions/BiScaleUncertainty/FactorialMuntzWeilSmoothing.lean), [FactorialMuntzZeroReadout.lean](../../../formal/GaloisForLFunctions/BiScaleUncertainty/FactorialMuntzZeroReadout.lean), [FactorialMuntzZeroSideLimit.lean](../../../formal/GaloisForLFunctions/BiScaleUncertainty/FactorialMuntzZeroSideLimit.lean), and [FactorialMuntzTailWeilGrowth.lean](../../../formal/GaloisForLFunctions/BiScaleUncertainty/FactorialMuntzTailWeilGrowth.lean).

The first three inputs suggest the immediate bound

\[
\mathcal Z(H_{n,k})\le\frac{C_H}{N},
\qquad
C_H=\frac{e^2}{4}\sum_\rho\frac{m_\rho}{|\rho|^2}<\infty.
\]

The [corrected-source certificate](../../../formal/GaloisForLFunctions/arithmetic-positivity-theory/FactorialCorrectedSampling.lean) proves summability and this uniform \(1/N\) scale on the literal zeta carrier. Its explicit constant uses a larger genus-one majorant instead of the displayed sharp reciprocal-square constant.

The required local target is:

> **[CERTIFIED STRONGER UPPER BOUND]** There are constants \(C_U>0\) and \(N_0\ge2\) such that, for every \(n\) with \(N=n+1\ge N_0\), every smoothing index \(k\) satisfies
> \[
> \mathcal Z(U_{n,k})\le C_U\frac{\log N}{N}.
> \]

The [dependency-closed paper proof](../../drafts/pipeline/2-fully-proven/arithmetic-positivity-factorial-log-sampling.md) and [actual-source Lean certificate](../../../formal/GaloisForLFunctions/arithmetic-positivity-theory/FactorialTailSampling.lean) prove the stronger bound \(\mathcal Z(T_n)+\mathcal Z(U_{n,k})\le C(1+\log N)/N\) for every \(n,k\), where \(T_n=G_n-r_n\) is the literal raw tail. Both zero sums are proved convergent. Constants are independent of both indices; no smoothing threshold is needed for this upper bound. The lower signed-energy bound retains its existing eventual smoothing quantifiers.

The paper proof also establishes sharpness in that eventual regime: signed tail energy and absolute square sampling both have order \(\log N/N\). An \(O(1/N)\) spectral budget is false for this family. The result is classified as a **bridge**, not an established novel general theory. The upper sampling theorem is certified; the assembled sharpness and relative-margin statements require their own certificates.

### Certified proof mechanism for the sampling budget

The argument uses classical complex analysis and logarithmic regularity. Its arithmetic input is the exact phase representation of the actual tail. The certificate preserves that identity and every scale quantifier through the following four steps.

1. **Sampling from unconditional zero counts.** Establish a sampling estimate of the form
   \[
   \mathcal Z(f)\le C_\delta
   \int_{-\delta}^{1+\delta}\int_{\mathbb R}
   \log(2+|t|)|F_f(\sigma+it)|^2\,dt\,d\sigma
   \]
   for readouts holomorphic on a neighborhood of the larger strip and with the required finite integral. The actual-tail certificate uses the mean-value inequality for \(|F_f|^2\), fixed-radius discs, and the unconditional \(O(\log(2+|t|))\) count of zeros in unit-height strips. [FactorialTailDiskSampling.lean](../../../formal/GaloisForLFunctions/arithmetic-positivity-theory/FactorialTailDiskSampling.lean) localizes the circle estimate to the actual half-plane. [ZeroDiskOverlap.lean](../../../formal/GaloisForLFunctions/arithmetic-positivity-theory/ZeroDiskOverlap.lean) uses `exists_xiUnitHeightPacket_global_log_bound` at every real height; the final sampling module applies the multiplicity-preserving dictionary in `WeilDeletionZeroSide.lean`.
2. **Weighted source norms.** For \(\sigma\in[-1/4,5/4]\), the paper proof writes the weighted raw tail as \(a_ne^{(1+\sigma)x}R_n(Ne^{-x})\mathbf1_{x\le0}\), with \(a_n\le15/\sqrt N\), \(|R_n|\le25/32\), and Lipschitz constant at most \(14\). These give squared mass \(O(1/N)\) and translation energy \(D_{n,\sigma}(h)\le C\min\{N^{-1},h\}\) for \(0<h\le1\), including the endpoint jump.
3. **Pay only a logarithm for zero density.** Integrate that minimum against \(dh/h\), splitting at \(h=1/N\). The [verified Fourier module](../../../formal/GaloisForLFunctions/arithmetic-positivity-theory/FactorialTailFourierEnergy.lean) uses the existing Gamma–Lévy identity and global logarithmic weight comparison to prove \(O((1+\log N)/N)\) Fourier energy uniformly over the enlarged strip. The [readout module](../../../formal/GaloisForLFunctions/arithmetic-positivity-theory/FactorialTailReadout.lean) certifies the Mellin–Fourier coordinate identification. The paper also gives an elementary cosine-integral proof of the same analytic transport.
4. **Pass through smoothing without losing uniformity.** [FactorialTailSampling.lean](../../../formal/GaloisForLFunctions/arithmetic-positivity-theory/FactorialTailSampling.lean) bounds the raw sum, then applies the exact convolution readout and critical-strip mollifier bound. This proves smoothed summability and the combined budget with constants independent of \(k\).

The zero-count input is classical. For a primary quantitative reference, see [Hasanalizade, Shen, Wong, *Counting zeros of the Riemann zeta function*](https://arxiv.org/abs/2107.06506). The unit-height \(O(\log T)\) bound follows from a counting formula with \(O(\log T)\) error; check the theorem's range and the finite-height remainder before importing it.

Two pitfalls deserve an early check. Endpoint jumps can invalidate an \(H^1\) estimate uniform under removal of smoothing; fractional regularity must be proved at an admissible exponent instead. Also, the existing low-frequency primitive estimate in [FactorialMuntzTailReadoutDecay.lean](../../../formal/GaloisForLFunctions/BiScaleUncertainty/FactorialMuntzTailReadoutDecay.lean) grows with height. It cannot by itself bound the entire zero sum.

**Sharp boundary and fallback.** The sharp logarithmic sampling scale rules out replacing the spectral budget by physical squared mass alone. For other families, a suitably uniform \(o(\log^2N/N)\) budget would still make this mixed comparison lower order than \(\log N/N\). If the independent comparison norm is too expensive, investigate the signed mixed pairing itself. Failure of a sufficient comparison estimate is not a negative Weil-energy theorem.

**Completion gate:** a dependency-closed paper proof or rigorous obstruction for the quantitative target, with all scale and smoothing quantifiers explicit. Search the literature before claiming novelty; established sampling or Sobolev theory may already supply much of the argument.

### APT-05: close the compact ramp application

The [complete ramp–tent paper proof](../../drafts/pipeline/2-fully-proven/arithmetic-positivity-factorial-ramp-gram-margin.md) reconciles the common domain and proves, eventually in \(n\),
\[
\texttt{factorialSpanWeil}(n,c,d)\ge
\frac{\log N}{8192N}c^2+\frac N2d^2
\quad\text{for every }c,d\in\mathbb R.
\]
This paper theorem still requires its complete Lean certificate. Its mechanism is as follows. For fixed sufficiently large \(n\), take \(k\) beyond the tail lower-bound threshold. Sesquilinearity and Hermitian symmetry give

\[
\operatorname{Re}\mathcal W(r_{n,k},r_{n,k})
=\operatorname{Re}\mathcal W(H_{n,k},H_{n,k})
+\operatorname{Re}\mathcal W(U_{n,k},U_{n,k})
-2\operatorname{Re}\mathcal W(H_{n,k},U_{n,k}).
\]

The independent comparison inequality then yields

\[
\operatorname{Re}\mathcal W(r_{n,k},r_{n,k})
\ge
\frac{c\log N-2\sqrt{C_HC_U\log N}-C_H}{N}.
\]

The paper sampling theorem supplies the upper budget. The corrected-source readout \(1/(2\sqrt N\rho)\), the kernel bound, and the summable genus-one zero majorant supply \(C_H/N\). The algebra uses only \(\operatorname{Re}\mathcal W(H,H)\ge-\mathcal Z(H)\), so a separate positivity theorem for \(H\) is unnecessary. The positive \(\log N\) term eventually dominates the square-root and constant terms.

The remaining formal certificate must include both passages:

1. **Removal of smoothing.** The [full ramp-limit paper proof](../../drafts/pipeline/2-fully-proven/arithmetic-positivity-factorial-ramp-smoothing-limit.md) proves convergence of the complete physical Weil energy for each fixed \(n\). Normalized nonnegative convolution contracts every translation square, providing an integrable majorant for the singular archimedean jump term. Common compact support controls the finite prime sum and polar integral. The compact mixed explicit formula `zeta_W_eq_weilFullFunctional_mixed` supplies the exact zero-side/physical-side identification. Formalize this limit and its application; physical \(L^2\) convergence alone is insufficient, and the corrected-source limit is a different theorem.
2. **The complete Gram margin.** In the existing ramp–tent span, write
   \[
   Q(c,d)=A_nc^2+M_ncd+D_nd^2,
   \qquad
   A_n-\frac{M_n^2}{4D_n}
   \]
   for its Schur margin. The recorded scales are \(D_n\ge N\) eventually and \(M_n=O(\log N/\sqrt N)\), hence the correction is \(O(\log^2N/N^2)\). Transfer the ramp lower bound of order \(\log N/N\) to this exact margin using [FactorialWeilGramDecoupling.lean](../../../formal/GaloisForLFunctions/BiScaleUncertainty/FactorialWeilGramDecoupling.lean).

**Completion gate:** the actual compact ramp–tent family is covered with its full form and precise eventual range. This is a family-level positivity theorem. It proves neither density of that family nor the universal RW criterion.

An independent fallback is to work directly with the resummed expression in [FactorialRampDiagonalIdentity.lean](../../../formal/GaloisForLFunctions/BiScaleUncertainty/FactorialRampDiagonalIdentity.lean). That route asks for an explicit archimedean/logarithmic/polar inequality after exact prime resummation. It does not require inventing a new prime-distribution estimate for this family. Preserve the polar term: [FactorialPolarGramScaleSeparation.lean](../../../formal/GaloisForLFunctions/BiScaleUncertainty/FactorialPolarGramScaleSeparation.lean) rules out paying its leading loss from the smaller Gram correction.

## APT-06: extract a source-level stability theorem

Only generalize after a mechanism has succeeded on an actual source. Determine which hypotheses did the work:

- Exact divisor or dilation relations responsible for cancellation.
- Weighted regularity and boundary corrections responsible for sampling control.
- Arithmetic or geometric constraints responsible for a positive diagonal.
- A quantitative comparison between the positive margin and the mixed coupling cost.

Try a finite collection of genuinely different sources satisfying those hypotheses. Moment cancellation alone should not be declared sufficient for positivity. Nor should a family of dilation stencils be declared total before a separate density theorem has been proved in the relevant form topology.

For stability, start with a precisely specified perturbation \(q=q_0+e\). Two useful conditional criteria are:

\[
q_0(f)\ge0,\quad |e(f)|\le\varepsilon q_0(f),\quad 0\le\varepsilon<1,
\]

or, on a specified space,

\[
q_0(f)\ge\delta\|f\|_*^2,\quad
|e(f)|\le\varepsilon\|f\|_*^2,\quad \varepsilon<\delta.
\]

Both give positivity by elementary algebra. The research content lies in deriving the relative bound or the gap and perturbation constants from actual arithmetic data. Do not present these abstract implications as the new theory. The first criterion also requires the perturbation to vanish on any null directions of \(q_0\).

Seek a sharp stability radius, sign threshold, negative-index classification, or exact residual decomposition. Useful results may identify a class where positivity fails rather than force an unjustified universal positive conclusion.

**Completion gate:** a theorem with source-level hypotheses, at least one application beyond the original pilot, and a serious boundary example explaining why its assumptions matter.

## APT-07: confront all directions and all scales

The global challenge is not solved by repeating finite positivity checks. A valid extension mechanism needs:

1. An approximation or filtration reaching every admitted test, with density in a topology that controls the complete form.
2. Exact relations between successive energies, including mixed blocks and all completion terms.
3. Bounds on the cumulative cost of elimination or extension, with the correct dependence on aperture and arithmetic scale.
4. A proved limit argument transferring the sign to the full domain.

For a positive invertible block \(A\), the residual after eliminating it is \(C-B^*A^{-1}B\). Positive diagonal blocks alone do not imply a positive residual. If a block is singular, inverse and range conditions must be replaced by a justified singular-block statement. Unbounded operator analogies do not waive closed-form domain requirements.

The existing [exact finite Schur theorem](../../../formal/GaloisForLFunctions/RHTower/CCMRestrictedWeilExactFiniteSchur.lean) and [arithmetic Schur laws](../../../formal/GaloisForLFunctions/RHTower/ArithmeticSchurRenormalizationLaw.lean) provide starting machinery. The latter programme's missing connection to the actual xi/Weil object must remain visible; positivity in a different arithmetic system does not automatically transfer.

The factorial family also supplies a concrete arithmetic comparison geometry. The [Bohr coercivity paper proof](../../drafts/pipeline/2-fully-proven/arithmetic-positivity-factorial-bohr-coercivity.md) gives a uniform coefficient lower bound for its exact remainder phases. The stronger [finite-window paper proof](../../drafts/pipeline/2-fully-proven/arithmetic-positivity-factorial-window-coercivity.md) uses the exact collar bounds and Montgomery–Vaughan estimates to prove that \((\sqrt{n+1}\,T_n)\) is a Riesz sequence in physical \(L^2\), uniformly over finite coefficient families. The [full signed span paper proof](../../drafts/pipeline/2-fully-proven/arithmetic-positivity-factorial-span-coercivity.md) adds quantitative low-frequency exclusion and complete prime/polar budgets, giving \(\Re\mathcal W(f_b,f_b)\ge(c\log M-C)\sum|b_N|^2\) when all source indices satisfy \(N\ge M\). Formalize these exact source statements through the [span task](../../drafts/pipeline/1-in-progress/arithmetic-positivity-factorial-span-sign.md). The signed result is a paper theorem, not yet a Lean certificate. Density and extension beyond this restricted span remain open obligations.

> **[OPEN CORE: GLOBAL ARITHMETIC SIGN]** Find an independently justified arithmetic mechanism controlling the complete residual or capacity cost for every admitted test and support aperture.

Meeting that requirement at full RW strength would solve RH. Likewise, proving the full fixed-side critical bound in WL would solve RH. Neither is currently supplied by this programme. Avoid renaming either endpoint as a “positivity axiom” and treating the remaining implications as a solution.

If a weaker extension theorem is all that can be proved, state its aperture range, source class, or loss explicitly. A fixed exponential loss in WL, or a bounded family of apertures in RW, is a different conclusion. A global uniform positive spectral gap is not an additional goal unless an application independently requires it.

## APT-08: evaluate a geometric realization

Keep this as a longer-term alternative unless a concrete construction becomes available. The required ingredients are substantial:

- Arithmetic objects whose construction does not assume zero location.
- A faithful correspondence with the relevant completed zeta divisor, including multiplicities, poles, and the correct local factors.
- An independently positive pairing on the relevant quotient or cohomological degree.
- A generator and compatibility law forcing the critical real part; for example, a rigorously defined relation making the shifted generator skew-adjoint in the positive pairing.
- Correct domains, boundary terms, and treatment of any continuous spectrum.

The finite-field model is [Deligne's weight theorem](https://www.numdam.org/item/PMIHES_1974__43__273_0.pdf). [Deninger's Hilbert–Polya and height-pairing programme](https://arxiv.org/abs/1001.1621) is a direct ancestor in the number-field setting. Our [existing geometric purity card](../../drafts/pipeline/1-in-progress/deninger-closed-generator-hodge-weil-purity-universality-law.md) already separates conditional purity implications from the missing arithmetic construction.

**Completion gate:** a genuinely constructed object or a partial construction with a nontrivial unconditional consequence. A conditional theorem whose positive-pairing premise already carries RH does not complete this task.

## Research workflow and acceptance criteria

For each task, keep one pipeline card with the exact statement, dependencies, proof attempt, falsifiers, literature audit, and current open core. Follow the repository stages from backlog through paper proof, Lean formalization, and publication preparation. This document is a programme, not a substitute for those proof records.

Before marking a mathematical task complete:

1. **Arithmetic fidelity:** retain the literal source, completion terms, multiplicities, and domains.
2. **Noncircularity:** classify every positivity, contraction, cancellation, and spectral assumption; identify any RH-equivalent one.
3. **Quantitative adequacy:** state all scale quantifiers and constants; verify that the estimate is strong enough for the claimed application.
4. **Closure:** justify every limit, density step, and passage from a finite family to a larger space.
5. **Falsification:** test the claimed mechanism against the controls in APT-03 and record failures honestly.
6. **Novelty:** separate established tools, new applications, new estimates, and speculative generalizations using primary sources and corpus searches.
7. **Formal verification:** after a dependency-closed paper proof, verify exact names in this toolchain, inspect theorem dependencies, compile the affected Lean work, and run `scripts/formal_tools.py lint` as required by repository instructions. These documentation files themselves introduce no Lean declarations.
8. **Positive salvage:** if a route fails, extract and audit its strongest useful survivor before retirement. Record `NO POSITIVE SALVAGE FOUND` only after a serious second pass finds none.

## Immediate next actions

1. Use the [factorial sampling card](../../drafts/pipeline/1-in-progress/arithmetic-positivity-factorial-tail-sampling.md) and [paper proof](../../drafts/pipeline/2-fully-proven/arithmetic-positivity-factorial-log-sampling.md) as the exact local statement and dependency ledger.
2. Use [FactorialCorrectedSampling.lean](../../../formal/GaloisForLFunctions/arithmetic-positivity-theory/FactorialCorrectedSampling.lean), which proves absolute square summability and the uniform \(C_H/N\) corrected-source budget on the literal zeta carrier.
3. Use the verified [complete sampling bound](../../../formal/GaloisForLFunctions/arithmetic-positivity-theory/FactorialTailSampling.lean), retaining its literal zero carrier and all-index uniformity, to certify the sharp lower scale and relative sign margin.
4. Finish APT-05, including the full ramp limit, before claiming the two-dimensional positivity application. Then test which source-level mechanisms survive beyond the factorial family.

Corpus indexes guide discovery; stale or pending compiler entries do not certify a theorem. Repeat focused searches when undertaking a new statement and verify the actual dependencies directly. Source links and proof cards provide the durable record; temporary search outputs do not establish novelty or correctness.
