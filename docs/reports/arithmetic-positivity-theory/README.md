# Arithmetic positivity theory

**Status:** proposed research programme. **Started:** 2026-10-18.

We want to understand when exact arithmetic structure forces global positivity and cancellation at the critical scale, and how that structure governs the sign and stability of spectral energies.

This directory gives future research agents a common starting point. This README explains the motivation, objects, existing foundations, and constraints. [research-foundational.md](research-foundational.md) specifies the first research tasks, their dependencies, and their success and failure criteria.

“Arithmetic positivity theory” names a programme, not an established field or a claim of novelty. The absence of a known solution does not establish that a new field is necessary. A decisive estimate, a new invariant, or a synthesis of existing methods could suffice. The programme earns its scope by proving useful results below its hardest endpoints.

## Why develop it?

The immediate motivation is the gap between our substantial RH reduction machinery and the arithmetic estimates those reductions still require. [Route WL](../rh-current-frontier-map.md) has receivers for critical-scale bounds on an integrated prime deficit. [Route RW](../rh-current-frontier-map.md) has exact identities, spectral realizations, and positivity criteria for the Weil form. Neither collection of receivers manufactures the needed arithmetic bound.

Our project mission is to develop rigorous mathematics toward an unconditional proof of RH, with completed arguments verified in Lean. The purpose of this programme is broader: explain which arithmetic hypotheses determine spectral sign, which perturbations preserve it, and which obstructions force negative directions. Results should remain valuable even if they do not settle RH. RH itself remains open; see the [Clay problem statement](https://www.claymath.org/millennium/riemann-hypothesis/).

The recurring difficulty is concrete. Exact identities expose positive and negative contributions, but arithmetic must still control their interaction. A self-adjoint realization does not determine the sign of its ground energy. A positive component does not determine the sign of the full form. A successful family of test functions does not establish positivity in every direction.

## The two motivating endpoints

These are destinations and circularity checks, not assumptions available to the programme.

### WL: critical-scale cancellation

Write

\[
\psi(x)=\sum_{p^j\le x}\log p,
\qquad
D(T)=\int_0^T\bigl(e^t-\psi(e^t)\bigr)\,dt.
\]

The corpus has receivers taking either of the following **fixed choices of side**, with a single constant valid for every scale, to RH:

\[
\exists B>0\ \forall T\ge0:\quad D(T)\le B(1+T)e^{T/2},
\]

or

\[
\exists B>0\ \forall T\ge0:\quad D(T)\ge-B(1+T)e^{T/2}.
\]

The side cannot change with \(T\). These existential bounds are RH-equivalent in the current route ledger. The missing input is an independent arithmetic proof of such a bound. A finite range, a growing constant, or a bound with a fixed exponent loss does not satisfy this receiver. This is an integrated deficit; it must not be confused with a pointwise \(\psi(x)-x=O(\sqrt x)\) assertion.

Source: [ChebyshevDeficitPrimitiveOneSidedRH.lean](../../../formal/GaloisForLFunctions/RHTower/ChebyshevDeficitPrimitiveOneSidedRH.lean), read with the [frontier map](../rh-current-frontier-map.md).

### RW: sign of the complete arithmetic energy

For the real compact tests and support-compatible cutoffs in the corpus, the exact decomposition has the form

\[
\mathcal W(g,g)=\mathcal M_N(g)+\tfrac12 C(g)^2-\tfrac12 S(g)^2,
\qquad
\mathcal M_N(g)=V_N\|g\|_2^2+J_N(g),
\]

where \(J_N\) is a sum of nonnegative jump energies, while

\[
V_N=\operatorname{gammaBracket}(0)
-2\sum_{2\le m\le N}\frac{\Lambda(m)}{\sqrt m},
\quad
C(g)=\int_{\mathbb R}2\cosh(u/2)g(u)\,du,
\quad
S(g)=\int_{\mathbb R}2\sinh(u/2)g(u)\,du.
\]

No positivity of \(V_N\), or of \(\mathcal M_N\) by itself, is supplied by this decomposition. The missing capacity inequality is

\[
S(g)^2\le 2\mathcal M_N(g)+C(g)^2
\]

for every admitted real compact test, at every support aperture, with the cutoff beyond its autocorrelation support. That universal assertion is RH-equivalent. It is not enough to prove it on a preferred finite-dimensional family.

Source: [WeilMarkovPoleCapacity.lean](../../../formal/GaloisForLFunctions/RHTower/WeilMarkovPoleCapacity.lean).

## Objects and language

The initial language should stay close to quantities we can compute, estimate, and formalize. Each object must carry its normalization, domain, and dependence on scale.

| Object | Meaning and role |
|---|---|
| Exact arithmetic source | Prime-power weights, divisor identities, and any genuine Euler relations being used. For zeta, retain the literal \(\Lambda\)-weights rather than a generic positive sequence. |
| Completed source data | Arithmetic contribution together with the actual archimedean factor, poles, boundary terms, and normalization. These jointly determine the energy. |
| Test and readout | A physical test \(f\), its admissibility conditions, and its Mellin readout \(F_f(s)=\int_{\mathbb R}f(x)e^{(s-1/2)x}\,dx\). Compact and noncompact tests require separate domain checks. |
| Complete Weil form | A sesquilinear spectral energy \(\mathcal W(f,g)\), identified with its full arithmetic expression on the proved domain. Positivity is a property to establish, not part of its definition. |
| Positive comparison form | An independently nonnegative quantity that can bound mixed terms without assuming the sign of \(\mathcal W\). The zero-sampling form below is an existing example. |
| Correction and defect | The exact difference between the source of interest and a tractable comparison source. Its diagonal and its mixed pairings must both be controlled. |
| Scale and residual form | Support aperture, arithmetic cutoff, frequency range, or smoothing parameter, together with what remains after an exact elimination. Distinguish these parameters. |
| Sign and stability data | Coercivity on a specified space, relative perturbation bounds, negative index, or a sharp sign threshold. A global uniform positive gap is not required by RH. |

The spectral dictionary already contains an important distinction. Let \(\rho\) range over distinct nontrivial zeta zeros, with multiplicity \(m_\rho\), and set

\[
\mathcal Z(f)=\sum_\rho m_\rho |F_f(\rho)|^2.
\]

On the admitted domain, the Weil pairing is represented by

\[
\mathcal W(f,g)
=\sum_\rho m_\rho F_f(\rho)
 \overline{F_g(1-\overline\rho)}.
\]

Reflection \(\rho\mapsto1-\overline\rho\) preserves the zero multiset. On its \(\ell^2\) space it induces a unitary involution \(J\), so the pairing is an inner product with \(J\). Consequently,

\[
|\mathcal W(f,g)|^2\le\mathcal Z(f)\mathcal Z(g).
\]

This is an **existing unconditional comparison inequality**. It does not imply \(\mathcal W(f,f)\ge0\): an involution can have negative directions. Moreover, \(\mathcal Z\) can be only a seminorm squared on physical tests unless injectivity is proved or a quotient is taken. Its positivity is easy; obtaining useful bounds from arithmetic source data is the research question.

Sources: [XiWeilLineConjHilbert.lean](../../../formal/GaloisForLFunctions/RHTower/XiWeilLineConjHilbert.lean), especially `norm_xiWeilPolarization_le`, and [XiCompactSpectralSampling.lean](../../../formal/GaloisForLFunctions/RHTower/XiCompactSpectralSampling.lean).

## What the corpus already supplies

“Existing” here describes source declarations and recorded research status inspected for this programme. These documentation changes do not constitute a fresh build or dependency audit. Future proof work must verify applicability with the current toolchain.

| Foundation | What it provides | What it leaves open |
|---|---|---|
| WL and RW receivers | Precise routes from critical cancellation or full Weil positivity to RH. | An independent arithmetic proof of their premises. |
| Positive zero-sampling comparison | Square summability and an unconditional bound on mixed Weil pairings. | Quantitative bounds with the required dependence on the source and scale. |
| Exact finite Schur reduction | A finite residual form controlling the relevant sign question. | The sign of that residual and estimates uniform enough for the full domain. |
| Exact factorial prime resummation | Conversion of the chosen family's prime sum into finite logarithmic data. | The resulting archimedean/logarithmic/polar inequality. |
| Actual factorial-tail growth | A positive tail diagonal of order at least \(\log N/N\) in the established eventual regime. | A complete Lean certificate of the paper-level mixed estimate and compact-ramp transfer. |
| Arithmetic Schur laws | Existing arithmetic recursions and positivity statements in their own setting. | A faithful connection carrying the needed inequalities to the actual xi/Weil object. |

Relevant starting points:

- [Exact finite Schur theorem](../../../formal/GaloisForLFunctions/RHTower/CCMRestrictedWeilExactFiniteSchur.lean).
- [Prime resummation](../../../formal/GaloisForLFunctions/BiScaleUncertainty/ClampedPrimeLogResummation.lean) and [exact ramp diagonal](../../../formal/GaloisForLFunctions/BiScaleUncertainty/FactorialRampDiagonalIdentity.lean).
- [Tail growth card](../../drafts/pipeline/3-formalized/factorial-muntz-tail-archimedean-growth-2026-10-18.md) and [tail growth declarations](../../../formal/GaloisForLFunctions/BiScaleUncertainty/FactorialMuntzTailWeilGrowth.lean).
- [Current ramp margin card](../../drafts/pipeline/1-in-progress/factorial-ramp-diagonal-margin-2026-10-18.md).
- [Arithmetic Schur programme](../../drafts/pipeline/1-in-progress/arithmetic-schur-renormalization-law.md).

## Mechanisms worth developing

**Exact arithmetic compression.** Use identities to expose structure before estimating. For example, \(\sum_{d\mid k}\Lambda(d)=\log k\) can collapse a finite weighted prime rectangle to a logarithmic sum when its support conditions hold. The result removes a distribution-of-primes question from that particular calculation; it does not remove the remaining sign question.

**Independent control of mixed terms.** Decompose the actual source into tractable pieces, preserve every correction, and bound interactions using a separately positive comparison form. The factorial pilot supplies a Lean certificate for the correction-tail sampling budget and a paper proof of the resulting complete ramp–tent margin. Its mechanism combines the exact arithmetic phase with logarithmic translation energy; the full ramp application still requires its assembled Lean certificate.

**Exact elimination with controlled residuals.** In a positive invertible block, Schur elimination replaces the remaining energy by \(C-B^*A^{-1}B\). Arithmetic must bound the coupling cost, not merely the two diagonal blocks. Singular blocks and unbounded forms require their own hypotheses. Repeated elimination needs control of accumulated losses and limits.

**Relative stability.** Determine which changes in source data preserve a proved positive form, which create negative directions, and which only change a finite negative index. Relative bounds can be more useful than demanding an absolute gap that may vanish as support grows.

**Geometric realization, as a longer-term alternative.** Seek arithmetic objects with a faithful spectral correspondence and an independently positive pairing whose compatibility with a generator forces the right weights. Finite-field cohomology supplies a successful model; the number-field construction remains conjectural. Deninger's programme already articulates this direction, so constructing the missing object would be progress, while restating the conditional implication would not be a new mechanism.

These mechanisms are candidates for a shared theory only if their hypotheses explain both successful cases and failures. A theory should tell us when positivity is forced and when the available arithmetic structure permits instability.

## Boundaries every agent must respect

| Tempting shortcut | Why it does not close the problem |
|---|---|
| Apply Cauchy–Schwarz using \(\mathcal W(f,f)\) and \(\mathcal W(g,g)\). | This requires positivity of the form on the relevant span. Use an independently positive majorant instead. |
| Infer sign from self-adjointness, existence of a ground state, or finite negative index. | None excludes a negative ground energy. |
| Replace a test by its absolute value and retain only the favorable change. | The Markov and polar pieces respond differently; the complete energy must be compared. |
| Verify many tests, heights, or support apertures. | Global positivity quantifies over all admitted tests and scales. Off-line zero orbits can produce negative compact-test directions at larger support. |
| Absorb the factorial polar loss into the Gram correction. | Their scales differ: the loss has order \(\log N/N\), while the Gram correction is only \(O(\log^2N/N^2)\). |
| Give a new name to a positive cone, invariant metric, contraction, or critical bound. | If the premise is already equivalent to RH, the arithmetic work remains unchanged. |
| Replace exact completion data by symmetries alone. | Functional-equation symmetry by itself permits off-line zeros. Each claimed countermodel must state exactly which arithmetic hypotheses it retains. |

See [STATUS.md](../STATUS.md), [compact orbit inertia](../../../formal/GaloisForLFunctions/RHTower/WeilCompactOrbitInertia.lean), [polar/Gram scale separation](../../../formal/GaloisForLFunctions/BiScaleUncertainty/FactorialPolarGramScaleSeparation.lean), and the [finite-filter saturation obstruction](../../drafts/pipeline/5-failed/finite-filter-schur-saturation-2026-10-17.md).

## First concrete milestone

For the actual raw factorial correction tail \(T_n\) and its normalized smoothing \(U_{n,k}\), with \(N=n+1\), the [sampling paper proof](../../drafts/pipeline/2-fully-proven/arithmetic-positivity-factorial-log-sampling.md) establishes:

\[
\mathcal Z(T_n)+\mathcal Z(U_{n,k})\le C\frac{1+\log N}{N}
\]

for every \(n,k\). **This upper bound and convergence of both literal zero sums are certified in Lean** by `exists_factorialTail_raw_and_smoothed_zeroSquare_bound`. The exact phase is bounded and Lipschitz; its weighted squared translation increments satisfy \(D(h)\le C\min\{N^{-1},h\}\). Integration against \(dh/h\), followed by Fourier and holomorphic sampling arguments, supplies the logarithmic budget. Existing tail positivity shows that the logarithm is necessary in the eventual smoothing regime.

The following ingredients have Lean certificates:

| Ingredient | Source |
|---|---|
| Literal arithmetic phase identity and bounds | [FactorialTailPhase.lean](../../../formal/GaloisForLFunctions/arithmetic-positivity-theory/FactorialTailPhase.lean) |
| Uniform weighted square mass \(96/N\) | [FactorialTailWeightedMass.lean](../../../formal/GaloisForLFunctions/arithmetic-positivity-theory/FactorialTailWeightedMass.lean) |
| Two translation regimes, including the endpoint jump | [FactorialTailTranslation.lean](../../../formal/GaloisForLFunctions/arithmetic-positivity-theory/FactorialTailTranslation.lean) |
| Logarithmic translation budget | [FactorialTailLogTranslation.lean](../../../formal/GaloisForLFunctions/arithmetic-positivity-theory/FactorialTailLogTranslation.lean) |
| Complete positive Gamma jump budget | [FactorialTailLevyEnergy.lean](../../../formal/GaloisForLFunctions/arithmetic-positivity-theory/FactorialTailLevyEnergy.lean) |
| Logarithmic Fourier budget | [FactorialTailFourierEnergy.lean](../../../formal/GaloisForLFunctions/arithmetic-positivity-theory/FactorialTailFourierEnergy.lean) |
| Literal Mellin readout, half-plane holomorphy, and exact Fourier normalization | [FactorialTailReadout.lean](../../../formal/GaloisForLFunctions/arithmetic-positivity-theory/FactorialTailReadout.lean) |
| Corrected-source square summability and \(C_H/N\) budget | [FactorialCorrectedSampling.lean](../../../formal/GaloisForLFunctions/arithmetic-positivity-theory/FactorialCorrectedSampling.lean) |
| Disk mean-square estimate using the actual half-plane of holomorphy | [FactorialTailDiskSampling.lean](../../../formal/GaloisForLFunctions/arithmetic-positivity-theory/FactorialTailDiskSampling.lean) |
| Global logarithmic disk overlap, with every multiplicity copy | [ZeroDiskOverlap.lean](../../../formal/GaloisForLFunctions/arithmetic-positivity-theory/ZeroDiskOverlap.lean) |
| Vertical energy with exact Fourier Jacobian | [FactorialTailVerticalEnergy.lean](../../../formal/GaloisForLFunctions/arithmetic-positivity-theory/FactorialTailVerticalEnergy.lean) |
| Integrable enlarged-strip energy and uniform bound | [FactorialTailStripEnergy.lean](../../../formal/GaloisForLFunctions/arithmetic-positivity-theory/FactorialTailStripEnergy.lean) |
| Complete raw and smoothed sampling theorem on the literal zeta carrier | [FactorialTailSampling.lean](../../../formal/GaloisForLFunctions/arithmetic-positivity-theory/FactorialTailSampling.lean) |

The sampling certificate retains the actual zero divisor and multiplicities. Its public conclusion has no RH, positivity, or unproved analytic premise.

The [complete ramp–tent paper proof](../../drafts/pipeline/2-fully-proven/arithmetic-positivity-factorial-ramp-gram-margin.md) makes the smaller corrected-source budget explicit and proves, eventually in \(n\),
\[
\texttt{factorialSpanWeil}(n,c,d)
\ge\frac{\log N}{8192N}c^2+\frac N2d^2
\qquad(c,d\in\mathbb R).
\]
The remaining ramp deliverables are the full compact-ramp smoothing limit and assembled Gram margin, as specified in the [foundational programme](research-foundational.md#first-pilot-the-actual-factorial-correction-tail). The mechanism is classified as a **bridge**, with no claim of literature novelty. This family result does not establish cross-scale or all-source RW positivity.

For whole coefficient families, the [finite-window coercivity paper proof](../../drafts/pipeline/2-fully-proven/arithmetic-positivity-factorial-window-coercivity.md) proves that the normalized actual tails form a Riesz sequence in physical \(L^2\). Exact collar separation and a dominant first harmonic prevent cancellation of the physical norm. This paper theorem still requires a Lean certificate; it does not control the complete signed form. The [knowledge ledger](knowledge-ledger-primary.md) records these boundaries and rejected shortcuts.

The [signed span paper proof](../../drafts/pipeline/2-fully-proven/arithmetic-positivity-factorial-span-coercivity.md) adds the missing energy estimates for this restricted family. For normalized phase coefficients supported on \(N\ge M\), it proves \(\Re\mathcal W(f_b,f_b)\ge(c\log M-C)\sum_N|b_N|^2\). Low-frequency exclusion forces logarithmic Gamma energy; uniform dilation bounds keep the entire prime and polar costs bounded on coefficient space. This assembled theorem still requires a Lean certificate. Its restricted positive span is not asserted dense, so the global RW endpoint remains open.

## What success would look like

1. A precise dictionary connecting literal arithmetic data, physical tests, and spectral energies without losing poles, multiplicities, or domains.
2. New source-derived bounds or classifications with hypotheses independently checkable below RH.
3. A mechanism that predicts positive cases and negative or unstable cases, with sharp boundaries where possible.
4. Stability and scale-extension theorems whose constants and limits are strong enough for their stated applications.
5. Eventually, an independent arithmetic theorem meeting a full WL or RW receiver. Until then, every weaker result must retain its exact scope.

Broader targets can include completed L-functions and arithmetic spectral systems once their coefficients, local factors, poles, involutions, and analytic domains are specified. No universal positivity claim for arbitrary arithmetic-looking data is intended.

## Instructions for future research agents

- Read the [foundational programme](research-foundational.md), [current frontier map](../rh-current-frontier-map.md), and [constraints ledger](../STATUS.md) before choosing a task. Check the linked cards for newer results.
- Search prior work with the documented `scripts/formal_tools.py research "..."` command and inspect its coverage and freshness. Use `rg` for exhaustive source-text checks. A search hit is not a verified dependency.
- Before a hard proof task, open a scoped pipeline card using the [card template](../../drafts/pipeline/_card-template.md). State the exact theorem, quantifiers, source domain, independent premises, and strongest likely falsifier.
- Label claims as **existing corpus result**, **classical input**, **derived consequence awaiting verification**, **proposed estimate**, or **RH-equivalent endpoint**. Mark the remaining mathematical step `[OPEN CORE]` rather than hiding it behind an interface.
- Complete the paper proof and its circularity and literature audits before formalizing it. Verify Lean names and run the checks required by [AGENTS.md](../../../AGENTS.md) and [formal/AGENTS.md](../../../formal/AGENTS.md).
- When a mechanism fails, extract the strongest positive survivor: a sharp threshold, exact decomposition, classification, replacement hypothesis, or invariant. Record its proof and formalization status before retiring the route.

## Mathematical ancestry

These sources establish nearby foundations, not solutions to the proposed open estimates:

- [Deligne, *La conjecture de Weil. I*](https://www.numdam.org/item/PMIHES_1974__43__273_0.pdf): a successful arithmetic-geometric weight theorem over finite fields.
- [Deninger, *The Hilbert–Polya strategy and height pairings*](https://arxiv.org/abs/1001.1621): conjectural geometric and positive-pairing mechanisms in the number-field setting.
- [Burnol, *Sur les Formules Explicites I: analyse invariante*](https://arxiv.org/abs/math/0101068): invariant analysis of explicit formulas and restricted positivity.
- [Connes–Consani, *Weil positivity and Trace formula, the archimedean place*](https://arxiv.org/abs/2006.13771): archimedean positivity and trace-formula structure.
- [Connes–Consani, *The Riemann–Roch strategy, Complex lift of the Scaling Site*](https://arxiv.org/abs/1805.10501): an existing geometric strategy whose missing constructions should not be mistaken for available inputs.

Novelty must be assessed theorem by theorem. The programme title and these connections are not evidence that a new mathematical field has been established.
