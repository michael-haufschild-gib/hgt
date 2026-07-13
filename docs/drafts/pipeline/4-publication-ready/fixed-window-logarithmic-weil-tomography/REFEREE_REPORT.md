# Referee report

## Recommendation

**Major revision; invite resubmission after the central analytic and novelty comparisons are made fully explicit.**

The manuscript contains a potentially valuable theorem package. Its strongest result is not a proof of the Riemann hypothesis, but an exact source-defined scalar spectrum. For each fixed width *L > 0*, a finite-prime–Gamma coefficient *g_L(n)* agrees with the sharp rectangular Xi polarization at *a = (log n)/2*; its tail is nonnegative exactly under RH; and the abscissa of its negative part is either *−∞* under RH or *1 + δ\** under false RH. This gives a precise one-parameter encoding of every right half-plane containing the Xi divisor.

That theorem is interesting enough to be the paper. The present manuscript also combines it with an inverse-tilted dyadic source, critical-Mellin tomography, positive-channel conservation, sparse-exception criteria, and a minimal correction cone. The logical relations appear plausible, but the hierarchy and novelty boundary are not yet sharp enough for publication in the current form.

## Principal strengths

1. The main coefficient *g_L(n)* is defined on the prime–Gamma side and does not use zeros as input.
2. The fixed-width statement is genuinely cofinal: neither *L* nor deletion of a finite prefix changes the transverse abscissa.
3. The false-RH alternative is quantitative. It recovers the exact supremal horizontal displacement *δ\**, not merely the existence of an off-line zero.
4. Multiplicity is treated through residues and local orders rather than being silently reduced to the simple-zero case.
5. The contour proof supplies an explicit *R^(−1/2) + R^(−1)* vertical-edge majorant, stronger than an unspecified zero-avoiding subsequence argument.
6. The manuscript states its limitation correctly: it does not establish the required tail nonnegativity or critical correction estimate and therefore does not prove RH.

## Mandatory mathematical revisions

### 1. Make the prime–Gamma spectrum the unique Theorem A

The paper should announce one main theorem with four parts, in this order:

1. *g_L(n) = Q_L((log n)/2)*;
2. *RH ⇔ g_L(n) ≥ 0* on any admissible tail;
3. the complete half-plane energy equivalence for every *α ≥ 0*;
4. the abscissa dichotomy *−∞* versus *1 + δ\**.

All other results should be labeled as proof infrastructure, equivalent coordinates, or applications. The abstract and introduction still make the prime–Gamma sequence, the inverse-tilted source, the critical-Mellin defect, and the correction *c⁻ = 2E* compete for attention.

### 2. Give a theorem-by-theorem comparison with Guinand, Weil, and Barner

The autocorrelation *R_{L,a}* is compactly supported, continuous, and piecewise *C¹*, and therefore appears to lie in Barner's admissible class. The authors must state:

- which part of the sharp identity follows by direct specialization of Barner after matching conventions;
- which normalization, endpoint, or absolute-convergence assertion is not immediate from that specialization;
- whether the finite von Mangoldt window *n ≤ exp(2a)* is a new evaluation or simply the support consequence of the classical formula;
- precisely which logarithmic-sampling and abscissa results are claimed as new.

The paper should not claim a new general explicit formula. The defensible contribution is the exact evaluated two-edge specialization and the source-only spectrum built from it.

### 3. Expand the vertical-edge proof into a complete lemma

The new bound is the analytic heart of the sharp contour argument. Its proof should show, without omitted interchange steps:

- the centered Hadamard relative-resolvent identity;
- the per-zero integrated Cauchy estimate uniform in horizontal pole distance;
- the derivative estimate giving *K_{L,a}*;
- finiteness of *S_{3/2}* and *S_2*, with multiplicity;
- the near/far split and exchange of divisor sum with the far-edge integral;
- existence of arbitrarily large divisor-avoiding *R*;
- why one cofinal admissible sequence suffices in the argument-principle exhaustion.

The displayed estimate is credible, but a referee should not have to reconstruct the logarithmic-primitive argument from a paragraph.

### 4. Prove every normalization in the bottom-edge calculation

The Fourier convention is easy to misread because the square of a bilateral transform is being inverted. The manuscript should prove explicitly

*(1/π) ∫ ĥ_{L,a}(x−i)² exp(−ixt) dx = 2 exp(t) R_{L,a}(t),*

including the factor *2*, the exponential tilt, the reflection convention, and the values at the finitely many breakpoints. It should explain why endpoint representatives do not affect the von Mangoldt sum or specify them.

The reality of *A_{∞,L,a}* should be proved directly from its source integral, not inferred only after comparison with the real zero side. Since *g_L* is advertised as source-only, its reality should be source-visible.

### 5. Make the completeness proof independently checkable

The step from eventual lower boundedness of *Q_L((log n)/2)* to RH is the conceptual core. The exact scale-local Landau statement should include:

- the abscissa convention after deletion of a finite prefix;
- the holomorphic disc crossing the real boundary *1 + δ\**;
- the positive gap between that real point and the shifted nontrivial divisor;
- local normal convergence of the filled shifted-zeta sum;
- why nonattainment of *δ\** causes no problem;
- why the multiplicity order calculation prevents cancellation at every shifted pole.

This proof should not remain a chain of references whose hypotheses must be mentally recombined.

### 6. Clarify “source-only” and effective accessibility

The authors should state explicitly that:

- *P_{L,a}* is a finite von Mangoldt sum;
- *A_{∞,L,a}* uses only elementary factors, Gamma, and an absolutely convergent integral;
- the admissible cutoff depends only on *L*;
- *g_L(n)* can be evaluated without locating a zeta zero.

The paper need not supply an optimized algorithm, but it should distinguish definability from practical computability and provide at least one numerical sanity check of the identity and signs.

### 7. Separate the two source constructions

The prime–Gamma sequence *g_L* and the inverse-tilted dyadic source *P_-* are not the same sequence. Their equivalence in the principal theorem comes from each independently detecting the same zero-free half-plane. The paper must not suggest an unproved direct identity.

The logical picture is

*g_L⁻ ↔ sharp Weil energy*

and, independently,

*P_- ↔ S_- ↔ D̃*.

If no direct source-to-source transform is proved, “one-source” and “shared source” should be revised. The clean alternative is to keep the prime–Gamma spectrum in the main paper and move the inverse-tilted Mellin tomography to a companion paper.

### 8. Separate the exact RH criterion from the sufficient correction criterion

The manuscript has two different endpoint statements:

- *σ_abs(g_{L,N}⁻) ≤ 1* is equivalent to RH;
- *σ_abs(c⁻) ≤ 1* is sufficient for RH, but necessity is not proved.

These must remain visually and verbally distinct. Minimality of *c⁻* inside its correction cone does not make its critical abscissa an RH equivalence.

### 9. Moderate the Connes claim

The manuscript derives scalar obligations relevant to the Connes route. It does not construct a semilocal Sonin space, prove cofinal operator convergence, identify a self-adjoint spectrum with the Xi divisor, or produce a trace formula whose positive part equals *g_L*.

The warranted conclusion is:

> Any Connes-type realization satisfying the stated scalar identification must dominate or reproduce this negative carrier.

The paper should not imply that every conceivable Connes architecture is exhausted by the scalar sequence without a theorem mapping that architecture to the coefficientwise order used here.

### 10. Distinguish structural theorems from elementary order facts

The finite-channel maximum law, aggregate domination, and least-negative-part lemma are correct and useful, but much of their proof is elementary order theory for nonnegative Dirichlet coefficients. Their significance lies in identifying the particular carrier, not in the abstract inequalities. They should not be presented as comparable in novelty to the prime–Gamma spectrum.

## Questions the authors must answer

1. Does Barner's theorem, with *F = R_{L,a}*, already imply equation (6.6) after a change of normalization? If not, identify the failed hypothesis exactly.
2. Can the reality of *A_{∞,L,a}* be read directly from the Gamma integrand?
3. Is *g_L(n)* independent of endpoint representatives of the sharp indicator?
4. Why does positivity on one admissible logarithmic tail detect every remote off-line zero rather than only an attained rightmost zero?
5. Which assertion uses *L > 0*, and what degenerates at *L = 0*?
6. Are all sums over *Z* sums over multiplicity copies? State this once and use it consistently.
7. Is *σ_abs(0) = −∞* the adopted convention? State it at first occurrence.
8. Is the inverse-tilted source logically needed for the prime–Gamma spectrum, or only a second coordinate? If the latter, why is it in the same paper?
9. Is there a direct formula connecting *g_L⁻* and *c⁻ = 2E*? If not, what justifies calling them manifestations of one carrier?
10. What operator or trace-formula estimate would imply *g_L(n) ≥ 0* on a tail?
11. What is the simplest consequence of the exact spectrum that is not an immediate restatement of Weil positivity or a known screw-function criterion?
12. Can the authors give a numerical example comparing the finite prime–Gamma expression with the zero polarization?

## Expository and editorial revisions

- Shorten the abstract and keep Theorem A dominant.
- Add a notation table for *Q_L*, *q_L*, *g_L*, *d_L*, *P_-*, *c*, *E*, *S_-*, and *D̃*.
- Replace “candidate-new” with a precise contribution statement supported by the literature comparison.
- State Fourier and Mellin conventions at the beginning.
- Use “Xi” and “xi” consistently.
- Explain why squares, rather than absolute squares, are real and nonnegative under RH.
- State all abscissae in the extended real line and give the zero-series convention once.
- Add stable identifiers for references and verify all 2025–2026 publication statuses at submission.
- The target journal's authorship and accountability policy must be resolved before submission.

## Publication threshold

I would support publication after the following minimum package is supplied:

1. one Theorem A centered on *g_L*;
2. a complete contour and Fourier-normalization proof;
3. a precise Barner comparison;
4. a clear separation of *g_L*, *P_-*, and *c⁻*;
5. a moderated Connes interpretation;
6. one reproducible numerical check;
7. a shorter abstract and clearer notation.

The strongest publishable narrative is:

> A fixed sharp two-edge Weil window, sampled only at logarithmic integer apertures, admits an exact finite-prime–Gamma realization. The negative part of that explicit arithmetic sequence has an absolute-convergence abscissa equal to the rightmost horizontal displacement of the Xi divisor plus one; it vanishes identically exactly under RH. Thus one scalar source sequence records the complete family of right half-plane bounds for the Xi divisor.

That statement is strong, precise, and does not overstate what remains open.
