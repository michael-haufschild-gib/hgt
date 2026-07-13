# Referee report

## Recommendation

**Major revision; invite resubmission after the source hierarchy, classical comparison, and two
central analytic transfers are made independently checkable.**

The manuscript contains a strong theorem package.  Its sharpest formulation is now the
Gamma-free cumulative prime--polar spectrum.  For each fixed width (L>0), the authors define a
literal finite prime--polar sequence (S_L(n)), its retained negative part (S_{L,N}^-), and

\[
A_{L,N}(X)=\sum_{n\le X}S_{L,N}^-(n).
\]

They claim, for every (alpha\ge0),

\[
\Re\rho\le\tfrac12+\alpha\quad(\Xi(\rho)=0)
\iff \sigma_{\rm abs}(S_{L,N}^-)\le1+\alpha
\iff A_{L,N}(X)=O_\varepsilon(X^{1+\alpha+\varepsilon}),
\]

and hence

\[
\mathrm{RH}
\iff \sigma_{\rm abs}(S_{L,N}^-)\le1
\iff A_{L,N}(X)=O_\varepsilon(X^{1+\varepsilon}).
\]

The paper also proves that the cumulative exponent is sharp at (1+\delta_*), while the exact
prime--Gamma Weil channel retains the stronger pointwise sign criterion and the dichotomy
(-\infty) under RH versus (1+\delta_*) under false RH.

This is potentially publishable.  The manuscript nevertheless combines several logically
distinct constructions, and the strongest new statement rests on transfers that are elementary
in principle but easy to overstate at the endpoints.  A journal version should be reorganized
around one combined Theorem A and should make the bounded Gamma removal and cumulative-abscissa
argument completely transparent.

## Principal strengths

1. The finite prime--polar coefficient is defined without using zeros as input.
2. One positive monotone quantity, (A_{L,N}(X)), records every right half-plane containing the
   Xi divisor.
3. The false-RH alternative is quantitative: the sharp cumulative power threshold recovers the
   full supremal displacement (delta_*).
4. The exact prime--Gamma sequence remains available and gives a stronger pointwise sign
   criterion, rather than being discarded when the Gamma-free carrier is introduced.
5. The fixed-width statement is cofinal and insensitive to deletion of a finite prefix.
6. Multiplicity is retained through residues and local analytic orders.
7. The contour proof supplies an explicit (R^{-1/2}+R^{-1}) vertical-edge majorant.
8. The manuscript correctly states that none of the critical source estimates is proved and that
   the paper therefore does not prove RH.

## Mandatory mathematical revisions

### 1. State one combined Theorem A

The paper should announce a single main theorem with the following hierarchy:

1. (g_L(n)=Q_L((\log n)/2)), and RH is equivalent to (g_L(n)\ge0) on one admissible tail;
2. (S_L) is obtained by removing the uniformly bounded Gamma--polar correction from (g_L);
3. the half-plane bound, the abscissa bound for (S_{L,N}^-), and the cumulative bound for
   (A_{L,N}) are equivalent for every (alpha\ge0);
4. the cumulative exponent is exactly (1+\delta_*);
5. the exact Weil channel (g_{L,N}^-), but not necessarily (S_{L,N}^-), vanishes under RH.

This last distinction is essential.  The manuscript must never transfer the
(-\infty)/(1+\delta_*) dichotomy from (g_{L,N}^-) to (S_{L,N}^-) without an additional
argument.  A bounded Gamma correction preserves all convergence statements to the right of one,
but it does not force the Gamma-free negative part to vanish under RH.

### 2. Expand the derivation of the named Gamma-removal proposition

The cumulative theorem depends on the uniform estimate

\[
|S_{L,N}^-(n)-g_{L,N}^-(n)|\le C_L.
\]

Proposition 6.4 now gives an explicit kernel, near-zero bound, exponential tail bound, and
aperture-uniform constant.  This is a substantial improvement.  The remaining presentation gap
is the sentence asserting that the time-domain Gamma integral yields equation (6.21b).  The paper
should derive explicitly:

- the exact identity relating (S_L), (g_L), and the Gamma--polar correction;
- why the polar-square subtraction produces precisely ((\gamma+\log\pi)(2L));
- the change of variables from the Gamma integral to (K_{L,a});
- the (1)-Lipschitz property of the negative-part map;
- both comparison inequalities (S^-\le g^-+C_L) and (g^-\le S^-+C_L);
- why the constant channel is summable at every real exponent greater than one.

This lemma, not a verbal appeal to boundedness, is the bridge that justifies calling the final
criterion Gamma-free.

### 3. Make the cumulative-abscissa theorem fully precise

For (c(n)\ge0), (C(X)=\sum_{n\le X}c(n)), and (sigma\ge0), the paper uses

\[
\sigma_{\rm abs}(c)\le\sigma
\iff C(X)=O_\varepsilon(X^{\sigma+\varepsilon})
\quad(\varepsilon>0).
\]

The proof should state whether (X) ranges over positive integers or real numbers, make clear
that the implied constant may depend on (arepsilon), and spell out the Abel-summation converse.
It should also state the extended-real convention for the zero sequence.  This is elementary
Tauberian infrastructure, not an independent novelty claim, but the exact quantifiers are central
to Theorem A.

### 4. Justify the sharp lower cumulative exponent without assuming a rightmost zero

The lower statement

\[
A_{L,N}(X)\ne O(X^{1+\delta_*-\eta})
\qquad(0<\eta<\delta_*)
\]

must be proved from the supremum property alone.  The authors should explain why no attainment of
(delta_*) is needed: an assumed smaller cumulative exponent yields a smaller abscissa, hence a
strictly smaller zero-free half-plane, contradicting the definition of the supremum.  The proof
should not select a nonexistent rightmost zero.

The phrase "exact power threshold" should be tied to precisely these upper and lower Big-O
statements.  If the authors want to claim an equality involving a logarithmic limsup, that would
require a separate theorem.

### 5. Give a theorem-by-theorem comparison with Guinand, Weil, and Barner

The autocorrelation (R_{L,a}) is compactly supported, continuous, and piecewise (C^1), and
therefore appears to lie in Barner's admissible class.  The authors must state:

- which part of the sharp identity follows by direct specialization of Barner after matching
  conventions;
- which normalization, endpoint, or absolute-convergence assertion is established by their
  independent contour argument;
- whether the finite support (n\le e^{2a}) is a new evaluation or the direct support consequence
  of the classical formula;
- precisely which logarithmic-sampling, Gamma-removal, abscissa, and cumulative-spectrum results
  are claimed as new.

The defensible contribution is not a new general explicit formula.  It is the exact evaluated
sharp specialization and the source spectra built from it.

### 6. Expand the vertical-edge proof into a complete lemma

The analytic heart of the sharp contour argument should show:

- the centered Hadamard relative-resolvent identity;
- the per-zero integrated Cauchy estimate uniform in horizontal pole distance;
- the derivative estimate giving the window constant;
- finiteness of the required divisor sums, with multiplicity;
- the near/far split and the exchange of the divisor sum with the far-edge integral;
- existence of arbitrarily large divisor-avoiding heights;
- why one cofinal admissible sequence suffices for the contour exhaustion.

### 7. Prove every Fourier and reality normalization

The manuscript should prove explicitly

\[
\frac1\pi\int_{\mathbb R}\widehat h_{L,a}(x-i)^2e^{-ixt}\,dx
=2e^tR_{L,a}(t),
\]

including the factor (2), the exponential tilt, the reflection convention, and the breakpoint
values.  The reality of the archimedean contribution should be visible directly from its source
integral.  Otherwise the claim that (g_L) is source-defined remains partly dependent on the zero
side.

### 8. Keep the three source coordinates separate

The manuscript uses:

- (g_L), the exact prime--Gamma Weil sample;
- (S_L), the bounded-correction finite prime--polar sample;
- (P_-), the independent inverse-tilted dyadic source whose continuation reconstructs the
  divisor.

These are not coefficientwise identical.  Their relationship should be summarized in one
diagram or proposition.  In particular, the equivalence of their RH endpoints comes from proved
transfers through the same divisor bounds, not from an unstated source-to-source identity.

The signed dyadic coefficient (c) and its least correction (c^-=2E) form a fourth, merely
sufficient endpoint.  Its critical abscissa must not be described as necessary for RH unless that
converse is separately proved.

### 9. Moderate the Connes interpretation

The paper derives scalar obligations relevant to Connes's route.  It does not construct a
semilocal Sonin space, prove cofinal operator convergence, identify a self-adjoint spectrum with
the Xi divisor, or produce a positive trace formula whose scalar coefficient is (S_L).

The warranted conclusion is:

> Any Connes-type realization satisfying the stated scalar identification must control the
> cumulative negative prime--polar mass at the corresponding exponent.

The manuscript should not imply that every possible Connes architecture factors through this
particular scalar sequence.

### 10. Separate structural content from elementary order theory

The finite-channel maximum law, aggregate domination, least-negative-part lemma, and
cumulative-abscissa lemma are correct and useful.  Their significance lies in the identification
of the explicit Xi carrier.  The abstract inequalities themselves should not be presented as
novel results comparable to the sharp source spectrum.

## Questions the authors must answer

1. Is (S_L(n)) literally a finite von Mangoldt sum plus an explicit polar term for every retained
   (n)?  State the finite summation range.
2. What is the exact formula for (g_L-S_L), and where is its aperture-uniform bound proved?
3. Under RH, can (S_{L,N}^-) be nonzero?  If so, state this immediately after Theorem A.
4. Why does a bounded correction preserve the abscissa criterion at thresholds (1+\alpha) but
   not the (-\infty) branch?
5. Does the cumulative lower bound assert only failure of Big-O, or also an Omega result or a
   logarithmic limsup?  The terminology must match the proved statement.
6. Why does the supremum (delta_*) control all zeros even when it is not attained?
7. Does Barner's theorem already imply the sharp identity after normalization?  If not, identify
   the exact failed or unproved hypothesis.
8. Is the Gamma integral real directly from its integrand?
9. Are endpoint representatives of the sharp indicator immaterial to the von Mangoldt sum?
10. Which assertion genuinely requires (L>0), and what degenerates at (L=0)?
11. Are all divisor sums counted with multiplicity copies?
12. Is (sigma_{\rm abs}(0)=-\infty) the convention throughout?
13. Is the inverse-tilted source needed for the prime--polar cumulative spectrum, or only an
    independent divisor coordinate?
14. Is there a direct formula connecting (S_L^-) and (c^-=2E)?
15. What operator or trace estimate would imply
    (A_{L,N}(X)=O_\varepsilon(X^{1+\varepsilon}))?
16. What is the simplest consequence of the cumulative spectrum that is not already a direct
    restatement of Weil positivity?

## Expository and editorial revisions

- Add a notation table for (Q_L), (g_L), (S_L), (A_{L,N}), (P_-), (mathcal S_-),
  (widetilde D), (c), and (E).
- Shorten the abstract if the target journal imposes a conventional word limit.
- State Fourier and Mellin conventions before their first use.
- Use "Xi" and "xi" consistently.
- Explain why squares, rather than absolute squares, are real and nonnegative under RH.
- State every abscissa in the extended real line and give the zero-series convention once.
- Verify the publication status of every 2025--2026 citation at submission.
- Resolve the target journal's authorship and accountability policy before submission.
- A small reproducible numerical identity check would improve accessibility, although it is not
  a substitute for any analytic proof.

## Publication threshold

I would support publication after the following minimum package is supplied:

1. one combined Theorem A centered on (S_L) and (A_{L,N}), with (g_L) retained as the exact
   Weil coordinate;
2. a complete derivation of Proposition 6.4 and its two-sided negative-part comparison;
3. a fully quantified cumulative-abscissa proof;
4. a complete contour and Fourier-normalization proof;
5. a precise Barner comparison;
6. a clear separation of (g_L), (S_L), (P_-), and (c^-);
7. a moderated Connes interpretation.

The strongest publishable narrative is:

> A fixed sharp two-edge Weil window, sampled at logarithmic integer apertures, admits an exact
> finite-prime--Gamma realization.  Removing a uniformly bounded Gamma--polar correction produces
> a literal finite prime--polar sequence whose cumulative negative mass has exact power threshold
> (1+\delta_*).  Every horizontal zero-free region, and RH at the critical endpoint, is
> equivalent to the corresponding cumulative growth bound.

That statement is strong, precise, and does not overstate the unresolved critical estimate.
