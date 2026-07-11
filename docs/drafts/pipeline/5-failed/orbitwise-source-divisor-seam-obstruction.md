# Orbitwise source--divisor seam obstruction (flat-transport no-go)

- **ID:** orbitwise-source-divisor-seam-obstruction
- **Stage:** 5-failed
- **Type:** FALSIFIED RH ROUTE + THEOREM (Lean)
- **Lean:** `formal/GaloisForLFunctions/RHTower/OrbitwiseSourceDivisorSeam.lean`
- **Statement:** The far-right von Mangoldt source gives a faithful first-prime detector of the
  FE--Schwarz endpoint separation, but its multiplicative transport is an exact coboundary.
  Consequently orbit composition does not force the detector to vanish.

## The unconditional source seam

Let
\[
P(s)=\sum_{n\ge1}\Lambda(n)n^{-s}=-\frac{\zeta'(s)}{\zeta(s)}
\qquad (\Re s>1).
\]
For arbitrary fixed `a,b in C`,
\[
2^x\bigl(P(x+a)-P(x+b)\bigr)
\longrightarrow
(\log 2)\bigl(2^{-a}-2^{-b}\bigr)
\qquad (x\longrightarrow+\infty).
\]
This is the exact least-source-atom asymptotic; no prime cutoff or zero ordering occurs.

For the lower endpoints of the FE--Schwarz orbit,
\[
a=\overline\rho,\qquad b=1-\rho,
\]
define
\[
\mathcal S_2(\rho)
=(\log2)\left(2^{-\overline\rho}-2^{-(1-\rho)}\right).
\]
Then
\[
\mathcal S_2(\rho)=0
\quad\Longleftrightarrow\quad
\Re\rho=\frac12.
\]
Thus a single prime atom reads the horizontal separation exactly.

## Why it is not an obstruction

The associated multiplicative transport is
\[
H_2(a,b)=2^{b-a}=\frac{2^b}{2^a}.
\]
It obeys
\[
H_2(a,b)H_2(b,c)=H_2(a,c),\qquad
H_2(a,b)H_2(b,a)=1.
\]
Therefore it is the coboundary of the scalar gauge `u(a)=2^a`.  Every closed orbit word has
trivial holonomy for every base point.  A free FE--Schwarz orbit may have a nontrivial individual
edge, but the reverse edge cancels it; involutivity does not imply `H_2(a,b)^2=1`.

Equal divisor multiplicities at `conj rho` and `1-rho` identify only the principal Laurent
coefficients.  They do not identify the regular germs or impose `H_2(a,b)=1`.  Adding that edge
triviality is exactly the desired equality `conj rho = 1-rho`, hence an RH restatement.

## Full prime grading and the normed escape

For every prime power `p^m`, horizontal translation acts by the character
\[
e_{p,m}\longmapsto p^{-m\delta}e_{p,m}.
\]
The full raw prime-graded transport is therefore the same flat additive-translation
representation, coordinate by coordinate.  Retaining all prime labels does not by itself create
curvature or a non-character seam.

Putting a strong norm on the prime module can make endpoint differences nontrivial, but the
critical \(\ell^2\)/Hilbert--Schmidt threshold is the already-known prime-zeta recut at
\(\Re s=1/2\).  Deriving normed source regularity from scalar divisor pole cancellation would
require a new boundedness, square-function, or positivity principle.  That is extra analytic
structure, not a consequence of the orbit divisor.

## Formal theorem surface

- `LSeries_shiftedVonMangoldtCoeff`
- `tendsto_two_cpow_mul_shiftedVonMangoldtLSeries`
- `tendsto_firstPrimeTranslationSeam`
- `tendsto_orbitwiseFirstPrimeSeamCharge_infinitePrimeFlux`
- `orbitwiseFirstPrimeSeamCharge_eq_zero_iff`
- `firstPrimeOrbitTransport_eq_coboundary`
- `firstPrimeOrbitTransport_trans`
- `orbitwiseFirstPrimeTransport_reverse_cancels`

## Parent-literature audit

- Hedenmalm--Lindqvist--Seip, *A Hilbert space of Dirichlet series and systems of dilated
  functions in L2(0,1)*, Duke Math. J. 86 (1997), 1--37
  ([arXiv:math/9512211](https://arxiv.org/abs/math/9512211)), already places square-summable
  coefficient completions and their character/polydisk model in the standard Hardy--Dirichlet
  framework.
- C.-E. Fröberg, *On the prime zeta function*, BIT 8 (1968), 187--202, is the classical parent for
  prime-zeta continuation and the half-plane recut.
- The least-coefficient asymptotic used here is the standard uniqueness mechanism for ordinary
  Dirichlet series and is already supplied by mathlib as
  `LSeries.tendsto_cpow_mul_atTop`.

## Scientific verdict

- `[PROVED]` The first-prime orbit seam is an unconditional, source-pure, faithful detector.
- `[PROVED]` Its multiplicative transport is an exact coboundary with trivial loop holonomy.
- `[FALSIFIED]` The raw orbitwise source seam is not a constraint beyond the translation flow.
- `[OPEN CORE]` A live successor would need a canonically forced, non-character coupling between
  prime labels and divisor regular germs.  Neither equal residues, the FE--Schwarz orbit, nor the
  Euler source alone supplies such a coupling.

## Dual-gate verdict

The first-coefficient asymptotic and coboundary identities are standard Dirichlet-series and
exponential algebra.  Their application closes a project route, but it does not pass the
NOVEL x SIGNIFICANT gate as new mathematical knowledge.  The candidate is retired rather than
promoted.
