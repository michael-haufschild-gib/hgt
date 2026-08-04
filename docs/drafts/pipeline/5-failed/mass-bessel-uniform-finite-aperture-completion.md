# Mass-Bessel uniform finite-aperture completion

**Stage:** Failed / retired  
**Date frozen:** 2026-08-04  
**Label:** `[FALSIFIED]`  
**Parent route:** `docs/reports/mass-shifted-spectral-trace-route.md`, §9.3

## 1. Exact claim, frozen before attack

For fixed `a>1/2` and `\sigma>0`, define the finite prime aperture

\[
 P_{a,\sigma;X}(u)=
 \sum_{n\le X}\frac{\Lambda(n)}{\sqrt n}
 \frac{2a(\sigma+iu)
 K_1\!\left(a\sqrt{(\sigma+iu)^2+(\log n)^2}\right)}
 {\sqrt{(\sigma+iu)^2+(\log n)^2}}.
\]

The conjecture was:

> The finite apertures are Cauchy in `C_b(\mathbb R_u)` after adding the
> aperture-independent pole and archimedean terms.  Consequently their
> pointwise source completion can be upgraded to a uniform vertical-line
> completion.

Adding the same auxiliary terms to every aperture does not affect Cauchy
differences, so the claim is exactly

\[
 \sup_{u\in\mathbb R}|P_{a,\sigma;Y}(u)-P_{a,\sigma;X}(u)|\longrightarrow0
 \quad(X,Y\to\infty).
\]

## 2. Hostile attack: deep-time phase alignment

Take the dyadic shell `X<n\le2X`, put `L=\log X`, and evaluate at

\[
 u_X=L^4,
 \qquad t_X=\sigma+iL^4.
\]

Uniformly for `X<n\le2X`, `\log n=L+O(1)` and

\[
 \sqrt{t_X^2+(\log n)^2}
 =t_X+O(L^{-2}).
\]

The standard sectorial asymptotic

\[
 K_1(z)=\sqrt{\frac{\pi}{2z}}e^{-z}(1+O(|z|^{-1}))
\]

therefore yields, uniformly on the shell,

\[
 \frac{2at_X K_1\!\left(a\sqrt{t_X^2+(\log n)^2}\right)}
 {\sqrt{t_X^2+(\log n)^2}}
 =\sqrt{2\pi a}\,t_X^{-1/2}e^{-at_X}
   \left(1+O(L^{-2})\right).
\]

Crucially, the leading phase is independent of `n`.  Positivity of
`\Lambda(n)` therefore prevents cancellation on this shell.  The prime number
theorem and partial summation give

\[
 \sum_{X<n\le2X}\frac{\Lambda(n)}{\sqrt n}
 =2(\sqrt2-1)\sqrt X+o(\sqrt X).
\]

It follows that, for some `c_{a,\sigma}>0` and all sufficiently large `X`,

\[
 \left|P_{a,\sigma;2X}(u_X)-P_{a,\sigma;X}(u_X)\right|
 \ge c_{a,\sigma}\frac{\sqrt X}{(\log X)^2}.
\]

The right side tends to infinity.  Thus the apertures are not merely
non-Cauchy in vertical sup norm: dyadic tail norms diverge cofinally.

## 3. Verdict

`[FALSIFIED]`.  Pointwise absolute convergence for every fixed `u` cannot be
upgraded to uniform convergence in `u`.  Every fixed finite aperture decays
like `|u|^{-1/2}` at vertical infinity, but a growing aperture can move its
common-phase radiation farther out and increase its amplitude exponentially
in the logarithmic cutoff.

Pole and archimedean terms cannot repair the failure because they cancel from
aperture differences.

## 4. Strongest positive survivor

The quantitative cofinal radiation-divergence theorem is recorded in
`docs/drafts/pipeline/2-fully-proven/mass-bessel-cofinal-radiation-divergence.md`.

It identifies the exact noncommuting limits:

\[
 \lim_{X\to\infty}\lim_{|u|\to\infty}P_{a,\sigma;X}(u)=0,
 \qquad
 \text{but convergence is violently nonuniform in }(X,u).
\]

## 5. Higher universal principle

The source-to-trace seam is a singular completion, not a Banach-space limit of
finite prime traces.  Uniform output stability, if true, must be created by
cancellation between every fixed aperture and primes at later cofinal scales.
No finite-aperture certificate can see it.

This is the mass-Bessel realization of the corpus-wide rule that regular scalar
completions cannot replace the missing source selector.

## 6. Prior-art collision

The proof uses only the classical sectorial asymptotic of `K_1` and the prime
number theorem.  No exact statement about divergence of the dyadic
mass-Bessel vertical sup tails was found in the internal corpus or external
collision search.  It is route-local new knowledge, not a claim of a new
Bessel asymptotic or prime number theorem.

## 7. Lean status

`[PAPER-PROVED]`, not yet `[LEAN-PROVED]`.  Mathlib lacks modified Bessel
functions, so exact formalization requires first adding the Fourier-integral
carrier and a uniform stationary-phase/asymptotic theorem.  No placeholder
interface is acceptable.
