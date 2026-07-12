# Prime–archimedean source upper-bound RH gate

- **ID:** `prime-arch-source-upper-bound-rh-gate`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** RH is equivalent to the existence of any finite global upper bound for the
  imaginary part of the continued prime--archimedean source on its centered upper-half-strip
  pole-free domain.

## Goal

Weaken the rank-one anti-Herglotz sign to a source estimate that does not require positivity. The
local positive-multiplicity pole law shows that an off-line zero forces positive blow-up, so mere
boundedness above is enough.

## Theorem

Let

\[
T(z)=\texttt{continuedPrimeArchSourceRelativeTrace}(z).
\]

Define the source domain by

\[
0<\operatorname{Im}z<\frac12,
\qquad
\zeta\!\left(\frac12+iz\right)\ne0.
\]

Then

\[
\mathrm{RH}
\iff
\exists C\in\mathbb R\ \forall z,
\quad \operatorname{Im}T(z)\le C.
\]

The reverse implication is quantitative. If RH fails, a right-half Xi zero reflects to a zero
`sigma` in the left half-strip. Along `s_n=sigma+1/(n+1)`, the normalized local logarithmic
derivative satisfies

\[
(s_n-\sigma)\frac{\xi'(s_n)}{\xi(s_n)}
\longrightarrow m,
\qquad m\ge1.
\]

After returning to the centered coordinate this gives

\[
\forall C\in\mathbb R\ \exists z,
\quad \operatorname{Im}T(z)>C.
\]

Thus failure of RH is not merely a sign violation: it creates unbounded positive source charge.

There is also a countable original-coordinate form. With

\[
F(s)=-\frac{\zeta'(s)}{\zeta(s)}-
  \frac{\operatorname{archFactor}'(s)}{\operatorname{archFactor}(s)},
\]

RH is equivalent to the existence of any finite lower bound for `Re F(s)` on the
Gaussian-rational points of `0 < Re s < 1/2` where `zeta(s) != 0`. Density and continuity upgrade
the countable bound to the complete source domain.

## Positive carrier law

A successful prime, theta, Sonin, determinant, or contour construction no longer needs to prove
the sharp sign `Im T <= 0`. It is sufficient to prove any finite uniform upper bound on `Im T` over
the centered upper half-strip. The bound may be positive and need not be explicit.

This interfaces directly with inverse-horizontal-charge estimates: every off-line pole of depth
`a` produces a positive source excursion of order `1/a` near its reflected location. A source norm
or maximum-principle estimate preventing such excursions closes RH.

## Lean certificate

Module:

- `formal/GaloisForLFunctions/RHTower/PrimeArchSourceUpperBoundGate.lean`

Main declarations:

- `ContinuedPrimeArchUpperImBoundedAbove`
- `riemannHypothesis_of_continuedPrimeArchUpperImBoundedAbove`
- `continuedPrimeArchUpperImBoundedAbove_of_riemannHypothesis`
- `continuedPrimeArchUpperImBoundedAbove_iff_riemannHypothesis`
- `exists_continuedPrimeArchSource_im_gt_of_not_riemannHypothesis`
- `CompletedPrimeGammaGaussianRatLeftHalfBoundedBelow`
- `completedPrimeGammaGaussianRatLeftHalfBoundedBelow_iff_riemannHypothesis`

Verification:

- `lake build GaloisForLFunctions.RHTower.PrimeArchSourceUpperBoundGate` passes.
- Axiom audit: only `propext`, `Classical.choice`, and `Quot.sound`.

## Gates

- [x] 0 → 1 in-progress: finite-upper-bound weakening identified
- [x] 1 → 2 fully-proven: local-pole blow-up proof completed
- [x] 2 → 3 formalized: exact equivalence and quantitative failure law proved in Lean
- [ ] 3 → 4 publication-ready: connect a concrete source norm estimate to the global bound
