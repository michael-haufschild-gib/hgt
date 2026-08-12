# Fisher compactness is selection properness

- **ID:** ULF-PRCM-FAIL-1
- **Stage:** 5 — falsified
- **Type:** FALSIFIED FIELD CONJECTURE
- **Statement:** Relative compactness or finite total length in the positive Fisher geometry of an
  amplified formation forces bounded reciprocal information work and can serve as a selector.

## Exact countermodel

For the balanced Bernoulli escort

\[
 p_t(1)=\frac{e^t}{1+e^t},
\]

the Fisher response is

\[
 I(t)=\frac1{4\cosh^2(t/2)}.
\]

Its entire natural-parameter orbit has Fisher length

\[
 \int_{-\infty}^{\infty}\sqrt{I(t)}\,dt=\pi,
\]

and compactifies to the two closed-simplex vertices.  Its reflected Jeffreys work is

\[
 J(p_t,p_{-t})=2t\tanh(t/2)\to\infty.
\]

More strongly, every Fisher tail has diameter tending to zero while every Jeffreys tail has
infinite diameter.

## No-go closure

- **Exact killing theorem/mechanism:** ULF-PRCM-1.  Fisher length uses root accumulation
  `int sqrt(I)`; reciprocal work uses aperture-weighted response mass
  `(b-a) int I`.  They share a local germ but define different bounded sets and completions.
- **Strongest positive survivor:** response-polarization law, common-recovery invariance, and
  observer-deficit escape theorem together with the exact global law
  `bounded complete reflected work iff response vanishes` in
  `pipeline/2-fully-proven/universal-law-field/polarized-response-completion-mechanics/response-polarization-fisher-tail-collapse-and-jeffreys-tail-escape-law.md`.
- **New insight:** compact positive observation is compatible with, and can conceal, globally
  proper law history.  RH selection needs a complete-work bound or a sufficiency theorem, not
  Fisher compactness.
- **Status:** falsification and survivor are dependency-closed on paper.  Lean formalization remains
  open, so this no-go is not marked formally closed under the project's Lean standard.

## Log

- 2026-08-12 — conjecture killed by the binary escort and generalized to every nonconstant finite
  escort family; positive survivor promoted to ULF-PRCM-1.
