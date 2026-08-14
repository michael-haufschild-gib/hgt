# Common mass recovery and affine Ward conservation select the normalized source current

- **ID:** ULF-SRSM-FAIL-2
- **Stage:** 5 — failed
- **Type:** FALSIFIED SELECTOR
- **Source:** attempted fusion of ULF-SRSM-8 and Inverse-Response Ward Mechanics
- **Statement:** Differentiate the source-normalized probability formation, apply common mass
  recovery as a Ward reporter, and use affine source response to force the positive response current
  to vanish.

## Goal

Close the remaining SRSM physical-current gate without introducing a route-specific reporter:
probability formation would supply topology and common recovery, while inverse-response Ward
conservation would supply the null identity.

## Exact killing theorem/mechanism

For every differentiable probability family `mu_t`,

\[
 \frac{d^n}{dt^n}\mu_t(\Omega)=0\qquad(n\ge1).
\]

Thus common mass recovery annihilates every positive-order normalized shape jet. More strongly,
the all-order Leibniz jet of `c(t)mu_t` recovers only `c^(n)(t)`; shape derivatives lie in the
vertical kernel. Every linear reporter invariant under all Markov refinements factors through mass
and annihilates the same tower.

In score coordinates, affine normalized response gives

\[
 s'+s^2=0
\]

pointwise, but this does not imply `s=0`. For

\[
 p_t(+)=\frac{1+t}{2},\qquad p_t(-)=\frac{1-t}{2},
\]

the Fisher mass at zero is one and the mean score derivative is minus one. Ward balance is exact
because those two terms cancel.

## No-go closure

- **Exact killing theorem/mechanism:** normalized positive-order jets lie in the mass kernel;
  universal Markov-invariant reporters are mass reporters; affine Ward balance is Bartlett
  cancellation, not faithful-square selection.
- **Strongest positive survivor:** all-order coefficient/shape jet splitting plus the exact law
  that Markov Fisher loss equals migration of the mean Ward connection.
- **New insight:** “landing in the common formed range” is insufficient. The physical current must
  be typed as a recovered coefficient jet or as a vertical shape jet with a separately derived
  nonconstant harmonic/boundary reporter.
- **Status:** survivor dependency-closed on paper in
  `../../../2-fully-proven/universal-law-field/source-response-signature-mechanics/normalized-jet-splitting-markov-coinvariant-and-ward-anomaly-migration-law.md`.
  Lean remains read-only in this research pass.

## Log

- 2026-08-14 — conjecture killed by the two-point normalized affine family; all-order and Markov
  classification proved; positive survivor promoted to Stage 2.
