# An independent quadratic count on arithmetic correspondences

- **ID:** RIAC-surface-count
- **Stage:** 0-backlog
- **Type:** CONJECTURE
- **Source:** [RIAC](../1-in-progress/renormalized-intersection-arithmetic-counts.md), arithmetic counts
- **Statement:** Construct integer counts on Hecke correspondences whose quadratic Tate coefficient is the full Weil form, with independently proved sign control.

## Required construction

Define the arithmetic objects, sections or finite counting spaces before
introducing `Q`. Establish scaling, correspondence composition and the local
contribution `deg p=log p`. The archimedean contribution must come from the
same construction and account for torsion self-energy. It cannot be chosen
to cancel negative values of the desired coefficient.

For a correspondence `D`, the target asymptotic is
`count(tD)=t² Q(D,D)+o(t²)` along positive integers. A nonnegative count
would force `Q(D,D)≥0`. If the count is instead an Euler characteristic,
its integrality gives no sign. One must separately bound the total negative
cohomological contribution by `o(t²)`, or prove another geometric sign law.
The existing Tate-count equivalence makes this a genuine RH-strength input,
not a missing definition that can be installed as a premise.

## Calibration before the global target

Recover curve counts for elliptic and hyperelliptic curves through their
actual sections or correspondences. Distinguish correspondences with the
same two degrees but different primitive data. Preserve full probe rank.
Identify the precise construction step that fails for Golden, the complex
fake, shifted data with nonnegative Tate coefficients and the genus-two graph.
A formal identity satisfied by those countermodels is insufficient.

## Existing lead and unresolved gap

[Connes–Consani](https://arxiv.org/abs/2205.01391) construct integer dimensions
and Riemann–Roch on the Arakelov compactification of `Spec ℤ`; see also the
[2024 refinement](https://www.numdam.org/articles/10.5802/crmath.543/).
These are arithmetic-curve results. The needed quadratic product geometry,
correspondence count and independent sign do not follow from that lead.

No arithmetic surface count satisfying these requirements has been constructed.
No Lean interface assuming such a count is accepted as a proof of existence.
