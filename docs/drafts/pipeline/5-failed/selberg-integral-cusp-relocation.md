# Integral cusp relocation cannot replace core control

- **ID:** SELBERG-INTEGRAL-CUSP-RELOCATION
- **Stage:** 5-failed, specific covering shortcut only.
- **Parent:** [Constructive Selberg loop](../1-in-progress/selberg-quarter-conjecturing-loop.md), cycle 13.

## Proposal and failure

After proving zero constant Fourier term, try to apply the cusp-tail quarter inequality everywhere by choosing a suitable integral cusp coordinate at each point.

The inspected modular-height theorem bounds every translated height by `max(y,1/y)`. Thus the modular orbit of `i` never rises above one. More strongly, for every cutoff `M>1`, the open band `1/M<Im(z)<M` is nonempty and every integral translate of every point in it has height strictly below `M`. The shortcut therefore fails on an open region, not only an isolated point.

This retires only the claim that integral cusp relocation alone supplies the required covering. It does not retire the full analytic route, a core-plus-cusp gluing argument, or the Selberg conjecture. The frequency-to-width energy bridge has not been assumed in making this geometric statement.

## Positive survivor after second pass

The first failure witness is the point `i`. The second pass extracts the sharp result: the imaginary-axis orbit has attained maximum `max(y,1/y)`, giving an exact classification of reachable cutoffs. It also gives the explicit nonempty open excluded band at every cutoff above one.

**New insight for this loop:** moving among all integral cusp coordinates cannot eliminate the core obligation. The obstruction retains an exact height threshold and a full open region, so it is not an artifact of a chosen cusp or isolated point.

**Paper status:** complete, using the actual modular denominator bound and the two attaining matrices, identity and inversion.

**Lean status:** complete in `SelbergCuspRelocation`, including the exact maximum, reachability equivalence, reciprocal-band estimate, openness, nonemptiness, and uniform failure of relocation on the band. [Positive-survivor proof and audit](../3-formalized/selberg-sharp-cusp-orbit-height.md).

## Live successor

Use the established constant-term elimination and tail identity while keeping the compact-core boundary response explicit. Any spectral closure now needs actual core or arithmetic information; integral coordinate changes are insufficient by themselves.
