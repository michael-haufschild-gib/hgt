# HB FF: weighted admission for the original cap source

Target: full temporal/metric/left-QNM matching. The previous turn is progress:
ModularBallGrowth proves the actual response's quantitative mean-square bound.
This card attacks the remaining absolute-integration step, not a substitute
source or clock. Full matching and RH remain open.

[BRIDGE] Attach weighted absolute integrability to the actual response and
then to the full source `B-s(s-1)Q/4`, at the original physical exponent
`p=1-2 Re(s)>3`. Frozen analytical proof is in
`hb-fe-absolute-angular-admission.md`.

Exact ball-area formula is unnecessary for this estimate. From the original
hyperbolic metric formula, a radius-R ball about i satisfies
`y>=exp(-R)` and `x^2<=2 exp(R)y`. It lies strictly between the graphs
`x=+-2 exp(R/2)sqrt(y)`. In the original measure `dx dy/y^2`, the enclosing
region has area `4 exp(R/2) integral_(exp(-R))^infinity y^(-3/2)dy=8 exp(R)`.
Combined with the actual mean-square estimate this gives L1 ball growth
`C exp(5R/2)`. Geometric shell summation then admits all weights with p>5/2
for the remainder. The already established cusp/square growth bounds provide
the remaining source terms for p>3.

Formal status: `ThetaCuspHawkingBMWeightedResponseAdmission` proves the actual
hyperbolic area bound, absolute ball growth `C exp(5R/2)` of `globalResponse`,
and its weighted absolute integrability for every `p>5/2`. The native L2 input
is discharged; no additional growth premise is imposed on that response.
Scratch check: 5.69 seconds. Exact single-module audit: 7.26 seconds, two jobs,
no warnings, default heartbeats; umbrella import wired without building it.
Repository lint still reports the pre-existing unreachable
`ThetaCuspHawkingBMOnsetTransgressionHorizon` module and existing size warnings;
the new leaf is reachable. Audited source and installed source match exactly.
The full cutoff, `Q`, physical exponent and two-arm plane-kernel admission are
now attached in `hb-fg-complete-source-admission.md`. The global cap identity,
parameter differentiation and physical left-QNM field/action matching remain
open. Existing cap identities, clock, characteristic gates and both arms are
retained. The admission results do not prove full matching.

Search evidence: broad polar/regionBetween and deep/method shell-admission
queries. Partial=false for completed searches; compiler metadata mostly
pending/source-only. A retrieved statement is not treated as a checked lemma.
Broad recent arXiv searches coarea/localization found
[Liu, 2605.08309](https://arxiv.org/abs/2605.08309) and
[Vergara, 2603.23645](https://arxiv.org/abs/2603.23645). Their change-of-variable
and pushforward viewpoints suggest keeping exact density transport explicit;
neither abstract discharges this source's estimates, and no result is assumed.
