# CCM-FU: incompatible fixed weights and exact completion intervals

- Stage: 3-formalized.
- Type: source-specific local obstruction and exact positive classification.
- Modules: `MobiusDivisorTransverseDissipationTrap`, `DivisorTwentyTwoAnalyticBounds`.
- Main complete-path candidate: [fixed coercive head weight](../1-in-progress/ccm-fu-weighted-head-dissipation.md), still open.

## Result and relation to RH

Write Q for actual retained energy, H for its empty-label head and V=Q-H².
The new definition is `L_alpha=V+alpha H²`. For 0≤alpha≤1, Lean proves

`0≤L_alpha`, `alpha Q≤L_alpha≤Q`.

Thus a fixed positive alpha and complete nonincreasing L_alpha paths at
every cutoff would bound the terminal signed arithmetic sum using the
already proved quadratic initial diagonal. Those paths are not proved.

The stronger rule demanding a nonincreasing next operation at every
proper actual state is false for EVERY real fixed alpha, already at
cutoff 25. The obstruction uses two states of the same arithmetic source,
not artificial coefficients. Each state admits a complete monotone order
under its own positive head weights; their exact intervals are disjoint.

## Exact positive classification

Let P={2,7,11,13,17,19,23}. Its remaining labels are empty, {3}, {5}
and {3,5}, with actual coefficients h,a,b,c. The existing analytic
source bounds give

`-.75≤h≤-.73`, `.007≤a≤.010`, `.013≤b≤.015`, `.173≤c≤.175`.

Define the source-derived threshold

`sigma=(2ac-b²)/(h²-(h+b)²)`.

Lean proves `1/20<sigma<1/5`. For every nonnegative alpha, a complete
nonincreasing L_alpha order of the two remaining primes exists exactly
when `sigma≤alpha`. Prime five is the strictly better first choice for
every nonnegative alpha. The second step of either order strictly
decreases both nonempty energy and head square. Consequently the exact
first-step comparison supplies the complete two-step criterion.

The other actual state is T=primes_below_25\{7}. Put

`t=-K_7+K_14+K_21`, `g=h+a+b+c-t`,

where K denotes the actual unsigned dilation channels at cutoff 25.
Only head g and the seven-singleton t survive. A new analytic theorem
proves `-.020≤t≤-.017`; the four earlier bounds imply `g≤-.51`.
Define

`beta=t²/((g+t)²-g²)`.

Lean proves `0<beta<1/20`. The sole remaining seven merger is
nonincreasing for L_alpha exactly when `alpha≤beta`, for every real
alpha. This completes the second exact admissible-weight classification.

Thus positive weights work separately on both actual states, while no
weight works on both. These intervals are the positive survivor of the
failed universal local rule. They do not classify paths from the empty
processed core; such paths can avoid incompatible states.

## Analytic proof of the incompatibility

At P the two possible L_alpha gains are

`2bc-a²+alpha((h+a)²-h²)`,
`2ac-b²+alpha((h+b)²-h²)`.

Both head-square changes are negative. The proved V increases exceed
1/500; analytic head and singleton bounds show both weighted gains stay
positive for every alpha≤1/20. For nonnegative alpha the difference of
the first and second successor potentials is

`(a-b)[alpha(2h+a+b)-(a+b+2c)]>0`.

Hence five is uniformly preferable. Its gain is negative at alpha=1/5,
positive at alpha=1/20, and affine with strictly negative slope. This
proves the exact sigma criterion, including its strict rational bounds.

At T, exact source sum preservation and the one-remaining-prime identity
give the two coordinates g,t. Its gain is

`alpha((g+t)²-g²)-t²`.

The denominator in beta is positive. Since g≤-.51 and -.020≤t≤-.017,
the gain is strictly positive already at alpha=1/20 and increases with
alpha. At alpha=0 it is strictly negative. This proves the exact beta
criterion and rational bounds. Splitting arbitrary alpha at 1/20 now
constructs a proper actual core whose every next operation increases
L_alpha. No numerical interval supplies a proof premise.

## Lean declarations

- `mobiusDivisorWeightedHeadEnergy_bounds`: positivity and full-energy comparison.
- `mobiusDivisorTwentyFiveWeightThreshold_bounds`: `1/20<sigma<1/5`.
- `mobiusDivisorTwentyFive_weighted_completion_iff`: exact two-prime completion criterion.
- `mobiusDivisorWeightedHeadEnergy_twentyFive_local_obstruction`: failure for every fixed real weight.
- `mobiusDivisorTwentyFiveSevenWeightThreshold_bounds`: `0<beta<1/20`.
- `mobiusDivisorTwentyFive_seven_weighted_completion_iff`: exact one-prime criterion.
- `divisorUnsignedDilationChannel_twentyFive_seven_leaf_box`: analytic source bound for t.

## Scientific evidence and validation

The [single RunPod diagnostic](../2-fully-proven/computations/ccm-fu-weighted-head-dissipation-2026-09-08/README.md)
finds complete monotone paths at every saved cutoff through 32 for a
common positive weight interval extending slightly beyond 1/5. This
remains finite guidance. The stronger local rule fails at 25 independently
of smaller cutoffs. Both assertions were evaluated over full weight
intervals without a grid; restrictive cutoffs were independently rebuilt
from the source at 80 digits. Runtime was under one second; all owned
remote files and workers were cleaned up.

Scratch proofs and exact foreground `lake env lean` emissions passed for
both changed leaves. All seven new public theorems were axiom-audited once
in a temporary file; each uses only `propext`, `Classical.choice` and
`Quot.sound`. No previously audited theorem was re-audited. Both changed
modules are already wired into RHTower; no new module was introduced.

Generated indexes were refreshed. The single global
`scripts/formal_tools.py lint --check-generated` run reported one unrelated
concurrent module missing its RHTower umbrella import:
`GaloisForLFunctions.RHTower.SelbergMaassCuspTransport`. Neither changed
proof leaf was flagged; no proof-debt error was reported. The unrelated
module was not edited or built by this task. Owned-scope whitespace checks
passed. Owned scratch files were removed and all owned processes exited.

No full or umbrella build ran. A scoped Lake package audit remains pending
because earlier package planning expanded prohibited broad dependencies;
that planning was not repeated. This task made no frontier-map edits.
