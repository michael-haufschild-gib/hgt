# Theta inner large-action current

Status: FORMALIZED (direct leaf and axiom audits passed). Route TH; neighboring routes TT and HCF.
Selected after reviewing all 27 live routes and 18 candidates, following the
user's explicit request to stop repeatedly working on one route.

## Exact proved subregion and remaining target

For the literal functions in `RHTower.ThetaCuspDefect`, the new leaf proves

`0 < enrichedClockCurrent u t` whenever `0 < t`, `t ≤ 2`, `t ≤ u`, and
`4050 * Real.exp 4 ≤ curvatureShapeAction u t`.

Removing the action threshold remains open. The stronger sufficient conjecture
`0 ≤ currentCorrelatedSourceRemainder u t` on the whole inner chamber also remains open.
The source-domain estimate does not establish all-degree heat-Hankel positivity
or RH. Any claimed landing needs a separate dependency audit.

## Existing source evidence

- `ThetaCuspC5OuterClockCurrent.lean` proves the actual complete current is
  positive for `2 ≤ t ≤ u`, retaining the clock and source derivatives.
- `ThetaCuspC5EnrichedClockCurrent.lean` defines the literal current and its
  derivative relation to the enriched inverse-source/clock ratio.
- `ThetaCuspC5ClockQuarticCancellation.lean` proves that replacing the clock by
  its quadratic relaxation makes the constant-shape current negative. Keeping
  the rational quartic correction restores that model's positive sign. The
  constant-shape model is not the actual theta source.
- `ThetaCuspC5CorrelatedFourthSource.lean` retains the local transport rate
  times the actual curvature defect and decomposes the current into the
  correlated remainder plus a Schur reserve and a strictly positive integral.
  The remainder's sign remains open. Repeating this decomposition is not new
  progress.
- `ThetaCuspC5IntrinsicClockGerm.lean` already proves the actual regularized
  intrinsic ratio has zero first three jets and a strictly positive fourth jet
  at nonnegative centers, then obtains local increase. Do not redo that germ.
  Check its exact relation to the enriched ratio before attempting to extend
  the source sign through the intermediate chamber.
- `XiHeatHankelFormOrthantPositivity.lean` and `XiHeatStableTestPositivity.lean`
  prove restricted all-degree small-time positivity. Neither discharges the
  arbitrary signed-polynomial sign in TH/HCF.

## Remaining work before any broader claim

1. The intermediate region `0<t<2`, `Z<4050 exp(4)` remains unpaid. The
   intrinsic local germ does not provide a uniform interval reaching this
   entire region; its transport to the enriched ratio also needs an exact audit.
2. Any interval extension must retain the rational clock and actual
   source-coordinate/curvature correlations.
3. Even a global current sign needs a separate all-degree heat-Hankel landing.
4. This bounded research cycle is finished. Reassess the route portfolio and
   choose a different mechanism; do not continue automatically with another
   theta-current refinement.

## Search and verification status

`scripts/formal_tools.py research "theta moment positivity heat source degree"
--json` completed with `partial=false` and no errors. Coverage was a stale
snapshot and semantic coverage unavailable. Candidate lemmas and source
arguments were inspected; no new closing producer was returned. No proof ideas
or ingredient sets were returned by that search.

A targeted deep search completed with query
`complete enriched inverse source clock current positivity small displacement
physical chamber`, budget 300 seconds, `partial=false`, no errors, and semantic
coverage unavailable. Output: `/tmp/hgt-theta-current-rotation-deep.json`;
exec session 15780 is terminal. All 20 candidate lemmas and 20 source arguments
were inspected. The one proposed ingredient set is explicitly `not_verified`
and leaves the connection from an unrelated coordinate current to this actual
current unproved; reject it as a closing argument. Exact source search found
the existing intrinsic germ omitted from the ranked result.

The bounded-action-free global inner sign is not claimed. No numerical
experiment or web research has been performed.
The frontier map and framework READMEs remain read-only. Concurrent BVI and
factorial-diagonal work is outside this card's write scope.

## Paper reduction: large action in the inner chamber

Positive subregion now checked in Lean: write `c0=c(u)`,
`E=completedDecayEvenPrimitive u t`, `Z=t E`, `k=sqrt(9/(2 c0))`.
For `0<t≤2`, `t≤u`, and `4050 exp(4)≤Z`, the complete actual enriched
clock current is strictly positive. This extends the outer-displacement
theorem into the inner chamber at large source action. It leaves the region
`0<t<2`, `Z<4050 exp(4)` unpaid, and does not prove RH.

Dependency-closed paper argument using source lemmas inspected above:

1. Let `e(s)=(c(u+s)+c(u-s))/2` and `p=e'`. The same literal source velocity
   bounds used in `beta_lt` give `p(s)<2e(s)` for `0≤s≤t≤u`.
   Differentiating `exp(-2s)e(s)` proves `e(s)≤c0 exp(2s)≤c0 exp(4)`.
   Since `E(0)=0` and `E'=e`, integration gives `E≤c0 t exp(4)`.
2. For normalized shape variables `a,b`, the existing bounds give
   `D=2a+b<2(1+t)(1+2t)≤30` and `T=D/(1+a)<2(1+t)≤6`.
   Exact denominator identities are `t d=D E`, `y=E(1+a)`, and `T=t d/y`.
3. The retained rational clock satisfies `C<T*linearClockEnvelope(k y)`
   and `linearClockEnvelope(z)<z+3` for `z>0`. Thus
   `C<k t d+3T<30kE+18`.
4. The source upper bound gives
   `(30kE)^2=4050 E^2/c0≤4050 exp(4) Z≤Z^2`.
   Both sides are nonnegative, so `30kE≤Z` and `C<Z+18`.
   As `Z≥4050 exp(4)>4050`, this is strictly below `1+12Z/5`.
5. Existing source laws give `gamma≥1`, positive reserves at parameters
   16 and 36, and positive flows at both parameters. The two current
   factors `(9+12Z+m gamma)/5-4-C` are therefore positive. Their reserve
   products plus flows, with the positive action-square enrichment, give
   the claimed actual current sign.

This argument uses no independent bounds on adverse high derivatives and no
numerical experiment. Exact source definitions and existing inequalities were
checked. An exhaustive source search in the C5 modules found no earlier
large-action threshold statement; this is not an external novelty claim.
Do not claim a globally positive inner current.

Implementation checkpoint: the scratch proof
`/tmp/hgt_ThetaInnerLargeActionCurrent.lean` finished with five elaboration
diagnostics: three `convert` sites needed `convert!`, and a positivity call
needed the explicit positive clock rate (one site emitted two diagnostics).
The corrected proof is now
`formal/GaloisForLFunctions/BiScaleUncertainty/ThetaInnerLargeActionCurrent.lean`.
Canonical session 31908 found one residual composition simplification in the
weighted derivative proof. `simp only [Function.comp_apply]` was added before
`ring`. The corrected canonical check with `lake --old env lean -j 1 -o ... -i ...`
passed in session 56759, producing `.olean` and `.ilean`. Log:
`/tmp/hgt-theta-inner-large-action-final.log`; only two unnecessary sequence-focus
style warnings remain. The module import is wired into `BiScaleUncertainty.lean`.
Source SHA256: `710545445bfb7538a8556b81d9a9e1372c3e5e78d25c58414a94c32079065bc5`.
Its 2,078 local dependency objects were present before launch.

The three-theorem axiom audit `/tmp/hgt_theta_inner_axioms.lean` passed in
session 94525. Every theorem depends only on `propext`, `Classical.choice`, and
`Quot.sound`; log `/tmp/hgt-theta-inner-axioms.log`. The canonical source hash
was unchanged after this audit. No owned Lean process remains active.

Final index session 20944 passed (one changed module), log
`/tmp/hgt-rotation-final-index.log`. Final lint session 94539 exited 1 solely on
five concurrent modules unreachable from their umbrellas: `EndpointCycleDeterminant`,
`SharpCycleGramRealization`, `SharpGramDetectionOrder`,
`StationaryResolventMarkovPositivityAndNodalDefectProducer`, and
`SixModeStabilityAndSharpQuarterDecorrelation`. No error concerned this
contribution, and no forbidden declaration was reported. The global lint gate
is not claimed passed. RW's larger dependency closure is still being rebuilt
by an external worker. Manifest: `/tmp/hgt-theta-inner-audit-manifest.json`.

Audit boundary: the producer uses the literal theta source and complete clock,
with an explicit action threshold and no zero-divisor or RH premise. It proves
no all-degree heat-Hankel sign. After this bounded cycle, reassess another route
family or candidate; do not spend the next cycle tuning the constant 4050.
