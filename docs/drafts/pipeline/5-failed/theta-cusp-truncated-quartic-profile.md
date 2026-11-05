# Truncated quartic flux: scale-six obstruction and exact capacity

- **Stage:** 5-failed
- **Type:** FALSIFIED; positive survivor formalized
- **Wall:** Σ6
- **Refuted claim:** The profile `P₊(r)=max(1−r²/2,0)²` makes the fifth even source positive at every radius and critical aperture.

Put `x₆=log(6/π)/2`, `r₆=2x₆`, `H=H₅(x₆)`,
`B=loadMapᵀ paidSevenSchur loadMap`, and `K=4·6²exp(x₆−12)`.
The complete quartic correction satisfies

`−126K ≤ G_P(x₆) ≤ −(1251/10)K`.

The normalized complete native source differs in every quadratic direction
from the rational leading-pair model with weight `1522998/10¹⁴` by at most
`(1/20)∑vᵢ²`. The rational model with normalized load coefficient `−100` and positive
allowance `(1/20)I` has a negative direction, proved by exact Schur elimination.
Consequently every complete-source coefficient `c≤−100K` fails PSD.
No theta atom is omitted from the error bound.

For `0<a<1/2`, division by `r₆sinh(ar₆)` leaves an aperture remainder
of at most `(83/17)K` above `G_P`. Thus the literal weighted
source also fails PSD at `r₆`. Since `r₆≤2/3<√2`, truncation leaves this
obstruction unchanged.

## Positive survivor

There is a sharp `τ₆` with `0<τ₆<1000/1251` such that, for every real `t`,

- `H+tG_P(x₆)B` is PD exactly when `t<τ₆`;
- it is PSD exactly when `t≤τ₆`;
- its matrix at `t=τ₆` is singular and PSD.

Native positivity gives the nonempty initial interval. Since `G_P(x₆)<0`
and `B` is PSD, the pencil is decreasing. Continuity closes the interval
at a PSD endpoint; strict positivity would extend it. Any PSD point beyond
the endpoint would make that endpoint PD by convexity with the native source.
At `t=1000/1251`, the scalar bound gives load at most `−100K`, hence strict
failure and the stated upper bound.

For every `0<a<1/2`, the literal coefficient `c_a` satisfies
`G_P≤c_a≤−120K`. Together with `G_P≥−126K`, this gives
`c_a=α(a)G_P` with `20/21≤α(a)≤1`. Its exact scaling capacity is `τ₆(a)=τ₆/α(a)`, hence
`τ₆≤τ₆(a)≤21τ₆/20<350/417`. Strict positivity, semidefiniteness, and
singularity have the same endpoint classification because the weighted matrix
is `r₆sinh(ar₆)` times the base pencil at load `tα(a)`.

The profile still preserves every mixed integral and gives a PD literal
weighted source for `q≥7`, together with an origin neighborhood. Those
positive results do not imply integrated rank-nine positivity.

## No-go closure

- **Killing mechanism:** negative complete-source direction at scale six, inside the truncation support, persisting for every `0<a<1/2`.
- **Strongest positive survivor:** the exact base and aperture scaling intervals, singular PSD endpoints, and uniform aperture-capacity bound `τ₆(a)<350/417`.
- **New insight:** deleting the outer branch cannot repair the loss; a successful profile with this fixed load must change its flux derivative at scale six.
- **Paper proof:** dependency-closed as above.
- **Lean:** `SixSourceBounds.truncated_weightedRepair_not_posSemidef` and `SixCrossCapacity.exact_scaling_capacity`, and the endpoint classification in `SixApertureCapacity`, in `FifthEvenScaleSixSourceBounds.lean`, `FifthEvenScaleSixCapacity.lean`, and `FifthEvenScaleSixApertureCapacity.lean`. All nineteen transitive audits use only `propext`, `Classical.choice`, and `Quot.sound`. All five canonical checks passed. The four new modules are wired into the owner umbrella.

Supporting results: [entry preservation](../3-formalized/truncated-quartic-flux-preserves-fifth-even-matrix.md),
[positive upper ray](../3-formalized/theta-cusp-quartic-cross-load-ray.md),
[complete scalar bounds](../3-formalized/quartic-theta-compensation-interval-reserves.md),
[four-atom remainder](../3-formalized/four-atoms-control-the-fifth-even-source.md).
