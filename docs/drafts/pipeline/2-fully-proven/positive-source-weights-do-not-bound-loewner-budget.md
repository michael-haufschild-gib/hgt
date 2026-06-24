# Positive Source Weights Do Not Bound Loewner Budget

- **ID:** positive-source-weights-do-not-bound-loewner-budget
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / source-transfer guardrail
- **Source:** `positive-source-weights-require-pointwise-hankel-kernels.md`,
  `axis-positivity-does-not-imply-hankel-positivity.md`,
  `source-selector-repair-obligation-ledger.md`
- **Statement:** Positive source weights can certify a cone direction only after
  the pointwise kernels have the right sign. They do not certify a fixed
  Loewner upper budget. A budget theorem needs scale data, normalization, or a
  source identity beyond positivity.

## Setup

Let `V` be a finite-dimensional real Hilbert space. Let `B >= 0` be a fixed
positive semidefinite form on `V`. Let `X` be a source set and let

`K_x >= 0`, for `x in X`,

be positive semidefinite source kernels.

For a finitely supported nonnegative weight function `w:X -> R_{\ge 0}`, set

`S(w)=sum_x w_x K_x`.

The repair bridge needs an inequality of the form

`S(w) <= B`

in the Loewner order. In the zeta route, this models the desired domination

`-R^P_d <= M_{triv,d}`.

## Theorem

Assume

`S(w) <= B`

for every finitely supported nonnegative weight `w`. Then `K_x=0` for every
`x in X`.

Equivalently, if any pointwise positive source kernel is nonzero, positivity of
the weights alone cannot imply a fixed Loewner budget for all positive weights.

## Proof

Fix `x_0 in X` and take the point mass weight

`w=t delta_{x_0}`, with `t>=0`.

The assumed budget inequality gives

`t K_{x_0} <= B`

for every `t>=0`.

For any vector `v in V`,

`t <K_{x_0}v,v> <= <Bv,v>`

for every `t>=0`. Letting `t -> infinity` gives

`<K_{x_0}v,v> <= 0`.

Since `K_{x_0}>=0`, this forces `<K_{x_0}v,v>=0` for every `v`. Hence
`K_{x_0}=0`. The source point was arbitrary.

## Normalized Variant

If the weights are constrained by a total-mass bound, with `C>0`,

`sum_x w_x <= C`,

then

`S(w) <= B` for every such `w`

is equivalent to the pointwise budget condition

`C K_x <= B` for every `x in X`.

Necessity follows by taking `w=C delta_x`. For sufficiency, use
`K_x <= B/C` and sum:

`S(w)=sum_x w_x K_x <= (sum_x w_x/C) B <= B`.

This is the budget analogue of the pointwise-kernel positivity theorem. Once a
proof appeals only to positivity plus a total-mass bound, the whole problem has
not disappeared; it has moved to pointwise Loewner domination at the correct
scale.

## Consequence for the Euler-Product Transfer

The sign pattern

`w_x >= 0`

can show that a source sum lies in a positive cone, assuming the source kernels
themselves are positive. It cannot show that the sum fits under a fixed
archimedean budget.

Thus the bridge target

`-R^P_d <= M_{triv,d}`

cannot be proved from positive Euler/local-factor weights alone. A valid source
proof must provide at least one of the following:

1. exact arithmetic weights and a direct estimate of the actual sum;
2. a normalization or total-mass theorem plus pointwise budget bounds;
3. multiplicative structure that prevents arbitrary cone scaling;
4. archimedean cancellation or a completed explicit-formula identity that is
   stronger than coefficient positivity.

Positive signs can increase the finite-place demand. They do not cap that
demand.

## Theatre Test

When a proposed proof says that Euler positivity controls the repair, ask:

1. Does it prove only that the prime/source part has a favorable sign?
2. Where is the fixed upper budget `M_{triv,d}` used?
3. Are the actual Euler weights used with their magnitudes, or only with their
   signs?
4. If the proof were repeated with `t` times the same positive weights, what
   line would fail?

If no line fails under scaling, the argument has not proved a budget theorem.

## Route Impact

This theorem does not prove RH. It removes a common fake bridge:

`positive Euler coefficients => Loewner domination`.

The live theorem is sharper:

`actual Euler/Gamma/FE source data => -R^P_d <= M_{triv,d}`,

uniformly in degree and channel scale.

That claim is a scale-sensitive domination theorem, not a sign theorem.

## Novelty Status

The matrix-cone argument is elementary and not claimed as external mathematical
novelty. Its value in the pipeline is diagnostic: it marks the exact point at
which an Euler-positivity proof stops being evidence for the RH bridge unless
the proof also supplies scale control.

## Gates

- [x] 0 -> 1 in-progress: Loewner budget gap isolated.
- [x] 1 -> 2 fully-proven: scaling proof and normalized variant completed.
- [ ] 2 -> 3 formalized: finite PSD cone lemma.

## Log

- 2026-06-24 -- Codex: created to separate source sign positivity from the
  fixed archimedean-budget domination required by the bridge theorem.

## 2026-06-24 contraction form is the same Loewner budget

`loewner-contraction-congruence-normalization.md` records the finite-dimensional coordinate change behind the budget statement. For a positive budget `M`,

`-R<=M <=> M^(-1/2)(-R)M^(-1/2)<=I`.

Therefore moving from the Loewner inequality `-R^P_d<=M_triv,d` to the relative contraction `K_d<=I` does not by itself add proof content. The missing theorem remains scale-sensitive source domination of the actual residual by the actual Gamma/trivial-zero budget.

## 2026-06-24 scale-invariant orientation version

`scale-invariant-source-orientation-cannot-pay-budget.md` gives the general form of the scaling obstruction. A source predicate closed under `R -> tR` can imply `B+R>=0` for a fixed budget `B` only if every admissible residual `R` is already PSD.

Thus the issue is not limited to positive source weights. Any orientation-only proof must identify where the exact residual magnitude enters; otherwise it cannot prove `-R^P_d<=M_triv,d`.
