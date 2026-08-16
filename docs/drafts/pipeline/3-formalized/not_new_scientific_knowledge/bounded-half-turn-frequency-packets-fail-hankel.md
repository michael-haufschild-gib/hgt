# Bounded Half-Turn Frequency Packets Fail The First Hankel Gate

- **ID:** bounded-half-turn-frequency-packets-fail-hankel
- **Stage:** 3-formalized
- **Type:** THEOREM (paper) / source-transfer guardrail
- **Grade:** BRIDGE / guardrail. The theorem quantifies how much cross-scale
  spread is necessary before the half-turn repaired frequency model can even
  pass the first shifted Hankel test.
- **Source:** `../../3-formalized/not_new_scientific_knowledge/half-turn-repaired-frequency-not-markov.md`;
  `positive-source-weights-require-pointwise-hankel-kernels.md`

## Statement

Let

`theta=(17+2 sqrt(70))/3`.

Let `c_i>0` and `x_i>0` be a nonzero finite positive packet of half-turn
repaired squared frequencies, and define

`M_k=sum_i c_i x_i^k`,

`U_k=M_k/(2k-1)!`.

If the squared-frequency support lies in a multiplicative interval
`[a,b]`, with `0<a<=b`, and

`b/a < theta`,

then the first shifted Hankel determinant is strictly negative:

`U_1 U_3 - U_2^2 < 0`.

Equivalently, for a positive repaired packet to pass the first Hankel gate, it
is necessary that its squared-frequency support have ratio at least `theta`.
In the original frequency variable `lambda`, this means a necessary frequency
ratio at least

`sqrt(theta)=sqrt((17+2 sqrt(70))/3) ~= 3.353`.

This separation condition is necessary, not sufficient.

## Proof

Write

`U_1=M_1`,

`U_2=M_2/6`,

`U_3=M_3/120`.

Then

`U_1 U_3-U_2^2=(3 M_1 M_3-10 M_2^2)/360`.

It remains to bound the moment ratio `M_1 M_3/M_2^2`. Since the packet is
nonzero and `c_i,x_i>0`, `M_2>0`. Define a probability packet

`p_i=c_i x_i^2/M_2`.

Then

`M_3/M_2=sum_i p_i x_i`,

and

`M_1/M_2=sum_i p_i / x_i`.

For each `x_i in [a,b]`,

`x_i + ab/x_i <= a+b`,

because `(x_i-a)(x_i-b)<=0`. Averaging against `p_i`, with

`u=sum_i p_i x_i`,

`v=sum_i p_i / x_i`,

gives

`u+ab v <= a+b`.

Since `u>0` and `v>0`,

`4abuv <= (u+abv)^2 <= (a+b)^2`.

Therefore

`M_1 M_3/M_2^2 = uv <= (a+b)^2/(4ab)`.

Put `r=b/a`. The inequality needed for a nonnegative first Hankel determinant is

`M_1 M_3/M_2^2 >= 10/3`.

But

`(a+b)^2/(4ab) = (r+1)^2/(4r)`.

The equation

`(r+1)^2/(4r)=10/3`

is

`3r^2-34r+3=0`,

whose roots are

`(17-2 sqrt(70))/3` and `(17+2 sqrt(70))/3=theta`.

For `1<=r<theta`, the ratio `(r+1)^2/(4r)` is strictly less than `10/3`.
Thus

`3 M_1 M_3 < 10 M_2^2`,

so

`U_1 U_3-U_2^2 < 0`.

At the endpoint `r=theta`, this argument gives nonpositivity. Equality requires
an extremal two-endpoint distribution with the balancing condition hidden in
the Cauchy/AM-GM step, so the strict failure statement is stated for
`b/a<theta`.

## Consequence

The half-turn repair does not merely fail on single atoms. It also fails on
finite positive repaired packets whose squared-frequency support lies in any
multiplicative interval of ratio strictly below `theta`.

Therefore the surviving source proof cannot be a local packet argument around
nearby FE-even frequencies. It must provide broad cross-scale interaction with
squared-frequency ratio at least `theta`, and then still prove the higher
Hankel gates. The alternative is nonlinear multiplicative correlation, signed
completed counterterms, or a boundary/index object whose positivity is not
assembled from narrow repaired frequency packets.

## Boundary

This theorem does not rule out broad repaired packets, infinite measures,
signed completed corrections, multiplicative correlations, or a closed
boundary/index proof. It only proves that a positive half-turn repaired
frequency model must clear a quantitative cross-scale gate before the first
Hankel square test can even be nonnegative.

The earlier two-frequency cross-term threshold `(10+sqrt(91))/3` only marks
when a positive cross coefficient can appear. It is not enough to make the full
determinant nonnegative, because the two diagonal negative terms still have to
be paid. The optimized first-gate spread threshold is
`theta=(17+2 sqrt(70))/3`.

## Theatre Test

For any proof that invokes the half-turn and then mixes repaired frequencies:

1. Is the mixture positive and finite?
2. Is its squared-frequency support contained in a multiplicative interval of
   ratio strictly below `(17+2 sqrt(70))/3`?
3. If yes, the first shifted Hankel determinant is negative.
4. If no, identify the source mechanism that forces the required cross-scale
   separation and then prove the remaining all-order Hankel tests.

## Novelty Status

The algebra is elementary. The significance is route control: the half-turn
route now has a quantitative first-gate obstruction, not only a one-atom
counterexample. The proof identifies a necessary cross-scale spread that any
positive repaired frequency model must source-build.

## Gates

- [x] 0 -> 1 in-progress: post-half-turn packet loophole isolated.
- [x] 1 -> 2 fully-proven: determinant expansion and threshold proof written.
- [x] formal core: two-frequency numerator identity and negative criterion
  proved as
  `GaloisForLFunctions.twoFrequency_halfTurn_pairNumerator_identity` and
  `GaloisForLFunctions.twoFrequency_halfTurn_det_neg_of_cross_nonpos`.
- [x] formal core: optimized moment-ratio and two-frequency quadratic criteria
  proved as `GaloisForLFunctions.halfTurn_det_neg_of_moment_ratio_lt` and
  `GaloisForLFunctions.twoFrequency_halfTurn_det_neg_of_ratio_quad_lt`.

## Log

- 2026-06-24 -- Codex: created after the half-turn single-frequency determinant
  and upgraded from the cross-term threshold `(10+sqrt(91))/3` to the optimized
  first-gate threshold `(17+2 sqrt(70))/3`.

## 2026-06-24 sharpness companion

`../../3-formalized/not_new_scientific_knowledge/half-turn-first-gate-threshold-sharp.md` proves that the threshold `theta=(17+2 sqrt(70))/3` is sharp for the first shifted Hankel gate. Above that squared-frequency spread, a balanced positive repaired two-endpoint packet has positive first determinant. Therefore this card is a below-threshold obstruction, not an all-order rejection of broad repaired packets.

## Lean formalization

Modules (namespace `GaloisForLFunctions`):
`formal/GaloisForLFunctions/HTGeometry/SingleEvenFrequency.lean` and
`formal/GaloisForLFunctions/HTGeometry/EvenFrequencySeamMoments.lean`, both wired into the
`GaloisForLFunctions.HTGeometry` umbrella.

| Paper statement | Lean declaration |
|---|---|
| `U_1 U_3 - U_2^2 = (3 M_1 M_3 - 10 M_2^2)/360` and its sign gate | `halfTurn_det_neg_of_moment_ratio_lt` |
| `x + ab/x <= a + b` on `[a,b]`, in packet form | `boundedPacket_moment_inequality` |
| `M_1 M_3 / M_2^2 <= (a+b)^2/(4ab)` and the strict Hankel failure | `boundedPacket_halfTurn_det_neg` |
| `3r^2 - 34r + 3` and its roots `(17 ± 2 sqrt 70)/3` | `halfTurnLowerThreshold`, `halfTurnUpperThreshold`, `halfTurn_ratio_factor` |
| `1 <= r < theta` implies the quadratic is negative | `halfTurn_ratio_quad_neg_iff` |
| sharp threshold trichotomy for the balanced two-frequency packet | `twoFrequency_halfTurn_balanced_det_threshold_sharp` |

Audit: direct `lake env lean` check clean, targeted module build clean, umbrella imports wired,
`#print axioms` returns only `propext`, `Classical.choice`, `Quot.sound`.
