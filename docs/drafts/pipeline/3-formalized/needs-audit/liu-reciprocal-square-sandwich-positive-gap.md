# Liu reciprocal-square sandwich has a strictly positive gap

- **ID:** liu-reciprocal-square-sandwich-positive-gap
- **Stage:** 3-formalized / needs-audit
- **Type:** THEOREM (paper)
- **Source:** Dasheng Liu, *Disproof of the Riemann Hypothesis*, arXiv:2404.06306v3, equations (4.17)--(4.26)
- **Statement:** The upper and lower reciprocal-square bounds used in Liu's contradiction are analytically compatible: under their stated positive-product hypotheses, the alleged upper bound exceeds the alleged lower bound by an explicit strictly positive quantity.

## Goal

Audit the only contradiction in Liu's proposed RH disproof without using its
decimal evaluation.  This is a route discriminator, not an RH result.

## Gates

- [x] 0 -> 1 in-progress: the claimed contradiction reduces to two explicit logarithmic bounds
- [x] 1 -> 2 fully-proven: exact sign and exact gap proved below, `[PROVED HERE]`
- [x] 2 -> 3 formalized: complete unconditional Lean surface in
      `formal/GaloisForLFunctions/HTGeometry/LiuReciprocalSquareSandwich.lean`, axiom-clean
- [ ] 3 -> 4 publication-ready
- [ ] external source/provenance audit against the current preprint version

## Theorem

Let `(a_m)` be a nonempty finite or countable family with `a_m > 0`,
`S_1 = sum_m a_m < infinity`, and `S_2 = sum_m a_m^2 < infinity`.  Fix
`z > 0` such that `q := z sup_m a_m < 1`, and put

```text
Psi(z)  = sum_m log(1 + a_m z),
Psi(-z) = sum_m log(1 - a_m z),
L(z)    =  (2/z^2)(S_1 z - Psi(z)),
U(z)    = -(2/z^2)(S_1 z + Psi(-z)).
```

Then

```text
L(z) < S_2 < U(z)
```

and, more sharply,

```text
U(z) - L(z)
  = (2/z^2) sum_m [log((1+a_m z)/(1-a_m z)) - 2a_m z]
  = (4/z^2) sum_m sum_{k>=1} (a_m z)^(2k+1)/(2k+1)
  > 0.
```

## Proof `[PROVED HERE]`

For `x > 0`, differentiation gives

```text
d/dx [log(1+x) - x + x^2/2] = x^2/(1+x) > 0.
```

Both sides vanish at `x=0`, hence
`log(1+x) > x-x^2/2`.  Apply this with `x=a_m z`, sum, and rearrange:

```text
L(z) < sum_m a_m^2 = S_2.
```

For `0 < x < 1`, similarly,

```text
d/dx [-x - x^2/2 - log(1-x)] = x^2/(1-x) > 0,
```

so `log(1-x) < -x-x^2/2`.  Termwise summation and rearrangement give
`S_2 < U(z)`.

Finally, direct subtraction yields

```text
U(z)-L(z)
  = (2/z^2) sum_m [log(1+a_m z)-log(1-a_m z)-2a_m z].
```

For `0<x<1`, the convergent logarithmic series gives

```text
log((1+x)/(1-x))-2x
  = 2 sum_{k>=1} x^(2k+1)/(2k+1) > 0.
```

The uniform bound `a_m z <= q < 1` and `sum_m a_m < infinity` justify
termwise summation and passage from finite partial sums.  Nonemptiness makes
the inequality strict.  This proves both the sandwich and its positive gap.

## Application to the claimed disproof

Under the preprint's RH assumption, take
`a_m = 1/(1/4 + beta_m^2)`.  Its equations (4.17) and (4.19) are precisely
the bounds `L(z) < S_2` and `S_2 < U(z)`.  Consequently an exact evaluation
cannot put `U(z)` below `L(z)`: the displayed reversal in equations (4.25)
and (4.26) is incompatible with the preceding identities and inequalities.
The reversal is introduced only after evaluating differences at a very small
`z` and dividing by `z^2`; it is not an analytic consequence of the product.

No decimal approximation is used in this audit.

## Independent defect

The paper also infers from a Riemann--von Mangoldt asymptotic formula that
there are no zeros for `T <= 2 pi`.  An asymptotic with an error term cannot
by itself imply that exact finite zero-free interval.  This defect is not
needed for the positive-gap route kill above.

## Lean status

`[FORMALIZED]` The whole analytic theorem is now an unconditional Lean 4 development in
`formal/GaloisForLFunctions/HTGeometry/LiuReciprocalSquareSandwich.lean`, namespace
`HTGeometry.LiuSandwich`.  Nothing is postulated: no `axiom`, no `sorry`, no packaged input
hypothesis.  Axiom inspection of every endpoint reports only `propext`, `Classical.choice`,
`Quot.sound`.

Theorem surface, in the card's own notation (`a : ι → ℝ`, `Nonempty ι`, `0 < a m`, `Summable a`,
`0 < z`, `a m * z ≤ q < 1`):

- `log_one_add_lower` : `x - x^2/2 < log (1 + x)` for `0 < x`, by the card's derivative argument
  (`t ↦ log (1+t) - t + t^2/2` has derivative `t^2/(1+t) > 0` on `Ici 0`).
- `log_one_sub_upper` : `log (1 - x) < -x - x^2/2` for `0 < x < 1`, derivative `t^2/(1-t) > 0`
  on `Ico 0 1`.
- `summable_logAdd`, `summable_logSub`, `summable_sq` : the termwise-summation justification of
  section 4 of the proof, from `0 ≤ log(1 + a_m z) ≤ a_m z` and `0 ≤ -log(1 - a_m z) ≤ a_m z/(1-q)`.
- `logSum`, `lowerBd`, `upperBd` : the literal definitions of `Psi`, `L(z)`, `U(z)`.
- `lowerBd_lt_sumSq` : `L(z) < S_2`.
- `sumSq_lt_upperBd` : `S_2 < U(z)`.
- `upperBd_sub_lowerBd_eq` : the exact gap
  `U(z) - L(z) = (2/z^2) sum_m [log(1 + a_m z) - log(1 - a_m z) - 2 a_m z]`.
- `hasSum_logRatio` / `hasSum_logRatio_tail` : `log((1+x)/(1-x)) = 2 sum_{j>=0} x^(2j+1)/(2j+1)`
  and its `2x`-subtracted tail, obtained from the mathlib log power series by an even/odd
  reindexing.
- `upperBd_sub_lowerBd_eq_oddSeries` : the card's display `(45)`,
  `U(z) - L(z) = (4/z^2) sum_m sum_{k>=1} (a_m z)^(2k+1)/(2k+1)`.
- `liu_sandwich` : the packaged `L(z) < S_2 < U(z)` together with `0 < U(z) - L(z)`.
- `not_upperBd_le_lowerBd` : the route kill — `¬ (U(z) ≤ L(z))`.

Note on the earlier decision: `../../5-failed/liu-xi-reciprocal-sum-disproof-numerical-cancellation.md`
recorded that no Lean build was authorized for this dead route, on the ground that certifying the
failure mechanism would not move the RH-false frontier.  That cost assessment is superseded only in
the sense that the build turned out to be cheap; the epistemic verdict is unchanged.  The Lean
surface here certifies the *audit*, is not source-bearing for RH, and must not be read as progress
on the RH-false frontier.

## Status

The analytic theorem is complete and formalized.  The source/provenance and its relation to
the current preprint version still require the repository's external audit,
so this card remains in `needs-audit`.

## Next generative move

The formalized object worth pushing is not the kill but the gap functional itself:
`G(z) = U(z) - L(z) = (4/z^2) sum_m sum_{k>=1} (a_m z)^(2k+1)/(2k+1)` is a strictly positive,
`z`-parametrised functional of the zero family that vanishes to third order at `z = 0`.  Its
small-`z` expansion is a moment ladder `sum_m a_m^3, sum_m a_m^5, ...` in the reciprocal-square
data.  `[CONJECTURE]` The odd reciprocal moments `sum_m (1/4 + beta_m^2)^(-(2k+1))` carry the same
information as the Li/Keiper coefficients through this positivity funnel, so a *lower* bound on
`G(z)` at a fixed small `z` is an odd-moment positivity statement rather than a cancellation
artifact.  Constructing that lower bound — and checking whether it is a genuinely new positivity
channel or reduces to the known Li-coefficient chain — is the next object to build on top of
`upperBd_sub_lowerBd_eq_oddSeries`.

