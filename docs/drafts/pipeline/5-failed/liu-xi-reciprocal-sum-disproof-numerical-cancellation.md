# Liu xi reciprocal-sum contradiction

- **ID:** liu-xi-reciprocal-sum-disproof-numerical-cancellation
- **Stage:** 5-failed
- **Type:** FALSIFIED
- **Source:** Dasheng Liu, *Disproof of the Riemann Hypothesis*, arXiv:2404.06306v3
- **Statement:** The proposed contradiction between equations (4.25) and (4.26) is impossible under the exact identities used to derive them; the exact upper-minus-lower gap is strictly positive.

## Proposed route

Assume RH, express the centered xi function as a product with positive
parameters `a_m = 1/(1/4+beta_m^2)`, and use `log(1+a_m z)` and
`log(1-a_m z)` to place lower and upper bounds on `sum_m a_m^2`.  The
preprint then evaluates both bounds at a very small `z` and reports them in
the reverse order, declaring a contradiction.

## Exact obstruction `[PROVED HERE]`

With the preprint's notation translated as in
`../3-formalized/needs-audit/liu-reciprocal-square-sandwich-positive-gap.md`,
the two bounds satisfy

```text
L(z) < sum_m a_m^2 < U(z)
```

and

```text
U(z)-L(z)
  = (4/z^2) sum_m sum_{k>=1} (a_m z)^(2k+1)/(2k+1)
  > 0.
```

Thus the reported inequality `U(z) < L(z)` cannot follow from exact
arithmetic.  It first appears after subtracting nearly equal quantities and
dividing the residual by `z^2`.  The claimed contradiction is therefore an
evaluation/cancellation artifact, not an off-critical zero certificate.

The additional deduction of an exact zero-free interval from the
Riemann--von Mangoldt asymptotic is also invalid, but repairing it would not
repair the contradiction.

## Anti-theatre verdict

This route supplies no unconditional off-critical zero, no negative exact
Weil-form sample, and no source-bearing Lean endpoint.  Formalizing the
positive-gap identity certifies the failure mechanism but does not move
the RH-false frontier.

**Update.** The positive-gap identity has since been formalized after all, in
`formal/GaloisForLFunctions/HTGeometry/LiuReciprocalSquareSandwich.lean`
(`HTGeometry.LiuSandwich.liu_sandwich`, `not_upperBd_le_lowerBd`,
`upperBd_sub_lowerBd_eq_oddSeries`), unconditionally and axiom-clean.  The original refusal was a
cost judgement, and the cost turned out to be small.  The verdict above is unchanged: the Lean
surface is audit-side only and is not source-bearing for RH.  It does not reopen this route; the
re-entry condition below still stands.

## Re-entry condition

Reopen only if an exact symbolic inequality is supplied that survives the
strict positive-gap identity above.  Higher-precision decimal evaluation is
not a re-entry condition.

