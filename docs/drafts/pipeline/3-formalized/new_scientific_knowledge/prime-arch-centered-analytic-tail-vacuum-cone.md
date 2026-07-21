# Prime--archimedean centered analytic-tail vacuum cone

- **ID:** `prime-arch-centered-analytic-tail-vacuum-cone`
- **Stage:** 3-formalized
- **Type:** `[NEW THEOREM] [RIGHT-EDGE HYPOTHESIS DISCHARGE] [NOT RH]`
- **Parent:** `sonin-coupled-projective-quantum-fisher`
- **Statement:** A real polynomial whose nonconstant coefficient `l1` mass is at most eight times
  the magnitude of its constant coefficient has nonnegative prime--Gamma trace--Hankel value.
  Applied after vacuum centering, this unconditionally discharges the normalized-variance
  comparison on an explicit family of zero-constant integer tails.

## Exact statement

For `p in R[X]`, put

```text
tailL1(p) = sum_(1 <= n <= deg p) |p_n|.
```

Then

```text
tailL1(p) <= 8 |p_0|
  -> Re primeArchSourceTraceHankel(p) >= 0.                 (1)
```

For a zero-constant integer tail `q`, write

```text
E_PG(q) = momentNormalizedExpectation(normalizedPrimeArchMoment, q),
q_perp  = q - E_PG(q).
```

The nonconstant coefficients of `q_perp` are those of `q`, while its constant coefficient is
`-E_PG(q)`.  Hence `(1)` gives

```text
tailL1(q) <= 8 |E_PG(q)|
  -> momentNormalizedVariance(normalizedPrimeArchMoment, q) >= 0.   (2)
```

Define the centered residual family by strict failure of the coefficient condition in `(2)`.
The current coupled-Sonin normalized-variance upper comparison is therefore required only on that
residual family.  On its complement `(2)` supplies target nonnegativity directly; on the residual
family nonnegativity of the coupled source variance contradicts a negative target variance.  The
complete vacuum-Feshbach criterion then yields RH.

## Exact counterexample localization

The cone theorem has a contrapositive consequence stronger than interface restriction. If RH is
false, the countable vacuum-Feshbach equivalence supplies a zero-constant integer polynomial `q`
with negative target normalized variance. Such a `q` cannot lie in the discharged cone, so every
possible RH counterexample has a witness satisfying

```text
q(0) = 0,
8 |E_PG(q)| < tailL1(q),
momentNormalizedVariance(normalizedPrimeArchMoment,q) < 0.       (CE)
```

Lean exposes `(CE)` as
`exists_centeredAnalyticTailResidual_negativeVariance_of_not_riemannHypothesis`.
This localizes the surviving obstruction; it does not prove that the residual is empty.

## Paper proof

Let `u=xiZeroCopyReciprocalSquare(q)`.  Existing corpus theorems give

```text
Re u > 0,
|u| < 2/41,
|u| <= (85/84) Re u.                                      (3)
```

The last inequality follows from
`normSq(u) <= (85/84)(Re u)^2`, positivity of `Re u`, and `85/84>1`.

Write `p(X)=a+r(X)` with `a=p_0` and `r(0)=0`.  From the finite coefficient expansion and
`|u|<1`,

```text
|r(u)|
  <= sum_(n>=1) |p_n| |u|^n
  <= |u| tailL1(p)
  <= (16/41)|a|.                                          (4)
```

Set `w=r(u)`.  Expanding around the constant channel gives

```text
Re[u(a+w)^2]
 >= (Re u)a^2 - |u| (2|a||w|+|w|^2).
```

Using `(3)--(4)`, the error is at most

```text
(85/84)(Re u) * (2*(16/41)+(16/41)^2) a^2
  < (Re u)a^2,                                            (5)
```

because

```text
(85/84) * (32/41 + 256/1681) < 1.
```

Thus every multiplicity copy contributes a nonnegative real trace--Hankel term.  Absolute
summability is already proved in `XiSquaredEulerAllDegreeChargeCriterion.lean`, so summing `(5)`
gives `(1)` through
`xiSquaredEulerApertureHankelValue_eq_traceHankel_re` and
`xiCentralTraceHankel_eq_primeArchSourceTraceHankel`.

For `(2)`, use the existing exact identity

```text
momentNormalizedExpectation(q_perp^2)
  = momentNormalizedVariance(q)
```

and positivity of `normalizedPrimeArchMoment 0` to pass between the normalized expectation and
the unnormalized trace--Hankel value.

## Hostile audit

1. **Not the existing circle cone.**  The prior shifted-circle theorem gives an `l2` coefficient
   cone for an uncentered polynomial.  It explicitly records centered transport as missing.  This
   theorem instead uses atomwise analytic evaluation and gives a centered `l1` cone.
2. **Not finite-packet interpolation.**  No separator, localization, or divisor-dependent
   polynomial is chosen.  One fixed coefficient condition makes every divisor-copy term
   nonnegative.
3. **Not an RH-equivalent sign assumption.**  Condition `(2)` is decidable from the explicit
   coefficients and the fixed prime--Gamma normalized mean.  The conclusion is proved from the
   unconditional sector and endpoint-radius laws.
4. **Not a complete RH proof.**  Tails with `tailL1(q)>8|E_PG(q)|` remain.  The result weakens the
   rightmost coupled-Sonin Prop interface to that strict residual family; it does not discharge
   the residual comparison.
5. **External novelty:** not audited, by current task scope.  Project-corpus novelty was checked
   declaration-by-declaration against centered/Feshbach, shifted-circle, coefficient-cone, and
   all-degree charge files before promotion.

## Gates

- [x] existing right-edge interface and all stronger superseded interfaces audited
- [x] no matching centered-sector/Feshbach theorem found in formal or pipeline corpus
- [x] dependency-closed paper proof
- [x] Lean formalization of `(1)` and `(2)`
- [x] exact negative-variance residual witness under `not RH`
- [x] restricted residual normalized-variance Prop and RH consumer
- [x] targeted Lean check, final module build, axiom audit, lint, process audit
- [ ] full unconditional residual comparison
- [ ] RH
