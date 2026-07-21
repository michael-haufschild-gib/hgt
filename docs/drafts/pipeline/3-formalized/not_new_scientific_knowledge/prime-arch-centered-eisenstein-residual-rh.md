# Prime--archimedean centered Eisenstein residual RH law

- **ID:** `prime-arch-centered-eisenstein-residual-rh`
- **Stage:** 3-formalized
- **Type:** `[BRIDGE] [LEAN-PROVED] [RIGHT-EDGE HYPOTHESIS REDUCTION] [NOT RH]`
- **Parents:** `prime-arch-centered-analytic-tail-vacuum-cone`,
  `prime-arch-theta-hankel-degree-tail`
- **Claim:** For every infinite degree set `D`, target normalized-variance nonnegativity is
  RH-complete after simultaneously restricting to strict centered analytic-tail residuals and to
  vacuum tails of monic integer polynomials Eisenstein at `2` whose exact degrees lie in `D`.

## Exact statement

For `P in Z[X]`, let

```text
tail(P) = P - C(P(0)),
Residual(q) := 8 |E_PG(q)| < tailL1(q).
```

Define

```text
CenteredTwoEisensteinResidualVarianceNonnegative(D) :=
  for every P in Z[X],
    Monic(P) -> EisensteinAt(2,P) -> degree(P) in D ->
    Residual(tail(P)) ->
    Var_PG(tail(P)) >= 0.
```

Then, for every infinite `D subseteq N`,

```text
CenteredTwoEisensteinResidualVarianceNonnegative(D) <-> RH.      (E1)
```

Consequently, if RH is false, every infinite `D` contains the exact degree of a monic
`2`-Eisenstein polynomial `P` whose zero-constant vacuum tail satisfies

```text
Residual(tail(P)),
Var_PG(tail(P)) < 0.                                            (E2)
```

Let `BadDeg` be the set of degrees admitting such a `P`. Then `(E2)` has the sharp cofinite form

```text
not RH -> Finite(N \\ BadDeg).                                  (E2c)
```

Thus failure is not represented by one exceptional polynomial degree: every sufficiently large
degree carries a structured negative centered witness.

The coupled-Sonin normalized-variance comparison is therefore needed only on these structured
residual tails for any one chosen infinite degree set.

## Dependency-closed paper proof

Assume `D` is infinite and `(E1)`'s left side. The corpus theorem
`primeArchSourceTraceHankelIntTwoEisensteinDegreeSetNonnegative_iff_riemannHypothesis`
reduces RH to proving nonnegativity of the prime--Gamma trace--Hankel value for every monic
`2`-Eisenstein `P` with `degree(P) in D`.

Fix such a `P`; write `q=tail(P)` and `c=P(0)`. The exact vacuum decomposition gives

```text
Re TraceHankel(P)
  = m0 * (c + E_PG(q))^2 + Feshbach_PG(q),
Feshbach_PG(q) = m0 * Var_PG(q),
m0 > 0.                                                        (E3)
```

If `Residual(q)`, the assumed restricted condition gives `Var_PG(q)>=0`. If not, linear order
gives `tailL1(q)<=8|E_PG(q)|`, and the formalized centered analytic-tail cone gives the same
conclusion unconditionally. Hence `Feshbach_PG(q)>=0`; the first term in `(E3)` is a square, so
`Re TraceHankel(P)>=0`. The Eisenstein sparse-degree criterion yields RH.

Conversely assume RH. The vacuum-Feshbach equivalence gives nonnegative Feshbach remainder for
every zero-constant integer tail. Since `m0>0`, `(E3)` gives nonnegative normalized variance for
every `tail(P)`, in particular for every structured residual tail. This proves `(E1)`.

For `(E2)`, negate `(E1)`. Failure of the restricted universal condition supplies `P` with all
four structural hypotheses and failure of variance nonnegativity, which is strict negativity over
the reals.

For `(E2c)`, suppose `N \\ BadDeg` were infinite. Apply `(E2)` with this complement as `D`. The
resulting polynomial has degree both in `BadDeg` by its witness data and in its complement by the
chosen degree-set membership, contradiction. Hence the complement is finite.

For the Sonin connector, suppose the normalized source variance upper comparison holds only for
the tails in `(E1)`. If one such target variance were negative, choose
`epsilon=-m0*Var_PG(q)/2`. Every coupled source variance is nonnegative, while the comparison's
right side becomes negative, contradiction. Thus `(E1)` holds and RH follows.

## Hostile corpus audit

1. **Minimal-degree normalization is rediscovered.** The corpus already proves much more:
   positivity on monic `2`-Eisenstein tests in any infinite degree set is RH-complete.
2. **Not another coefficient estimate.** The only estimate used is the already-formalized centered
   cone. New content is exact intersection with vacuum elimination and the fixed arithmetic
   Eisenstein chamber.
3. **Not a proof of RH.** Source variance collapse is now unconditional, but the structured
   source--target comparison remains unproved and is itself exactly equivalent to RH; see
   `SoninCoupledVarianceCollapse.lean`.
4. **Not merely the old Eisenstein criterion.** That criterion concerns uncentered trace squares.
   `(E1)` proves that, after removing the positive vacuum square, only strict centered residual
   tails retain the full obstruction.
5. **Scientific status.** This is a new project-corpus connector and counterexample-localization
   law. The cofinite bad-degree dichotomy is stronger than the existing sparse-degree criterion's
   stated endpoint, but its proof is a short composition of existing structural theorems. Label
   remains `[BRIDGE]`, not candidate new scientific knowledge.
6. **External literature audit omitted** under explicit user instruction that this lane concerns
   corpus theorem closure rather than literature research.

## Gates

- [x] complete formalized and failed-route corpus search
- [x] minimal/primitive route rejected as already surpassed
- [x] exact claim survives circularity and vacuity checks
- [x] dependency-closed paper proof
- [x] Lean definitions, equivalence, counterexample localization, cofinite replication, and Sonin consumer
- [x] targeted Lean, final module build, axiom audit, lint, process audit
- [ ] structured residual source--target comparison (proved iff RH)
- [ ] RH

## Lean certificate

Formal module:
`formal/GaloisForLFunctions/RHTower/PrimeArchCenteredEisensteinResidual.lean`.

The permanent declarations include the structured residual variance Prop, its equivalence with RH,
the direct complete source-cone connector, all-degree charge and full-Weil consumers, arbitrary
infinite-degree counterexample localization, cofinite bad-degree replication, and the restricted
coupled-Sonin capstone. Targeted `lake env lean` and final module build pass. Axiom inspection
reports only `propext`, `Classical.choice`, and `Quot.sound`; formal lint passes. No owned Lean or
lake process remains.
