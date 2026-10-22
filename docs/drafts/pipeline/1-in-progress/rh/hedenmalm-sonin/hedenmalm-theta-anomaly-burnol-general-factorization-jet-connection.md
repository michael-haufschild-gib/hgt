# Hedenmalm theta anomaly: general Burnol factorization-jet connection

- **Label:** `P-G121`
- **Route:** P
- **Parents:** `P-G117`, `P-G118`, `P-G120`
- **Status:** theorem proved in Lean; all-prime aggregation pivot active

## Conjecture tested

P-G118's `6=2*3` jet connection should be a universal multiplicative law, not a two-prime
accident.  For arbitrary integers `m,n>1`, sine addition should give an exact completed-cell
factorization

```text
A_(mn) = u_(m,n) A_m + v_(m,n) A_n.
```

After differentiation, explicit nonzero weights should give

```text
du = -k_n z A_n,
dv = -k_m z A_m,
J_(m,n) = du/k_n conj(A_n) + dv/k_m conj(A_m)
          = -z (|A_m|²+|A_n|²).
```

Where the pair frame is nonzero, normalized connection is exactly `z`.  Swapping `m,n` should
preserve the Hermitian connection, closing the tentative odd-triangle sign-holonomy idea.

## Scientific decision gate

- **Success:** multiplicative jet connection is factorization-independent and commutative.  Use
  its division-free all-prime family to test a critical summability/renormalization wall.
- **Failure:** identify arithmetic obstruction and pivot to continuous head-frame exhaustion.
- Generalization must include actual factorization identity, literal derivatives, nonzero weights,
  division-free numerator law, normalized reconstruction under exact nondegeneracy, and swap law.

## Verification log

- 2026-08-13 — Card opened after corpus search found only fixed `6=2*3` construction.
- 2026-08-13 — Direct `lake env lean` passed for
  `HedenmalmThetaAnomalyBurnolGeneralFactorizationJetConnection.lean`.
- 2026-08-13 — Exact module build passed: `[12941/12941]`.
- 2026-08-13 — `#print axioms` on factorization, derivative, numerator, swap,
  independence, and `2,3` recovery capstones reports only `propext`, `Classical.choice`, and
  `Quot.sound`.
- 2026-08-13 — Full `GaloisForLFunctions.RHTower` umbrella build passed: `[19800/19800]`.

## Result

The conjecture is true for every `m,n>1`.  Lean proves the completed-cell factorization and its
literal product-rule derivative, then proves the division-free Hermitian law

```text
J_(m,n)(z) = -z E_(m,n)(z),
E_(m,n)(z) = |A_m(z)|² + |A_n(z)|².
```

Consequently every nondegenerate factorization frame reconstructs exactly the same normalized
connection `z`.  Both numerator and energy are invariant under swapping factors.  The fixed
`2,3` theory from P-G118 is recovered definitionally, not merely propositionally.

This falsifies odd-triangle sign holonomy for the Hermitian connection: orientation lives in the
determinant-line gauge, while the connection itself descends through the commutative factorization
quotient.  Remaining leverage must come from aggregation or boundary conditions, not factor order.
