# G-CE finite-order log-curve hard lock (2026-09-02)

- Physical unit-clock determinant curve is exactly `(log p, -log p)` (`primeGammaUnitLogDeterminantCurve_eq`).
- Every finite-order entire response restricted to this curve that vanishes at all but finitely many primes is identically zero (`primeGammaUnitFiniteOrderLogCurve_eq_zero_of_cofinite`).
- Route kill: `not_GCEPrimeLocalCofiniteFiniteOrderLogCurveAnnihilatorExists`.
- **DO NOT REOPEN** finite Laurent, finite-frequency, exponential-type, or arbitrary finite-order entire prime-local scalarizers, including finite exceptional-prime counterterms.
- Survivors: genuinely cross-prime; infinite-order/singular on physical log curve; or non-scalar before cofinal assembly.
- Lean module: `GaloisForLFunctions.RHTower.PrimeGammaFiniteOrderLogCurveAnnihilatorNoGo`.
- Card: `docs/drafts/pipeline/3-formalized/g-ce-finite-order-entire-log-curve-no-go.md`.
- Targeted Lean/build passed; axioms only `propext`, `Classical.choice`, `Quot.sound`.
