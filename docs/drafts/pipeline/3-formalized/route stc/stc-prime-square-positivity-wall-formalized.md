# Prime-square sign wall for the continued Euler Gram — Lean certificate

- **Paper card:** `stc-prime-square-positivity-wall.md`
- **Lean module:** `GaloisForLFunctions.RHTower.STCPrimeSquarePositivityWall`
  (uses `STCPrimeHeightFiberAbel`, `XiPrimeLogHigherValuationCriticalBoundary`, `ZetaLogDerivResidue`)
- **Umbrella:** `GaloisForLFunctions.RHTower`
- **Verification:** `lake --old build`; `lake --old env lean` clean; `#print axioms` =
  `propext`, `Classical.choice`, `Quot.sound`; no `sorry`.

`Q = primeLogCriticalContinuation = A - (A(2·) - H(2·) + H_{≥3})`, `F = primeLogSquareContinuation = -Q'`,
`K(w,z) = primeSquareGramKernel w z = F(w + z̄ - 1)`.

| Card item | Lean theorem |
|-|-|
| `Q` continues the prime-log current (`Re s > 1/2`) | `primeLogCriticalContinuation_eq` |
| `F = -Q'` is the log-square series on `Re s > 1` | `primeLogSquareContinuation_eq`, `primeLogSquareComplex_eq_neg_deriv_continuation` |
| `Q(s) = 1/(s-1) + holomorphic` near `1` | `primeLogCriticalContinuation_laurent_one` |
| (2) valuation split ⇒ `Q(s) = -1/(2s-1) + holomorphic` near `1/2` | `primeLogCriticalContinuation_laurent_half` |
| (1) `F(s) = -2/(2s-1)² + holomorphic` near `1/2` | `primeLogSquareContinuation_laurent_half` |
| real form `(2σ-1)² F(σ) → -2` | `tendsto_primeLogSquareContinuation_real` |
| `F(σ) < 0` (real part) for `σ ↓ 1/2` | `eventually_re_primeLogSquareContinuation_neg` |
| negative diagonal at real `w` near `3/4` | `exists_primeSquareGramKernel_diag_neg` |
| `K` not positive semidefinite on `Re w > 3/4` | `not_posSemidef_primeSquareGramKernel` |
| `K` not a Gram kernel of Hilbert vectors | `not_gram_primeSquareGramKernel` |
