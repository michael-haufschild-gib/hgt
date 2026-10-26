# The prime source is typical except for its pole

- **ID:** acg-prime-pole-2026-10-26
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** ArithmeticCorrelationGeometry (typicality of gauge points; P10 archimedean boundary)
- **Statement:** For Haar-almost every gauge point `|Σ_{n≤N} Λ(n)χ_x(n)| ≤ C_x√(N+1)(1+log(N+1))³`;
  at the gauge point `0`, `ψ(N)/N → 1`; RH ⇔ `ψ(x) − x = O(√x log²x)`.

## Proof
`Λ(n)/log(n+1)` is bounded by one: almost-sure square-root law; Abel summation with the
increasing weight `log(n+1)` costs one logarithm. At `0`: prime number theorem
(`RHTower.tendsto_chebyshevPsiReal_div`); RH: von Koch (`RHTower.riemannHypothesis_iff_chebyshevPsi_sub_isBigO`).

## Lean
`formal/GaloisForLFunctions/ArithmeticCorrelationGeometry/ThePrimeSourceIsTypicalExceptForItsPole.lean`.

## Insight
For `μ`, RH asks that the point 0 be typical; for `Λ`, the point 0 is provably atypical by its
pole (the archimedean place), and RH asks that this be its only atypicality.
