# Finite-prime Gibbs modular phase realization — formalized

- **ID:** `finite-prime-gibbs-modular-phase-realization-formalized`
- **Stage:** 3-formalized
- **Paper proof:** `finite-prime-gibbs-modular-phase-realization.md` (same directory)
- **Status:** `[LEAN COMPLETE] [UNCONDITIONAL] [NO SORRY] [NO NEW AXIOMS]`

## Lean modules

| Module | Path |
|---|---|
| `GaloisForLFunctions.HTGeometry.ConstraintRelativity.GibbsModularPhase` | `formal/GaloisForLFunctions/HTGeometry/ConstraintRelativity/GibbsModularPhase.lean` |

Wired into `GaloisForLFunctions.HTGeometry`.

## Corpus reuse

As the card's Lean-return note instructed, the prime-log Kronecker layer was **not** rebuilt:
`kronecker_approx` and `expChar` come from `HTGeometry.KroneckerWeylDensity`, and
`linearIndependent_log_primes` from `GaloisForLFunctions.Core`.  The `primesLE`-indexed wrapper
`primeTorus_kronecker_dense` was deliberately not used: applying `kronecker_approx` to the
three-element family avoids any decision procedure on `Nat.primesBelow`.

## New infrastructure

- `diagonal_mul_single_mul_diagonal` — conjugating a matrix unit by two diagonal matrices;
  mathlib has neither `diagonal_mul_single` nor `single_mul_diagonal`.
- `cubeRoot`, `cubeRoot_sq_add`, `norm_cubeRoot`, `subdiscriminant_three` — the factorization
  `H₂(z) = 2·(z₀ + ω z₁ + ω² z₂)(z₀ + ω² z₁ + ω z₂)`, i.e. the classical equilateral-triangle
  criterion, which mathlib does not have.
- `exists_sum_eq_zero_of_triangle` — three prescribed positive moduli obeying the triangle
  inequalities are realized by three complex numbers summing to zero.

## Formal theorem chain

All declarations live in namespace `HTGeometry.ConstraintRelativity`.

1. `gibbsWeight`, `gibbsPartition`, `gibbsEigen`, `gibbsState` — **card `(1)`**: the faithful Gibbs
   state `ρ_β = Z⁻¹ diag(1, p_1^{-β}, …, p_N^{-β})`, with positivity of all eigenvalues.
2. `gibbsPower`, `gibbsPower_one` — the complex powers `ρ_β^z`, with `ρ_β^1 = ρ_β`.
3. `modularFlow` — **card `(2)`**: `σ_s(Y) = ρ_β^{is} Y ρ_β^{-is}`.
4. `modularFlow_single` — **card `(10)`**: the flow multiplies `E_{i0}` by the phase of the
   eigenvalue ratio, `(p_i^{-β})^{is}`.
5. `primeFrame`, `primeClock` — **card `(3)`**: `X = ∑ (log p_i) E_{i0}` and `X(t) = σ_{-t/β}(X)`.
6. `frameCoord`, `frameCoord_single` — **card `(5)`**: the framed coordinate functionals.
7. `frameCoord_primeClock` — **card `(4)`, boxed**: `X(t) = ∑ (log p_i) e^{it log p_i} E_{i0}`.
8. `subdiscriminant` — **card `(8)`**: `H₂(z) = N ∑ z_i² − (∑ z_i)²`, the displayed determinant.
9. `framedReader` — **card `(6)`**: the framed two-copy quadratic polynomial `Q_N`.
10. `framedReader_primeClock` — **card `(7)`, boxed**: `Q_N(X(t)) = H₂(z(t))`.
11. `subdiscriminant_three`, `subdiscriminant_eq_zero_of_equilateral` — the zero locus of `H₂` on
    three points is exactly the equilateral configuration.
12. `exists_sum_eq_zero_of_triangle`, `exists_phase_subdiscriminant_eq_zero` — three concentric
    circles whose radii obey the triangle inequalities carry a zero of `H₂`.  This is the card's
    "existing fixed-radius theorem", proved here rather than cited.
13. `phaseReader`, `continuous_phaseReader`, `exists_norm_framedReader_lt` — Kronecker density plus
    continuity: the reader comes arbitrarily close to zero along the modular clock.
14. `csInf_norm_framedReader_eq_zero` — **card `(9)`** for any rationally independent triple whose
    logarithms obey the triangle inequalities.
15. `triplePrimeNat`, `triplePrimes`, `tripleRadii`, `log_triple_triangle`,
    `csInf_norm_framedReader_triple` — **card `(9)`, boxed**: `inf_t |Q_3(X(t))| = 0` for the prime
    triple `(101, 103, 107)`.  As the card says, no exact finite-time zero is claimed and none is
    proved: the statement is an infimum.

## Scope

The "Exact boundary", "Predictions and falsifiers" and "Novelty boundary" sections are commentary:
they record that this finite matrix realization carries no DVR order, no Kähler Smith wall and no
nontrivial extension phase.  Nothing there is a further theorem.

## Verification

```text
lake env lean GaloisForLFunctions/HTGeometry/ConstraintRelativity/GibbsModularPhase.lean  # clean
lake build GaloisForLFunctions.HTGeometry.ConstraintRelativity.GibbsModularPhase          # green
```
