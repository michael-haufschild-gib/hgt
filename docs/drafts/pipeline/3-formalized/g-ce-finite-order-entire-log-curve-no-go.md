# G-CE finite-order entire log-curve no-go

**Status:** formalized in Lean 4  
**Route:** G-CE  
**Label:** `GCE-LOG-ENTIRE-NOGO`

## Exact theorem

At unit clock, forward/reflected physical prime--Gamma determinants have logarithmic-modulus
coordinate `(log p, -log p)`. No nonzero finite-order entire restriction to this physical curve
can vanish at every ordinary prime, or at every prime outside a fixed finite exceptional set.

Equivalently, `GCEPrimeLocalCofiniteFiniteOrderLogCurveAnnihilatorExists E` is false for every
finite `E`.

## RH proof chain closed or killed

G-CE local prime--Gamma determinant transgression
→ fixed analytic local scalarizer restricted to physical forward/reflected log curve
→ all-prime source annihilation
→ proposed G-CE source cancellation
→ RH receiver.

Proving conjecture kills whole finite-order entire local-scalarizer link. Survivors must be
cross-prime, infinite-order/singular on physical log curve, or non-scalar before cofinal assembly.

## Corpus basis and non-duplication

- `PrimeGammaAllPrimeLaurentAnnihilatorNoGo`: physical determinant is `-p`, reflection is inverse;
  finite Laurent local class already killed.
- `PrimeLogFiniteOrderUniqueness`: prime logarithms are a uniqueness set for arbitrary
  finite-order entire functions, robust after deleting finitely many primes.
- Corpus search found no theorem composing physical G-CE determinant curve with finite-order
  prime-log uniqueness.

This is strictly broader than finite Laurent response: restriction may be any finite-order entire
function, not algebraic or finite-frequency.

## Literature audit through 2026-08

Classical Jensen/entire-function zero-density theory supplies generic finite-order zero-count
bounds. Search found no treatment of G-CE prime--Gamma determinant transgression or this physical
log-curve annihilator class. Novelty claimed for route classification, not Jensen theory.

## Lean closure

- Module: `GaloisForLFunctions.RHTower.PrimeGammaFiniteOrderLogCurveAnnihilatorNoGo`.
- Exact curve: `primeGammaUnitLogDeterminantCurve_eq`.
- Cofinite erasure: `primeGammaUnitFiniteOrderLogCurve_eq_zero_of_cofinite`.
- Route kill: `not_GCEPrimeLocalCofiniteFiniteOrderLogCurveAnnihilatorExists`.
- All-prime corollary: `not_GCEPrimeLocalFiniteOrderLogCurveAnnihilatorExists`.
- Direct `lake env lean` and targeted `lake build` passed. Axiom audit reports only `propext`,
  `Classical.choice`, and `Quot.sound`.
