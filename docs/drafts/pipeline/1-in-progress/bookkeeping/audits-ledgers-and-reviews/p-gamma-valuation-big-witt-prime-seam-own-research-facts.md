# P Gamma-valuation / Big-Witt prime-seam: own fact log

## Dependency-checked facts

- No existing `gammaValuation`/`BigWitt` or
  `PrimeSeamSourceEnergyBounded`/`gammaValuation` bridge was found by exact
  corpus search over `formal/GaloisForLFunctions/RHTower` and the live pipeline
  notes before this work began.
- `GammaValuationSchurLabelledProfile` supplies an ordered profile
  `u_a(e,n) = (n + 1) (a_{e,n} - a_{e,n+1})`.  It is globally summable and is
  zero exactly when every literal prime-power source coordinate is zero.
- Existing source theorem
  `deningerBigWittPrimeSeamSourceEnergyBounded_iff_constant` classifies bounded
  reciprocal-prime Big-Witt seam energy on `Nat.Primes → ℂ` by constant prime
  potentials.

## New closed Lean result

`GammaValuationSchurBigWittPrimeSeamNoGo.lean` defines the depthwise marked-prime
profile `p ↦ u_a(e, nthPrimeEquiv.symm p)` and proves:

```lean
DeningerBigWittPrimeSeamSourceEnergyBounded
    (gammaValuationAdjacentPrimitivePrimeProfile a e)
  ↔ ∀ n, gammaValuationNthPrimeCoord e a n = 0
```

It also proves that the bound at every depth is equivalent to the entire
ordered primitive profile being zero.  Mechanism is exact: seam boundedness
makes each depthwise prime profile constant; summability makes the constant
zero; zero adjacent primitive forces a constant literal axis; source height
summability makes that axis constant zero.

## Route consequence

- The canonical reciprocal-prime Big-Witt seam energy cannot be the completed,
  nonzero, coefficient-faithful P transport of the labelled Gamma valuation
  profile.  This is a proved obstruction, not an RH argument.
- Positive survivor: finite Big-Witt prime-seam source incidence remains an
  actual source boundary with its explicit pair coefficient.  What fails is
  uniform completion of that particular pair energy on the retained profile.
- Therefore the P hard core sharpens to a non-scalar relation on prime/depth
  labels whose tail law preserves nonzero profile data without reducing to the
  constant-radical reciprocal-prime seam norm.  A candidate must be checked
  against this theorem before any completion claim.

## Audit

- Direct source check passed:
  `lake env lean GaloisForLFunctions/RHTower/GammaValuationSchurBigWittPrimeSeamNoGo.lean`.
- Exact leaf build passed:
  `lake build GaloisForLFunctions.RHTower.GammaValuationSchurBigWittPrimeSeamNoGo`.
- `#print axioms` for all three declarations reports only
  `propext`, `Classical.choice`, and `Quot.sound`.
