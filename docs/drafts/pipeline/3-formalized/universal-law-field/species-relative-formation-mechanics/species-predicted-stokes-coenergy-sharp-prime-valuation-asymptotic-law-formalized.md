# ULF-SRFM-3 — Lean formalization record

**Card:** `species-predicted-stokes-coenergy-sharp-prime-valuation-asymptotic-law.md`
**Module:** `formal/GaloisForLFunctions/RHTower/SourceHorizontalStokesCoenergySharpPrimeAsymptotic.lean`
**Namespace:** `RHTower.HedenmalmThetaSource`
**Umbrellas:** `GaloisForLFunctions.RHTower`, `GaloisForLFunctions.HTGeometry.UniversalLawField`

## Result → declaration

| Card result | Lean declaration |
|---|---|
| (2.3)–(2.6) combined exact scaled product form | `stokesCoenergy_scaled_eq` |
| (3.5) exponential normal form of `V(u)`, divided by `L` | `virialClock_eq` (private) |
| (3.8) renormalized virial clock limit `(1-s)(e+1)/2` | `tendsto_virialClock` |
| (3.4) `r → 0` | `tendsto_xiMobiusContinuousApertureDiskNode_cofinite_zero` |
| (3.4) `q → 0` | `tendsto_xiTransversePrimeApertureDiskNode_one_cofinite_zero` |
| (3.3) `c_s(p)^2 → 1/√8` | `tendsto_gammaSewnMobiusValuationContractionMultiplier_sq_cofinite` |
| **Theorem 3.1**, (3.1) | `tendsto_stokesCoenergy_sharp` |
| Theorem 3.1 in exponential normalization | `tendsto_stokesCoenergy_sharp_exp` |
| **Theorem 3.1**, (3.2) | `isEquivalent_stokesCoenergy_sharp` |
| **Corollary 3.2**, (3.10) | `tendsto_stokesCoenergy_div_majorant` |

`p → ∞ through primes` is `Filter.cofinite` on `Nat.Primes`; the prime-at-infinity input is
`GaloisForLFunctions.HTGeometry.tendsto_primeRealLog_cofinite_atTop`.

## Corpus inputs reused (no duplication)

* `RHTower.HedenmalmThetaSource.sourceHorizontalStokesConditionedInformationTerm`,
  `…Majorant` — the literal objects of the card.
* `sourceHorizontalPrimeGeometricKLScaleTerm`, `sourceHorizontalPrimePowerHolonomy_scaleVirial`,
  `sourceHorizontalHolonomyVirial` — rewrite (2.3).
* `gammaSewnMobiusApertureStokesReflectedWeight_eq_source` — rewrite (2.4).
* `RHTower.gammaSewnMobiusValuationContractionMultiplier_pow_four`, `…_pos` — rewrite (2.5).
* `RHTower.xiTransversePrimeApertureDiskNode`, `RHTower.xiMobiusContinuousApertureDiskNode`.

## Verification

* `lake env lean GaloisForLFunctions/RHTower/SourceHorizontalStokesCoenergySharpPrimeAsymptotic.lean`
  — 0 errors, 0 warnings.
* Axiom audit of all 9 public declarations: only `propext`, `Classical.choice`, `Quot.sound`.
* No hypotheses beyond `0 < s`, `s < 1` and the fixed valuation depth `e`, which are the card's own
  standing assumptions (2.1).
