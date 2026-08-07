# Cofinal Gamma Bockstein determinant transgression — formalized

- **ID:** `cofinal-gamma-bockstein-determinant-transgression-formalized`
- **Stage:** 3-formalized
- **Paper proof:** `cofinal-gamma-bockstein-determinant-transgression.md`
- **Type:** FORMALIZATION CERTIFICATE

## Lean modules

```text
formal/GaloisForLFunctions/RHTower/PrimeFirstTraceGradedVariableIdealFixedXiComparison.lean
formal/GaloisForLFunctions/RHTower/PrimeFirstTraceGammaCofinalNormalizerFrontier.lean
formal/GaloisForLFunctions/RHTower/PrimeGammaCofinalBocksteinSchattenWall.lean
formal/GaloisForLFunctions/RHTower/PrimeGammaCofinalBocksteinDeterminantTransgression.lean
```

The activation-Fisher twist `F_t(p) = p^t d(p)` and its strictly positive density `d(p)` come from
the first module; the absolute Bockstein representative comes from the Schatten-wall module.  The
last module carries the whole card.

## Formal theorem chain

```text
1  primeGammaCofinalBocksteinCoefficient                b_t(p) = F_(-t)(p) - F_t(p)
2  primeGammaPhysicalRotationDeterminant                det R_t(p) = -p^t
3  primeGammaSourceRotationDeterminant                  det tau = -1
4  primeGammaCommonCorrectedRotationDeterminant         c · det R_t(p)
5  primeGammaCofinalBocksteinCoefficient_eq_determinantTransgression      identity (1)
6  primeGammaPhysicalRotationDeterminant_eq_reflection_iff  det R_t = det R_(-t) ↔ t = 0
7  primeGammaPhysicalRotationDeterminant_eq_source_iff      det R_t = det tau   ↔ t = 0
8  primeGammaCofinalBocksteinCoefficient_eq_zero_iff_determinants  b_t(p)=0 ↔ determinants agree
9  primeGammaCofinalBocksteinCoefficient_eq_zero_iff        b_t(p) = 0 ↔ t = 0
10 primeGammaCofinalBocksteinMagnitude_eq_abs_determinantTransgression
                                                          the Schatten reader is |transgression|
11 primeGammaCommonCorrectedRotationDeterminant_eq_reflection_iff        equivalence (3), c ≠ 0
12 primeGammaDeterminantOneStokesCorrection_eq_iff_bockstein_eq_zero     det2/BV correction no-go
13 primeGammaBothPhysicalDeterminants_eq_source_iff_bockstein_eq_zero    the source comparison of (2)
```

Steps 5–9 and 13 together are the equivalence chain (2) of the card; step 11 is (3); step 12 is
its determinant-one specialization.  The strict monotonicity of `x ↦ p^x` for an ordinary prime is
`Real.strictMono_rpow_of_base_gt_one`, and positivity of `d(p)` is
`primeActivationOccupancyFisherDensity_eq` together with `p > 0`.

## Verification

```text
lake env lean GaloisForLFunctions/RHTower/PrimeGammaCofinalBocksteinDeterminantTransgression.lean  -- clean
lake build GaloisForLFunctions.RHTower                                                             -- success
```

`#print axioms` on all 9 named declarations of the module reports exactly
`[propext, Classical.choice, Quot.sound]`.  No `sorry`, `admit`, `axiom`, `opaque`, or `unsafe`
declaration occurs.  The module is imported by `GaloisForLFunctions.RHTower`.
