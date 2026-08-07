# Burnol prime-dilation co-Poisson quotient law — formalized

- **ID:** `burnol-prime-dilation-copoisson-quotient-law-formalized`
- **Stage:** 3-formalized
- **Paper proof:** `burnol-prime-dilation-copoisson-quotient-law.md`
- **Type:** FORMALIZATION CERTIFICATE

## Lean modules

```text
formal/GaloisForLFunctions/RHTower/BurnolSoninDilationMellin.lean
formal/GaloisForLFunctions/RHTower/BurnolSoninProjectedEvaluationTransport.lean
formal/GaloisForLFunctions/RHTower/BurnolPrimeDilationCoPoissonQuotient.lean
```

## Formal theorem chain

```text
1  soninMellinEvaluation_evenDilation                  M(D_r f)(w) = r^(w-1/2) M(f)(w)      (1)
2  evenDilation_mem_soninExtendedSpace_inv_mul         D_r sends K_a into K_(a/r)           (1)
3  burnolProjectedAdjointEvaluationVector_eq           projected inverse jet transport      (2)
4  burnolProjectedForwardEvaluationVector_eq           projected forward jet transport      (2)
5  burnolExtendedApertureDefectPlus / ...Minus         the retained orthogonal defect       (2)
6  burnolPrimeCharacter                                lambda_p(s) = p^(s-1/2)
7  burnolPrimeCharacter_sub_mul_dslope                 the divided-difference identity
8  dslope_burnolPrimeCharacter_eq_gammaCoPoissonIntervalCell
     the explicit finite-log-support cell on [0, log p]
9  burnolPrime_resolvent_quotient_identity             the zero-radical quotient action     (6)
10 orbitwiseScaleSeamCharge_eq_burnolPrimeCharacter_reflection   the prime-seam split       (7)
```

## Verification

```text
lake env lean GaloisForLFunctions/RHTower/BurnolPrimeDilationCoPoissonQuotient.lean  -- clean
lake env lean GaloisForLFunctions/RHTower/BurnolSoninProjectedEvaluationTransport.lean -- clean
```

Both card endpoints, registered as `burnolPrimeDilationCoPoissonQuotientCard` and
`burnolPrimeDilationReflectionSeamCard` in `BurnolFormalizedCards.lean`, report
`[propext, Classical.choice, Quot.sound]` under `#print axioms`.
All modules are wired into `GaloisForLFunctions.RHTower`.
