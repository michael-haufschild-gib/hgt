# Central promotion/admission exchange -- Lean certification

- **ID:** ULF-RLM-11
- **Paper card:**
  `docs/drafts/pipeline/2-fully-proven/universal-law-field/central-promotion-admission-exchange-and-quotient-obstruction-law.md`
- **Lean module:**
  `GaloisForLFunctions.HTGeometry.ConstitutiveCentralAdmissionExchange`
- **Umbrella:** `GaloisForLFunctions.HTGeometry.UniversalLawField`
- **Status:** [LEAN-CERTIFIED] [NO PROJECT AXIOMS] [CROSS-MODE MECHANISM LAW] [NOT RH]

## Certified declarations

- `CompensatorAdmitted`;
- `AdmittedCarrierClosed`;
- `compensatorAdmitted_iff_carrierClosed`;
- `compensatorAdmitted_iff_observed_zero`;
- `AdmittedPromotedCarrier`;
- `admittedCarrierInclusion` and its injectivity;
- `admittedCompensator`;
- `admittedPromotedBinary`;
- `admittedCarrierInclusion_promoted`;
- `admittedPromotedBinary_unique`;
- `admittedPromotedBinary_associative_of_ambient`;
- `bilinearPromotionCarry_associator_zero`;
- `bilinearPromotionCarry_ambient_associative`;
- `bilinearPromotionCarry_not_modTwo_admitted`;
- `bilinearPromotionCarry_observed_nonzero`;
- `bilinearPromotionCarry_evenCarrier_not_closed`;
- `constitutiveCentralAdmissionExchangeMechanism_closed`.

## Exact content

An additive compensator survives an admission quotient exactly when all its values lie in the
quotient kernel.  Lean proves this is equivalent both to closure of the admitted promoted carrier
and to vanishing of the quotient-valued compensator.  Under this condition, the restricted
promoted operation exists uniquely, its inclusion preserves ambient promotion, and ambient
associativity descends.

Lean also certifies the sharp separation laboratory: integer multiplication has zero promotion
associator and gives an associative ambient promoted law, while parity admission rejects its value
at `(1,1)`, detects a nonzero quotient residual, and leaves the even-coefficient carrier nonclosed.
Thus exact coherence does not imply exact admission.

## Verification

Foreground checks:

```text
lake env lean GaloisForLFunctions/HTGeometry/ConstitutiveCentralAdmissionExchange.lean
lake build GaloisForLFunctions.HTGeometry.UniversalLawField
```

The axiom audit reports only standard quotient/classical foundations.  No `sorry`, `admit`, new
axiom, `opaque`, `unsafe`, `native_decide`, or computational certificate is used.
