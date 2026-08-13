# Triptic HT Kummer-content root classification — formalized

- **ID:** `triptic-ht-kummer-content-root-classification-formalized`
- **Stage:** 3-formalized
- **Paper proof:** `triptic-ht-kummer-content-root-classification.md`
- **Type:** FORMALIZATION CERTIFICATE

## Lean modules

```text
formal/GaloisForLFunctions/HTGeometry/TripticMultiplicativeSourceClass.lean
formal/GaloisForLFunctions/HTGeometry/TripticSourceDivisorFinsupp.lean
formal/GaloisForLFunctions/HTGeometry/TripticGammaProductRealization.lean
formal/GaloisForLFunctions/HTGeometry/TripticKummerRootClassification.lean
formal/GaloisForLFunctions/HTGeometry/TripticSourceReciprocity.lean
formal/GaloisForLFunctions/HTGeometry/TripticSourceClassGroup.lean
```

together with the abstract Kummer core in
`formal/GaloisForLFunctions/HTGeometry/MinimalHTCompletionArchitecture.lean` and
`formal/GaloisForLFunctions/HTGeometry/SourceDivisorSurjectivity.lean`, and the kernel theorems of
the parent certificate `triptic-orbit-residue-reciprocity-formalized.md`.

## The formal theorem chain

The class is `TripticMultiplicativeSource τ σ Y Cst`: `Y` meromorphic on `ℂ` with finite order
everywhere, exactly `1`-periodic, and with `MixedConstGerm (logDeriv Y) τ σ Cst` — the mixed
multiplicative coboundary has constant logarithmic derivative as an identity of meromorphic germs.
Throughout, `(τ, σ)` carry only the data of the class: positive imaginary parts and rational
independence of `1, τ, σ`.

1. **The divisor** `(3)`.  `tripticDivisor : ℤ[ℂ ⧸ H₃]` — the orbital charge is `H₃`-invariant
   (`shiftOrder_add_tau_of_source` supplies the `τ`-direction from the mixed germ constraint) and
   finitely supported on classes (`finite_support_tripticChargeClass`, by reducing the
   `1`/`τ`-invariant shift-order support into one compact fundamental parallelogram of `ℤ + ℤτ`).
   `tripticOrbitCharge_reciprocity_source` proves `D_σ = D_τ` on the class, so the two elliptic
   realizations define one divisor.
2. **Additivity and kernel** `(4)`, `(5)`.  `tripticOrbitCharge_mul/_pow/_div/_zpow` (additivity),
   and the kernel identification in both directions:
   `differentiallyAlgebraic_logDeriv_of_vanishing_orbitCharge_source` and
   `tripticOrbitCharge_eq_zero_of_differentiallyAlgebraic_source`.
3. **Surjectivity.**  `gammaDivisorSource` realizes every finite integral divisor by a product of
   translated elliptic gamma functions with integer exponents, inside the class
   (`tripticMultiplicativeSource_gammaDivisorSource`,
   `tripticOrbitCharge_gammaDivisorSource`).
4. **The root theorem and content spectrum** `(7)`–`(9)`.
   `hasTripticSourceRoot_iff_dvd_charge`, `hasTripticSourceRoot_iff_content_dvd`,
   `tripticSourceRoot_unique`, `hasTripticSourceRoot_content`,
   `tripticSource_maximal_root_order` — an `m`-th source root modulo differentially algebraic
   factors exists iff `m` divides every divisor coefficient, iff `m` divides the Kummer content;
   the root class is unique modulo DA; the content is the exact maximum root order.
5. **The group packaging and effective quotient** `(6)`.  `tripticSourceUnitClass` packages the
   class as a subgroup of the units of the codiscrete-germ ring of `ℂ` (as functions the class is
   a group only away from the divisors); `tripticDivisorHom : M →+ ℤ[ℂ ⧸ H₃]` is well defined by
   `tripticOrbitCharge_congr`; `tripticDivisorHom_single` realizes every class `[g]`;
   `tripticSourceQuotientEquiv : M ⧸ ker D ≃+ ℤ[ℂ ⧸ H₃]`;
   `tripticSource_hasSourceRootModuloKernel_iff_content_dvd` is the abstract classification
   applied verbatim; `mem_ker_tripticDivisorHom_iff` identifies `ker D` with the differentially
   algebraic members.

## Verification

- `lake env lean` and `lake build GaloisForLFunctions.HTGeometry.<Module>` pass for each module.
- `#print axioms` on every declaration listed above reports
  `[propext, Classical.choice, Quot.sound]`.
- All six modules are imported by the `GaloisForLFunctions.HTGeometry` umbrella.
- The hypothesis class is inhabited: every translated elliptic gamma function is a proved member
  (`tripticMultiplicativeSource_ellipticGammaConeTranslate`), so no statement is vacuous.
