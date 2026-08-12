# Deninger rational-Witt localization over arbitrary rings

- **ID:** `deninger-rational-witt-localization`
- **Stage:** 3-formalized
- **Route:** L — rational-Witt source foundation
- **Status:** closed in Lean 4 (2026-08-12)
- **Primary source:** Christopher Deninger, *Rational Witt vectors and associated sheaves*,
  arXiv:2508.05329v1, Proposition 1.1.

## Exact theorem

Let `A` be any commutative ring, `M` any submonoid of `A`, and `S` any localization of `A` at
`M`. Then the coefficientwise map on canonical rational-Witt rings exhibits

```text
W_rat(S) ≃ [M]⁻¹ W_rat(A),
```

where `[M]` is the image of `M` under the Teichmüller monoid homomorphism. No domain,
reducedness, regular-denominator, torsion-freeness, or characteristic hypothesis occurs. Thus the
theorem includes coefficient rings with nilpotents and localization submonoids containing zero
divisors.

## Proof architecture

1. Prove the fixed-degree resultant identity `[b] ⊙ P(T)=P(bT)` over an algebraically closed
   field by normalized root factorization.
2. Descend the identity through a universal integer polynomial ring and evaluate into an arbitrary
   commutative ring, including the degree-drop case `b=0`.
3. Extend the identity to normalized fractions.
4. For a polynomial over `S`, use one common coefficient denominator `d`; coefficient `n` gains
   `d^n`, producing a normalized polynomial lift over `A` without assuming `A → S` injective.
5. Prove surjectivity by lifting numerator and denominator with one product denominator.
6. Prove the kernel condition independently: finitely many coefficient equalities after
   localization admit one product annihilator `m`; then powers of `m` force literal equality after
   dilation. This handles zero divisors and nilpotents.
7. Install `IsLocalization`, then obtain canonical algebra and ring equivalences from the
   localization universal property.

## Formal certificate

Module:

```text
GaloisForLFunctions.RHTower.DeningerRationalWittLocalization
```

Headline declarations:

- `deningerWittTensorPolynomial_teichmuller_arbitrary`
- `deningerCanonicalRationalWittTeichmuller_mul_normalizedFraction`
- `deningerPolynomialDilation_exists_normalized_lift`
- `deningerPolynomial_exists_common_annihilator_of_map_eq`
- `deningerCanonicalRationalWittCoefficientMap_surj`
- `deningerCanonicalRationalWittCoefficientMap_exists_of_eq`
- `deningerCanonicalRationalWitt_isLocalization`
- `deningerCanonicalRationalWittLocalizationAlgEquiv`
- `deningerCanonicalRationalWittLocalizationEquiv`

Audit:

- `lake env lean GaloisForLFunctions/RHTower/DeningerRationalWittLocalization.lean` — passed.
- `lake build GaloisForLFunctions.RHTower.DeningerRationalWittLocalization` — passed; no full or
  umbrella build run.
- `#print axioms` on all headline layers — only `propext`, `Classical.choice`, `Quot.sound`.
- Module imported by `GaloisForLFunctions.RHTower` umbrella.
- Global formal lint reached only unrelated pre-existing/uncommitted umbrella reachability errors;
  it reported no forbidden declaration in this module.

## Novelty boundary

Proposition 1.1 is literature mathematics, not a new RH theorem. New contribution is a
dependency-closed Lean proof on the literal rational-function carrier that retains the paper's
full arbitrary-ring strength, especially its noninjective-localization and nilpotent cases. This
closes rational-Witt algebra/localization infrastructure. It does not construct Route L's missing
singular source-to-physical comparison or prove RH.
