# Normalized formal relations specialize to leading-coefficient differential relations

- **ID:** `formal-leading-coefficient-specialization`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) / DIFFERENTIAL-ALGEBRA BRIDGE / NOT NEW SCIENTIFIC KNOWLEDGE
- **Parent:** `../../2-fully-proven/not_new_scientific_knowledge/leading-laurent-coefficient-differential-algebraicity.md`
- **Statement:** A polynomial-in-parameter relation on power-series lifts of finitely many jets
  specializes at parameter zero to a relation on their constant coefficients; if the specialized
  relation is nonzero and those coefficients are the jets of one element, that element is
  differentially algebraic.
- **Scientific status:** `[PROVED HERE] [FORMALIZED] [NOT NEW SCIENTIFIC KNOWLEDGE]`

## Goal

Provide the exact machine-checked specialization receiver used by the cosmological total-energy
singularity program.  The theorem is purely algebraic and makes no cosmology claim by itself.

## Formal content

The module
`formal/GaloisForLFunctions/HTGeometry/FormalLeadingCoefficientSpecialization.lean` defines

```text
formalParameterSpecialization
polynomialFormalParameterMap
```

and proves

```text
constantCoeff_comp_polynomialFormalParameterMap
algebraMap_comp_evalRingHom_zero
constantCoeff_eval₂_polynomialFormalParameterMap
aeval_formalParameterSpecialization_eq_constantCoeff
differentialAlgebraicOver_of_normalized_formalParameterRelation
```

The final theorem assumes:

1. a finite polynomial-coefficient relation in a formal parameter;
2. power-series lifts whose constant coefficients are the required differential jets;
3. vanishing of the formal relation;
4. nonvanishing of the relation after setting the parameter to zero.

It concludes differential algebraicity of the leading coefficient over the scalar base.

## Exact boundary

The full Laurent theorem also requires clearing rational parameter denominators, multiplying away
the finite principal part, and dividing the relation coefficients by their common lowest parameter
power so that the specialization is nonzero.  Those normalization steps are paper-proved but not
yet formalized here.

The module does not construct a cosmological wavefunction, identify a total-energy pole, or prove
that an HT flat-space amplitude occurs in cosmology.

## Verification

- direct touched-file `lake env lean` -- PASS
- `lake build +GaloisForLFunctions.HTGeometry.FormalLeadingCoefficientSpecialization` -- PASS
- axiom audit of the specialization and DA capstones -- only `propext`, `Classical.choice`, and
  `Quot.sound`

## Novelty gate

This is formal polynomial specialization and finite-jet differential algebra.  It is required
infrastructure, not new scientific knowledge.
