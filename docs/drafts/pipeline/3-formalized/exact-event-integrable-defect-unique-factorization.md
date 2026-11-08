# Integrable FE defects force unique norm factorization

- **ID:** exact-event-integrable-defect-unique-factorization
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** obstacles-summary §2.5, §2.10; B84, B103
- **Statement:** A countable Beurling system in the integrable uncompleted Riemann FE-defect class has injective generalized-integer norm, even with arbitrary real generator norms and unrestricted finite defect size.

## Proof mechanism

Regroup the generalized integers by their ordered distinct norms λₙ, with multiplicities Aₙ.
The defective theta relation and integrability give Abel limits C₀ → β/π and
C_{λₙ} → Aₙ/(2π). Positivity gives C_{λₙ} ≤ C₀, hence Aₙ ≤ 2β uniformly.

If distinct factorizations u and v have equal norm r, the k+1 factorizations
j·u+(k−j)·v, 0 ≤ j ≤ k, are distinct and all have norm rᵏ. Their multiplicity
exceeds 2β for large k, a contradiction. Thus every norm has exactly one factorization.

This removes every multiplicative relation between real prime norms from the possible
nonclassical finite-defect class. It does not identify multiplicatively independent norms
with rational primes or settle the finite-layer question.

## Audit

- [x] Corpus: `NormCollisionAmplification.uniform_finite_fibres_iff_norm_injective` supplies
  collision amplification; the Abel multiplicity bound occurs inside unit-density rigidity.
- [x] Paper argument has no missing analytic input within the stated defect class.
- [x] Direct Lean check of the theta and critical-line statements; transitive axioms only
  `propext`, `Classical.choice`, `Quot.sound`.

## Lean

`ExactEventTheory/IntegrableDefectsForbidNormCollisions.lean`:

- `atom_mass_le_of_integrable_theta_defect`
- `intNorm_injective_of_integrable_theta_defect`
- `intNorm_injective_of_integrable_critical_line_defect`

Final audit: `lake --old env lean GaloisForLFunctions/ExactEventTheory/IntegrableDefectsForbidNormCollisions.lean`.
The programme umbrella imports the module. The critical-line theorem displays the inverse-3/2
moment, strip continuity, holomorphy, decay and boundary identities, together with measurability,
polynomial growth and integrability of the uncompleted defect. No regularity of an individual
nonclassical example is assumed to have been established.
