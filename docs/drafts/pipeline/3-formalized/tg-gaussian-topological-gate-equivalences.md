# TG — the topological gate in nine equivalent forms (capstone)

- **ID:** TG-CAP-1
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean, unconditional TFAE)
- **Statement:** RH ⟺ (2) P ≤ C + K on (0,1] ⟺ (3) P < C eventually ⟺ (4) P − C ≤ −1/10 + 32√y on (0,1]
  ⟺ (5) Π − C → −∞ ⟺ (6) sign abscissa = ½ ⟺ (7) ∀θ>½ ∀τ: θ-weighted Bohr coefficient = 0 (new spectral form)
  ⟺ (8) anchored-cubic sub-unit gate on every strict-right rectangle ⟺ (9) Route-P base-Cauchy trace capacity law (P-G181).
- **New item:** (7) via visibility (TG-BOHR-2): a zero on Re ρ = θ is exactly a nonzero θ-weighted coefficient.

## Lean
`RHTower/GaussianTopologicalGateEquivalences.lean`, wired after GaussianGapSignPhaseTransition.
`riemannHypothesis_tfae_gaussianTopologicalGate`, `riemannHypothesis_iff_forall_weightedBohrCoefficient_eq_zero`.
Build exit 0; axioms [propext, Classical.choice, Quot.sound].

## Reading
All TG targets — budget, sign, explicit criterion, primes-only Chebyshev, sign abscissa, Bohr spectrum,
anchored cubic gate, Burnol capacity law — are one statement. The producer missing in every form is
the Loewner transport of RoutePMatrixCompleteBoundaryRestrictionLaw (zero Cauchy Gram ≤ prime window Gram);
function-field benchmark: there it is Stepanov's Frobenius-algebraic auxiliary polynomial.
