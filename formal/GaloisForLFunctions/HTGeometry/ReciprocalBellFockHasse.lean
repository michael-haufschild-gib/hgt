import GaloisForLFunctions.HTGeometry.GammaPoleReciprocalBellOrder

/-!
# Particle-number Hasse reconstruction for reciprocal-Bell jets

The reciprocal-Bell Fock transform restores the cross-degree information lost by dehomogenizing an
inverse-section jet polynomial.  This file treats particle number as a family of local coordinates:
all coefficients reconstruct the source polynomial, zero is detected coefficientwise, and every
nonzero finite jet appears in one finite particle sector.

This supplies Gamma-pole, inverse-section, and Fock-space routes with a lossless graded interface.
It does not identify a physical particle observable with any arithmetic source term.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- Finite jet polynomials are equivalent to the reciprocal-Bell Fock profiles they realize. -/
noncomputable def reciprocalBellFockTransformHasseEquivRange (n : ℕ) :
    MvPolynomial (Fin (n + 2)) ℂ ≃ Set.range (reciprocalBellFockTransform n) :=
  Equiv.ofInjective (reciprocalBellFockTransform n)
    (reciprocalBellFockTransform_injective n)

@[simp]
theorem reciprocalBellFockTransformHasseEquivRange_apply
    (n : ℕ) (P : MvPolynomial (Fin (n + 2)) ℂ) :
    (reciprocalBellFockTransformHasseEquivRange n P :
      Polynomial (MvPolynomial (Fin (n + 1)) ℂ)) =
        reciprocalBellFockTransform n P := rfl

/-- Equality of all particle-number coefficients detects equality of finite jet polynomials. -/
theorem reciprocalBellFock_congr_particle_hasse_iff
    (n : ℕ) (P Q : MvPolynomial (Fin (n + 2)) ℂ) :
    P = Q ↔ ∀ D : ℕ,
      (reciprocalBellFockTransform n P).coeff D =
        (reciprocalBellFockTransform n Q).coeff D := by
  constructor
  · rintro rfl
    exact fun _ ↦ rfl
  · intro h
    apply reciprocalBellFockTransform_injective n
    apply Polynomial.ext
    exact h

/-- A finite jet polynomial vanishes iff all particle-number coordinates vanish. -/
theorem reciprocalBellFock_eq_zero_particle_hasse_iff
    (n : ℕ) (P : MvPolynomial (Fin (n + 2)) ℂ) :
    P = 0 ↔ ∀ D : ℕ, (reciprocalBellFockTransform n P).coeff D = 0 := by
  constructor
  · rintro rfl
    intro D
    simp
  · intro h
    exact (reciprocalBellFock_congr_particle_hasse_iff n P 0).2 (by simpa using h)

/-- Every nonzero finite jet polynomial is detected in one finite particle-number sector. -/
theorem exists_particleCoefficient_ne_zero_of_reciprocalBellFock_ne_zero
    (n : ℕ) (P : MvPolynomial (Fin (n + 2)) ℂ) (hP : P ≠ 0) :
    ∃ D : ℕ, (reciprocalBellFockTransform n P).coeff D ≠ 0 := by
  by_contra h
  push Not at h
  exact hP ((reciprocalBellFock_eq_zero_particle_hasse_iff n P).2 h)

end GaloisForLFunctions.HTGeometry
