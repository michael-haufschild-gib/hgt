import GaloisForLFunctions.HTGeometry.AppellHumbertJetAmple

/-!
# A concrete positive integer-lattice factor is all-order jet ample

For every complex dimension, the standard Hermitian form and the trivial
semicharacter define one explicit Appell--Humbert factor on the standard
integer lattice.  Its positive semidefinite form, lattice semicharacter, and
all-order Poincare interpolation theorem are all constructed here; the final
jet-ampleness theorem has no analytic or geometric premises.
-/

open Complex

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Standard positive Hermitian form, linear in its first argument. -/
def standardHermitianForm (d : ℕ) : (Fin d → ℂ) → (Fin d → ℂ) → ℂ :=
  fun x y => ∑ i, x i * star (y i)

/-- The standard coordinate form is Hermitian. -/
theorem standardHermitianForm_isHermitian (d : ℕ) :
    IsHermitianForm (standardHermitianForm d) where
  add_left := by
    intro x y z
    simp [standardHermitianForm, Finset.sum_add_distrib, add_mul]
  smul_left := by
    intro a x y
    simp [standardHermitianForm, Finset.mul_sum, Pi.smul_apply, mul_assoc]
  symm := by
    intro x y
    rw [standardHermitianForm, standardHermitianForm, map_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [star_mul, star_star]
    ring

/-- The standard Hermitian form is positive semidefinite. -/
theorem standardHermitianForm_nonneg (d : ℕ) (x : Fin d → ℂ) :
    0 ≤ (standardHermitianForm d x x).re := by
  rw [standardHermitianForm]
  rw [map_sum]
  apply Finset.sum_nonneg
  intro i hi
  rw [Complex.star_def, Complex.mul_conj]
  positivity

/-- The standard form has real values on pairs of integer-lattice vectors. -/
theorem standardHermitianForm_integerCast_im (d : ℕ)
    (k l : Fin d → ℤ) :
    (standardHermitianForm d (integerCastVector k) (integerCastVector l)).im = 0 := by
  rw [standardHermitianForm, map_sum]
  apply Finset.sum_eq_zero
  intro i hi
  simp [integerCastVector, Complex.star_def]

/-- Trivial semicharacter for the standard integer lattice. -/
def standardSemicharacter (d : ℕ) : (Fin d → ℂ) → ℂ := fun _ => 1

/-- The trivial semicharacter is unitary. -/
theorem standardSemicharacter_unit (d : ℕ) (γ : Fin d → ℂ) :
    ‖standardSemicharacter d γ‖ = 1 := by
  simp [standardSemicharacter]

/-- The trivial semicharacter obeys the Appell--Humbert law on the integer lattice. -/
theorem standardSemicharacter_isSemicharacterOn (d : ℕ) :
    IsSemicharacterOn (standardHermitianForm d) (standardSemicharacter d)
      (standardIntegerLattice d) := by
  intro γ hγ γ' hγ'
  obtain ⟨k, hk⟩ := hγ
  obtain ⟨l, hl⟩ := hγ'
  have him : (standardHermitianForm d γ γ').im = 0 := by
    rw [← hk, ← hl]
    exact standardHermitianForm_integerCast_im d k l
  simp [standardSemicharacter, him]

universe u

/-- The explicit positive Appell--Humbert factor on the standard integer lattice. -/
noncomputable def standardPositiveAppellHumbertFactor (d : ℕ) :
    AutomorphicFactor d (standardIntegerLattice d) :=
  appellHumbertAutomorphicFactor (standardHermitianForm_isHermitian d)
    (standardSemicharacter_unit d) (standardSemicharacter_isSemicharacterOn d)

/-- **Closed all-order interpolation theorem for the standard positive factor.** -/
theorem standardPositiveAppellHumbertFactor_jetAmpleEveryFiniteOrder (d : ℕ) :
    AutomorphicFactor.JetAmpleEveryFiniteOrder.{u}
      (standardPositiveAppellHumbertFactor d) := by
  exact jetAmpleEveryFiniteOrder_appellHumbert.{u}
    (standardHermitianForm_isHermitian d)
    (standardHermitianForm_nonneg d)
    (standardSemicharacter_unit d)
    (standardSemicharacter_isSemicharacterOn d)

end

end GaloisForLFunctions.HTGeometry
