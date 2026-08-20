import GaloisForLFunctions.HTGeometry.RadicalDifferentialIdealMaximal
import GaloisForLFunctions.HTGeometry.QuotientDerivation
import GaloisForLFunctions.HTGeometry.FractionRingDerivation
import Mathlib.Algebra.Module.LinearMap.Rat

/-!
# A consistent differential system has a solution in a differential field

A proper radical differential ideal of a differential `ℚ`-algebra sits inside a prime differential
ideal; the quotient is a differential domain, and its fraction field carries the extended
derivation.  The composite is a differential ring map to a differential field that kills the ideal —
the weak differential Nullstellensatz, and the step a differential closure is built from.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open scoped Differential

/-- The derivation of a differential `ℚ`-algebra, as a `ℚ`-derivation. -/
def ratDerivation (A : Type*) [CommRing A] [Algebra ℚ A] [Differential A] :
    Derivation ℚ A A :=
  Derivation.mk'
    ((Differential.deriv : Derivation ℤ A A).toLinearMap.toAddMonoidHom.toRatLinearMap)
    (fun a b => by
      have h := (Differential.deriv : Derivation ℤ A A).leibniz a b
      simp [smul_eq_mul] at h ⊢)

@[simp] theorem ratDerivation_apply {A : Type*} [CommRing A] [Algebra ℚ A] [Differential A]
    (a : A) : ratDerivation A a = a′ := rfl

/-- The derivation of the fraction field of a differential domain. -/
@[reducible] def fractionRingDifferential (A : Type*) [CommRing A] [IsDomain A] [Algebra ℚ A]
    [Differential A] : Differential (FractionRing A) where
  deriv :=
    letI : Algebra ℤ (FractionRing A) := Ring.toIntAlgebra _
    Derivation.restrictScalars ℤ
      (GaloisForLFunctions.fractionRingDerivation
        ((Algebra.linearMap A (FractionRing A)).compDer (ratDerivation A)))

theorem fractionRingDifferential_algebraMap (A : Type*) [CommRing A] [IsDomain A] [Algebra ℚ A]
    [Differential A] (a : A) :
    letI := fractionRingDifferential A
    (algebraMap A (FractionRing A) a)′ = algebraMap A (FractionRing A) (a′) := by
  letI := fractionRingDifferential A
  show GaloisForLFunctions.fractionRingDerivation
      ((Algebra.linearMap A (FractionRing A)).compDer (ratDerivation A))
      (algebraMap A (FractionRing A) a) = _
  rw [GaloisForLFunctions.fractionRingDerivation_algebraMap]
  rfl

/-- **A consistent differential system has a solution in a differential field extension.**  A proper
radical differential ideal of a differential `ℚ`-algebra is killed by a differential ring map to a
differential field. -/
theorem exists_differentialField_hom_of_ne_top {R : Type u} [CommRing R] [Algebra ℚ R]
    [Differential R] {I : Ideal R} (hrad : I.IsRadical)
    (hδ : ∀ x ∈ I, Differential.deriv x ∈ I) (hne : I ≠ ⊤) :
    ∃ (L : Type u) (_ : Field L) (_ : Differential L) (f : R →+* L),
      (∀ x : R, f (Differential.deriv x) = Differential.deriv (f x)) ∧ (∀ x ∈ I, f x = 0) := by
  classical
  obtain ⟨P, hPprime, hPδ, hIP⟩ := exists_isPrime_radicalDifferential hrad hδ hne
  letI : Differential (R ⧸ P) := quotientDifferential P hPδ
  haveI : IsDomain (R ⧸ P) := Ideal.Quotient.isDomain P
  letI : Algebra ℚ (R ⧸ P) := (Ideal.Quotient.mk P).comp (algebraMap ℚ R) |>.toAlgebra
  letI : Differential (FractionRing (R ⧸ P)) := fractionRingDifferential (R ⧸ P)
  refine ⟨FractionRing (R ⧸ P), inferInstance, inferInstance,
    (algebraMap (R ⧸ P) (FractionRing (R ⧸ P))).comp (Ideal.Quotient.mk P), ?_, ?_⟩
  · intro x
    show algebraMap (R ⧸ P) (FractionRing (R ⧸ P)) (Ideal.Quotient.mk P (Differential.deriv x))
      = Differential.deriv (algebraMap (R ⧸ P) (FractionRing (R ⧸ P)) (Ideal.Quotient.mk P x))
    rw [← quotientDifferential_deriv_mk P hPδ x, fractionRingDifferential_algebraMap]
  · intro x hx
    show algebraMap (R ⧸ P) (FractionRing (R ⧸ P)) (Ideal.Quotient.mk P x) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr (hIP hx), map_zero]

end

end GaloisForLFunctions.HTGeometry
