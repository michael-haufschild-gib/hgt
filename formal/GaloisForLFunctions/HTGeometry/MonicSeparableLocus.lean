import GaloisForLFunctions.HTGeometry.AlgebraSpectrumTopology
import GaloisForLFunctions.HTGeometry.BivariateSeparableResultant

/-!
# Open separable locus of a monic polynomial family

For a monic polynomial over a complex algebra, separability of its specialization at a complex
point is equivalent to nonvanishing of one resultant element of the algebra.  Point evaluation is
continuous in `AlgSpec`, so the separable locus is open.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

namespace AlgSpec

/-- Resultant element controlling separability of all complex specializations of a monic
polynomial. -/
noncomputable def monicSpecializationResultant
    {A : Type*} [CommRing A] [Algebra ℂ A] (p : Polynomial A) : A :=
  Polynomial.resultant p (Polynomial.derivative p) p.natDegree (p.natDegree - 1)

/-- Evaluation of the global resultant element is the resultant of the specialized polynomial. -/
theorem apply_monicSpecializationResultant
    {A : Type*} [CommRing A] [Algebra ℂ A] (p : Polynomial A) (hp : p.Monic)
    (χ : AlgSpec A) :
    χ (monicSpecializationResultant p) =
      Polynomial.resultant (p.map χ.toRingHom) (Polynomial.derivative (p.map χ.toRingHom))
        (p.map χ.toRingHom).natDegree ((p.map χ.toRingHom).natDegree - 1) := by
  have hdeg : (p.map χ.toRingHom).natDegree = p.natDegree := hp.natDegree_map χ.toRingHom
  rw [monicSpecializationResultant, hdeg, Polynomial.derivative_map]
  exact (Polynomial.resultant_map_map (f := p) (g := Polynomial.derivative p)
    (m := p.natDegree) (n := p.natDegree - 1) χ.toRingHom).symm

/-- Complex points where the specialized polynomial is separable. -/
def monicSeparableLocus
    {A : Type*} [CommRing A] [Algebra ℂ A] (p : Polynomial A) : Set (AlgSpec A) :=
  {χ | (p.map χ.toRingHom).Separable}

/-- Membership in the separable locus is nonvanishing of the specialization resultant. -/
theorem mem_monicSeparableLocus_iff_resultant_ne_zero
    {A : Type*} [CommRing A] [Algebra ℂ A] (p : Polynomial A) (hp : p.Monic)
    (χ : AlgSpec A) :
    χ ∈ monicSeparableLocus p ↔ χ (monicSpecializationResultant p) ≠ 0 := by
  rw [monicSeparableLocus, Set.mem_setOf_eq,
    separable_iff_resultant_ne_zero (hp.map χ.toRingHom),
    apply_monicSpecializationResultant p hp χ]

/-- **Separability of a monic polynomial family is an open condition on complex points.** -/
theorem isOpen_monicSeparableLocus
    {A : Type*} [CommRing A] [Algebra ℂ A] (p : Polynomial A) (hp : p.Monic) :
    IsOpen (monicSeparableLocus p) := by
  rw [show monicSeparableLocus p =
      {χ : AlgSpec A | χ (monicSpecializationResultant p) ≠ 0} by
    ext χ
    exact mem_monicSeparableLocus_iff_resultant_ne_zero p hp χ]
  exact (continuous_eval _).isOpen_preimage {z : ℂ | z ≠ 0} isOpen_ne

end AlgSpec

end GaloisForLFunctions.HTGeometry
