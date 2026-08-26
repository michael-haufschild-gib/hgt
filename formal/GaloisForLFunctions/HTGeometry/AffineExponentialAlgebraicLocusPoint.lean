import GaloisForLFunctions.HTGeometry.AffineExponentialFiniteType
import GaloisForLFunctions.HTGeometry.AffineExponentialPointRepresentation
import GaloisForLFunctions.HTGeometry.NullstellensatzPoint
import GaloisForLFunctions.HTGeometry.AlgebraicClosureAlgClosed

/-!
# Algebraic points on mixed affine-exponential loci

For a complex point of `Gₐⁿ × Gₘⁿ`, take the kernel of evaluation over the concrete algebraic
numbers `algebraicClosure ℚ ℂ`.  Weak Nullstellensatz produces another point on this exact locus
whose additive and torus coordinates are all algebraic numbers.
-/

namespace GaloisForLFunctions.HTGeometry
namespace AffineExponentialAlgebraicLocusPoint

open AffineExponentialGroup AffineExponentialPointEvaluation
open AffineExponentialPointRepresentation

noncomputable section

/-- Ideal of all mixed regular functions over the algebraic numbers that vanish at `p`. -/
def algebraicLocusIdeal {n : ℕ} (p : Point ℂ n) :
    Ideal (CoordinateAlgebra (algebraicClosure ℚ ℂ) n) :=
  RingHom.ker (eval (k := algebraicClosure ℚ ℂ) p).toRingHom

/-- Every mixed affine-exponential complex point has a coordinatewise algebraic point on its exact
`algebraicClosure ℚ ℂ`-locus. -/
theorem exists_algebraic_locus_point {n : ℕ} (p : Point ℂ n) :
    ∃ q : Point ℂ n,
      (∀ i, IsAlgebraic ℚ (additivePart q i)) ∧
      (∀ i, IsAlgebraic ℚ (torusPart q i : ℂ)) ∧
      ∀ f : CoordinateAlgebra (algebraicClosure ℚ ℂ) n,
        eval (k := algebraicClosure ℚ ℂ) p f = 0 →
          eval (k := algebraicClosure ℚ ℂ) q f = 0 := by
  let A := algebraicClosure ℚ ℂ
  let J := algebraicLocusIdeal p
  have hJ : J ≠ ⊤ := by
    simpa [J, algebraicLocusIdeal] using
      RingHom.ker_ne_top (eval (k := A) p).toRingHom
  letI : Nontrivial (CoordinateAlgebra A n ⧸ J) :=
    Ideal.Quotient.nontrivial_iff.mpr hJ
  letI : Algebra.FiniteType A (CoordinateAlgebra A n ⧸ J) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ A J)
      Ideal.Quotient.mk_surjective
  letI : IsAlgClosed A := algebraicClosure_isAlgClosed ℚ ℂ
  obtain ⟨rho⟩ := exists_algHom_of_finiteType_of_isAlgClosed
    (C := A) (E := CoordinateAlgebra A n ⧸ J)
  let chiA : CoordinateAlgebra A n →ₐ[A] A :=
    rho.comp (Ideal.Quotient.mkₐ A J)
  let chiC : CoordinateAlgebra A n →ₐ[A] ℂ :=
    (Algebra.ofId A ℂ).comp chiA
  let q : Point ℂ n := pointOfAlgHom chiC
  refine ⟨q, ?_, ?_, ?_⟩
  · intro i
    have heval := eval_pointOfAlgHom chiC (additiveCoordinate A i)
    rw [eval_additiveCoordinate] at heval
    rw [heval]
    exact mem_algebraicClosure_iff.mp (chiA (additiveCoordinate A i)).2
  · intro i
    have heval := eval_pointOfAlgHom chiC
      (torusCharacter A (Finsupp.single i 1))
    rw [eval_torusCharacter, AlgebraicTorusCharacter.character_single, zpow_one] at heval
    rw [heval]
    exact mem_algebraicClosure_iff.mp
      (chiA (torusCharacter A (Finsupp.single i 1))).2
  · intro f hf
    rw [eval_pointOfAlgHom]
    change algebraMap A ℂ (chiA f) = 0
    rw [map_eq_zero_iff (algebraMap A ℂ) (algebraMap A ℂ).injective]
    change rho (Ideal.Quotient.mk J f) = 0
    rw [show Ideal.Quotient.mk J f = 0 by
      exact Ideal.Quotient.eq_zero_iff_mem.mpr hf]
    exact map_zero rho

end

end AffineExponentialAlgebraicLocusPoint
end GaloisForLFunctions.HTGeometry
