import GaloisForLFunctions.HTGeometry.AffineExponentialAlgebraicLocusPoint
import GaloisForLFunctions.HTGeometry.FiniteTypeSpecialization

/-!
# Algebraic points in principal opens of mixed loci

Weak Nullstellensatz with localization chooses a coordinatewise algebraic point on the exact
algebraic-number locus of a mixed complex point while preserving nonvanishing of one prescribed
regular function.  This is the open-locus refinement needed when a Kähler identity is obtained
after clearing a denominator.
-/

namespace GaloisForLFunctions.HTGeometry
namespace AffineExponentialAlgebraicLocusOpenPoint

open GaloisForLFunctions
open AffineExponentialGroup AffineExponentialPointEvaluation
open AffineExponentialPointRepresentation
open AffineExponentialAlgebraicLocusPoint

noncomputable section

/-- A nonvanishing algebraic-number regular function remains nonzero at some coordinatewise
algebraic point of the exact locus. -/
theorem exists_algebraic_locus_point_avoiding {n : ℕ} (p : Point ℂ n)
    (g : CoordinateAlgebra (algebraicClosure ℚ ℂ) n)
    (hg : eval (k := algebraicClosure ℚ ℂ) p g ≠ 0) :
    ∃ q : Point ℂ n,
      (∀ i, IsAlgebraic ℚ (additivePart q i)) ∧
      (∀ i, IsAlgebraic ℚ (torusPart q i : ℂ)) ∧
      eval (k := algebraicClosure ℚ ℂ) q g ≠ 0 ∧
      ∀ f : CoordinateAlgebra (algebraicClosure ℚ ℂ) n,
        eval (k := algebraicClosure ℚ ℂ) p f = 0 →
          eval (k := algebraicClosure ℚ ℂ) q f = 0 := by
  let A := algebraicClosure ℚ ℂ
  let J := algebraicLocusIdeal p
  letI : J.IsPrime := by
    simpa [J, algebraicLocusIdeal] using
      RingHom.ker_isPrime (eval (k := A) p).toRingHom
  letI : IsDomain (CoordinateAlgebra A n ⧸ J) := Ideal.Quotient.isDomain J
  letI : Algebra.FiniteType A (CoordinateAlgebra A n ⧸ J) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ A J)
      Ideal.Quotient.mk_surjective
  letI : IsAlgClosed A := algebraicClosure_isAlgClosed ℚ ℂ
  have hgquot : Ideal.Quotient.mk J g ≠ 0 := by
    intro hzero
    have hmem : g ∈ J := Ideal.Quotient.eq_zero_iff_mem.mp hzero
    exact hg hmem
  obtain ⟨rho, hrho⟩ := exists_algHom_ne_zero_of_finiteType_domain
    A (CoordinateAlgebra A n ⧸ J) (Ideal.Quotient.mk J g) hgquot
  let chiA : CoordinateAlgebra A n →ₐ[A] A :=
    rho.comp (Ideal.Quotient.mkₐ A J)
  let chiC : CoordinateAlgebra A n →ₐ[A] ℂ :=
    (Algebra.ofId A ℂ).comp chiA
  let q : Point ℂ n := pointOfAlgHom chiC
  refine ⟨q, ?_, ?_, ?_, ?_⟩
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
  · rw [eval_pointOfAlgHom]
    change algebraMap A ℂ (rho (Ideal.Quotient.mk J g)) ≠ 0
    exact (algebraMap A ℂ).injective.ne hrho
  · intro f hf
    rw [eval_pointOfAlgHom]
    change algebraMap A ℂ (chiA f) = 0
    rw [map_eq_zero_iff (algebraMap A ℂ) (algebraMap A ℂ).injective]
    change rho (Ideal.Quotient.mk J f) = 0
    rw [show Ideal.Quotient.mk J f = 0 by
      exact Ideal.Quotient.eq_zero_iff_mem.mpr hf]
    exact map_zero rho

end

end AffineExponentialAlgebraicLocusOpenPoint
end GaloisForLFunctions.HTGeometry
