import GaloisForLFunctions.HTGeometry.HasseExactSequence
import GaloisForLFunctions.RHTower.DeningerCalderonWittKoszulQuotient

/-!
# Hasse classification for Calderón--Witt Koszul data

Local and all-prime finite-support Koszul data are classified by their degree-two boundary values
modulo the corresponding defect axes.
-/

namespace RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

/-- At one prime, equal degree-two boundary values are exactly congruence modulo the local defect
axis. -/
theorem deningerCalderonWitt_congr_hasse_iff
    (p : Nat.Primes) (x y : DeningerCalderonWittAlgebraicDegreeOne p) :
    x - y ∈ LinearMap.range (deningerCalderonWittDefectAxisInclusion p) ↔
      deningerCalderonWittKoszulBoundary p x =
        deningerCalderonWittKoszulBoundary p y :=
  linearHasse_congr_iff
    (deningerCalderonWittDefectAxisInclusion p)
    (deningerCalderonWittKoszulBoundary p)
    (deningerCalderonWittDefectAxis_exact (p := p)) x y

/-- Every local degree-two value has a source representative, unique modulo the local defect
axis. -/
theorem deningerCalderonWitt_exists_unique_mod_defect
    (p : Nat.Primes) (z : DeningerCalderonWittAlgebraicDegreeTwo p) :
    ∃ x : DeningerCalderonWittAlgebraicDegreeOne p,
      deningerCalderonWittKoszulBoundary p x = z ∧
      ∀ y : DeningerCalderonWittAlgebraicDegreeOne p,
        deningerCalderonWittKoszulBoundary p y = z ↔
          y - x ∈ LinearMap.range (deningerCalderonWittDefectAxisInclusion p) :=
  linearHasse_exists_unique_mod_global
    (deningerCalderonWittDefectAxisInclusion p)
    (deningerCalderonWittKoszulBoundary p)
    (deningerCalderonWittDefectAxis_exact (p := p))
    (deningerCalderonWittKoszulBoundary_surjective p) z

/-- Across all primes, equal finite-support degree-two profiles are exactly congruence modulo all
local defect axes. -/
theorem deningerCalderonWittGlobal_congr_hasse_iff
    (x y : DeningerCalderonWittAlgebraicGlobalDegreeOne) :
    x - y ∈ deningerCalderonWittGlobalDefectAxisInclusionAdd.range ↔
      deningerCalderonWittGlobalKoszulBoundary x =
        deningerCalderonWittGlobalKoszulBoundary y :=
  addHasse_congr_iff
    deningerCalderonWittGlobalDefectAxisInclusionAdd
    deningerCalderonWittGlobalKoszulBoundaryAdd
    deningerCalderonWittGlobalDefectAxis_exact_add x y

/-- Every finite-support all-prime degree-two profile has a global source representative, unique
modulo the direct sum of local defect axes. -/
theorem deningerCalderonWittGlobal_exists_unique_mod_defects
    (z : DeningerCalderonWittAlgebraicGlobalDegreeTwo) :
    ∃ x : DeningerCalderonWittAlgebraicGlobalDegreeOne,
      deningerCalderonWittGlobalKoszulBoundary x = z ∧
      ∀ y : DeningerCalderonWittAlgebraicGlobalDegreeOne,
        deningerCalderonWittGlobalKoszulBoundary y = z ↔
          y - x ∈ deningerCalderonWittGlobalDefectAxisInclusionAdd.range :=
  addHasse_exists_unique_mod_global
    deningerCalderonWittGlobalDefectAxisInclusionAdd
    deningerCalderonWittGlobalKoszulBoundaryAdd
    deningerCalderonWittGlobalDefectAxis_exact_add
    deningerCalderonWittGlobalKoszulBoundary_surjective z

end
end RHTower
