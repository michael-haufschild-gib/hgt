import GaloisForLFunctions.RHTower.SoninSourceGlobalGradedCorona
import GaloisForLFunctions.HTGeometry.TailQuotientSeparationLaw

/-!
# Finite-observation separation for singular-grade coronas

The Sonin singular-grade relation ignores every finite modification of a
section.  The universal quotient-completion separation law therefore applies:
no nonconstant reporter on the singular-grade quotient is determined by
finitely many depth coordinates.
-/

open Filter

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry

/-- Finite coordinate changes preserve every positive singular-grade
equivalence relation. -/
theorem singularGradeSetoid_finiteModificationSaturated
    {H : Type*} [NormedAddCommGroup H]
    (epsilon : ℕ → ℝ) (hepsilon : ∀ n, 0 < epsilon n) :
    FiniteModificationSaturated (singularGradeSetoid (H := H) epsilon hepsilon) := by
  intro x y hfinite
  change SingularGradeEquivalent epsilon x y
  unfold SingularGradeEquivalent
  have heq : ∀ᶠ n : ℕ in atTop, x n = y n := by
    rw [← Nat.cofinite_eq_atTop, Filter.eventually_cofinite]
    exact hfinite
  apply tendsto_const_nhds.congr'
  filter_upwards [heq] with n hn
  simp [hn]

/-- Every finite coordinate cylinder projects onto the full singular-grade
quotient. -/
theorem finiteCoordinateCylinder_surjective_singularGradeQuotient
    {H : Type*} [NormedAddCommGroup H]
    (epsilon : ℕ → ℝ) (hepsilon : ∀ n, 0 < epsilon n)
    (s : Finset ℕ) (observed : ℕ → H)
    (q : Quotient (singularGradeSetoid (H := H) epsilon hepsilon)) :
    ∃ candidate : ℕ → H,
      FiniteCoordinatesAgree s candidate observed ∧
        Quotient.mk (singularGradeSetoid (H := H) epsilon hepsilon) candidate = q :=
  finiteCoordinateCylinder_surjective_quotient
    (singularGradeSetoid (H := H) epsilon hepsilon)
    (singularGradeSetoid_finiteModificationSaturated epsilon hepsilon)
    s observed q

/-- No nonconstant singular-grade quotient reporter is determined by finitely
many depth coordinates. -/
theorem finiteCoordinate_singularGradeReporter_constant
    {H Y : Type*} [NormedAddCommGroup H]
    (epsilon : ℕ → ℝ) (hepsilon : ∀ n, 0 < epsilon n)
    (s : Finset ℕ)
    (F : Quotient (singularGradeSetoid (H := H) epsilon hepsilon) → Y)
    (hF : FiniteCoordinateQuotientReporterDeterminedBy
      (singularGradeSetoid (H := H) epsilon hepsilon) s F) :
    ReporterConstant F :=
  finiteCoordinate_quotientReporter_constant
    (singularGradeSetoid (H := H) epsilon hepsilon)
    (singularGradeSetoid_finiteModificationSaturated epsilon hepsilon)
    s F hF

end

end RHTower
