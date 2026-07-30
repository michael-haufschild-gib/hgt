import GaloisForLFunctions.RHTower.SoninSourceGlobalGradedCorona
import GaloisForLFunctions.RHTower.SoninCofinalContractiveInwardIncidence

/-!
# Contractive descent on singular-grade coronas

A singular Rees grade is represented by a uniformly bounded moving section
modulo an `o(epsilon)` difference.  Any uniformly contractive moving operator
family preserves both conditions, so it descends canonically to the quotient.

This is the reusable carrier theorem.  Its Sonin specialization places the
oriented inward dilation corner on every positive singular grade without
choosing an ultrafilter, a divisor point, or a new target-fitted norm.
-/

open Complex Filter Topology
open scoped ENNReal InnerProductSpace

noncomputable section

namespace RHTower

/-- A uniformly contractive moving family sends bounded sections to bounded
sections, with the same uniform ceiling. -/
def singularGradeSectionMapOfContractive
    {H K : Type*}
    [NormedAddCommGroup H] [NormedSpace ℂ H]
    [NormedAddCommGroup K] [NormedSpace ℂ K]
    (T : ℕ → H →L[ℂ] K) (hT : ∀ n, ‖T n‖ ≤ 1)
    (x : SingularGradeSection H) :
    SingularGradeSection K := by
  refine ⟨fun n => T n (x.1 n), ?_⟩
  rcases x.2 with ⟨C, hC, hx⟩
  exact ⟨C, hC, fun n => by
    calc
      ‖T n (x.1 n)‖ ≤ ‖T n‖ * ‖x.1 n‖ := (T n).le_opNorm _
      _ ≤ 1 * ‖x.1 n‖ :=
        mul_le_mul_of_nonneg_right (hT n) (norm_nonneg _)
      _ = ‖x.1 n‖ := one_mul _
      _ ≤ C := hx n⟩

/-- The representative-level map is pointwise contractive. -/
theorem norm_singularGradeSectionMapOfContractive_apply_le
    {H K : Type*}
    [NormedAddCommGroup H] [NormedSpace ℂ H]
    [NormedAddCommGroup K] [NormedSpace ℂ K]
    (T : ℕ → H →L[ℂ] K) (hT : ∀ n, ‖T n‖ ≤ 1)
    (x : SingularGradeSection H) (n : ℕ) :
    ‖(singularGradeSectionMapOfContractive T hT x).1 n‖ ≤
      ‖x.1 n‖ := by
  calc
    ‖T n (x.1 n)‖ ≤ ‖T n‖ * ‖x.1 n‖ := (T n).le_opNorm _
    _ ≤ 1 * ‖x.1 n‖ :=
      mul_le_mul_of_nonneg_right (hT n) (norm_nonneg _)
    _ = ‖x.1 n‖ := one_mul _

/-- Uniform contractions preserve little-oh singular-grade equivalence. -/
theorem singularGradeEquivalent_map_contractive
    {H K : Type*}
    [NormedAddCommGroup H] [NormedSpace ℂ H]
    [NormedAddCommGroup K] [NormedSpace ℂ K]
    (epsilon : ℕ → ℝ) (hepsilon : ∀ n, 0 < epsilon n)
    (T : ℕ → H →L[ℂ] K) (hT : ∀ n, ‖T n‖ ≤ 1)
    {x y : ℕ → H}
    (hxy : SingularGradeEquivalent epsilon x y) :
    SingularGradeEquivalent epsilon
      (fun n => T n (x n)) (fun n => T n (y n)) := by
  apply squeeze_zero'
    (Filter.Eventually.of_forall fun n =>
      div_nonneg (norm_nonneg _) (hepsilon n).le)
    (Filter.Eventually.of_forall fun n => ?_)
    hxy
  rw [← map_sub]
  apply div_le_div_of_nonneg_right _ (hepsilon n).le
  calc
    ‖T n (x n - y n)‖ ≤ ‖T n‖ * ‖x n - y n‖ := (T n).le_opNorm _
    _ ≤ 1 * ‖x n - y n‖ :=
      mul_le_mul_of_nonneg_right (hT n) (norm_nonneg _)
    _ = ‖x n - y n‖ := one_mul _

/-- Every uniformly contractive moving family descends canonically to the
bounded singular-grade corona. -/
def singularGradeCoronaMapOfContractive
    {H K : Type*}
    [NormedAddCommGroup H] [NormedSpace ℂ H]
    [NormedAddCommGroup K] [NormedSpace ℂ K]
    (epsilon : ℕ → ℝ) (hepsilon : ∀ n, 0 < epsilon n)
    (T : ℕ → H →L[ℂ] K) (hT : ∀ n, ‖T n‖ ≤ 1) :
    SingularGradeCorona H epsilon hepsilon →
      SingularGradeCorona K epsilon hepsilon :=
  Quotient.map
    (singularGradeSectionMapOfContractive T hT)
    (fun _ _ hxy =>
      singularGradeEquivalent_map_contractive
        epsilon hepsilon T hT hxy)

/-- The induced corona map is represented by the pointwise operator family. -/
theorem singularGradeCoronaMapOfContractive_mk
    {H K : Type*}
    [NormedAddCommGroup H] [NormedSpace ℂ H]
    [NormedAddCommGroup K] [NormedSpace ℂ K]
    (epsilon : ℕ → ℝ) (hepsilon : ∀ n, 0 < epsilon n)
    (T : ℕ → H →L[ℂ] K) (hT : ∀ n, ‖T n‖ ≤ 1)
    (x : SingularGradeSection H) :
    singularGradeCoronaMapOfContractive epsilon hepsilon T hT
        (Quotient.mk (singularGradeSectionSetoid H epsilon hepsilon) x) =
      Quotient.mk (singularGradeSectionSetoid K epsilon hepsilon)
        (singularGradeSectionMapOfContractive T hT x) :=
  rfl

/-- The inward Sonin corner therefore acts on every positive singular
Rees-corona grade. -/
def centralSoninInwardDilationCornerCoronaMap
    (epsilon : ℕ → ℝ) (hepsilon : ∀ n, 0 < epsilon n)
    (a r : ℝ) (hr : 1 < r) :
    SingularGradeCorona SoninL2 epsilon hepsilon →
      SingularGradeCorona SoninL2 epsilon hepsilon :=
  singularGradeCoronaMapOfContractive epsilon hepsilon
    (fun _ => centralSoninInwardDilationCorner a r hr)
    (fun _ => norm_centralSoninInwardDilationCorner_le_one a r hr)

end RHTower
