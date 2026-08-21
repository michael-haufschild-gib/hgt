/-
# Chen--Gupta--Li Class-I finite tail witness

The exact Section 12.1 tail-versus-integral alternative has a finite-prefix
form. This eliminates the infinite-series obstacle before the later dyadic
subdivision required by the CGL large-value argument.
-/
import GaloisForLFunctions.RHTower.ChenGuptaLiClassIMellinAlternative
import GaloisForLFunctions.RHTower.ChenGuptaLiClassITailPrefixes

open Complex Filter Topology MeasureTheory
open GaloisForLFunctions.HTGeometry

noncomputable section
namespace RHTower

/-- **Chen--Gupta--Li, Section 12.1: finite Class-I tail witness.**
Every certified primitive Class-I zero forces either one literal finite prefix
of the exponentially smoothed shifted detector tail to be large, or the
normalized critical-line Mellin integral to be large. -/
theorem cglPrimitiveClassI_partialTail_or_safeLineIntegral_large
    (X n Y : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal)
    (z : CGLPrimitiveClassIWindowZero n χ τ H) :
    (∃ K : ℕ,
      Real.exp (-(((Y + 1 : ℕ) : ℝ)⁻¹)) / 4 ≤
        ‖cglShiftedDetectorTailPartialProfile X n χ.1.1
          (cglPrimitiveClassIWindowZeroRightHalfPlanePoint n χ τ H z)
          ⟨((Y + 1 : ℕ) : ℝ)⁻¹, by positivity⟩ K‖) ∨
      Real.exp (-(((Y + 1 : ℕ) : ℝ)⁻¹)) / 2 ≤
        ‖(1 / (2 * Real.pi) : ℝ) • (∫ t : ℝ,
          cglSmoothedNonprincipalDetectorMellinIntegrand X n Y
            (cglPrimitiveNonprincipalCriticalStripLZeroOfClassIWindowZero n χ τ H z).toCGLNonprincipalCriticalStripLZero
            ((2 : ℂ) + (t : ℂ) * I))‖ := by
  let s : CGLRightHalfPlanePoint :=
    cglPrimitiveClassIWindowZeroRightHalfPlanePoint n χ τ H z
  let x : CGLPositiveSmoothingScale := ⟨((Y + 1 : ℕ) : ℝ)⁻¹, by positivity⟩
  have halt := cglPrimitiveClassI_tail_or_safeLineIntegral_large X n Y χ τ H z
  rcases halt with htail | hsafe
  · left
    have hxpos : 0 < Real.exp (-(((Y + 1 : ℕ) : ℝ)⁻¹)) / 4 := by positivity
    obtain ⟨K, hK⟩ := Metric.tendsto_atTop.1
      (cglShiftedDetectorTailPartialProfile_tendsto X n χ.1.1 s x)
      (Real.exp (-(((Y + 1 : ℕ) : ℝ)⁻¹)) / 4) hxpos
    refine ⟨K, ?_⟩
    change Real.exp (-(((Y + 1 : ℕ) : ℝ)⁻¹)) / 4 ≤
      ‖cglShiftedDetectorTailPartialProfile X n χ.1.1 s x K‖
    have hnear : dist (cglShiftedDetectorTailPartialProfile X n χ.1.1 s x K)
        (coeffLaplaceProfile (cglShiftedDetectorTailCoefficient X n χ.1.1 s) x.1) <
        Real.exp (-(((Y + 1 : ℕ) : ℝ)⁻¹)) / 4 := hK K le_rfl
    have hnear' : ‖coeffLaplaceProfile (cglShiftedDetectorTailCoefficient X n χ.1.1 s) x.1 -
        cglShiftedDetectorTailPartialProfile X n χ.1.1 s x K‖ <
        Real.exp (-(((Y + 1 : ℕ) : ℝ)⁻¹)) / 4 := by
      simpa [dist_eq_norm_sub, norm_sub_rev] using hnear
    have hnorm : ‖coeffLaplaceProfile (cglShiftedDetectorTailCoefficient X n χ.1.1 s) x.1‖ ≤
        ‖cglShiftedDetectorTailPartialProfile X n χ.1.1 s x K‖ +
          ‖coeffLaplaceProfile (cglShiftedDetectorTailCoefficient X n χ.1.1 s) x.1 -
            cglShiftedDetectorTailPartialProfile X n χ.1.1 s x K‖ := by
      calc
        ‖coeffLaplaceProfile (cglShiftedDetectorTailCoefficient X n χ.1.1 s) x.1‖ =
            ‖cglShiftedDetectorTailPartialProfile X n χ.1.1 s x K +
              (coeffLaplaceProfile (cglShiftedDetectorTailCoefficient X n χ.1.1 s) x.1 -
                cglShiftedDetectorTailPartialProfile X n χ.1.1 s x K)‖ := by
          congr 1
          ring
        _ ≤ _ := norm_add_le _ _
    change Real.exp (-(((Y + 1 : ℕ) : ℝ)⁻¹)) / 2 ≤
      ‖coeffLaplaceProfile (cglShiftedDetectorTailCoefficient X n χ.1.1 s) x.1‖ at htail
    linarith
  · exact Or.inr hsafe

end RHTower
