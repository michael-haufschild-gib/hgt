/-
# Chen--Gupta--Li Class-I dyadic tail prefixes

The finite CGL tail witness can be selected at a power-of-two endpoint. This
is the exact entry point for decomposing it into source dyadic blocks.
-/
import GaloisForLFunctions.RHTower.ChenGuptaLiClassIMellinAlternative
import GaloisForLFunctions.RHTower.ChenGuptaLiClassITailPrefixes

open Complex Filter Topology MeasureTheory
open GaloisForLFunctions.HTGeometry

noncomputable section
namespace RHTower

/-- The CGL shifted-tail prefix ending at the canonical power-of-two endpoint. -/
def cglShiftedDetectorTailDyadicPrefix
    (X q : ℕ) (χ : DirichletCharacter ℂ (q + 1))
    (s : CGLRightHalfPlanePoint) (x : CGLPositiveSmoothingScale) (L : ℕ) : ℂ :=
  cglShiftedDetectorTailPartialProfile X q χ s x (2 ^ L + 1)

/-- Power-of-two CGL tail prefixes retain the exact infinite-tail limit. -/
theorem cglShiftedDetectorTailDyadicPrefix_tendsto
    (X q : ℕ) (χ : DirichletCharacter ℂ (q + 1))
    (s : CGLRightHalfPlanePoint) (x : CGLPositiveSmoothingScale) :
    Tendsto (cglShiftedDetectorTailDyadicPrefix X q χ s x) atTop
      (𝓝 (coeffLaplaceProfile (cglShiftedDetectorTailCoefficient X q χ s) x.1)) := by
  apply (cglShiftedDetectorTailPartialProfile_tendsto X q χ s x).comp
  exact (tendsto_add_atTop_nat 1).comp
    (tendsto_pow_atTop_atTop_of_one_lt (r := 2) (by norm_num))

/-- **Chen--Gupta--Li, Section 12.1: dyadic-prefix alternative.**
Every certified primitive Class-I zero forces either one canonical
power-of-two CGL tail prefix to be large, or the normalized critical-line
Mellin integral to be large. -/
theorem cglPrimitiveClassI_dyadicPrefix_or_safeLineIntegral_large
    (X n Y : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal)
    (z : CGLPrimitiveClassIWindowZero n χ τ H) :
    (∃ L : ℕ,
      Real.exp (-(((Y + 1 : ℕ) : ℝ)⁻¹)) / 4 ≤
        ‖cglShiftedDetectorTailDyadicPrefix X n χ.1.1
          (cglPrimitiveClassIWindowZeroRightHalfPlanePoint n χ τ H z)
          ⟨((Y + 1 : ℕ) : ℝ)⁻¹, by positivity⟩ L‖) ∨
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
    obtain ⟨L, hL⟩ := Metric.tendsto_atTop.1
      (cglShiftedDetectorTailDyadicPrefix_tendsto X n χ.1.1 s x)
      (Real.exp (-(((Y + 1 : ℕ) : ℝ)⁻¹)) / 4) hxpos
    refine ⟨L, ?_⟩
    change Real.exp (-(((Y + 1 : ℕ) : ℝ)⁻¹)) / 4 ≤
      ‖cglShiftedDetectorTailDyadicPrefix X n χ.1.1 s x L‖
    have hnear : dist (cglShiftedDetectorTailDyadicPrefix X n χ.1.1 s x L)
        (coeffLaplaceProfile (cglShiftedDetectorTailCoefficient X n χ.1.1 s) x.1) <
        Real.exp (-(((Y + 1 : ℕ) : ℝ)⁻¹)) / 4 := hL L le_rfl
    have hnear' : ‖coeffLaplaceProfile (cglShiftedDetectorTailCoefficient X n χ.1.1 s) x.1 -
        cglShiftedDetectorTailDyadicPrefix X n χ.1.1 s x L‖ <
        Real.exp (-(((Y + 1 : ℕ) : ℝ)⁻¹)) / 4 := by
      simpa [dist_eq_norm_sub, norm_sub_rev] using hnear
    have hnorm : ‖coeffLaplaceProfile (cglShiftedDetectorTailCoefficient X n χ.1.1 s) x.1‖ ≤
        ‖cglShiftedDetectorTailDyadicPrefix X n χ.1.1 s x L‖ +
          ‖coeffLaplaceProfile (cglShiftedDetectorTailCoefficient X n χ.1.1 s) x.1 -
            cglShiftedDetectorTailDyadicPrefix X n χ.1.1 s x L‖ := by
      calc
        ‖coeffLaplaceProfile (cglShiftedDetectorTailCoefficient X n χ.1.1 s) x.1‖ =
            ‖cglShiftedDetectorTailDyadicPrefix X n χ.1.1 s x L +
              (coeffLaplaceProfile (cglShiftedDetectorTailCoefficient X n χ.1.1 s) x.1 -
                cglShiftedDetectorTailDyadicPrefix X n χ.1.1 s x L)‖ := by
          congr 1
          ring
        _ ≤ _ := norm_add_le _ _
    change Real.exp (-(((Y + 1 : ℕ) : ℝ)⁻¹)) / 2 ≤
      ‖coeffLaplaceProfile (cglShiftedDetectorTailCoefficient X n χ.1.1 s) x.1‖ at htail
    linarith
  · exact Or.inr hsafe

end RHTower
