/-
# Chen--Gupta--Li Class-I tail prefixes

Finite-prefix approximation for CGL's actual exponentially smoothed shifted
detector tail. This is the bridge from the infinite Section 12.1 tail to a
finite source object; dyadic extraction is a later, separate step.
-/
import GaloisForLFunctions.RHTower.ChenGuptaLiClassIMellinTail

open Complex Filter Topology MeasureTheory
open GaloisForLFunctions.HTGeometry

noncomputable section
namespace RHTower

/-- The literal finite prefix of the exponentially smoothed shifted CGL tail. -/
def cglShiftedDetectorTailPartialProfile
    (X q : ℕ) (χ : DirichletCharacter ℂ (q + 1))
    (s : CGLRightHalfPlanePoint) (x : CGLPositiveSmoothingScale) (K : ℕ) : ℂ :=
  ∑ m ∈ Finset.range K, cglShiftedDetectorTailCoefficient X q χ s m *
    Complex.exp (-((m : ℝ) * x.1 : ℝ))

/-- Finite CGL tail prefixes converge to the literal exponentially smoothed
shifted detector tail. -/
theorem cglShiftedDetectorTailPartialProfile_tendsto
    (X q : ℕ) (χ : DirichletCharacter ℂ (q + 1))
    (s : CGLRightHalfPlanePoint) (x : CGLPositiveSmoothingScale) :
    Tendsto (cglShiftedDetectorTailPartialProfile X q χ s x) atTop
      (𝓝 (coeffLaplaceProfile (cglShiftedDetectorTailCoefficient X q χ s) x.1)) := by
  change Tendsto (fun K : ℕ => ∑ m ∈ Finset.range K,
      cglShiftedDetectorTailCoefficient X q χ s m *
        Complex.exp (-((m : ℝ) * x.1 : ℝ))) atTop
      (𝓝 (∑' m : ℕ, cglShiftedDetectorTailCoefficient X q χ s m *
        Complex.exp (-((m : ℝ) * x.1 : ℝ))))
  exact (summable_cglShiftedDetectorTailCoefficient_laplace X q χ s x).hasSum.tendsto_sum_nat

/-- The norms of finite CGL tail prefixes converge to the norm of the literal
infinite exponentially smoothed tail. -/
theorem tendsto_norm_cglShiftedDetectorTailPartialProfile
    (X q : ℕ) (χ : DirichletCharacter ℂ (q + 1))
    (s : CGLRightHalfPlanePoint) (x : CGLPositiveSmoothingScale) :
    Tendsto (fun K : ℕ => ‖cglShiftedDetectorTailPartialProfile X q χ s x K‖) atTop
      (𝓝 ‖coeffLaplaceProfile (cglShiftedDetectorTailCoefficient X q χ s) x.1‖) := by
  exact (cglShiftedDetectorTailPartialProfile_tendsto X q χ s x).norm

end RHTower
