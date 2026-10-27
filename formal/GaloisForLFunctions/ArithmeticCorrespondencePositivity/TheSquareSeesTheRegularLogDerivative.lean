import GaloisForLFunctions.RHTower.HigherPoleResidueMode
import GaloisForLFunctions.HTGeometry.MeromorphicLaurentTranslation

/-!
# The simple Laurent coefficient of a squared logarithmic derivative

At a zero of multiplicity `m`, the simple coefficient of the squared
logarithmic derivative is twice `m` times its regular part.
-/

open Filter
open scoped Topology

noncomputable section

namespace GaloisForLFunctions.ArithmeticCorrespondencePositivity

/-- Squaring a simple pole with analytic regular part produces simple
Laurent coefficient `2 * m * R ρ`. -/
theorem laurentCoeff_square_of_pole_and_regular {F R : ℂ → ℂ} {ρ m : ℂ}
    (hF : MeromorphicAt F ρ) (hR : AnalyticAt ℂ R ρ)
    (hEq : F =ᶠ[𝓝[≠] ρ] fun z => m / (z - ρ) + R z) :
    GaloisForLFunctions.HTGeometry.laurentCoeff (fun z => F z ^ 2) ρ (-1) =
      2 * m * R ρ := by
  let A : ℂ → ℂ := fun z => (m + (z - ρ) * R z) ^ 2
  have hA : AnalyticAt ℂ A ρ := by
    dsimp only [A]
    fun_prop
  have hF2 : MeromorphicAt (fun z => F z ^ 2) ρ := by
    change MeromorphicAt (F ^ 2) ρ
    exact hF.pow 2
  have hmodel : (fun z => F z ^ 2) =ᶠ[𝓝[≠] ρ]
      fun z => ((z - ρ) ^ 2)⁻¹ * A z := by
    filter_upwards [hEq, self_mem_nhdsWithin] with z hz hne
    change z ≠ ρ at hne
    have hz0 : z - ρ ≠ 0 := sub_ne_zero.mpr hne
    rw [hz]
    dsimp only [A]
    field_simp [hz0]
  calc
    GaloisForLFunctions.HTGeometry.laurentCoeff (fun z => F z ^ 2) ρ (-1) =
        GaloisForLFunctions.HTGeometry.laurentCoeff
          (fun z => ((z - ρ) ^ 2)⁻¹ * A z) ρ (-1) :=
      GaloisForLFunctions.HTGeometry.laurentCoeff_congr hF2 hmodel (-1)
    _ = GaloisForLFunctions.HTGeometry.taylorCoeffZero (fun t => A (ρ + t)) 1 := by
      simpa using RHTower.laurentCoeff_inv_pow_mul_analytic hA (m := 2) (by norm_num)
    _ = 2 * m * R ρ := by
      have heq : (fun t : ℂ => A (ρ + t)) =
          (fun t : ℂ => (m + t * R (ρ + t)) ^ 2) := by
        funext t
        dsimp only [A]
        congr 1
        ring
      rw [heq]
      have hshift : AnalyticAt ℂ (fun t : ℂ => R (ρ + t)) 0 := by
        have hlin : AnalyticAt ℂ (fun t : ℂ => ρ + t) 0 := by fun_prop
        simpa only [Function.comp_def] using hR.comp_of_eq hlin (by simp)
      have ht : HasDerivAt (fun t : ℂ => t * R (ρ + t)) (R ρ) 0 := by
        simpa [Pi.mul_def] using!
          (hasDerivAt_id (0 : ℂ)).mul hshift.differentiableAt.hasDerivAt
      have hs : HasDerivAt (fun t : ℂ => m + t * R (ρ + t)) (R ρ) 0 :=
        ht.const_add m
      have hd : HasDerivAt (fun t : ℂ => (m + t * R (ρ + t)) ^ 2)
          (2 * m * R ρ) 0 := by
        simpa [Pi.pow_def] using! hs.pow 2
      simpa [GaloisForLFunctions.HTGeometry.taylorCoeffZero, iteratedDeriv_one] using hd.deriv

end GaloisForLFunctions.ArithmeticCorrespondencePositivity
