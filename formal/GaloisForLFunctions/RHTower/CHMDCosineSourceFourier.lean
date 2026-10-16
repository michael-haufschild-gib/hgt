import GaloisForLFunctions.RHTower.CHMDGraphCosineReadout
import GaloisForLFunctions.RHTower.ThetaCardinalOrbitReadout

/-! # The literal graph readout and both Fourier conventions -/

open MeasureTheory Set Filter Topology Complex Zeta23
open scoped ComplexConjugate
noncomputable section
namespace RHTower

theorem ExpMomentSource.ofReal_re {u : ℝ → ℂ} (hu : ExpMomentSource u) :
    ExpMomentSource (fun x => ((u x).re : ℂ)) := by
  refine ⟨Complex.continuous_ofReal.comp (Complex.continuous_re.comp hu.continuous), fun c => ?_⟩
  apply (hu.moment c).mono'
    (((Real.continuous_exp.comp (continuous_const.mul continuous_abs)).mul
      (Complex.continuous_ofReal.comp (Complex.continuous_re.comp hu.continuous)).norm).aestronglyMeasurable)
  exact Eventually.of_forall fun x => by
    change ‖Real.exp (c * |x|) * ‖((u x).re : ℂ)‖‖ ≤ _
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), abs_norm,
      Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) (Real.exp_pos _).le

theorem ExpMomentSource.integrable_paperFT_source {u : ℝ → ℂ} (hu : ExpMomentSource u) (z : ℂ) :
    Integrable (fun x => u x * Complex.exp (I*z*x)) := by
  have h := hu.integrable_cexp (-z)
  convert h using 1
  funext x
  rw [show -I * (-z) * (x : ℂ) = I*z*x by ring]
  exact mul_comm _ _

theorem paperFT_add_sources {u v : ℝ → ℂ} (hu : ExpMomentSource u) (hv : ExpMomentSource v) (z : ℂ) :
    paperFT (fun x => u x + v x) z = paperFT u z + paperFT v z := by
  simpa only [one_mul] using paperFT_smul_add_smul 1 1 z
    (hu.integrable_paperFT_source z) (hv.integrable_paperFT_source z)

theorem cosine_integral_eq_half_paperFT {u : ℝ → ℂ} (hu : ExpMomentSource u) (z : ℂ) :
    (∫ x, u x * Complex.cos (z*x)) = (paperFT u z + paperFT u (-z))/2 := by
  rw [paperFT, paperFT, ← integral_add (hu.integrable_paperFT_source z)
    (hu.integrable_paperFT_source (-z)), ← integral_div]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [Complex.cos, show (z*(x : ℂ))*I = I*z*x by ring,
    show -(z*(x : ℂ))*I = I*(-z)*x by ring]
  ring

namespace CHMDDoobGraph

theorem graphCosineReadout_of_source_eq_half {p : SourceGraph} {f : ℝ → ℝ}
    (hf : ExpMomentSource (fun x => (f x : ℂ)))
    (hp : p.val.fst =ᵐ[massMeasure] phiDoobInv f) (z : ℂ) :
    graphCosineReadout p z =
      (paperFT (fun x => (f x : ℂ)) z + paperFT (fun x => (f x : ℂ)) (-z))/2 := by
  rw [graphCosineReadout_of_source hp, cosine_integral_eq_half_paperFT hf]

theorem graphCosineReadout_of_even_source {p : SourceGraph} {f : ℝ → ℝ}
    (hf : ExpMomentSource (fun x => (f x : ℂ))) (he : ∀ x, f (-x) = f x)
    (hp : p.val.fst =ᵐ[massMeasure] phiDoobInv f) (z : ℂ) :
    graphCosineReadout p z = paperFT (fun x => (f x : ℂ)) z := by
  rw [graphCosineReadout_of_source_eq_half hf hp, paperFT_ofReal_neg_of_even he]
  ring

end CHMDDoobGraph
end RHTower
