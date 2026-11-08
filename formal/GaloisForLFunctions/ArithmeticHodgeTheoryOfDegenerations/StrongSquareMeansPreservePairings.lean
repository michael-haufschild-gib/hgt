import GaloisForLFunctions.HTGeometry.IntegralCauchySchwarz
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Strong square means preserve pairings

Strong square-mean convergence preserves fixed square-integrable pairings.
The proof applies integral Cauchy–Schwarz to the difference.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology
namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

/-- Squared differences of measurable square-integrable real functions are integrable. -/
lemma integrable_sq_sub_of_integrable_sq {U F : ℝ → ℝ}
    (hUm : AEStronglyMeasurable U volume) (hFm : AEStronglyMeasurable F volume)
    (hU2 : Integrable (fun u => U u ^ 2)) (hF2 : Integrable (fun u => F u ^ 2)) :
    Integrable (fun u => (U u - F u) ^ 2) := by
  have hUF := HTGeometry.integrable_mul_of_sq_integrable hUm hFm hU2 hF2
  have hh := (hU2.add hF2).sub (hUF.const_mul 2)
  exact hh.congr (Eventually.of_forall fun u => by
    dsimp only [Pi.add_apply, Pi.sub_apply]
    ring)

/-- Strong square-mean convergence preserves pairings against every square-integrable test. -/
theorem tendsto_integral_mul_of_square_mean {U : ℕ → ℝ → ℝ} {F f : ℝ → ℝ}
    (hUm : ∀ n, AEStronglyMeasurable (U n) volume) (hFm : AEStronglyMeasurable F volume)
    (hfm : AEStronglyMeasurable f volume)
    (hU2 : ∀ n, Integrable (fun u => U n u ^ 2))
    (hF2 : Integrable (fun u => F u ^ 2)) (hf2 : Integrable (fun u => f u ^ 2))
    (hlim : Tendsto (fun n => ∫ u, (U n u - F u) ^ 2) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ u, U n u * f u) atTop (𝓝 (∫ u, F u * f u)) := by
  have hs : Tendsto (fun n => (∫ u, (U n u - F u) * f u) ^ 2) atTop (𝓝 0) := by
    have hb := hlim.mul_const (∫ u, f u ^ 2)
    rw [zero_mul] at hb
    exact squeeze_zero (fun n => sq_nonneg _)
      (fun n => HTGeometry.sq_integral_mul_le ((hUm n).sub hFm) hfm
        (integrable_sq_sub_of_integrable_sq (hUm n) hFm (hU2 n) hF2) hf2) hb
  have ha := Real.continuous_sqrt.continuousAt.tendsto.comp hs
  simp only [Function.comp_def, Real.sqrt_sq_eq_abs, Real.sqrt_zero] at ha
  rw [tendsto_iff_norm_sub_tendsto_zero]
  apply ha.congr
  intro n
  rw [Real.norm_eq_abs, ← integral_sub
    (HTGeometry.integrable_mul_of_sq_integrable (hUm n) hfm (hU2 n) hf2)
    (HTGeometry.integrable_mul_of_sq_integrable hFm hfm hF2 hf2)]
  congr 1
  apply integral_congr_ae
  exact Eventually.of_forall fun u => by ring

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
