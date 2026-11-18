import GaloisForLFunctions.ExclusionOfTheCriticalState.TheZeroCauchyTransformIsSquareIntegrableUpToALogarithm
import GaloisForLFunctions.HTGeometry.FourierDecayFromDerivative
import GaloisForLFunctions.HTGeometry.GagliardoFourierConstant
import GaloisForLFunctions.RHTower.FourierPlancherelIntegral

/-!
# Square integrability of the derivative of a logarithmic primitive

Plancherel bounds the square integral of each difference quotient with the
same multiplier. Fatou passes the bound to the classical derivative.
-/

noncomputable section
open MeasureTheory Set Filter Topology
open scoped FourierTransform
namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open HTGeometry

/-- The squared translation symbol is bounded by the squared angular frequency
times the squared lag. -/
theorem square_differenceSymbol_le (h ξ : ℝ) :
    ‖differenceSymbol h ξ‖^2 ≤ h^2*(2*Real.pi*ξ)^2 := by
  rw [normSq_differenceSymbol]
  calc 4*Real.sin (Real.pi*(h*ξ))^2 ≤ 4*(Real.pi*(h*ξ))^2 :=
         mul_le_mul_of_nonneg_left Real.sin_sq_le_sq (by norm_num)
    _ = _ := by ring

/-- If the Fourier integral of a real differentiable primitive has finite
second frequency moment, its classical derivative lies in L². -/
theorem integrable_square_derivative_of_fourier_moment {B b : ℝ → ℝ}
    (hd : ∀ t, HasDerivAt B (b t) t)
    (hi : Integrable fun t : ℝ => (B t:ℂ)) (h2 : MemLp (fun t : ℝ => (B t:ℂ)) 2)
    (hM : Integrable fun ξ : ℝ => (2*Real.pi*ξ)^2*‖𝓕 (fun t : ℝ => (B t:ℂ)) ξ‖^2) :
    Integrable fun t : ℝ => (b t)^2 := by
  let f := fun t : ℝ => (B t:ℂ)
  let M := fun ξ : ℝ => (2*Real.pi*ξ)^2*‖𝓕 f ξ‖^2
  let d := fun n : ℕ => 1/((n:ℝ)+1)
  let q := fun n : ℕ => fun t : ℝ => (d n)⁻¹*(B (t+d n)-B t)
  have hdpos (n : ℕ) : 0 < d n := by dsimp only [d]; positivity
  have hc : Continuous B := continuous_iff_continuousAt.2 fun t => (hd t).continuousAt
  have hqc (n : ℕ) : Continuous (q n) := by dsimp only [q]; fun_prop
  have htime : Tendsto d atTop (𝓝[≠] 0) := tendsto_nhdsWithin_iff.2
    ⟨tendsto_one_div_add_atTop_nhds_zero_nat,Eventually.of_forall fun n => (hdpos n).ne'⟩
  have hq (n : ℕ) : Integrable (fun t => q n t^2) ∧ (∫ t, q n t^2) ≤ ∫ ξ, M ξ := by
    let g := fun t : ℝ => f t-f (t+d n)
    have hiG : Integrable g := hi.sub (hi.comp_add_right _)
    have h2G : MemLp g 2 := h2.sub (h2.comp_measurePreserving (measurePreserving_add_right volume (d n)))
    have hG := (memLp_two_iff_integrable_sq_norm hiG.aestronglyMeasurable).1 h2G
    have he (t : ℝ) : q n t^2 = ((d n)^2)⁻¹*‖g t‖^2 := by
      dsimp only [q,g,f]; rw [← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,sq_abs]
      ring
    simp_rw [he]
    refine ⟨hG.const_mul _,?_⟩
    rw [integral_const_mul,← _root_.RHTower.integral_norm_sq_fourier_eq hiG h2G]
    have hle : (∫ ξ, ‖𝓕 g ξ‖^2) ≤ (d n)^2*(∫ ξ, M ξ) := by
      rw [← integral_const_mul]
      apply integral_mono (_root_.RHTower.integrable_norm_sq_fourier hiG h2G) (hM.const_mul _)
      intro ξ
      have hg : 𝓕 g ξ = differenceSymbol (d n) ξ*𝓕 f ξ := fourier_sub_translate f hi _ ξ
      rw [hg,norm_mul,mul_pow]
      exact (mul_le_mul_of_nonneg_right (square_differenceSymbol_le (d n) ξ) (sq_nonneg _)).trans_eq (mul_assoc ..)
    calc ((d n)^2)⁻¹*_ ≤ ((d n)^2)⁻¹*((d n)^2*(∫ ξ, M ξ)) :=
           mul_le_mul_of_nonneg_left hle (inv_nonneg.2 (sq_nonneg _))
      _ = _ := inv_mul_cancel_left₀ (pow_ne_zero _ (hdpos n).ne') _
  refine (integrable_and_integral_le_of_tendsto (fun n => ((hqc n).pow 2).measurable)
    (fun n t => sq_nonneg (q n t)) (fun n => (hq n).1) (fun n => (hq n).2) ?_).1
  intro t
  exact (((hasDerivAt_iff_tendsto_slope_zero.1 (hd t)).comp htime).pow 2)

#print axioms integrable_square_derivative_of_fourier_moment
end GaloisForLFunctions.ExclusionOfTheCriticalState
