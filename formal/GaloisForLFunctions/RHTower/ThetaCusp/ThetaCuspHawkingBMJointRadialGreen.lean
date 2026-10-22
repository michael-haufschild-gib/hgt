import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMJointRadialCore

/-! Exact radial Green identity on the physical half-line, including vanishing endpoint term. -/
open MeasureTheory Set Filter Topology
open scoped ContDiff ComplexConjugate
namespace RHTower.D4BMJointWave
noncomputable section

theorem radialValue_ae (f : RadialCore) : radialValue f =ᵐ[radialMeasure] f.field :=
  (f.smooth.continuous.memLp_of_hasCompactSupport f.compact).coeFn_toLp

theorem radialDerivative_ae (f : RadialCore) :
    radialDerivative f =ᵐ[radialMeasure] deriv f.field :=
  ((f.smooth.continuous_deriv (by simp)).memLp_of_hasCompactSupport f.compact.deriv).coeFn_toLp

/-- Actual radial differentiation is skew symmetric on compact interior tests; the AdS endpoint
term is zero because the supports lie strictly inside the physical half-line. -/
theorem radialDerivative_green (f g : RadialCore) :
    inner ℂ (radialValue f) (radialDerivative g) +
      inner ℂ (radialDerivative f) (radialValue g) = 0 := by
  let p : ℝ → ℂ := fun t => conj (f.field t) * g.field t
  have hp : ContDiff ℝ ∞ p := (Complex.conjCLE.toContinuousLinearEquiv.contDiff.comp f.smooth).mul g.smooth
  have hpk : HasCompactSupport p := g.compact.mul_left
  have h0 : p 0 = 0 := by
    have hf0 : f.field 0 = 0 := image_eq_zero_of_notMem_tsupport
      (fun h => (lt_irrefl (0:ℝ)) (f.support h))
    simp [p,hf0]
  have hd (t : ℝ) : deriv p t =
      conj (f.field t) * deriv g.field t + conj (deriv f.field t) * g.field t := by
    have h := ((f.smooth.differentiable (by simp) t).hasDerivAt.star.mul
      (g.smooth.differentiable (by simp) t).hasDerivAt).deriv
    change deriv p t = conj (deriv f.field t) * g.field t + conj (f.field t) * deriv g.field t at h
    exact h.trans (add_comm _ _)
  have hi := HasCompactSupport.integral_Iic_deriv_eq (hp.of_le (by simp)) hpk 0
  rw [integral_Iic_eq_integral_Iio,h0] at hi
  have hA : Integrable (fun t => conj (f.field t) * deriv g.field t) radialMeasure :=
    ((f.smooth.continuous.star).mul (g.smooth.continuous_deriv (by simp))).integrable_of_hasCompactSupport
      g.compact.deriv.mul_left
  have hB : Integrable (fun t => conj (deriv f.field t) * g.field t) radialMeasure :=
    ((f.smooth.continuous_deriv (by simp)).star.mul g.smooth.continuous).integrable_of_hasCompactSupport
      g.compact.mul_left
  have hsplit : (∫ t, deriv p t ∂radialMeasure) =
      (∫ t, conj (f.field t) * deriv g.field t ∂radialMeasure) +
      (∫ t, conj (deriv f.field t) * g.field t ∂radialMeasure) := by
    simp_rw [hd]
    exact integral_add hA hB
  rw [hsplit] at hi
  rw [L2.inner_def,L2.inner_def]
  convert hi using 1
  congr 1
  · apply integral_congr_ae
    filter_upwards [radialValue_ae f,radialDerivative_ae g] with t hf hg
    rw [hf,hg,RCLike.inner_apply,mul_comm]
  · apply integral_congr_ae
    filter_upwards [radialDerivative_ae f,radialValue_ae g] with t hf hg
    rw [hf,hg,RCLike.inner_apply,mul_comm]

end
end RHTower.D4BMJointWave
