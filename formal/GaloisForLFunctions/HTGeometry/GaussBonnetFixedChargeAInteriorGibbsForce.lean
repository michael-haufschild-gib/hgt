import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAGibbsKernel

/-!
# The actual cubic Gibbs force at interior radii

The rescaled rational kernel is identified with the derivative of the
physical Gibbs function. Its cubic critical limit is therefore a force
law for the actual family, not only an auxiliary polynomial limit.
-/
noncomputable section
open Real Filter Set
open scoped Topology
namespace GaloisForLFunctions.HTGeometry

theorem egbFixedChargeAInteriorScale_pos (τ ψ : ℝ) : 0 < 1 + egbCoexistenceASymmetricRatio τ * sin ψ := by
  have hs := (egbFixedChargeAInteriorScale_mapsTo τ ⟨neg_one_le_sin ψ, sin_le_one ψ⟩).1
  have hd := (egbCoexistenceASymmetricRatio_bounds τ).2
  linarith

theorem egbFixedChargeAInteriorGibbs_hasDerivAt (w φ τ l ψ : ℝ) :
    HasDerivAt (egbOffShellGibbsA (egbFixedChargeAPressure w φ τ) (egbFixedChargeATemperature w φ τ)
      (exp w * cos φ) (exp w * sin φ) l)
      (egbCoexistenceASymmetricRatio τ ^ (3 : ℕ) / egbFixedChargeAMeanRadius w φ τ * egbFixedChargeAGibbsKernel w φ τ (sin ψ))
      (egbFixedChargeAInteriorRadius w φ τ ψ) := by
  have hv := egbFixedChargeAInteriorScale_pos τ ψ
  have hd := (egbCoexistenceASymmetricRatio_bounds τ).1
  have hm := egbFixedChargeAMeanRadius_pos w φ τ
  have hD := egbFixedChargeAMeanDenominator_pos τ φ
  have hx : 0 < 1 + egbCoexistenceASymmetricRatio τ ^ (2 : ℕ) := by positivity
  have h := egbFixedChargeA_mean_gibbs_derivative w φ τ l (log (1 + egbCoexistenceASymmetricRatio τ * sin ψ))
  rw [exp_log hv] at h
  apply h.congr_deriv
  rw [egbFixedChargeAGibbsKernel_polynomial_formula]
  field_simp

theorem egbFixedChargeAInteriorGibbs_force_formula (w φ τ l ψ : ℝ) :
    deriv (egbOffShellGibbsA (egbFixedChargeAPressure w φ τ) (egbFixedChargeATemperature w φ τ)
      (exp w * cos φ) (exp w * sin φ) l) (egbFixedChargeAInteriorRadius w φ τ ψ) /
      egbCoexistenceASymmetricRatio τ ^ (3 : ℕ) = egbFixedChargeAGibbsKernel w φ τ (sin ψ) / egbFixedChargeAMeanRadius w φ τ := by
  have hd := (egbCoexistenceASymmetricRatio_bounds τ).1
  rw [(egbFixedChargeAInteriorGibbs_hasDerivAt w φ τ l ψ).deriv]
  field_simp

theorem egbFixedChargeAInteriorGibbs_cubic_force_limit (w φ l ψ : ℝ) :
    Tendsto (fun τ => deriv (egbOffShellGibbsA (egbFixedChargeAPressure w φ τ) (egbFixedChargeATemperature w φ τ)
      (exp w * cos φ) (exp w * sin φ) l) (egbFixedChargeAInteriorRadius w φ τ ψ) /
      egbCoexistenceASymmetricRatio τ ^ (3 : ℕ))
      atBot (𝓝 (4 * egbFixedChargeAGibbsBarrierCoefficient w φ / egbFixedChargeACriticalRadius w φ *
        (sin ψ ^ (2 : ℕ) - 1) * sin ψ)) := by
  simp only [egbFixedChargeAInteriorGibbs_force_formula]
  have h := (egbFixedChargeAGibbsKernel_critical_limit w φ (sin ψ)).div
    (egbFixedChargeAMeanRadius_critical_limit w φ) (egbFixedChargeACriticalRadius_pos w φ).ne'
  have he : (4 * egbFixedChargeAGibbsBarrierCoefficient w φ * (sin ψ ^ (2 : ℕ) - 1) * sin ψ) / egbFixedChargeACriticalRadius w φ =
      4 * egbFixedChargeAGibbsBarrierCoefficient w φ / egbFixedChargeACriticalRadius w φ * (sin ψ ^ (2 : ℕ) - 1) * sin ψ := by ring
  rwa [he] at h

end GaloisForLFunctions.HTGeometry
