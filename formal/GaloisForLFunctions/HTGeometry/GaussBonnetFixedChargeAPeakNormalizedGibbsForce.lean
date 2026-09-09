import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAPeakInverseJacobian

/-!
# Actual Gibbs force in moving-peak coordinates

The rational radius derivative is valid at both phase endpoints. The
chain rule gives an exact derivative of the actual normalized Gibbs
energy, expressed using the physical force kernel and the inverse
coordinate Jacobian.
-/
noncomputable section
open Real Filter Set
open scoped Topology
namespace GaloisForLFunctions.HTGeometry

def egbFixedChargeAPeakNormalizedGibbs (w φ τ l₁ l₂ ψ : ℝ) : ℝ :=
  egbFixedChargeAPeakAlignedGibbsGap w φ τ l₁ ψ / egbFixedChargeAGibbsBarrier w φ τ l₂

def egbFixedChargeAPeakNormalizedGibbsForce (w φ τ l ψ : ℝ) : ℝ :=
  egbFixedChargeAGibbsKernel w φ τ (egbFixedChargeAPeakInverseCoordinate τ φ ψ) *
    egbFixedChargeAPeakInverseJacobian τ φ ψ * cos ψ / egbFixedChargeAGibbsBarrierScale w φ τ l

theorem egbFixedChargeAPeakAlignedRadius_rational_formula (w φ τ ψ : ℝ) :
    egbFixedChargeAPeakAlignedRadius w φ τ ψ =
      egbFixedChargeAMeanRadius w φ τ * (1 + egbCoexistenceASymmetricRatio τ * egbFixedChargeAPeakInverseCoordinate τ φ ψ) := by
  unfold egbFixedChargeAPeakAlignedRadius egbFixedChargeAInteriorRadius
  rw [egbFixedChargeAPeakInverseAngle_sin]

theorem egbFixedChargeAPeakAlignedRadius_hasDerivAt (w φ τ ψ : ℝ) :
    HasDerivAt (egbFixedChargeAPeakAlignedRadius w φ τ)
      (egbFixedChargeAMeanRadius w φ τ * egbCoexistenceASymmetricRatio τ * egbFixedChargeAPeakInverseJacobian τ φ ψ * cos ψ) ψ := by
  have hf : egbFixedChargeAPeakAlignedRadius w φ τ = fun x =>
      egbFixedChargeAMeanRadius w φ τ * (1 + egbCoexistenceASymmetricRatio τ * egbFixedChargeAPeakInverseCoordinate τ φ x) := by
    funext x
    exact egbFixedChargeAPeakAlignedRadius_rational_formula w φ τ x
  rw [hf]
  have h := (((egbFixedChargeAPeakInverseCoordinate_hasDerivAt τ φ ψ).const_mul (egbCoexistenceASymmetricRatio τ)).const_add 1).const_mul
    (egbFixedChargeAMeanRadius w φ τ)
  apply h.congr_deriv
  ring

theorem egbFixedChargeAPeakNormalizedGibbs_hasDerivAt (w φ τ l₁ l₂ ψ : ℝ) :
    HasDerivAt (egbFixedChargeAPeakNormalizedGibbs w φ τ l₁ l₂)
      (egbFixedChargeAPeakNormalizedGibbsForce w φ τ l₂ ψ) ψ := by
  have hg := egbFixedChargeAInteriorGibbs_hasDerivAt w φ τ l₁ (egbFixedChargeAPeakInverseAngle τ φ ψ)
  rw [egbFixedChargeAPeakInverseAngle_sin] at hg
  have h := ((hg.comp ψ (egbFixedChargeAPeakAlignedRadius_hasDerivAt w φ τ ψ)).sub_const
    (egbOffShellGibbsA (egbFixedChargeAPressure w φ τ) (egbFixedChargeATemperature w φ τ)
      (exp w * cos φ) (exp w * sin φ) l₁ (egbFixedChargeALargeRadius w φ τ))).div_const
    (egbFixedChargeAGibbsBarrier w φ τ l₂)
  change HasDerivAt (fun x => (egbOffShellGibbsA (egbFixedChargeAPressure w φ τ) (egbFixedChargeATemperature w φ τ)
    (exp w * cos φ) (exp w * sin φ) l₁ (egbFixedChargeAPeakAlignedRadius w φ τ x) -
      egbOffShellGibbsA (egbFixedChargeAPressure w φ τ) (egbFixedChargeATemperature w φ τ)
        (exp w * cos φ) (exp w * sin φ) l₁ (egbFixedChargeALargeRadius w φ τ)) /
      egbFixedChargeAGibbsBarrier w φ τ l₂) _ ψ
  apply h.congr_deriv
  have hm := egbFixedChargeAMeanRadius_pos w φ τ
  have hd := (egbCoexistenceASymmetricRatio_bounds τ).1
  have hb := egbFixedChargeAGibbsBarrier_pos w φ τ l₂
  unfold egbFixedChargeAPeakNormalizedGibbsForce egbFixedChargeAGibbsBarrierScale
  field_simp <;> ring

theorem egbFixedChargeAPeakNormalizedGibbs_derivative (w φ τ l₁ l₂ ψ : ℝ) :
    deriv (egbFixedChargeAPeakNormalizedGibbs w φ τ l₁ l₂) ψ = egbFixedChargeAPeakNormalizedGibbsForce w φ τ l₂ ψ :=
  (egbFixedChargeAPeakNormalizedGibbs_hasDerivAt w φ τ l₁ l₂ ψ).deriv

end GaloisForLFunctions.HTGeometry
