import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAStates
import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeASmooth

/-!
# Actual Clapeyron differential relation for model A

Differentiate the two equal Gibbs energies along the path with both charge
and coupling fixed. The actual first law cancels the moving-radius terms.
This proves the differential relation without presupposing a nonzero
coexistence-temperature derivative.
-/
noncomputable section
open Real
namespace GaloisForLFunctions.HTGeometry
open CPV

theorem egbMass_pressure_split (P Q a r : ℝ) :
    egbMass P Q a r = egbMass 0 Q a r + P * egbThermodynamicVolume r := by
  unfold egbMass egbThermodynamicVolume
  ring

theorem egbMass_explicit_derivative (P Q a x : ℝ) :
    HasDerivAt (egbMass P Q a)
      (1 / 2 - (Q ^ (2 : ℕ) + a ^ (2 : ℕ)) / (2 * exp x ^ (2 : ℕ)) + 4 * Real.pi * P * exp x ^ (2 : ℕ)) (exp x) := by
  apply (egbMass_derivative P Q a x).congr_deriv
  unfold egbTemperatureB
  field_simp
  ring

def egbFixedChargeAEntropyJump (w φ τ : ℝ) : ℝ :=
  egbEntropyA (exp w * sin φ) 0 (egbFixedChargeALargeRadius w φ τ) -
    egbEntropyA (exp w * sin φ) 0 (egbFixedChargeASmallRadius w φ τ)

def egbFixedChargeAVolumeJump (w φ τ : ℝ) : ℝ :=
  egbThermodynamicVolume (egbFixedChargeALargeRadius w φ τ) - egbThermodynamicVolume (egbFixedChargeASmallRadius w φ τ)

def egbFixedChargeALargeGibbs (w φ l τ : ℝ) : ℝ :=
  egbOffShellGibbsA (egbFixedChargeAPressure w φ τ) (egbFixedChargeATemperature w φ τ) (exp w * cos φ) (exp w * sin φ) l (egbFixedChargeALargeRadius w φ τ)

def egbFixedChargeASmallGibbs (w φ l τ : ℝ) : ℝ :=
  egbOffShellGibbsA (egbFixedChargeAPressure w φ τ) (egbFixedChargeATemperature w φ τ) (exp w * cos φ) (exp w * sin φ) l (egbFixedChargeASmallRadius w φ τ)

theorem egbFixedChargeALargeGibbs_hasDerivAt (w φ l τ : ℝ) :
    HasDerivAt (egbFixedChargeALargeGibbs w φ l)
      (egbThermodynamicVolume (egbFixedChargeALargeRadius w φ τ) * deriv (egbFixedChargeAPressure w φ) τ -
        egbEntropyA (exp w * sin φ) l (egbFixedChargeALargeRadius w φ τ) * deriv (egbFixedChargeATemperature w φ) τ) τ := by
  have hRpos := egbFixedChargeALargeRadius_pos w φ τ
  have hr := ((egbFixedChargeALargeRadius_differentiable w φ) τ).hasDerivAt
  have hp := ((egbFixedChargeAPressure_differentiable w φ) τ).hasDerivAt
  have ht := ((egbFixedChargeATemperature_differentiable w φ) τ).hasDerivAt
  have hb := egbMass_explicit_derivative 0 (exp w * cos φ) (exp w * sin φ) (log (egbFixedChargeALargeRadius w φ τ))
  rw [exp_log hRpos] at hb
  have hv := ((hr.pow 3).const_mul (4 * Real.pi)).div_const 3
  have hm₀ := (hb.comp τ hr).add (hp.mul hv)
  have hm := hm₀.congr_of_eventuallyEq (Filter.Eventually.of_forall
    (fun u => egbMass_pressure_split (egbFixedChargeAPressure w φ u) (exp w * cos φ) (exp w * sin φ) (egbFixedChargeALargeRadius w φ u)))
  have hs₀ := egbEntropyA_derivative (exp w * sin φ) l (log (egbFixedChargeALargeRadius w φ τ))
  rw [exp_log hRpos] at hs₀
  have hs := hs₀.comp τ hr
  have hg := hm.sub (ht.mul hs)
  have hf := (egb_firstLaw_both_prescriptions (egbFixedChargeAPressure w φ τ) (exp w * cos φ) (exp w * sin φ) l (log (egbFixedChargeALargeRadius w φ τ))).1
  rw [(egbMass_explicit_derivative (egbFixedChargeAPressure w φ τ) (exp w * cos φ) (exp w * sin φ) (log (egbFixedChargeALargeRadius w φ τ))).deriv,
    (egbEntropyA_derivative (exp w * sin φ) l (log (egbFixedChargeALargeRadius w φ τ))).deriv, exp_log hRpos,
    egbFixedChargeA_large_temperature] at hf
  apply hg.congr_deriv
  simp only [Function.comp_apply, Pi.mul_apply, Pi.pow_apply, Nat.cast_ofNat]
  unfold egbThermodynamicVolume
  linear_combination (deriv (egbFixedChargeALargeRadius w φ) τ) * hf

theorem egbFixedChargeASmallGibbs_hasDerivAt (w φ l τ : ℝ) :
    HasDerivAt (egbFixedChargeASmallGibbs w φ l)
      (egbThermodynamicVolume (egbFixedChargeASmallRadius w φ τ) * deriv (egbFixedChargeAPressure w φ) τ -
        egbEntropyA (exp w * sin φ) l (egbFixedChargeASmallRadius w φ τ) * deriv (egbFixedChargeATemperature w φ) τ) τ := by
  have hRpos := (egbFixedChargeA_radii_order w φ τ).1
  have hr := ((egbFixedChargeASmallRadius_differentiable w φ) τ).hasDerivAt
  have hp := ((egbFixedChargeAPressure_differentiable w φ) τ).hasDerivAt
  have ht := ((egbFixedChargeATemperature_differentiable w φ) τ).hasDerivAt
  have hb := egbMass_explicit_derivative 0 (exp w * cos φ) (exp w * sin φ) (log (egbFixedChargeASmallRadius w φ τ))
  rw [exp_log hRpos] at hb
  have hv := ((hr.pow 3).const_mul (4 * Real.pi)).div_const 3
  have hm₀ := (hb.comp τ hr).add (hp.mul hv)
  have hm := hm₀.congr_of_eventuallyEq (Filter.Eventually.of_forall
    (fun u => egbMass_pressure_split (egbFixedChargeAPressure w φ u) (exp w * cos φ) (exp w * sin φ) (egbFixedChargeASmallRadius w φ u)))
  have hs₀ := egbEntropyA_derivative (exp w * sin φ) l (log (egbFixedChargeASmallRadius w φ τ))
  rw [exp_log hRpos] at hs₀
  have hs := hs₀.comp τ hr
  have hg := hm.sub (ht.mul hs)
  have hf := (egb_firstLaw_both_prescriptions (egbFixedChargeAPressure w φ τ) (exp w * cos φ) (exp w * sin φ) l (log (egbFixedChargeASmallRadius w φ τ))).1
  rw [(egbMass_explicit_derivative (egbFixedChargeAPressure w φ τ) (exp w * cos φ) (exp w * sin φ) (log (egbFixedChargeASmallRadius w φ τ))).deriv,
    (egbEntropyA_derivative (exp w * sin φ) l (log (egbFixedChargeASmallRadius w φ τ))).deriv, exp_log hRpos,
    egbFixedChargeA_small_temperature] at hf
  apply hg.congr_deriv
  simp only [Function.comp_apply, Pi.mul_apply, Pi.pow_apply, Nat.cast_ofNat]
  unfold egbThermodynamicVolume
  linear_combination (deriv (egbFixedChargeASmallRadius w φ) τ) * hf

/-- Cross-multiplied Clapeyron relation on the actual fixed-charge, fixed-coupling curve. -/
theorem egbFixedChargeA_clapeyron_cross (w φ τ : ℝ) :
    egbFixedChargeAVolumeJump w φ τ * deriv (egbFixedChargeAPressure w φ) τ =
      egbFixedChargeAEntropyJump w φ τ * deriv (egbFixedChargeATemperature w φ) τ := by
  have he : egbFixedChargeALargeGibbs w φ 0 = egbFixedChargeASmallGibbs w φ 0 :=
    funext (fun u => (egbFixedChargeA_equal_gibbs w φ u 0).symm)
  have hd := congrArg (fun f : ℝ → ℝ => deriv f τ) he
  rw [(egbFixedChargeALargeGibbs_hasDerivAt w φ 0 τ).deriv,
    (egbFixedChargeASmallGibbs_hasDerivAt w φ 0 τ).deriv] at hd
  unfold egbFixedChargeAVolumeJump egbFixedChargeAEntropyJump
  linear_combination hd

end GaloisForLFunctions.HTGeometry
