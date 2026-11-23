import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.RelativeGibbs.PhysicalSpectrum
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.RelativeGibbs.ExtremalSpectra

/-! # The fourth Gibbs trace as the calibrating relative measurement -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open Set ContinuousLinearMap _root_.RHTower

def quadraticResponse : SpectralResponse where
  value x := x^2
  cont := (continuous_id.pow 2).continuousOn
  inc := by intro x hx y _ h; exact pow_lt_pow_left₀ h hx.1 two_ne_zero

theorem quadratic_head (r : ℕ) : relativeHead quadraticResponse r = traceCeiling r := by
  simp only [relativeHead,quadraticResponse,zero_pow two_ne_zero,sub_zero,traceCeiling]

private theorem square_mass_sum {T : GasOp} (hh : T.IsHilbertSchmidt) :
    HasSum (fun n => approxNumber T n^2) (hsNormSq T) := by
  have h := (memSchattenClass_two_iff_isHilbertSchmidt T).mpr hh
  change Summable (fun n => approxNumber T n^(2:ℝ)) at h
  rw [hsNormSq_eq_tsum_approxNumber_sq hh]
  exact (show Summable (fun n => approxNumber T n^2) by simpa only [Real.rpow_two] using h).hasSum

/-- The quadratic reading coincides with the measured fourth trace loss, including its calibration. -/
theorem quadratic_physicalReading (P : Projection) {r : ℕ} (hd : MissingDimension P r)
    (hc : Conserving (projected P)) :
    relativeReading quadraticResponse (physicalSpectrum P hd hc) = traceLoss (projected P) := by
  let G : Propagator := ⟨projected P,projected_positive _,hc⟩
  have hB := conserving_square_hs G
  have ha := _root_.HTGeometry.opTrace_sq_eq_ofReal_hsNormSq squareHeat.property.2 squareHeat.property.1.star_eq
  have hb := _root_.HTGeometry.opTrace_sq_eq_ofReal_hsNormSq hB (G.property.1.isSelfAdjoint.pow 2).star_eq
  change opTrace ((criticalOperator^2)^2) = _ at ha
  rw [critical_fourth_trace] at ha
  have hs := ((square_mass_sum squareHeat.property.2).sub (square_mass_sum hB)).tsum_eq
  simp only [squareHeat_approxNumber] at hs
  change (∑' n, (occupationWeight n ^ 2 - approxNumber (G.val ^ 2) n ^ 2)) = traceLoss G.val
  rw [traceLoss,ha,show (4:ℕ) = 2*2 from rfl,pow_mul,hb,Complex.ofReal_re,Complex.ofReal_re]
  exact hs

/-- Strictness at the quadratic response excludes both endpoints for every detector. -/
theorem physical_reading_interior (f : SpectralResponse) (P : Projection) {r : ℕ} (hr : 0 < r)
    (hd : MissingDimension P r) (hc : Conserving (projected P)) :
    relativeReading f (physicalSpectrum P hd hc) ∈ Ioo 0 (relativeHead f r) := by
  apply (reading_interior_iff f _).mpr
  apply (reading_interior_iff quadraticResponse _).mp
  rw [quadratic_head,quadratic_physicalReading]
  exact lossesAtRank_subset r hr ⟨P,hd,hc,rfl⟩

#print axioms quadratic_physicalReading
#print axioms physical_reading_interior

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
