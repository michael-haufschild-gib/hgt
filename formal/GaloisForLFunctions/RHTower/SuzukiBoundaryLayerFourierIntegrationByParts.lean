import GaloisForLFunctions.RHTower.SuzukiBoundaryLayerFourierEnvelope
import GaloisForLFunctions.HTGeometry.FourierDecayFromDerivative

open MeasureTheory Set intervalIntegral Complex

noncomputable section

namespace RHTower

def boundaryFourierPhase (ξ x : ℝ) : ℂ :=
  Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (ξ : ℂ) * (x : ℂ)))

theorem norm_boundaryFourierPhase (ξ x : ℝ) : ‖boundaryFourierPhase ξ x‖ = 1 := by
  rw [boundaryFourierPhase, Complex.norm_exp]
  simp [Complex.mul_re, Complex.mul_im]

theorem hasDerivAt_boundaryFourierPhase (ξ x : ℝ) :
    HasDerivAt (boundaryFourierPhase ξ)
      (-(2 * (Real.pi : ℂ) * Complex.I * (ξ : ℂ)) * boundaryFourierPhase ξ x) x := by
  unfold boundaryFourierPhase
  have hid : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 x := Complex.ofRealCLM.hasDerivAt
  convert ((hid.const_mul
    (-(2 * (Real.pi : ℂ) * Complex.I * (ξ : ℂ)))).cexp) using 1 <;> ring

theorem continuous_boundaryFourierPhase (ξ : ℝ) : Continuous (boundaryFourierPhase ξ) := by
  exact continuous_iff_continuousAt.2 fun x =>
    (hasDerivAt_boundaryFourierPhase ξ x).continuousAt

/-- The interval Fourier transform of an absolutely continuous profile has the exact uniform
boundary-plus-variation `1 / |ξ|` bound used in Suzuki's equation (3.4). -/
theorem norm_intervalFourier_le_boundary_add_integral_deriv
    {f f' : ℝ → ℂ} {a b ξ : ℝ} (hab : a ≤ b)
    (hf : ∀ x ∈ Icc a b, HasDerivAt f (f' x) x)
    (hf' : ContinuousOn f' (Icc a b)) (hξ : ξ ≠ 0) :
    ‖∫ x in a..b, boundaryFourierPhase ξ x * f x‖ ≤
      (‖f a‖ + ‖f b‖ + ∫ x in a..b, ‖f' x‖) / (2 * Real.pi * |ξ|) := by
  let c : ℂ := -(2 * (Real.pi : ℂ) * Complex.I * (ξ : ℂ))
  have hphase : ∀ x ∈ uIcc a b, HasDerivAt (boundaryFourierPhase ξ)
      (c * boundaryFourierPhase ξ x) x := by
    intro x hx
    simpa [c] using hasDerivAt_boundaryFourierPhase ξ x
  have hfder : ∀ x ∈ uIcc a b, HasDerivAt f (f' x) x := by
    simpa [uIcc_of_le hab] using hf
  have hphaseInt : IntervalIntegrable
      (fun x => c * boundaryFourierPhase ξ x) volume a b :=
    ((continuous_const.mul (continuous_boundaryFourierPhase ξ)).intervalIntegrable _ _)
  have hf'Int : IntervalIntegrable f' volume a b :=
    (hf'.intervalIntegrable_of_Icc hab)
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    hphase hfder hphaseInt hf'Int
  have hfactor : (∫ x in a..b, (c * boundaryFourierPhase ξ x) * f x) =
      c * ∫ x in a..b, boundaryFourierPhase ξ x * f x := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr fun x hx => by ring
  rw [hfactor] at hibp
  have hnormc : ‖c‖ = 2 * Real.pi * |ξ| := by
    unfold c
    rw [norm_neg, norm_mul, norm_mul, norm_mul]
    simp [abs_of_nonneg Real.pi_nonneg]
  have hmain : ‖c‖ * ‖∫ x in a..b, boundaryFourierPhase ξ x * f x‖ ≤
      ‖f a‖ + ‖f b‖ + ∫ x in a..b, ‖f' x‖ := by
    rw [← norm_mul]
    have hsolve : c * ∫ x in a..b, boundaryFourierPhase ξ x * f x =
        boundaryFourierPhase ξ b * f b - boundaryFourierPhase ξ a * f a -
          ∫ x in a..b, boundaryFourierPhase ξ x * f' x := by
      rw [hibp]
      ring
    rw [hsolve]
    calc
      ‖boundaryFourierPhase ξ b * f b - boundaryFourierPhase ξ a * f a -
          ∫ x in a..b, boundaryFourierPhase ξ x * f' x‖
          ≤ ‖boundaryFourierPhase ξ b * f b‖ +
              ‖boundaryFourierPhase ξ a * f a‖ +
              ‖∫ x in a..b, boundaryFourierPhase ξ x * f' x‖ := by
                calc
                  _ ≤ ‖boundaryFourierPhase ξ b * f b -
                        boundaryFourierPhase ξ a * f a‖ +
                      ‖∫ x in a..b, boundaryFourierPhase ξ x * f' x‖ := norm_sub_le _ _
                  _ ≤ _ := add_le_add_right (norm_sub_le _ _) _
      _ ≤ ‖f b‖ + ‖f a‖ + ∫ x in a..b, ‖f' x‖ := by
        gcongr
        · rw [norm_mul, norm_boundaryFourierPhase, one_mul]
        · rw [norm_mul, norm_boundaryFourierPhase, one_mul]
        · exact intervalIntegral.norm_integral_le_of_norm_le (μ := volume)
            (ae_of_all _ fun x hx => by
              rw [norm_mul, norm_boundaryFourierPhase, one_mul]) hf'Int.norm
      _ = ‖f a‖ + ‖f b‖ + ∫ x in a..b, ‖f' x‖ := by ring
  rw [hnormc] at hmain
  exact (le_div_iff₀ (mul_pos (by positivity) (abs_pos.mpr hξ))).2 (by
    simpa [mul_comm] using hmain)

end RHTower

