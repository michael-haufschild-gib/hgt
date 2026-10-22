import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticSlopeTerminalPositive
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticControl18Obstruction
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticControl18Endpoint
namespace HTGeometry.ThetaRatioKineticContraction
noncomputable section
set_option autoImplicit false

theorem reducedKineticValue_fixed_endpoint_neg (h : ℝ)
    (hh0 : 1/10 ≤ h) (hh1 : h ≤ 1/8) :
    reducedKineticValue h (9-(361/25)*h^2) (1/3) < 0 := by
  have hc := reducedKineticControl_eighteen_fixed_endpoint_neg h hh0 hh1
  have hd := reducedKineticValue_terminal_deriv_neg h (361/25)
    (by linarith) (by linarith) (by norm_num) le_rfl
  have hm := mul_neg_of_pos_of_neg (show (0:ℝ) < 1/3 by norm_num) hd
  rw [reducedKineticControl_eighteen_endpoint] at hc
  linarith only [hc,hm]

theorem reducedKineticValue_window_zero_pos (h : ℝ)
    (hh0 : 1/10 ≤ h) (hh1 : h ≤ 1/8) :
    0 < reducedKineticValue h (9-(361/25)*h^2) 0 := by
  have hp := reducedKineticControl_zero_pos h (361/25) 0
    (by linarith) (by linarith) (by norm_num) le_rfl
  rw [reducedKineticControl_zero] at hp
  simpa [reducedKineticValue,Finset.sum_range_succ] using hp

/-- A zero of the auxiliary kinetic source polynomial, with no assertion about zeta zeros. -/
theorem reducedKineticValue_window_exists_zero (h : ℝ)
    (hh0 : 1/10 ≤ h) (hh1 : h ≤ 1/8) :
    ∃ z : ℝ, 0 < z ∧ z < 1/3 ∧
      reducedKineticValue h (9-(361/25)*h^2) z=0 := by
  have hpos := reducedKineticValue_window_zero_pos h hh0 hh1
  have hneg := reducedKineticValue_fixed_endpoint_neg h hh0 hh1
  have hf : Continuous (reducedKineticValue h (9-(361/25)*h^2)) := by
    unfold reducedKineticValue
    fun_prop
  obtain ⟨z,hz,hzero⟩ := intermediate_value_Icc' (f := reducedKineticValue h (9-(361/25)*h^2))
    (show (0:ℝ) ≤ 1/3 by norm_num) hf.continuousOn ⟨hneg.le,hpos.le⟩
  have hz0 : 0 < z := by
    by_contra hn
    have he : z=0 := le_antisymm (not_lt.mp hn) hz.1
    rw [he] at hzero
    linarith
  have hz1 : z < 1/3 := by
    by_contra hn
    have he : z=1/3 := le_antisymm hz.2 (not_lt.mp hn)
    rw [he] at hzero
    linarith
  exact ⟨z,hz0,hz1,hzero⟩

end
end HTGeometry.ThetaRatioKineticContraction
