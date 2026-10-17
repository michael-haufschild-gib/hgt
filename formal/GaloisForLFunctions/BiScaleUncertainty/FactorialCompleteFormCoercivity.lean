import GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolarFactorialLocalCertificate
import GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolarSourceArchimedeanCertificate
import GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolarHalfLineDomain

/-! The complete real-space prime–Gamma–polar expression on the two balanced
factorial source families has normalized energy tending to positive infinity.
The statement concerns the literal real-space expression; identification with
the spectral Weil functional on these Lipschitz sources is separate. -/

open MeasureTheory Set Filter
open scoped CompactlySupported
namespace GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm
noncomputable section
set_option autoImplicit false

theorem factorialPacketSource_autocorr_tail (n : ℕ) (b : Bool) {x : ℝ}
    (hx : cutoff (10*(n+1)) ≤ x) :
    autocorr (factorialPacketSource n b) x = 0 := by
  have hd := sourceFactorialWidth_pos (by omega : 1 ≤ n+1)
  have hc := factorial_packet_cutoff (by omega : 1 ≤ n+1)
    (show 10*(n+1) ≤ 10*(n+1) from le_rfl)
  unfold autocorr
  apply integral_eq_zero_of_ae
  filter_upwards [] with u
  change factorialPacketSource n b u * factorialPacketSource n b (u+x) = 0
  by_cases hu : u ≤ -2*sourceFactorialWidth (n+1)
  · rw [factorialPacketSource_zero_left n b hu, zero_mul]
  · rw [factorialPacketSource_zero_right n b (u := u+x) (by linarith), mul_zero]

/-- Exact finite stabilization of each complete individual arithmetic–polar pairing. -/
theorem factorialPacketSource_fullPairing_eq (n : ℕ) (b : Bool) :
    fullPairing (autocorr (factorialPacketSource n b)) =
      pairing (10*(n+1)) (autocorr (factorialPacketSource n b)) :=
  fullPairing_eq_pairing_of_tail _ _ fun _ hx => factorialPacketSource_autocorr_tail n b hx

theorem factorialPacketSource_origin_pos (n : ℕ) (b : Bool) :
    0 < autocorr (factorialPacketSource n b) 0 := by
  have hr : 0 < Real.sqrt (n+1 : ℕ) := by positivity
  linarith only [(factorialPacketSource_energy_bounds n b).1, hr]

theorem factorialPacketSource_fullPairing_sq_le (n : ℕ) (b : Bool) :
    fullPairing (autocorr (factorialPacketSource n b))^2 ≤
      50000*autocorr (factorialPacketSource n b) 0^2 := by
  rw [factorialPacketSource_fullPairing_eq]
  simpa only [Nat.add_zero] using factorialPacketSource_pairing_sq_le n b 0

/-- A cutoff-independent individual bound, retaining both polar branches. -/
theorem factorialPacketSource_abs_fullPairing_le (n : ℕ) (b : Bool) :
    |fullPairing (autocorr (factorialPacketSource n b))| ≤
      224*autocorr (factorialPacketSource n b) 0 := by
  have h := factorialPacketSource_fullPairing_sq_le n b
  have hr := factorialPacketSource_origin_pos n b
  apply abs_le.mpr
  constructor <;> nlinarith only [h, hr]

theorem factorialPacketSource_normalized_jump_lower (n : ℕ) (b : Bool) :
    factorialSourceNormalizedJumpLower n ≤
      biScaleLevyEnergy (factorialPacketSource n b)/autocorr (factorialPacketSource n b) 0 := by
  simp only [biScaleLevyEnergy, factorialPacketSource_autocorr]
  cases b
  · exact (factorialSource_normalized_jump_energy_lower n).1
  · exact (factorialSource_normalized_jump_energy_lower n).2

/-- Complete real-space expression, including the signed arithmetic–polar term. -/
def factorialCompleteEnergy (n : ℕ) (b : Bool) : ℝ :=
  Zeta23.EF.gammaBracket 0 * autocorr (factorialPacketSource n b) 0 +
    biScaleLevyEnergy (factorialPacketSource n b) -
      2*fullPairing (autocorr (factorialPacketSource n b))

theorem factorialCompleteEnergy_normalized_lower (n : ℕ) (b : Bool) :
    Zeta23.EF.gammaBracket 0 + factorialSourceNormalizedJumpLower n - 448 ≤
      factorialCompleteEnergy n b/autocorr (factorialPacketSource n b) 0 := by
  have hr := factorialPacketSource_origin_pos n b
  have hj := factorialPacketSource_normalized_jump_lower n b
  have hp := (abs_le.mp (factorialPacketSource_abs_fullPairing_le n b)).2
  have hj' := (le_div_iff₀ hr).mp hj
  apply (le_div_iff₀ hr).mpr
  unfold factorialCompleteEnergy
  nlinarith only [hj', hp]

theorem factorialSourceNormalizedJumpLower_tendsto :
    Tendsto factorialSourceNormalizedJumpLower atTop atTop := by
  have hn : Tendsto (fun n : ℕ => ((n+1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hl := Real.tendsto_log_atTop.comp hn
  have hm := hl.const_mul_atTop
    (show 0 < (3/23 : ℝ)*Real.exp (-(1/2 : ℝ)) by positivity)
  change Tendsto (fun n : ℕ => (3/23 : ℝ)*Real.exp (-(1/2 : ℝ))*
    Real.log ((n+1 : ℕ) : ℝ)-(41+2*Real.log (1000000 : ℝ))/6) atTop atTop
  simpa only [Function.comp_def, sub_eq_add_neg] using
    tendsto_atTop_add_const_right atTop (-((41+2*Real.log (1000000 : ℝ))/6)) hm

/-- Neither sign of the balanced factorial family can have bounded normalized
complete real-space energy along an unbounded sequence of indices. -/
theorem factorialCompleteEnergy_normalized_tendsto (b : Bool) :
    Tendsto (fun n => factorialCompleteEnergy n b/autocorr (factorialPacketSource n b) 0)
      atTop atTop := by
  have h := tendsto_atTop_add_const_left atTop
    (Zeta23.EF.gammaBracket 0) factorialSourceNormalizedJumpLower_tendsto
  have h' := tendsto_atTop_add_const_right atTop (-448 : ℝ) h
  apply tendsto_atTop_mono (fun n => factorialCompleteEnergy_normalized_lower n b)
  simpa only [sub_eq_add_neg] using h'

/-- Both complete real-space energies are strictly positive at every sufficiently
large index, with no arithmetic discrepancy or positivity assumption. -/
theorem factorialCompleteEnergy_eventually_pos :
    ∀ᶠ n in atTop, ∀ b : Bool, 0 < factorialCompleteEnergy n b := by
  have hp := (factorialCompleteEnergy_normalized_tendsto false).eventually (eventually_gt_atTop 0)
  have hm := (factorialCompleteEnergy_normalized_tendsto true).eventually (eventually_gt_atTop 0)
  filter_upwards [hp, hm] with n hp hm b
  have hr := factorialPacketSource_origin_pos n b
  cases b
  · exact (div_pos_iff_of_pos_right hr).mp hp
  · exact (div_pos_iff_of_pos_right hr).mp hm

end
end GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
