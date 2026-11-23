import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ClockStability.NoisyData

/-! # Predicting complex thermal readings from noisy critical clocks -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open Set
open scoped NNReal

private theorem complex_distance_bound {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (hx₁ : x ≤ 1) (hy₁ : y ≤ 1)
    (δ : GibbsExponent) {z : ℂ} (hz : δ.val ≤ z.re) :
    ‖(x : ℂ)^z - (y : ℂ)^z‖ ≤ ‖z‖ / δ.val * |x^δ.val-y^δ.val| := by
  rcases le_total y x with h | h
  · rw [abs_of_nonneg (sub_nonneg.mpr (Real.rpow_le_rpow hy.le h δ.property.le))]
    exact norm_thermal_chord hy h hx₁ δ.property hz
  · rw [norm_sub_rev,abs_sub_comm,abs_of_nonneg (sub_nonneg.mpr (Real.rpow_le_rpow hx.le h δ.property.le))]
    exact norm_thermal_chord hx h hy₁ δ.property hz

/-- Total real spectral error bounds complex readout differences for any two interlacing spectra. -/
theorem relativePartition_le_detectorError {r : ℕ} (b c : SpectralBand r) (δ : GibbsExponent)
    {z : ℂ} (hz : δ.val ≤ z.re) :
    ‖relativePartition b z - relativePartition c z‖ ≤ ‖z‖ / δ.val * detectorError (powerResponse δ) b c := by
  have hb := summable_complexDrop b (δ.property.trans_le hz)
  have hc := summable_complexDrop c (δ.property.trans_le hz)
  have he (n : ℕ) : ‖complexDrop b n z - complexDrop c n z‖ ≤ ‖z‖ / δ.val * levelError (powerResponse δ) b c n := by
    have e : complexDrop b n z - complexDrop c n z = ((c n).val : ℂ)^z - ((b n).val : ℂ)^z := by unfold complexDrop; abel
    rw [e,norm_sub_rev]
    exact complex_distance_bound (band_pos b n) (band_pos c n) (band_in_unit b n).2 (band_in_unit c n).2 δ hz
  calc
    _ = ‖∑' n, (complexDrop b n z - complexDrop c n z)‖ := by simp only [relativePartition,hb.tsum_sub hc]
    _ ≤ ∑' n, (‖z‖ / δ.val) * levelError (powerResponse δ) b c n :=
      tsum_of_norm_bounded ((summable_levelError (powerResponse δ) b c).mul_left _).hasSum he
    _ = _ := by
      change (∑' n, (‖z‖ / δ.val) * levelError (powerResponse δ) b c n) =
        (‖z‖ / δ.val) * ∑' n, levelError (powerResponse δ) b c n
      rw [tsum_mul_left]

/-- A single finite noisy experiment controls the whole bounded window, including windows through the zeta pole. -/
theorem noisy_complex_window (r : ℕ) (l u : ℝ) (δ : GibbsExponent) (M : ℝ≥0)
    {ε : ℝ} (hε : 0 < ε) (start k : ℕ) :
    ∃ N : ℕ, ∀ (p q : ClockState l u r) (clock : ℝ) (y : ℕ → ℂ) (B C : Finset ℕ),
      B.card ≤ k → C.card ≤ k →
      fitsReadings p clock y start (start+N+2*k) B (occupationWeight N/2) →
      fitsReadings q clock y start (start+N+2*k) C (occupationWeight N/2) →
      ∀ z : ℂ, δ.val ≤ z.re → ‖z‖ ≤ M →
        ‖relativePartition p.2.val z - relativePartition q.2.val z‖ < ε := by
  have hM : 0 < (M:ℝ)/δ.val + 1 := add_pos_of_nonneg_of_pos (div_nonneg M.property δ.property.le) zero_lt_one
  obtain ⟨N,hN⟩ := noisy_clock_stability r l u (powerResponse δ) (div_pos hε hM) start k
  refine ⟨N,fun p q clock y B C hB hC hp hq z hz hnorm => ?_⟩
  have hE := (lt_div_iff₀ hM).mp (hN p q clock y B C hB hC hp hq)
  have h₀ : 0 ≤ detectorError (powerResponse δ) p.2.val q.2.val := tsum_nonneg (fun _ => abs_nonneg _)
  apply (relativePartition_le_detectorError _ _ δ hz).trans_lt
  rw [mul_comm]
  exact (mul_le_mul_of_nonneg_left ((div_le_div_of_nonneg_right hnorm δ.property.le).trans
    (le_add_of_nonneg_right zero_le_one)) h₀).trans_lt hE

#print axioms relativePartition_le_detectorError
#print axioms noisy_complex_window

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
