import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.HarmonicClocks.Tomography.Calibration.OneReading

/-! # Born normalization from the absolute slope of a single return -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open Filter Topology
open _root_.RHTower.PrimeCoShift

/-- At the partition pole the normalized deficit of one return measures the inverse block size. -/
theorem singleReturn_pole_deficit (χ : ℕ+ → Circle) (p : Nat.Primes) (D : ℕ+) :
    Tendsto (fun β : TraceTemperature => 1 - (β.val-1)/gibbsClockReturn χ β p D) atPartitionPole
      (𝓝 (Real.exp (-energy (primeRayLabel p D.val)))) := by
  have he : Real.exp (-((D.val:ℝ)*energy (primePNat p))) < 1 :=
    Real.exp_lt_one_iff.mpr (neg_neg_of_pos (mul_pos (Nat.cast_pos.mpr D.pos) (prime_energy_pos p)))
  have h := (gibbsClockReturn_residue χ p D).inv₀ (inv_ne_zero (sub_pos.mpr he).ne')
  simp only [inv_div,inv_inv] at h
  simpa only [energy_primeRayLabel,sub_sub_cancel] using h.const_sub 1

theorem singleReturn_pole_blockSize (χ : ℕ+ → Circle) (p : Nat.Primes) (D : ℕ+) :
    Tendsto (fun β : TraceTemperature => 1 - (β.val-1)/gibbsClockReturn χ β p D) atPartitionPole
      (𝓝 (((primeRayLabel p D.val).val:ℝ)⁻¹)) := by
  have h := singleReturn_pole_deficit χ p D
  rwa [Real.exp_neg,energy,Real.exp_log (Nat.cast_pos.mpr (primeRayLabel p D.val).pos)] at h

/-- A calibrated temperature approach and one scalar return test the Born rule on an arbitrary block. -/
theorem singleReturn_born_iff (χ : ℕ+ → Circle) (p : Nat.Primes) (D : ℕ+) (s : ℂ) :
    Tendsto (fun β : TraceTemperature => 1 - (β.val-1)/gibbsClockReturn χ β p D) atPartitionPole
      (𝓝 (‖heat s (primeRayLabel p D.val)‖^2)) ↔ s.re = 1/2 := by
  let a := primeRayLabel p D.val
  have h := singleReturn_pole_deficit χ p D
  have ha : 0 < energy a := Real.log_pos (by exact_mod_cast clockBlock_gt_one p D)
  have eq : Real.exp (-energy a) = ‖heat s a‖^2 ↔ s.re = 1/2 := by
    rw [norm_heat,sq,← Real.exp_add,Real.exp_injective.eq_iff]
    constructor
    · intro he
      have hm : (1:ℝ)*energy a = (2*s.re)*energy a := by linear_combination -he
      linarith only [mul_right_cancel₀ ha.ne' hm]
    · rintro hs
      rw [hs]
      ring
  exact ⟨fun ht => eq.mp (tendsto_nhds_unique h ht),fun hs => (eq.mpr hs) ▸ h⟩

theorem singleReturn_iff_split_isometry (χ : ℕ+ → Circle) (p : Nat.Primes) (D : ℕ+) (s : ℂ) :
    Tendsto (fun β : TraceTemperature => 1 - (β.val-1)/gibbsClockReturn χ β p D) atPartitionPole
      (𝓝 (‖heat s (primeRayLabel p D.val)‖^2)) ↔
        ∃ T : Gas →ₗᵢ[ℂ] PairGas, ∀ f x, T f x = split s f x :=
  (singleReturn_born_iff χ p D s).trans (split_isometric_iff s).symm

#print axioms singleReturn_pole_deficit
#print axioms singleReturn_pole_blockSize
#print axioms singleReturn_born_iff
#print axioms singleReturn_iff_split_isometry

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
