import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.PinnedSpectra.Insertion
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.OmittedModes.LineRange
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing.HoleMoment
import GaloisForLFunctions.RHTower.NuclearRankOneTrace

/-! # A single prime insertion tests conservation on the full gas -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open ContinuousLinearMap

/-- The second-order relative trace exists because the difference is rank one. -/
theorem relative_square_trace (v : Gas) :
    opTrace (squareHeat.val-projected (omitLine v)^2) = (firstMoment v:ℂ) := by
  simp only [line_square,sub_sub_cancel,_root_.RHTower.opTrace_smul_rankOne_self,firstMoment,
    div_eq_inv_mul,Complex.ofReal_mul,Complex.ofReal_inv,Complex.ofReal_pow]

theorem relative_square_trace_insert (a : ℕ+) (v : Gas) :
    opTrace (squareHeat.val-projected (omitLine (insertWave a v))^2) =
      (attenuation a:ℂ)^2*opTrace (squareHeat.val-projected (omitLine v)^2) := by
  rw [relative_square_trace,relative_square_trace,firstMoment_insert,Complex.ofReal_mul,Complex.ofReal_pow]

private theorem norm_heat_eq_attenuation_iff (s : ℂ) (a : ℕ+) (ha : 1 < a.val) :
    ‖heat s a‖ = attenuation a ↔ s.re = 1/2 := by
  have hnorm : ‖heat (1/2) a‖ = attenuation a := by
    rw [← critical_heat,Complex.norm_real,Real.norm_of_nonneg (attenuation_pos _).le]
  have hc : (1/2:ℂ).re = 1/2 := by norm_num
  have he : energy a ≠ 0 := (Real.log_pos (show (1:ℝ) < (a.val:ℝ) by exact_mod_cast ha)).ne'
  rw [← hnorm,norm_heat,norm_heat,hc]
  exact ⟨fun h => neg_injective (mul_right_cancel₀ he (Real.exp_injective h)),fun h => by rw [h]⟩

/-- The ratio of two fourth-trace losses selects the critical line after a single nontrivial insertion. -/
theorem insertion_fourth_trace_iff (v : MissingWave) (a : ℕ+) (ha : 1 < a.val) (s : ℂ) :
    traceLoss (projected (omitLine (insertMissing a v).val)) =
      ‖heat s a‖^4*traceLoss (projected (omitLine v.val)) ↔ s.re = 1/2 := by
  change traceLoss (projected (omitLine (insertWave a v.val))) = _ ↔ _
  rw [fourth_loss_insert,traceLoss_omitLine,mul_left_inj' (line_loss_bounds v).1.ne',
    pow_left_inj₀ (attenuation_pos a).le (norm_nonneg _) (by decide : (4:ℕ) ≠ 0),eq_comm,
    norm_heat_eq_attenuation_iff s a ha]

/-- For every prime and every exterior wave the measured fourth-trace scaling is equivalent to global split isometry. -/
theorem prime_insertion_split_isometric (p : Nat.Primes) (v : MissingWave) (s : ℂ) :
    let a : ℕ+ := ⟨(p:ℕ),p.property.pos⟩
    traceLoss (projected (omitLine (insertMissing a v).val)) =
      ‖heat s a‖^4*traceLoss (projected (omitLine v.val)) ↔
      ∃ V : Gas →ₗᵢ[ℂ] PairGas, ∀ f x, V f x = split s f x := by
  dsimp only
  exact (insertion_fourth_trace_iff v ⟨(p:ℕ),p.property.pos⟩ p.property.one_lt s).trans (split_isometric_iff s).symm

/-- The reference omission with amplitudes 1/n has a calibration given entirely by three convergent zeta values. -/
theorem reciprocal_loss_calibration :
    traceLoss (projected (omitLine reciprocalTail)) =
      (2*riemannZeta 4/riemannZeta 2-(riemannZeta 3/riemannZeta 2)^2).re := by
  simp only [traceLoss,reciprocalTail,reciprocal_fourth_trace,Complex.add_re,Complex.sub_re]
  ring

/-- One measured fourth trace after insertion suffices when the original reciprocal wave is fixed. -/
theorem calibrated_prime_trace_test (p : Nat.Primes) (s : ℂ) :
    let a := _root_.RHTower.PrimeCoShift.primePNat p
    traceLoss (projected (omitLine (insertWave a reciprocalTail))) =
      ‖heat s a‖^4*(2*riemannZeta 4/riemannZeta 2-(riemannZeta 3/riemannZeta 2)^2).re ↔
      ∃ V : Gas →ₗᵢ[ℂ] PairGas, ∀ f x, V f x = split s f x := by
  have h := prime_insertion_split_isometric p ⟨reciprocalTail,reciprocalTail_outside⟩ s
  dsimp only [insertMissing] at h
  simpa only [_root_.RHTower.PrimeCoShift.primePNat,reciprocal_loss_calibration] using h

#print axioms reciprocal_loss_calibration
#print axioms calibrated_prime_trace_test
#print axioms relative_square_trace
#print axioms relative_square_trace_insert
#print axioms insertion_fourth_trace_iff
#print axioms prime_insertion_split_isometric

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
