import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.HarmonicClocks.Tomography.GibbsThermometry

/-! # Born normalization from relative probabilities of vanishing return events -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open Filter Topology
open _root_.RHTower.PrimeCoShift

private theorem real_temperature_limit :
    Tendsto (fun β : TraceTemperature => β.val) atPartitionPole (𝓝 1) :=
  tendsto_comap.mono_right nhdsWithin_le_nhds

private theorem block_ratio_boundary (p : Nat.Primes) (D : ℕ+) :
    Tendsto (fun β => gibbsBlockRatio β p D) atPartitionPole
      (𝓝 (Real.exp (-((D.val:ℝ)*energy (primePNat p))))) := by
  have h := Real.continuous_exp.continuousAt.tendsto.comp
    (real_temperature_limit.neg.mul_const ((D.val:ℝ)*energy (primePNat p)))
  simpa only [Function.comp_def,gibbsBlockRatio,neg_one_mul] using h

private theorem real_zeta_residue :
    Tendsto (fun β : TraceTemperature => (β.val-1)*(riemannZeta β.val).re) atPartitionPole (𝓝 1) := by
  have h := Complex.continuous_re.continuousAt.tendsto.comp
    (riemannZeta_residue_one.comp tendsto_temperature_punctured)
  simpa only [Function.comp_def,Complex.mul_re,Complex.sub_re,Complex.ofReal_re,Complex.one_re,
    Complex.sub_im,Complex.ofReal_im,Complex.one_im,sub_zero,zero_mul] using h

/-- The simple pole fixes the absolute rate at which each pure-ray return becomes rare. -/
theorem gibbsClockReturn_residue (χ : ℕ+ → Circle) (p : Nat.Primes) (D : ℕ+) :
    Tendsto (fun β : TraceTemperature => gibbsClockReturn χ β p D / (β.val-1)) atPartitionPole
      (𝓝 ((1 - Real.exp (-((D.val:ℝ)*energy (primePNat p))))⁻¹)) := by
  have hlt : Real.exp (-((D.val:ℝ)*energy (primePNat p))) < 1 :=
    Real.exp_lt_one_iff.mpr (neg_neg_of_pos (mul_pos (Nat.cast_pos.mpr D.pos) (prime_energy_pos p)))
  have h := ((tendsto_const_nhds.sub (block_ratio_boundary p D)).inv₀ (sub_ne_zero.mpr hlt.ne')).div
    real_zeta_residue one_ne_zero
  simp_rw [gibbsClockReturn_eq,div_div]
  simpa only [Pi.div_def,div_one,mul_comm] using h

theorem gibbsClockReturn_vanishes (χ : ℕ+ → Circle) (p : Nat.Primes) (D : ℕ+) :
    Tendsto (fun β => gibbsClockReturn χ β p D) atPartitionPole (𝓝 0) := by
  have h := (gibbsClockReturn_residue χ p D).mul (real_temperature_limit.sub_const 1)
  simp only [sub_self,mul_zero] at h
  exact h.congr' (Eventually.of_forall fun β => div_mul_cancel₀ _ (sub_ne_zero.mpr β.property.ne'))

/-- Comparing two return events of one prime characterizes the critical line by the Born rule. -/
theorem gibbsClockReturn_born_iff (χ : ℕ+ → Circle) (p : Nat.Primes) (s : ℂ) :
    Tendsto (fun β => gibbsClockReturn χ β p 1 / gibbsClockReturn χ β p 2 - 1)
      atPartitionPole (𝓝 (‖heat s (primePNat p)‖^2)) ↔ s.re = 1/2 := by
  have h : Tendsto (fun β => gibbsClockReturn χ β p 1 / gibbsClockReturn χ β p 2 - 1)
      atPartitionPole (𝓝 (Real.exp (-energy (primePNat p)))) := by
    simp_rw [gibbsClockReturn_ratio,add_sub_cancel_left]
    simpa using block_ratio_boundary p 1
  have he : Real.exp (-energy (primePNat p)) = ‖heat s (primePNat p)‖^2 ↔ s.re = 1/2 := by
    rw [norm_heat,sq,← Real.exp_add,Real.exp_injective.eq_iff]
    have hp := (prime_energy_pos p).ne'
    constructor
    · intro he
      have hm : (1:ℝ)*energy (primePNat p) = (2*s.re)*energy (primePNat p) := by linear_combination -he
      linarith only [mul_right_cancel₀ hp hm]
    · intro hs
      rw [hs]
      ring
  exact ⟨fun ht => he.mp (tendsto_nhds_unique h ht),fun hs => (he.mpr hs) ▸ h⟩

/-- Agreement at one elementary species is equivalent to norm conservation for every
input to the two-copy cyclic-order split. -/
theorem one_prime_returns_iff_global_isometry (χ : ℕ+ → Circle) (p : Nat.Primes) (s : ℂ) :
    Tendsto (fun β => gibbsClockReturn χ β p 1 / gibbsClockReturn χ β p 2 - 1)
      atPartitionPole (𝓝 (‖heat s (primePNat p)‖^2)) ↔
      ∃ T : Gas →ₗᵢ[ℂ] PairGas, ∀ f x, T f x = split s f x :=
  (gibbsClockReturn_born_iff χ p s).trans (split_isometric_iff s).symm

#print axioms one_prime_returns_iff_global_isometry
#print axioms gibbsClockReturn_residue
#print axioms gibbsClockReturn_vanishes
#print axioms gibbsClockReturn_born_iff

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
