import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.PinnedSpectra.GapReading
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.PinnedSpectra.Waves

/-! # Infinite-wave eigenvectors at the prescribed strict levels -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open InnerProductSpace ContinuousLinearMap

private theorem heat_squared_mass {m : ℕ} (b : PrefixData m) (n : ℕ) :
    ‖criticalOperator (prefixWave b) (number n)‖^2 = occupationWeight n*prefixProbability b n := by
  rw [critical_apply,norm_mul,mul_pow,Complex.norm_real,Real.norm_of_nonneg (attenuation_pos _).le,prefixWave_mass]
  rfl

/-- The resolvent of the native diagonal applied to the heated missing wave is a genuine square-summable eigenvector. -/
theorem mixed_gap_eigenvector {m : ℕ} {b : PrefixData m} (hb : StrictPrefix b) (j : Fin m) :
    ∃ y : Gas, y ≠ 0 ∧ (projected (omitLine (prefixWave b))^2) y = ((b j).val:ℂ) • y := by
  let x := (b j).val
  let v := prefixWave b
  let w := criticalOperator v
  let f (n : ℕ) := (occupationWeight n-x)⁻¹
  let z (n : ℕ) := (f n:ℂ)*w (number n)
  obtain ⟨C,hC,hbound⟩ := gap_inverse_bound (hb j)
  have hz : Summable (fun n => ‖z n‖^2) :=
    ((gas_coords_summable w).mul_left (C^2)).of_nonneg_of_le (fun _ => sq_nonneg _) (fun n => by
      rw [show ‖z n‖ = |f n|*‖w (number n)‖ by rw [z,norm_mul,Complex.norm_real,Real.norm_eq_abs],mul_pow]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) (hbound n) _) (sq_nonneg _))
  let y := gasOfCoords z hz
  have hi (n : ℕ) : inner ℂ (w (number n)) (y (number n)) = ((occupationWeight n*prefixProbability b n*f n:ℝ):ℂ) := by
    change inner ℂ (w (number n)) ((f n:ℂ) • w (number n)) = _
    rw [inner_smul_right,inner_self_eq_norm_sq_to_K,heat_squared_mass b n,Complex.ofReal_mul,mul_comm]
  have hsum := (probability_resolvent_overlap hb j).tsum_eq
  have hover : inner ℂ w y = 1 := by
    rw [lp.inner_eq_tsum,← Equiv.pnatEquivNat.symm.tsum_eq]
    change (∑' n, inner ℂ (w (number n)) (y (number n))) = 1
    simp only [hi,← Complex.ofReal_tsum]
    exact_mod_cast hsum
  refine ⟨y,fun h => one_ne_zero (hover.symm.trans (by rw [h,inner_zero_right])),?_⟩
  rw [line_square,prefixWave_norm,one_pow,Complex.ofReal_one,inv_one,one_smul,sub_apply]
  change squareHeat.val y-inner ℂ w y • w = (x:ℂ) • y
  rw [hover,one_smul]
  apply lp.ext
  funext l
  obtain ⟨n,rfl⟩ := number_surjective l
  let d := attenuation (number n)
  change (d:ℂ)*((d:ℂ)*((f n:ℂ)*w (number n)))-w (number n) = (x:ℂ)*((f n:ℂ)*w (number n))
  have he : d^2*f n-1 = x*f n := by
    change occupationWeight n*(occupationWeight n-x)⁻¹-1 = x*(occupationWeight n-x)⁻¹
    field_simp [native_ne_in_gap (hb j) n]
    ring
  have he' : (d:ℂ)^2*(f n:ℂ)-1 = (x:ℂ)*(f n:ℂ) := by exact_mod_cast he
  calc (d:ℂ)*((d:ℂ)*((f n:ℂ)*w (number n)))-w (number n) = ((d:ℂ)^2*(f n:ℂ)-1)*w (number n) := by ring
       _ = _ := by rw [he',mul_assoc]

#print axioms mixed_gap_eigenvector

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
