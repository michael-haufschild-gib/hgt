import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing.Canonical
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CompositionRigidity

/-!
# The critical line and its positive point from finite order experiments

The full complex heat family passes all nested isometry tests on the critical
line. Requiring positivity at unbounded cutoffs fixes the imaginary parameter
as well, since the heat values on shells two and three recover the clock.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open scoped ComplexOrder

def thermalKernel (s : ℂ) : Kernel := fun i j => if i = j then heat s (number i) else 0

private theorem critical_kernel : thermalKernel (1/2) = phaseKernel 1 := by
  funext i j
  rw [thermalKernel,phaseKernel,← critical_heat]
  by_cases h : i = j
  · rw [if_pos h,if_pos h]
    change (↑((gain (number i))⁻¹):ℂ) = (↑(gain (number i)):ℂ)⁻¹*1
    rw [Complex.ofReal_inv,mul_one]
  · rw [if_neg h,if_neg h]

private theorem same_norm {s : ℂ} (hs : s.re = 1/2) (n : ℕ+) :
    ‖heat s n‖ = attenuation n := by
  calc
    _ = ‖heat (1/2) n‖ := by rw [norm_heat,norm_heat,hs]; norm_num
    _ = _ := by rw [← critical_heat,Complex.norm_real,Real.norm_of_nonneg (attenuation_pos n).le]

theorem thermal_tests_iff (s : ℂ) : (∀ M, Test (thermalKernel s) M) ↔ s.re = 1/2 := by
  rw [nested_isometries_iff]
  constructor
  · rintro ⟨u,hu,he⟩
    have h := congrArg norm (congrFun (congrFun he 1) 1)
    change ‖thermalKernel s 1 1‖ = ‖phaseKernel u 1 1‖ at h
    rw [thermalKernel,phaseKernel,if_pos rfl,if_pos rfl,norm_mul,hu,mul_one] at h
    have hc := congrArg norm (congrFun (congrFun critical_kernel 1) 1)
    change ‖thermalKernel (1/2) 1 1‖ = ‖phaseKernel 1 1 1‖ at hc
    rw [thermalKernel,phaseKernel,if_pos rfl,if_pos rfl] at hc
    change ‖heat (1/2) (number 1)‖ = ‖(scale 1)⁻¹*1‖ at hc
    rw [mul_one] at hc
    have heq := h.trans hc.symm
    rw [norm_heat,norm_heat] at heq
    have hpos : 0 < energy (number 1) := Real.log_pos (by norm_num [number])
    have hx := neg_injective (mul_right_cancel₀ hpos.ne' (Real.exp_injective heq))
    simpa using hx
  · intro hs
    let u (i : ℕ) := scale i * heat s (number i)
    refine ⟨u,fun i => ?_,?_⟩
    · change ‖(gain (number i):ℂ)*heat s (number i)‖ = 1
      rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (gain_pos _).le,same_norm hs,attenuation,
        mul_inv_cancel₀ (gain_pos _).ne']
    · funext i j
      rw [thermalKernel,phaseKernel]
      by_cases h : i = j
      · rw [if_pos h,if_pos h]
        change _ = (gain (number i):ℂ)⁻¹*((gain (number i):ℂ)*heat s (number i))
        rw [← mul_assoc,inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr (gain_pos _).ne'),one_mul]
      · rw [if_neg h,if_neg h]

/-- Positivity eliminates the remaining prime phases and selects a single temperature. -/
theorem positive_thermal_tests_iff (s : ℂ) :
    (∀ m, ∃ M ≥ m, (corner (thermalKernel s) M).PosSemidef ∧ Test (thermalKernel s) M) ↔ s = 1/2 := by
  rw [cofinal_positive_iff,← critical_kernel]
  constructor
  · intro h
    have he (n : ℕ+) : heat s n = heat (1/2) n := by
      obtain ⟨i,rfl⟩ := number_surjective n
      simpa only [thermalKernel,if_pos rfl] using congrFun (congrFun h i) i
    exact two_prime_heat_injective (Prod.ext (he 2) (he 3))
  · rintro rfl
    rfl

#print axioms thermal_tests_iff
#print axioms positive_thermal_tests_iff

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
