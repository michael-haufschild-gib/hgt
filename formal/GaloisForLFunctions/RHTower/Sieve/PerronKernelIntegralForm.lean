import GaloisForLFunctions.RHTower.Sieve.PerronCompareKernel

/-!
# The comparison kernel kills every constant
-/

namespace RHTower.Sieve

open Complex MeasureTheory

noncomputable section

/-- **The Perron kernel as an interval integral.** -/
theorem perron_kernel_eq_intervalIntegral (x h t : ℝ) :
    (((x + h : ℝ) : ℂ) ^ ((1 : ℂ) + (t : ℝ) * Complex.I)
        - ((x : ℝ) : ℂ) ^ ((1 : ℂ) + (t : ℝ) * Complex.I))
      / ((1 : ℂ) + (t : ℝ) * Complex.I)
      = ∫ u in x..(x + h), ((u : ℝ) : ℂ) ^ (((t : ℝ) : ℂ) * Complex.I) := by
  have hr : (((t : ℝ) : ℂ) * Complex.I).re = 0 := by simp
  have hcpow := integral_cpow (a := x) (b := x + h) (r := ((t : ℝ) : ℂ) * Complex.I)
    (Or.inl (by rw [hr]; norm_num))
  have hcomm : (((t : ℝ) : ℂ) * Complex.I) + 1 = (1 : ℂ) + ((t : ℝ) : ℂ) * Complex.I := by ring
  rw [hcomm] at hcpow
  exact hcpow.symm

end

end RHTower.Sieve
