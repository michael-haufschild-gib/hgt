import GaloisForLFunctions.RHTower.PerronKernelIdentity

/-!
# The weighted Perron kernel `∫ e^{su}/s² dw = u⁺`

Multiplying the kernel identity by `e^{au}` absorbs the tent's
exponential decay: for `s = a + 2πiw`, `a > 0`,

`∫ e^{su}/s² dw = max u 0`.

At `u = log(x/n)` the integrand carries `n^{-s}`, so the von Mangoldt
sum against this kernel converges absolutely — the smoothed Perron
formula in the `2πξ` convention (the `dw`-normalization absorbs the
classical `1/2πi`).
-/

noncomputable section

namespace RHTower

open MeasureTheory Set Filter

/-- **The weighted Perron kernel**: `∫ e^{su}/s² dw = u⁺` for
`s = a + 2πiw`, `a > 0`. -/
theorem perron_weighted_kernel {a : ℝ} (ha : 0 < a) (u : ℝ) :
    ∫ w : ℝ, Complex.exp (((a : ℂ) + 2 * Real.pi * w * Complex.I) * u)
        / ((a : ℂ) + 2 * Real.pi * w * Complex.I) ^ (2 : ℕ)
      = ((max u 0 : ℝ) : ℂ) := by
  have hsplit : ∀ w : ℝ,
      Complex.exp (((a : ℂ) + 2 * Real.pi * w * Complex.I) * u)
        / ((a : ℂ) + 2 * Real.pi * w * Complex.I) ^ (2 : ℕ)
      = Complex.exp (((a * u : ℝ) : ℂ))
        * (Complex.exp (((2 * Real.pi * (w * u) : ℝ) : ℂ) * Complex.I)
          • (1 / ((a : ℂ) + 2 * Real.pi * w * Complex.I) ^ (2 : ℕ))) := by
    intro w
    rw [smul_eq_mul, ← mul_assoc, ← Complex.exp_add, mul_one_div]
    congr 2
    push_cast
    ring
  calc ∫ w : ℝ, Complex.exp (((a : ℂ) + 2 * Real.pi * w * Complex.I) * u)
        / ((a : ℂ) + 2 * Real.pi * w * Complex.I) ^ (2 : ℕ)
      = ∫ w : ℝ, Complex.exp (((a * u : ℝ) : ℂ))
          * (Complex.exp (((2 * Real.pi * (w * u) : ℝ) : ℂ) * Complex.I)
            • (1 / ((a : ℂ) + 2 * Real.pi * w * Complex.I) ^ (2 : ℕ))) :=
        integral_congr_ae (Filter.Eventually.of_forall hsplit)
    _ = Complex.exp (((a * u : ℝ) : ℂ))
          * ∫ w : ℝ, Complex.exp (((2 * Real.pi * (w * u) : ℝ) : ℂ)
              * Complex.I)
            • (1 / ((a : ℂ) + 2 * Real.pi * w * Complex.I) ^ (2 : ℕ)) :=
        integral_const_mul _ _
    _ = Complex.exp (((a * u : ℝ) : ℂ)) * perronTent a u := by
        rw [perron_kernel_identity ha u]
    _ = ((max u 0 : ℝ) : ℂ) := by
        rcases le_or_gt u 0 with hu | hu
        · rw [perronTent, Set.indicator_of_notMem (by simpa using hu),
            mul_zero, max_eq_right hu]
          simp
        · rw [perronTent, Set.indicator_of_mem (Set.mem_Ioi.2 hu),
            max_eq_left hu.le]
          rw [show Complex.exp (((a * u : ℝ) : ℂ))
              * ((u : ℂ) * Complex.exp (-((a : ℂ) * u)))
              = (u : ℂ) * (Complex.exp (((a * u : ℝ) : ℂ))
                * Complex.exp (-((a : ℂ) * u))) from by ring,
            ← Complex.exp_add]
          rw [show (((a * u : ℝ) : ℂ)) + -((a : ℂ) * u) = 0 from by
            push_cast; ring]
          rw [Complex.exp_zero, mul_one]

end RHTower
