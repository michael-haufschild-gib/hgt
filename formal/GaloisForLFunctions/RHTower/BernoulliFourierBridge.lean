/-
The periodic second-Bernoulli kernel as an absolutely-convergent Fourier series on the real line.

mathlib's `hasSum_one_div_pow_mul_fourier_mul_bernoulliFun` gives the Bernoulli Fourier expansion on
the additive circle `𝕌 = ℝ/ℤ` for `x ∈ [0,1]`.  Composing with the periodicity `↑x = ↑(Int.fract x)`
(`AddCircle.coe_fract`) lifts it to every real `x`, giving the `B₂` kernel `{x}² − {x} + 1/6` as the
sum of its Fourier series with coefficients `1/n²` (absolutely convergent, the `k = 2` case).  This is
the circle→interval bridge that carries the sawtooth's `B₂` form into the reflected-block mode
expansion: the coefficients decay like `1/n²`, so `RHTower.intervalIntegral_tsum` applies and the
per-mode van der Corput bounds sum.
-/
import Mathlib

open Complex Real

noncomputable section

namespace RHTower

/-- **Periodic `B₂` Fourier expansion on the real line.**  For every real `x`,
`∑_{n} (1/n²)·e(nx) = 2π²·({x}² − {x} + 1/6)`, obtained from the circle expansion at `Int.fract x`
by periodicity.  The `1/n²` coefficients are absolutely summable. -/
theorem fourier_hasSum_bernoulli2 (x : ℝ) :
    HasSum (fun n : ℤ => (1 / (n : ℂ) ^ 2) * fourier n (↑x : AddCircle (1 : ℝ)))
      (2 * (π : ℂ) ^ 2 * (((Int.fract x) ^ 2 - Int.fract x + 6⁻¹ : ℝ) : ℂ)) := by
  have hx : Int.fract x ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨Int.fract_nonneg x, (Int.fract_lt_one x).le⟩
  have h := hasSum_one_div_pow_mul_fourier_mul_bernoulliFun (k := 2) (by norm_num) hx
  simp only [AddCircle.coe_fract, bernoulliFun_two] at h
  convert h using 2
  have h2 : ((Nat.factorial 2 : ℕ) : ℂ) = 2 := by norm_num
  have hsq : (2 * (π : ℂ) * I) ^ 2 = -(4 * (π : ℂ) ^ 2) := by
    rw [mul_pow, Complex.I_sq]; ring
  rw [h2, hsq]; ring

end RHTower
