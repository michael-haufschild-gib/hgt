import GaloisForLFunctions.HTGeometry.HalfLineExponentialCoDistance
import GaloisForLFunctions.HTGeometry.PuncturedSineProduct
import GaloisForLFunctions.RHTower.XiThetaSquareRateHardy

/-!
# The square-rate Blaschke limit

The punctured Euler sine product is elementary and the punctured hyperbolic sine product is the
corpus's `tendsto_euler_sinh_prod` with its single deleted factor `2` restored.  Their quotient is
the Blaschke product of the square rates against one selected rate:

`∏_{m ≠ j} (m² - j²)/(m² + j²) → (-1)^{j-1} · π j / sinh (π j)`.

This is the limit that turns the finite co-distance law for the half-line exponential system into
the exact reader norm of the theta square-rate card.
-/

open Filter Topology Finset

namespace RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

/-! ## Euler's hyperbolic sine product on the real line -/

theorem tendsto_euler_sinh_prod_real (x : ℝ) :
    Tendsto (fun N : ℕ => Real.pi * x * ∏ k ∈ Finset.range N, (1 + x ^ 2 / ((k : ℝ) + 1) ^ 2))
      atTop (𝓝 (Real.sinh (Real.pi * x))) := by
  have h := tendsto_euler_sinh_prod ((x : ℝ) : ℂ)
  have hre := (Complex.continuous_re.tendsto _).comp h
  have hfun : ∀ N : ℕ,
      (((Real.pi : ℂ) * ((x : ℝ) : ℂ) *
        ∏ k ∈ Finset.range N, ((1 : ℂ) + ((x : ℝ) : ℂ) ^ 2 / ((k : ℂ) + 1) ^ 2)).re) =
      Real.pi * x * ∏ k ∈ Finset.range N, (1 + x ^ 2 / ((k : ℝ) + 1) ^ 2) := by
    intro N
    have hcast : ((Real.pi : ℂ) * ((x : ℝ) : ℂ) *
        ∏ k ∈ Finset.range N, ((1 : ℂ) + ((x : ℝ) : ℂ) ^ 2 / ((k : ℂ) + 1) ^ 2)) =
        (((Real.pi * x * ∏ k ∈ Finset.range N, (1 + x ^ 2 / ((k : ℝ) + 1) ^ 2) : ℝ)) : ℂ) := by
      push_cast
      ring
    rw [hcast, Complex.ofReal_re]
  have hlim : (Complex.sinh ((Real.pi : ℂ) * ((x : ℝ) : ℂ))).re =
      Real.sinh (Real.pi * x) := by
    have : ((Real.pi : ℂ) * ((x : ℝ) : ℂ)) = ((Real.pi * x : ℝ) : ℂ) := by push_cast; ring
    rw [this, ← Complex.ofReal_sinh, Complex.ofReal_re]
  rw [Function.comp_def] at hre
  simp only [hfun] at hre
  rw [hlim] at hre
  exact hre

/-! ## The punctured hyperbolic product -/

theorem tendsto_punctured_sinh_prod (n : ℕ) :
    Tendsto
      (fun M : ℕ => ∏ k ∈ (Finset.range (M + 1)).erase n,
        (1 + (((n : ℝ) + 1) ^ 2) / ((k : ℝ) + 1) ^ 2))
      atTop (𝓝 (Real.sinh (Real.pi * ((n : ℝ) + 1)) / (2 * (Real.pi * ((n : ℝ) + 1))))) := by
  have hpipos : 0 < Real.pi * ((n : ℝ) + 1) := by positivity
  have hfull : Tendsto
      (fun M : ℕ => ∏ k ∈ Finset.range (M + 1), (1 + (((n : ℝ) + 1) ^ 2) / ((k : ℝ) + 1) ^ 2))
      atTop (𝓝 (Real.sinh (Real.pi * ((n : ℝ) + 1)) / (Real.pi * ((n : ℝ) + 1)))) := by
    have h := tendsto_euler_sinh_prod_real ((n : ℝ) + 1)
    have hshift := h.comp (tendsto_add_atTop_nat 1)
    rw [Function.comp_def] at hshift
    have hdiv := hshift.div_const (Real.pi * ((n : ℝ) + 1))
    refine hdiv.congr (fun M => ?_)
    field_simp
  have herase : ∀ M : ℕ, n ≤ M →
      (∏ k ∈ (Finset.range (M + 1)).erase n,
        (1 + (((n : ℝ) + 1) ^ 2) / ((k : ℝ) + 1) ^ 2)) * 2 =
      ∏ k ∈ Finset.range (M + 1), (1 + (((n : ℝ) + 1) ^ 2) / ((k : ℝ) + 1) ^ 2) := by
    intro M hM
    have hmem : n ∈ Finset.range (M + 1) := by
      rw [Finset.mem_range]; omega
    have hval : (1 + (((n : ℝ) + 1) ^ 2) / ((n : ℝ) + 1) ^ 2) = 2 := by
      have hne : ((n : ℝ) + 1) ^ 2 ≠ 0 := by positivity
      field_simp
      norm_num
    rw [← hval]
    exact Finset.prod_erase_mul _ _ hmem
  have hdiv2 := hfull.div_const 2
  have hlimval : Real.sinh (Real.pi * ((n : ℝ) + 1)) / (Real.pi * ((n : ℝ) + 1)) / 2 =
      Real.sinh (Real.pi * ((n : ℝ) + 1)) / (2 * (Real.pi * ((n : ℝ) + 1))) := by
    field_simp
  rw [hlimval] at hdiv2
  refine hdiv2.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop n] with M hM
  rw [← herase M hM]
  field_simp

/-! ## The Blaschke limit -/

/-- **The square-rate Blaschke limit.** -/
theorem tendsto_blaschke_square_rate (n : ℕ) :
    Tendsto
      (fun M : ℕ => ∏ k ∈ (Finset.range (M + 1)).erase n,
        ((1 - (((n : ℝ) + 1) ^ 2) / ((k : ℝ) + 1) ^ 2) /
          (1 + (((n : ℝ) + 1) ^ 2) / ((k : ℝ) + 1) ^ 2)))
      atTop
      (𝓝 ((-1) ^ n * (Real.pi * ((n : ℝ) + 1)) /
        Real.sinh (Real.pi * ((n : ℝ) + 1)))) := by
  have hsinhpos : 0 < Real.sinh (Real.pi * ((n : ℝ) + 1)) := by
    have hx : (0 : ℝ) < Real.pi * ((n : ℝ) + 1) := by positivity
    have h0 : Real.sinh 0 < Real.sinh (Real.pi * ((n : ℝ) + 1)) :=
      Real.sinh_lt_sinh.mpr hx
    rwa [Real.sinh_zero] at h0
  have hnum : Tendsto
      (fun M : ℕ => ∏ k ∈ (Finset.range (M + 1)).erase n,
        (1 - (((n : ℝ) + 1) ^ 2) / ((k : ℝ) + 1) ^ 2))
      atTop (𝓝 ((-1) ^ n / 2)) := by
    have hlim := (tendsto_puncturedRatio (n + 1)).comp (tendsto_add_atTop_nat 1)
    rw [Function.comp_def] at hlim
    have hmul := hlim.const_mul ((-1 : ℝ) ^ n / 2)
    rw [mul_one] at hmul
    refine hmul.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop n] with M hM
    have hcast : ∀ k : ℕ, ((k : ℝ) + 1) = ((k + 1 : ℕ) : ℝ) := by
      intro k; push_cast; ring
    have := prod_punctured_sine n M hM
    simp only [← hcast] at this
    exact this.symm
  have hden := tendsto_punctured_sinh_prod n
  have hdenne : Real.sinh (Real.pi * ((n : ℝ) + 1)) / (2 * (Real.pi * ((n : ℝ) + 1))) ≠ 0 := by
    have hpipos : 0 < Real.pi * ((n : ℝ) + 1) := by positivity
    positivity
  have hquot := hnum.div hden hdenne
  have hval : ((-1 : ℝ) ^ n / 2) /
      (Real.sinh (Real.pi * ((n : ℝ) + 1)) / (2 * (Real.pi * ((n : ℝ) + 1)))) =
      (-1) ^ n * (Real.pi * ((n : ℝ) + 1)) / Real.sinh (Real.pi * ((n : ℝ) + 1)) := by
    have hpipos : 0 < Real.pi * ((n : ℝ) + 1) := by positivity
    field_simp
  rw [hval] at hquot
  refine hquot.congr (fun M => ?_)
  simp only [Pi.div_apply]
  rw [← Finset.prod_div_distrib]

end

end RHTower
