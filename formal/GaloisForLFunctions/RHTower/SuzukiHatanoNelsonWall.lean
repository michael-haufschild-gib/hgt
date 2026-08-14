import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# The exponential orbit weight hits a Hatano--Nelson wall

Conjugating the nearest-neighbour lattice adjacency by the radial exponential weight
`w(n) = e^{-κ|n|}` produces, on the far half-line, the nonreciprocal operator
`e^{κ}S + e^{-κ}S^{-1}`.  Its circle symbol is `2 cosh (κ + iθ)`, whose imaginary part
`2 sinh κ sin θ` is nonzero as soon as `κ > 0`: the spectrum leaves the real line, and the
propagator modulus at the quarter frequency is `e^{2 x sinh κ}`.  Exponential growth beats every
polynomial bound, so an exponential orbit weight never gives polynomial carrier distortion.
-/

open Complex

namespace RHTower

noncomputable section

/-- The Hatano--Nelson circle symbol of the exponentially conjugated adjacency. -/
def hatanoNelsonSymbol (κ θ : ℝ) : ℂ :=
  Complex.exp ((κ : ℂ) + (θ : ℂ) * I) + Complex.exp (-((κ : ℂ) + (θ : ℂ) * I))

theorem hatanoNelsonSymbol_re (κ θ : ℝ) :
    (hatanoNelsonSymbol κ θ).re = 2 * Real.cosh κ * Real.cos θ := by
  have hz : ((κ : ℂ) + (θ : ℂ) * I).re = κ ∧ ((κ : ℂ) + (θ : ℂ) * I).im = θ := by
    constructor <;> simp
  rw [hatanoNelsonSymbol, Complex.add_re, Complex.exp_re, Complex.exp_re, hz.1, hz.2]
  simp only [Complex.neg_re, Complex.neg_im, hz.1, hz.2, Real.cos_neg]
  rw [Real.cosh_eq]
  ring

theorem hatanoNelsonSymbol_im (κ θ : ℝ) :
    (hatanoNelsonSymbol κ θ).im = 2 * Real.sinh κ * Real.sin θ := by
  have hz : ((κ : ℂ) + (θ : ℂ) * I).re = κ ∧ ((κ : ℂ) + (θ : ℂ) * I).im = θ := by
    constructor <;> simp
  rw [hatanoNelsonSymbol, Complex.add_im, Complex.exp_im, Complex.exp_im, hz.1, hz.2]
  simp only [Complex.neg_re, Complex.neg_im, hz.1, hz.2, Real.sin_neg]
  rw [Real.sinh_eq]
  ring

theorem sinh_pos_of_pos {κ : ℝ} (hκ : 0 < κ) : 0 < Real.sinh κ := by
  rw [Real.sinh_eq]
  have h : Real.exp (-κ) < Real.exp κ := Real.exp_lt_exp.mpr (by linarith)
  linarith

/-- **The spectrum leaves the real line.**  A positive exponential weight makes the conjugated
symbol nonreal at the quarter frequency. -/
theorem hatanoNelsonSymbol_im_ne_zero {κ : ℝ} (hκ : 0 < κ) :
    (hatanoNelsonSymbol κ (Real.pi / 2)).im ≠ 0 := by
  rw [hatanoNelsonSymbol_im, Real.sin_pi_div_two, mul_one]
  have hsinh : 0 < Real.sinh κ := sinh_pos_of_pos hκ
  positivity

/-- The propagator modulus at one frequency is the exponential of the symbol's imaginary part. -/
theorem norm_exp_neg_mul_symbol (x κ θ : ℝ) :
    ‖Complex.exp (-((x : ℂ) * I) * hatanoNelsonSymbol κ θ)‖
      = Real.exp (x * (hatanoNelsonSymbol κ θ).im) := by
  rw [Complex.norm_exp]
  congr 1
  simp [Complex.mul_re, Complex.mul_im]

/-- **Exponential growth beats every polynomial bound.** -/
theorem exists_exponential_beats_polynomial {c : ℝ} (hc : 0 < c) (C : ℝ) (m : ℕ) :
    ∃ x : ℝ, 0 < x ∧ C * (1 + x) ^ m < Real.exp (c * x) := by
  have hlim : Filter.Tendsto (fun x : ℝ => (c * x) ^ m * Real.exp (-(c * x)))
      Filter.atTop (nhds 0) := by
    have hcomp : Filter.Tendsto (fun x : ℝ => c * x) Filter.atTop Filter.atTop :=
      Filter.Tendsto.const_mul_atTop hc Filter.tendsto_id
    exact (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero m).comp hcomp
  have hthresh : (0:ℝ) < c ^ m / (2 ^ m * (|C| + 1)) := by positivity
  have hev := hlim.eventually_lt_const hthresh
  obtain ⟨x, hxlt, hx1⟩ := (hev.and (Filter.eventually_ge_atTop (1:ℝ))).exists
  refine ⟨x, by linarith, ?_⟩
  have hx0 : (0:ℝ) < x := by linarith
  have hexp : (0:ℝ) < Real.exp (c * x) := Real.exp_pos _
  have hinv : Real.exp (-(c * x)) = (Real.exp (c * x))⁻¹ := Real.exp_neg _
  have hkey : (c * x) ^ m < c ^ m / (2 ^ m * (|C| + 1)) * Real.exp (c * x) := by
    rw [hinv] at hxlt
    rw [mul_inv_lt_iff₀ hexp] at hxlt
    linarith [hxlt]
  have hpow : (c * x) ^ m = c ^ m * x ^ m := by rw [mul_pow]
  rw [hpow] at hkey
  have hcm : (0:ℝ) < c ^ m := by positivity
  have hxm : x ^ m < Real.exp (c * x) / (2 ^ m * (|C| + 1)) := by
    rw [lt_div_iff₀ (by positivity)]
    have hstep : c ^ m * x ^ m * (2 ^ m * (|C| + 1))
        < c ^ m * Real.exp (c * x) := by
      calc c ^ m * x ^ m * (2 ^ m * (|C| + 1))
          < (c ^ m / (2 ^ m * (|C| + 1)) * Real.exp (c * x)) * (2 ^ m * (|C| + 1)) := by
            apply mul_lt_mul_of_pos_right hkey (by positivity)
        _ = c ^ m * Real.exp (c * x) := by field_simp
    nlinarith [hstep, hcm]
  have hbound : (1 + x) ^ m ≤ 2 ^ m * x ^ m := by
    have h2x : (1 + x) ≤ 2 * x := by linarith
    calc (1 + x) ^ m ≤ (2 * x) ^ m := pow_le_pow_left₀ (by linarith) h2x m
      _ = 2 ^ m * x ^ m := by rw [mul_pow]
  have habs : C ≤ |C| := le_abs_self C
  have hpos2 : (0:ℝ) < 2 ^ m := by positivity
  calc C * (1 + x) ^ m ≤ |C| * (2 ^ m * x ^ m) := by
        have hnn : (0:ℝ) ≤ (1 + x) ^ m := by positivity
        nlinarith [hbound, habs, hnn, abs_nonneg C, pow_nonneg hx0.le m, hpos2]
    _ < Real.exp (c * x) := by
        have hCnn : (0:ℝ) ≤ |C| := abs_nonneg C
        have hfrac : |C| / (|C| + 1) < 1 := by
          rw [div_lt_one (by positivity)]
          linarith
        have hstep := mul_le_mul_of_nonneg_left (le_of_lt hxm)
          (by positivity : (0:ℝ) ≤ |C| * 2 ^ m)
        calc |C| * (2 ^ m * x ^ m) = (|C| * 2 ^ m) * x ^ m := by ring
          _ ≤ (|C| * 2 ^ m) * (Real.exp (c * x) / (2 ^ m * (|C| + 1))) := hstep
          _ = (|C| / (|C| + 1)) * Real.exp (c * x) := by
              field_simp
          _ < 1 * Real.exp (c * x) := mul_lt_mul_of_pos_right hfrac hexp
          _ = Real.exp (c * x) := one_mul _

/-- **The Hatano--Nelson wall.**  For a positive exponential weight the conjugated propagator
modulus at the quarter frequency exceeds every polynomial bound. -/
theorem exists_no_polynomial_bound {κ : ℝ} (hκ : 0 < κ) (C : ℝ) (m : ℕ) :
    ∃ x : ℝ, 0 < x ∧
      C * (1 + x) ^ m
        < ‖Complex.exp (-((x : ℂ) * I) * hatanoNelsonSymbol κ (Real.pi / 2))‖ := by
  have hsinh : 0 < Real.sinh κ := sinh_pos_of_pos hκ
  obtain ⟨x, hx0, hlt⟩ := exists_exponential_beats_polynomial
    (c := 2 * Real.sinh κ) (by positivity) C m
  refine ⟨x, hx0, ?_⟩
  rw [norm_exp_neg_mul_symbol, hatanoNelsonSymbol_im, Real.sin_pi_div_two, mul_one]
  have hval : x * (2 * Real.sinh κ) = 2 * Real.sinh κ * x := by ring
  rw [hval]
  exact hlt

end

end RHTower
