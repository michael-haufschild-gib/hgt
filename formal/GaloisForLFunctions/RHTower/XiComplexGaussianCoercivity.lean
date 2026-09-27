import GaloisForLFunctions.RHTower.XiComplexGaussianSampling
import GaloisForLFunctions.RHTower.XiRealAxisGaussianCoercivity
import GaloisForLFunctions.HTGeometry.GaussianPolynomialParabolicDefect

/-!
# Coefficient-uniform relative floor for the full complex Xi Gaussian energy

Actual zero-window sampling and the simultaneous discrete strip estimate give
an independent lower bound for the complete complex energy. Degree-normalized
scaling gives a common positive margin for every polynomial. No assumption
that Xi spectral points are real, and no phase-debt positivity premise, occurs.
-/

open scoped Real SchwartzMap NNReal
open MeasureTheory Filter Topology GaloisForLFunctions
noncomputable section

namespace RHTower

/-- The full complex energy has an independent relative floor retaining every polynomial coupling. -/
theorem exists_xiScaledEvenGaussian_relative_floor :
    ∃ h : ℝ, 0 < h ∧ ∃ C : ℝ, 0 < C ∧
      ∀ (P : Polynomial ℝ) (r : {r : ℝ // 0 < r}),
        (1 / 4 - C * (r : ℝ) * Real.sqrt (((2 * P.natDegree : ℕ) : ℝ) + 1) -
          (1 + 2 * ((r : ℝ) * h) * Real.sqrt (4 * Real.pi * (((2 * P.natDegree : ℕ) : ℝ) + 2))) *
            verticalPolynomialGaussianDefect (2 * P.natDegree) ((r : ℝ) / 2) ^ 2) *
          ‖(polyGaussSchwartz (evenSquarePolynomial P)).toLp 2 (volume : Measure ℝ)‖ ^ 2 ≤
            ((r : ℝ) * h) * xiScaledEvenGaussianEnergy P r := by
  obtain ⟨a, ha, h, hh, hsample⟩ := exists_xiComplexGaussian_halfLine_sampling_bound
  refine ⟨h, hh, 9 * a / 2 + h * Real.sqrt (4 * Real.pi), by positivity, ?_⟩
  intro P r
  have hlow := evenPolynomialGaussian_tail_energy_lower P
    (⟨(r : ℝ) * a, (mul_pos r.property ha).le⟩ : ℝ≥0)
  have hupp := hsample P r
  rw [natDegree_evenSquarePolynomial] at hupp
  rw [Real.sqrt_mul (by positivity : 0 ≤ 4 * Real.pi)] at hupp
  change (1 / 2 - 9 * ((r : ℝ) * a) * Real.sqrt (((2 * P.natDegree : ℕ) : ℝ) + 1)) *
      ‖(polyGaussSchwartz (evenSquarePolynomial P)).toLp 2 (volume : Measure ℝ)‖ ^ 2 ≤
    ∫ x : ℝ in Set.Ioi ((r : ℝ) * a), ‖polyGaussSchwartz (evenSquarePolynomial P) x‖ ^ 2 at hlow
  nlinarith only [hlow, hupp]

/-- One common degree-normalized region gives a positive floor for complete complex Xi energy. -/
theorem exists_eventually_forall_xiScaledEvenGaussian_parabolic_floor :
    ∃ h : ℝ, 0 < h ∧ ∀ᶠ τ : ℝ in atBot, ∀ P : Polynomial ℝ,
      (1 / 8 : ℝ) *
          ‖(polyGaussSchwartz (evenSquarePolynomial P)).toLp 2 (volume : Measure ℝ)‖ ^ 2 ≤
        ((xiGaussianParabolicScale P τ : ℝ) * h) *
          xiScaledEvenGaussianEnergy P (xiGaussianParabolicScale P τ) := by
  obtain ⟨h, hh, C, hC, hfloor⟩ := exists_xiScaledEvenGaussian_relative_floor
  refine ⟨h, hh, ?_⟩
  let G : ℝ → ℝ := fun u => C * u +
    (1 + 4 * h * Real.sqrt (4 * Real.pi) * u) * parabolicGaussianDefect (u / 2) ^ 2
  have hcont : Continuous G := by
    unfold G parabolicGaussianDefect
    fun_prop
  have hzero : G 0 = 0 := by simp [G, parabolicGaussianDefect]
  have ht : Tendsto (fun τ : ℝ => G (Real.exp τ)) atBot (𝓝 0) := by
    simpa only [hzero, Function.comp_def] using hcont.continuousAt.tendsto.comp Real.tendsto_exp_atBot
  have he := ht.eventually (eventually_lt_nhds (by positivity : (0 : ℝ) < 1 / 8))
  filter_upwards [he] with τ hτ P
  let d := 2 * P.natDegree
  let r := xiGaussianParabolicScale P τ
  let u := Real.exp τ
  let v := Real.sqrt ((d : ℝ) + 1)
  let A := Real.sqrt (4 * Real.pi)
  have hv : 0 < v := Real.sqrt_pos.mpr (by positivity)
  have hu : 0 < u := Real.exp_pos _
  have hr : (r : ℝ) = u / v := rfl
  have hrpos : 0 < (r : ℝ) := r.property
  have hscale : C * (r : ℝ) * v = C * u := by
    rw [hr, mul_assoc, div_mul_cancel₀ _ hv.ne']
  have hsqrt : Real.sqrt ((d : ℝ) + 2) ≤ 2 * v := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
    rw [Real.sq_sqrt (by positivity), mul_pow]
    have hv2 : v ^ 2 = (d : ℝ) + 1 := Real.sq_sqrt (by positivity)
    rw [hv2]
    have hd := Nat.cast_nonneg (α := ℝ) d
    nlinarith only [hd]
  have hfactor : 1 + 2 * ((r : ℝ) * h) * Real.sqrt (4 * Real.pi * ((d : ℝ) + 2)) ≤
      1 + 4 * h * A * u := by
    rw [Real.sqrt_mul (by positivity : 0 ≤ 4 * Real.pi)]
    have hs := mul_le_mul_of_nonneg_left hsqrt
      (show 0 ≤ 2 * ((r : ℝ) * h) * A by positivity)
    have hcancel : 2 * ((r : ℝ) * h) * A * (2 * v) = 4 * h * A * u := by
      rw [hr]
      field_simp
      ring
    rw [hcancel] at hs
    nlinarith only [hs]
  have herr : verticalPolynomialGaussianDefect d ((r : ℝ) / 2) ≤
      parabolicGaussianDefect (u / 2) := by
    have hid : (r : ℝ) / 2 = (u / 2) / v := by rw [hr]; ring
    rw [hid]
    exact verticalPolynomialGaussianDefect_parabolic_le d (u / 2)
  have herr0 : 0 ≤ verticalPolynomialGaussianDefect d ((r : ℝ) / 2) := by
    have h1 : 0 ≤ Real.exp (Real.pi * ((r : ℝ) / 2) ^ 2) - 1 :=
      sub_nonneg.mpr (Real.one_le_exp (by positivity))
    have h2 : 0 ≤ Real.exp (|(r : ℝ) / 2| * Real.sqrt (4 * Real.pi * d)) - 1 :=
      sub_nonneg.mpr (Real.one_le_exp (by positivity))
    unfold verticalPolynomialGaussianDefect
    exact add_nonneg (mul_nonneg (Real.exp_pos _).le
      (add_nonneg h2 (mul_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)))) h1
  have herrsq := pow_le_pow_left₀ herr0 herr 2
  have herror := mul_le_mul hfactor herrsq (sq_nonneg _)
    (show 0 ≤ 1 + 4 * h * A * u by positivity)
  have hfull := hfloor P r
  change (1 / 4 - C * (r : ℝ) * v -
      (1 + 2 * ((r : ℝ) * h) * Real.sqrt (4 * Real.pi * ((d : ℝ) + 2))) *
        verticalPolynomialGaussianDefect d ((r : ℝ) / 2) ^ 2) *
      ‖(polyGaussSchwartz (evenSquarePolynomial P)).toLp 2 (volume : Measure ℝ)‖ ^ 2 ≤
        ((r : ℝ) * h) * xiScaledEvenGaussianEnergy P r at hfull
  rw [hscale] at hfull
  have hsmall : C * u +
      (1 + 2 * ((r : ℝ) * h) * Real.sqrt (4 * Real.pi * ((d : ℝ) + 2))) *
        verticalPolynomialGaussianDefect d ((r : ℝ) / 2) ^ 2 ≤ 1 / 8 := by
    change C * u + (1 + 4 * h * A * u) * parabolicGaussianDefect (u / 2) ^ 2 < 1 / 8 at hτ
    linarith only [hτ, herror]
  have hm := mul_le_mul_of_nonneg_right hsmall
    (sq_nonneg ‖(polyGaussSchwartz (evenSquarePolynomial P)).toLp 2 (volume : Measure ℝ)‖)
  nlinarith only [hfull, hm]

end RHTower
