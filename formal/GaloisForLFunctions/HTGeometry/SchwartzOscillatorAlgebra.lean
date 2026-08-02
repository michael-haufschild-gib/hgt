import GaloisForLFunctions.HTGeometry.SchwartzSobolevEstimate

/-!
# Multiplication and differentiation in terms of the oscillator operators

The creation and annihilation operators are `2πx − d/dx` and `2πx + d/dx`, so their sum is `4πx`
and their difference is `2 d/dx`.  Every operator built from multiplication by the coordinate and
differentiation is therefore a polynomial in the creation and annihilation operators.

Commuting the number operator past them costs a multiple of the operator itself — `[N, A] = 4πA`
and `[N, B] = −4πB` — which is what makes the iterated `L²` bounds close up.  Together with the
arithmetic–geometric mean inequality the quadratic `L²` bounds become linear ones.

* `creation_add_annihilation`, `annihilation_sub_creation` : the two combinations.
* `mulXCLM_eq_oscillator`, `derivSCLM_eq_oscillator` : **multiplication and differentiation in
  terms of the oscillator operators.**
* `numberCLM_creationCLM`, `numberCLM_annihilationCLM` : **the commutators.**
* `norm_toLp_creationCLM_le`, `norm_toLp_annihilationCLM_le` : the linear `L²` bounds.
-/

open scoped Real SchwartzMap
open Complex MeasureTheory

noncomputable section

namespace GaloisForLFunctions

/-! ## The two combinations -/

theorem creation_add_annihilation (f : 𝓢(ℝ, ℂ)) :
    creationCLM f + annihilationCLM f = (4 * (π : ℂ)) • mulXCLM f := by
  rw [creationCLM_eq, annihilationCLM_eq]
  module

theorem annihilation_sub_creation (f : 𝓢(ℝ, ℂ)) :
    annihilationCLM f - creationCLM f = (2 : ℂ) • derivSCLM f := by
  rw [creationCLM_eq, annihilationCLM_eq]
  module

theorem four_pi_ne_zero : (4 * (π : ℂ)) ≠ 0 :=
  mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)

/-- **Multiplication by the coordinate is the sum of the oscillator operators.** -/
theorem mulXCLM_eq_oscillator (f : 𝓢(ℝ, ℂ)) :
    mulXCLM f = ((4 * (π : ℂ))⁻¹) • (creationCLM f + annihilationCLM f) := by
  rw [creation_add_annihilation, smul_smul, inv_mul_cancel₀ four_pi_ne_zero, one_smul]

/-- **Differentiation is the difference of the oscillator operators.** -/
theorem derivSCLM_eq_oscillator (f : 𝓢(ℝ, ℂ)) :
    derivSCLM f = ((2 : ℂ)⁻¹) • (annihilationCLM f - creationCLM f) := by
  rw [annihilation_sub_creation, smul_smul, inv_mul_cancel₀ (two_ne_zero : (2 : ℂ) ≠ 0), one_smul]

/-! ## The commutators with the number operator -/

/-- **`[N, A] = 4πA`**: commuting the number operator past a creation operator costs `4π`. -/
theorem numberCLM_creationCLM (f : 𝓢(ℝ, ℂ)) :
    numberCLM (creationCLM f) = creationCLM (numberCLM f) + (4 * (π : ℂ)) • creationCLM f := by
  have hcomm := annihilationCLM_creationCLM_sub f
  rw [sub_eq_iff_eq_add] at hcomm
  rw [numberCLM_apply, hcomm, map_add, map_smul, numberCLM_apply]
  abel

/-- **`[N, B] = −4πB`**: commuting the number operator past an annihilation operator gains
`4π`. -/
theorem numberCLM_annihilationCLM (f : 𝓢(ℝ, ℂ)) :
    numberCLM (annihilationCLM f) + (4 * (π : ℂ)) • annihilationCLM f
      = annihilationCLM (numberCLM f) := by
  have hcomm := annihilationCLM_creationCLM_sub (annihilationCLM f)
  rw [numberCLM_apply, numberCLM_apply]
  rw [sub_eq_iff_eq_add] at hcomm
  rw [hcomm]
  abel

/-! ## The linear form of the `L²` bounds -/

theorem le_half_add_of_sq_le_mul {x a b : ℝ} (_hx : 0 ≤ x) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : x ^ 2 ≤ a * b) : x ≤ (a + b) / 2 := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (x - (a + b) / 2)]

/-- The linear `L²` bound for the creation operator. -/
theorem norm_toLp_creationCLM_le (g : 𝓢(ℝ, ℂ)) :
    ‖(creationCLM g).toLp 2 (volume : Measure ℝ)‖
      ≤ (‖g.toLp 2 (volume : Measure ℝ)‖
        + ‖(numberCLM g + (4 * (π : ℂ)) • g).toLp 2 (volume : Measure ℝ)‖) / 2 :=
  le_half_add_of_sq_le_mul (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
    (norm_toLp_creationCLM_sq_le g)

/-- The linear `L²` bound for the annihilation operator. -/
theorem norm_toLp_annihilationCLM_le (g : 𝓢(ℝ, ℂ)) :
    ‖(annihilationCLM g).toLp 2 (volume : Measure ℝ)‖
      ≤ (‖g.toLp 2 (volume : Measure ℝ)‖
        + ‖(numberCLM g).toLp 2 (volume : Measure ℝ)‖) / 2 :=
  le_half_add_of_sq_le_mul (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
    (norm_toLp_annihilationCLM_sq_le g)

end GaloisForLFunctions

end
