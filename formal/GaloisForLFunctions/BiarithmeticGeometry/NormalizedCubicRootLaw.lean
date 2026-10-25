import GaloisForLFunctions.BiarithmeticGeometry.NormalizedCubicTrace
import Mathlib.Analysis.Complex.Basic

/-!
# Root and point-count laws for fixed-determinant cubing

Newton's identities read normalized cubing directly on a reciprocal root
pair. The product is preserved, the normalized roots are cubed, and the
second point count is the exact square-trace bound used in the integral
classification. These laws distinguish determinant preservation from
preservation of arithmetic integrality and positive point counts.
-/

namespace GaloisForLFunctions.BiarithmeticGeometry

section Field
variable {K : Type*} [Field K]

/-- Cubing a reciprocal root while retaining its pair's determinant scale. -/
def normalizedCubicRoot (p z : K) : K := z ^ 3 / p

/-- The root product is preserved, including the zero-determinant algebraic endpoint. -/
theorem normalizedCubicRoot_product (a b p : K) (hab : a * b = p) :
    normalizedCubicRoot p a * normalizedCubicRoot p b = p := by
  rw [normalizedCubicRoot, normalizedCubicRoot, div_mul_div_comm, ← mul_pow, hab]
  by_cases hp : p = 0
  · simp [hp]
  · field_simp [hp] <;> ring

/-- Newton's cubic identity gives the transformed root trace exactly. -/
theorem normalizedCubicRoot_trace (a b p : K) (hab : a * b = p) :
    normalizedCubicRoot p a + normalizedCubicRoot p b =
      ((a + b) ^ 3 - 3 * p * (a + b)) / p := by
  rw [normalizedCubicRoot, normalizedCubicRoot, ← add_div, ← hab]
  congr 1
  ring

/-- After dividing by a square-root scale, normalized cubing is ordinary cubing. -/
theorem normalizedCubicRoot_scaled (r z : K) :
    normalizedCubicRoot (r ^ 2) z / r = (z / r) ^ 3 := by
  rw [normalizedCubicRoot, div_div, ← pow_succ, div_pow]

/-- The second point count is precisely the determinant square minus the trace square. -/
theorem secondPointCount_trace_identity (a b p : K) (hab : a * b = p) :
    p ^ 2 + 1 - (a ^ 2 + b ^ 2) = (p + 1) ^ 2 - (a + b) ^ 2 := by
  rw [← hab]
  ring

end Field

/-- Actual reciprocal roots with integral traces satisfy the exact integer trace equation. -/
theorem normalizedCubicRoot_integral_trace_equation {p : ℕ} (hp : p.Prime)
    (a b : ℝ) (T U : ℤ) (hab : a * b = (p : ℝ))
    (hT : a + b = (T : ℝ))
    (hU : normalizedCubicRoot (p : ℝ) a + normalizedCubicRoot (p : ℝ) b = (U : ℝ)) :
    (p : ℤ) * U = T ^ 3 - 3 * p * T := by
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have h := normalizedCubicRoot_trace a b (p : ℝ) hab
  rw [hT, hU] at h
  have he := (eq_div_iff hpR).mp h
  have he' : (p : ℝ) * (U : ℝ) = (T : ℝ) ^ 3 - 3 * (p : ℝ) * (T : ℝ) := by
    simpa only [mul_comm (U : ℝ) (p : ℝ)] using he
  exact_mod_cast he'

/-- The abstract integral classification applies to actual nonnegative second point counts. -/
theorem normalizedCubicTraceCondition_iff_rootPointCounts {p : ℕ} (hp : p.Prime)
    (a b : ℝ) (T U : ℤ) (hab : a * b = (p : ℝ))
    (hT : a + b = (T : ℝ))
    (hU : normalizedCubicRoot (p : ℝ) a + normalizedCubicRoot (p : ℝ) b = (U : ℝ)) :
    NormalizedCubicTraceCondition p T U ↔
      0 ≤ (p : ℝ) ^ 2 + 1 - (a ^ 2 + b ^ 2) ∧
      0 ≤ (p : ℝ) ^ 2 + 1 -
        (normalizedCubicRoot (p : ℝ) a ^ 2 + normalizedCubicRoot (p : ℝ) b ^ 2) := by
  rw [secondPointCount_trace_identity a b (p : ℝ) hab,
    secondPointCount_trace_identity _ _ (p : ℝ) (normalizedCubicRoot_product a b _ hab), hT, hU]
  have he := normalizedCubicRoot_integral_trace_equation hp a b T U hab hT hU
  change ((p : ℤ) * U = T ^ 3 - 3 * p * T ∧
    T ^ 2 ≤ ((p : ℤ) + 1) ^ 2 ∧ U ^ 2 ≤ ((p : ℤ) + 1) ^ 2) ↔ _
  constructor
  · intro h
    constructor
    · have hT' : (T : ℝ) ^ 2 ≤ ((p : ℝ) + 1) ^ 2 := by exact_mod_cast h.2.1
      exact sub_nonneg.mpr hT'
    · have hU' : (U : ℝ) ^ 2 ≤ ((p : ℝ) + 1) ^ 2 := by exact_mod_cast h.2.2
      exact sub_nonneg.mpr hU'
  · intro h
    refine ⟨he, ?_, ?_⟩
    · exact_mod_cast sub_nonneg.mp h.1
    · exact_mod_cast sub_nonneg.mp h.2

/-- Complex reciprocal roots with integral traces satisfy the same integer trace equation. -/
theorem normalizedCubicRoot_complex_integral_trace_equation {p : ℕ} (hp : p.Prime)
    (a b : ℂ) (T U : ℤ) (hab : a * b = (p : ℂ))
    (hT : a + b = (T : ℂ))
    (hU : normalizedCubicRoot (p : ℂ) a + normalizedCubicRoot (p : ℂ) b = (U : ℂ)) :
    (p : ℤ) * U = T ^ 3 - 3 * p * T := by
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have h := normalizedCubicRoot_trace a b (p : ℂ) hab
  rw [hT, hU] at h
  have he := (eq_div_iff hpC).mp h
  have he' : (p : ℂ) * (U : ℂ) = (T : ℂ) ^ 3 - 3 * (p : ℂ) * (T : ℂ) := by
    simpa only [mul_comm (U : ℂ) (p : ℂ)] using he
  exact_mod_cast he'

/-- Integral trace makes the complex second point count exactly a real integer. -/
theorem secondPointCount_complex_integral_trace (a b : ℂ) (p : ℕ) (T : ℤ)
    (hab : a * b = (p : ℂ)) (hT : a + b = (T : ℂ)) :
    (p : ℂ) ^ 2 + 1 - (a ^ 2 + b ^ 2) =
      ((((p : ℤ) + 1) ^ 2 - T ^ 2 : ℤ) : ℂ) := by
  rw [secondPointCount_trace_identity a b (p : ℂ) hab, hT]
  push_cast <;> rfl

/-- The positive-count classification applies to arbitrary complex reciprocal root pairs. -/
theorem normalizedCubicTraceCondition_iff_complexRootPointCounts {p : ℕ} (hp : p.Prime)
    (a b : ℂ) (T U : ℤ) (hab : a * b = (p : ℂ))
    (hT : a + b = (T : ℂ))
    (hU : normalizedCubicRoot (p : ℂ) a + normalizedCubicRoot (p : ℂ) b = (U : ℂ)) :
    NormalizedCubicTraceCondition p T U ↔
      0 ≤ ((p : ℂ) ^ 2 + 1 - (a ^ 2 + b ^ 2)).re ∧
      0 ≤ ((p : ℂ) ^ 2 + 1 -
        (normalizedCubicRoot (p : ℂ) a ^ 2 + normalizedCubicRoot (p : ℂ) b ^ 2)).re := by
  rw [secondPointCount_complex_integral_trace a b p T hab hT,
    secondPointCount_complex_integral_trace _ _ p U (normalizedCubicRoot_product a b _ hab) hU]
  have he := normalizedCubicRoot_complex_integral_trace_equation hp a b T U hab hT hU
  change ((p : ℤ) * U = T ^ 3 - 3 * p * T ∧
    T ^ 2 ≤ ((p : ℤ) + 1) ^ 2 ∧ U ^ 2 ≤ ((p : ℤ) + 1) ^ 2) ↔ _
  constructor
  · intro h
    constructor
    · exact_mod_cast sub_nonneg.mpr h.2.1
    · exact_mod_cast sub_nonneg.mpr h.2.2
  · intro h
    refine ⟨he, ?_, ?_⟩
    · have hz : (0 : ℤ) ≤ ((p : ℤ) + 1) ^ 2 - T ^ 2 := by exact_mod_cast h.1
      exact sub_nonneg.mp hz
    · have hz : (0 : ℤ) ≤ ((p : ℤ) + 1) ^ 2 - U ^ 2 := by exact_mod_cast h.2
      exact sub_nonneg.mp hz

/-- A reciprocal pair with real trace in the square-root interval has equal norm squares. -/
theorem complex_reciprocal_norm_sq_of_trace_bound (a b : ℂ) (p T : ℝ)
    (hab : a * b = (p : ℂ)) (hT : a + b = (T : ℂ)) (hbound : T ^ 2 ≤ 4 * p) :
    ‖a‖ ^ 2 = p ∧ ‖b‖ ^ 2 = p := by
  have hsumRe : a.re + b.re = T := by
    simpa only [Complex.add_re, Complex.ofReal_re] using congrArg Complex.re hT
  have hsumIm : a.im + b.im = 0 := by
    simpa only [Complex.add_im, Complex.ofReal_im] using congrArg Complex.im hT
  have hprodRe : a.re * b.re - a.im * b.im = p := by
    simpa only [Complex.mul_re, Complex.ofReal_re] using congrArg Complex.re hab
  have hprodIm : a.re * b.im + a.im * b.re = 0 := by
    simpa only [Complex.mul_im, Complex.ofReal_im] using congrArg Complex.im hab
  have him : b.im = -a.im := by linarith only [hsumIm]
  rw [him] at hprodRe hprodIm
  have hreal : a.re = b.re := by
    by_cases hy : a.im = 0
    · rw [hy] at hprodRe
      rw [← hsumRe] at hbound
      nlinarith only [hprodRe, hbound, sq_nonneg (a.re - b.re)]
    · have hz : a.im * (b.re - a.re) = 0 := by nlinarith only [hprodIm]
      exact (sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left hy)).symm
  rw [← hreal] at hprodRe
  constructor
  · rw [Complex.sq_norm, Complex.normSq_apply]
    nlinarith only [hprodRe]
  · rw [Complex.sq_norm, Complex.normSq_apply, ← hreal, him]
    nlinarith only [hprodRe]

/-- Every integral positive-count survivor consists of roots on the square-root circle. -/
theorem normalizedCubicRoot_survivor_pure {p : ℕ} (hp : p.Prime)
    (a b : ℂ) (T U : ℤ) (hab : a * b = (p : ℂ))
    (hT : a + b = (T : ℂ))
    (hU : normalizedCubicRoot (p : ℂ) a + normalizedCubicRoot (p : ℂ) b = (U : ℂ))
    (hcounts : 0 ≤ ((p : ℂ) ^ 2 + 1 - (a ^ 2 + b ^ 2)).re ∧
      0 ≤ ((p : ℂ) ^ 2 + 1 -
        (normalizedCubicRoot (p : ℂ) a ^ 2 + normalizedCubicRoot (p : ℂ) b ^ 2)).re) :
    ‖a‖ = Real.sqrt p ∧ ‖b‖ = Real.sqrt p := by
  have hcondition :=
    (normalizedCubicTraceCondition_iff_complexRootPointCounts hp a b T U hab hT hU).mpr hcounts
  have hbound : (T : ℝ) ^ 2 ≤ 4 * (p : ℝ) := by
    exact_mod_cast normalizedCubicTrace_pure_bound hp hcondition
  have hprod : a * b = ((p : ℝ) : ℂ) := by exact_mod_cast hab
  have htrace : a + b = ((T : ℝ) : ℂ) := by exact_mod_cast hT
  obtain ⟨ha, hb⟩ := complex_reciprocal_norm_sq_of_trace_bound a b p T hprod htrace hbound
  constructor
  · simpa only [Real.sqrt_sq (norm_nonneg a)] using congrArg Real.sqrt ha
  · simpa only [Real.sqrt_sq (norm_nonneg b)] using congrArg Real.sqrt hb

end GaloisForLFunctions.BiarithmeticGeometry

