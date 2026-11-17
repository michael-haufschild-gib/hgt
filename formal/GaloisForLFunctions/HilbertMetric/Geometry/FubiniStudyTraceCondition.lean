import GaloisForLFunctions.HilbertMetric.Geometry.FubiniStudyPotential

/-!
# The Fubini–Study trace condition

Polarizing the actual Levi form gives a Hermitian metric. Its signed trace
excess over the imaginary pairing is exactly the Levi energy of the
antiholomorphic tangent combination. Strict Levi positivity identifies
the equality case without a coordinate or dimension restriction.
-/

noncomputable section
open scoped ComplexConjugate
namespace GaloisForLFunctions.HilbertMetric.FubiniStudy
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The Hermitian form whose real diagonal is the actual Levi quadratic form. -/
def hermitian (z v w : E) : ℂ :=
  inner ℂ v w / (denominator z : ℂ) -
    inner ℂ v z * inner ℂ z w / (denominator z : ℂ) ^ 2

theorem hermitian_add_left (z u v w : E) :
    hermitian z (u + v) w = hermitian z u w + hermitian z v w := by
  simp only [hermitian, inner_add_left]
  ring

theorem hermitian_add_right (z u v w : E) :
    hermitian z u (v + w) = hermitian z u v + hermitian z u w := by
  simp only [hermitian, inner_add_right]
  ring

theorem hermitian_smul_left (z v w : E) (c : ℂ) :
    hermitian z (c • v) w = conj c * hermitian z v w := by
  simp only [hermitian, inner_smul_left]
  ring

theorem hermitian_smul_right (z v w : E) (c : ℂ) :
    hermitian z v (c • w) = c * hermitian z v w := by
  simp only [hermitian, inner_smul_right]
  ring

/-- Conjugate symmetry of the affine projective metric. -/
theorem hermitian_conj (z v w : E) : conj (hermitian z v w) = hermitian z w v := by
  simp only [hermitian, map_sub, map_div₀, map_mul, map_pow, Complex.conj_ofReal,
    inner_conj_symm]
  ring

/-- The metric is the complex polarization of the differentiated Kähler potential. -/
theorem hermitian_self (z v : E) : hermitian z v v = (levi z v : ℂ) := by
  have hv : inner ℂ v v = ((‖v‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]
    change (‖v‖ : ℂ) ^ 2 = ((‖v‖ ^ 2 : ℝ) : ℂ)
    rw [Complex.ofReal_pow]
  have hp : inner ℂ v z * inner ℂ z v = ((‖inner ℂ z v‖ ^ 2 : ℝ) : ℂ) := by
    rw [← inner_conj_symm v z, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
  rw [hermitian, hv, hp, levi_formula]
  simp only [Complex.ofReal_sub, Complex.ofReal_div, Complex.ofReal_pow]

/-- Complex scaling acts quadratically on the Levi energy. -/
theorem levi_smul (z v : E) (c : ℂ) : levi z (c • v) = ‖c‖ ^ 2 * levi z v := by
  simp only [levi_formula, norm_smul, inner_smul_right, norm_mul, mul_pow]
  ring

/-- The Levi form vanishes exactly on the zero tangent. -/
theorem levi_eq_zero_iff (z v : E) : levi z v = 0 ↔ v = 0 := by
  constructor
  · intro h
    by_contra hv
    exact ((levi_pos_iff z v).mpr hv).ne' h
  · rintro rfl
    simp only [levi_formula, norm_zero, inner_zero_right,
      zero_pow (by decide : 2 ≠ 0), zero_div, sub_zero]

/-- Signed trace excess of the quantum metric over its curvature component. -/
def traceDefect (z v w : E) : ℝ := levi z v + levi z w - 2 * (hermitian z v w).im

/-- The quantum-metric trace defect is exactly the antiholomorphic tangent energy. -/
theorem traceDefect_eq_levi (z v w : E) : traceDefect z v w = levi z (v + Complex.I • w) := by
  have h := congrArg Complex.re (hermitian_self z (v + Complex.I • w))
  rw [hermitian_add_left, hermitian_add_right, hermitian_add_right,
    hermitian_smul_left, hermitian_smul_right, hermitian_smul_left,
    hermitian_smul_right, ← hermitian_conj z v w, hermitian_self, hermitian_self] at h
  simp only [Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, mul_zero, one_mul, zero_add, sub_zero, zero_sub] at h
  unfold traceDefect
  linarith only [h]

/-- The ideal-geometry trace inequality follows from strict Levi positivity. -/
theorem traceDefect_nonneg (z v w : E) : 0 ≤ traceDefect z v w := by
  rw [traceDefect_eq_levi]
  exact (div_nonneg (sq_nonneg _) (sq_nonneg _)).trans (levi_lower_bound z _)

/-- Saturation of the trace inequality is the Cauchy–Riemann tangent relation. -/
theorem traceDefect_eq_zero_iff (z v w : E) :
    traceDefect z v w = 0 ↔ v + Complex.I • w = 0 := by
  rw [traceDefect_eq_levi, levi_eq_zero_iff]

#print axioms hermitian_self
#print axioms levi_smul
#print axioms levi_eq_zero_iff
#print axioms traceDefect_eq_levi
#print axioms traceDefect_nonneg
#print axioms traceDefect_eq_zero_iff
end GaloisForLFunctions.HilbertMetric.FubiniStudy
