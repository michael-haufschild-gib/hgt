import GaloisForLFunctions.HilbertMetric.Geometry.FubiniStudyScaling
import GaloisForLFunctions.HilbertMetric.Geometry.FubiniStudyMatrix
import GaloisForLFunctions.HilbertMetric.Geometry.RadialKahlerLogistic

/-!
# Explicit radial Kähler–Einstein solutions

Dilated logarithmic projective potentials vanish on the unit sphere.
Their differentiated Levi matrices are positive and satisfy the exact
Monge–Ampère equation. Below the maximal parameter, the explicit radial
family has exactly two distinct potentials, distinguished at the center.
-/

noncomputable section
open scoped BigOperators ComplexConjugate ComplexOrder
namespace GaloisForLFunctions.HilbertMetric.RadialKahler
open FubiniStudy

abbrev Coordinate (n : ℕ) := EuclideanSpace ℂ (Fin (n + 1))
local instance (n : ℕ) : InnerProductSpace ℝ (Coordinate n) :=
  InnerProductSpace.rclikeToReal ℂ (Coordinate n)

/-- The normalized radial Kähler potential in positive logarithmic scale. -/
def solution (n : ℕ) (t : ℝ) (z : Coordinate n) : ℝ :=
  (n + 2) * (dilatedPotential (Real.exp t) z - Real.log (1 + Real.exp (2 * t)))

private theorem exp_sq (t : ℝ) : Real.exp t ^ 2 = Real.exp (2 * t) := by
  rw [pow_two, ← Real.exp_add, ← two_mul]

/-- The radial denominator is computed from the actual norm of the dilated coordinate. -/
theorem solution_denominator (n : ℕ) (t : ℝ) (z : Coordinate n) :
    denominator (Real.exp t • z) = 1 + Real.exp (2 * t) * ‖z‖ ^ 2 := by
  rw [denominator, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos t), mul_pow, exp_sq]

private theorem solution_hasFDerivAt (n : ℕ) (t : ℝ) (z : Coordinate n) :
    HasFDerivAt (solution n t)
      ((n + 2 : ℝ) • fderiv ℝ (dilatedPotential (Real.exp t)) z) z :=
  (((hasFDerivAt_dilatedPotential (Real.exp t) z).differentiableAt.hasFDerivAt).sub_const
    (Real.log (1 + Real.exp (2 * t)))).const_mul (n + 2 : ℝ)

/-- First directional derivative of the normalized radial solution. -/
theorem fderiv_solution_apply (n : ℕ) (t : ℝ) (z v : Coordinate n) :
    fderiv ℝ (solution n t) z v =
      (n + 2) * fderiv ℝ (dilatedPotential (Real.exp t)) z v := by
  rw [(solution_hasFDerivAt n t z).fderiv]
  rfl

/-- The actual second derivative of the radial solution. -/
def solutionHessian (n : ℕ) (t : ℝ) (z x y : Coordinate n) : ℝ :=
  fderiv ℝ (fun w : Coordinate n => fderiv ℝ (solution n t) w x) z y

/-- Normalization scales the actual Hessian by the complex dimension plus one. -/
theorem solutionHessian_eq (n : ℕ) (t : ℝ) (z x y : Coordinate n) :
    solutionHessian n t z x y = (n + 2) * dilatedHessian (Real.exp t) z x y := by
  have h := (differentiableAt_dilatedPotential_direction (Real.exp t) z x).hasFDerivAt.const_mul
    (n + 2 : ℝ)
  unfold solutionHessian
  simp_rw [fderiv_solution_apply]
  rw [h.fderiv]
  rfl

/-- Levi energy extracted from the actual radial solution derivatives. -/
def solutionLevi (n : ℕ) (t : ℝ) (z v : Coordinate n) : ℝ :=
  (solutionHessian n t z v v +
    solutionHessian n t z (Complex.I • v) (Complex.I • v)) / 4

/-- The differentiated radial solution has the scaled Fubini–Study Levi metric. -/
theorem solutionLevi_eq (n : ℕ) (t : ℝ) (z v : Coordinate n) :
    solutionLevi n t z v =
      (n + 2) * Real.exp (2 * t) * levi (Real.exp t • z) v := by
  have h := dilatedLevi_scale (Real.exp t) z v
  rw [exp_sq] at h
  rw [solutionLevi, solutionHessian_eq, solutionHessian_eq]
  calc
    _ = (n + 2 : ℝ) * dilatedLevi (Real.exp t) z v := by
      rw [dilatedLevi]
      ring
    _ = _ := by rw [h]; ring

/-- Strict plurisubharmonicity holds at every finite point and every positive radial scale. -/
theorem solutionLevi_pos_iff (n : ℕ) (t : ℝ) (z v : Coordinate n) :
    0 < solutionLevi n t z v ↔ v ≠ 0 := by
  rw [solutionLevi_eq, mul_pos_iff_of_pos_left
    (mul_pos (by positivity : (0 : ℝ) < n + 2) (Real.exp_pos _)), levi_pos_iff]

/-- The Hermitian matrix representing the actual radial Levi form. -/
def solutionMatrix (n : ℕ) (t : ℝ) (z : Coordinate n) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  (((n + 2) * Real.exp (2 * t) : ℝ) : ℂ) • metricMatrix (Real.exp t • z)

/-- Matrix quadratic evaluation agrees with the actual differentiated Levi energy. -/
theorem solutionMatrix_quadratic (n : ℕ) (t : ℝ) (z v : Coordinate n) :
    (fun i => conj (v i)) ⬝ᵥ (solutionMatrix n t z *ᵥ (fun i => v i)) =
      (solutionLevi n t z v : ℂ) := by
  have he : (fun i => conj (v i)) ⬝ᵥ (solutionMatrix n t z *ᵥ (fun i => v i)) =
      (((n + 2) * Real.exp (2 * t) : ℝ) : ℂ) *
        ((fun i => conj (v i)) ⬝ᵥ (metricMatrix (Real.exp t • z) *ᵥ (fun i => v i))) := by
    simp only [solutionMatrix, dotProduct, Matrix.mulVec, Matrix.smul_apply, smul_eq_mul]
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he, metricMatrix_quadratic, solutionLevi_eq]
  simp only [Complex.ofReal_mul]
  ring

/-- The determinant of the differentiated radial metric has its exact closed density. -/
theorem det_solutionMatrix (n : ℕ) (t : ℝ) (z : Coordinate n) :
    (solutionMatrix n t z).det =
      (((n + 2 : ℝ) ^ (n + 1) * Real.exp (2 * t) ^ (n + 1) /
        denominator (Real.exp t • z) ^ (n + 2) : ℝ) : ℂ) := by
  rw [solutionMatrix, Matrix.det_smul, det_metricMatrix]
  simp only [Fintype.card_fin, Complex.ofReal_div, Complex.ofReal_mul,
    Complex.ofReal_pow, Complex.ofReal_one, mul_pow, mul_one_div]

/-- The zero set of the normalized potential is exactly the unit sphere. -/
theorem solution_eq_zero_iff (n : ℕ) (t : ℝ) (z : Coordinate n) :
    solution n t z = 0 ↔ ‖z‖ = 1 := by
  constructor
  · intro h
    have hn : (n + 2 : ℝ) ≠ 0 := by positivity
    have hl : Real.log (denominator (Real.exp t • z)) =
        Real.log (1 + Real.exp (2 * t)) := by
      exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_left hn)
    have he := congrArg Real.exp hl
    rw [Real.exp_log (denominator_pos _), Real.exp_log (by positivity),
      solution_denominator] at he
    have hs : Real.exp (2 * t) * ‖z‖ ^ 2 = Real.exp (2 * t) * 1 := by
      linarith only [he]
    have hsq := mul_left_cancel₀ (Real.exp_ne_zero (2 * t)) hs
    have hz := norm_nonneg z
    nlinarith only [hsq, hz]
  · intro h
    rw [solution, dilatedPotential, potential, solution_denominator, h,
      one_pow, mul_one, sub_self, mul_zero]

/-- Exponentiating the normalized potential gives the exact radial density ratio. -/
theorem exp_neg_solution (n : ℕ) (t : ℝ) (z : Coordinate n) :
    Real.exp (-solution n t z) =
      (1 + Real.exp (2 * t)) ^ (n + 2) / denominator (Real.exp t • z) ^ (n + 2) := by
  have hb : 0 < 1 + Real.exp (2 * t) := by positivity
  have hd := denominator_pos (Real.exp t • z)
  have he (m : ℕ) : Real.exp ((m : ℝ) *
      (Real.log (1 + Real.exp (2 * t)) - Real.log (denominator (Real.exp t • z)))) =
        ((1 + Real.exp (2 * t)) / denominator (Real.exp t • z)) ^ m := by
    induction m with
    | zero => simp only [Nat.cast_zero, zero_mul, Real.exp_zero, pow_zero]
    | succ m hm =>
      rw [Nat.cast_succ, add_mul, one_mul, Real.exp_add, hm,
        Real.exp_sub, Real.exp_log hb, Real.exp_log hd, pow_succ]
  have ha : -solution n t z = ((n + 2 : ℕ) : ℝ) *
      (Real.log (1 + Real.exp (2 * t)) - Real.log (denominator (Real.exp t • z))) := by
    simp only [solution, dilatedPotential, potential, Nat.cast_add, Nat.cast_ofNat]
    ring
  rw [ha, he, div_pow]

/-- The actual Levi matrix solves the radial Kähler–Einstein Monge–Ampère equation. -/
theorem solution_mongeAmpere (n : ℕ) (t : ℝ) (z : Coordinate n) :
    (solutionMatrix n t z).det = ((parameter n t * Real.exp (-solution n t z) : ℝ) : ℂ) := by
  rw [det_solutionMatrix, parameter_exp, exp_neg_solution]
  congr 1
  have hb : 1 + Real.exp (2 * t) ≠ 0 := by positivity
  have hd := (denominator_pos (Real.exp t • z)).ne'
  field_simp [hb, hd] <;> ring

/-- The central value strictly records the logarithmic radial scale. -/
theorem solution_zero (n : ℕ) (t : ℝ) :
    solution n t 0 = -(n + 2 : ℝ) * Real.log (1 + Real.exp (2 * t)) := by
  simp only [solution, dilatedPotential, potential, smul_zero, denominator, norm_zero,
    zero_pow (by decide : 2 ≠ 0), add_zero, Real.log_one, zero_sub, mul_neg, neg_mul]

/-- Distinct logarithmic scales give distinct actual radial potentials. -/
theorem solution_injective (n : ℕ) : Function.Injective (solution n) := by
  intro t s h
  have h0 := congrFun h 0
  rw [solution_zero, solution_zero] at h0
  have hc : -(n + 2 : ℝ) ≠ 0 := neg_ne_zero.mpr (by positivity)
  have hl := mul_left_cancel₀ hc h0
  have he := congrArg Real.exp hl
  rw [Real.exp_log (by positivity), Real.exp_log (by positivity)] at he
  have hx : Real.exp (2 * t) = Real.exp (2 * s) := by linarith only [he]
  have ht := Real.exp_injective hx
  linarith only [ht]

/-- Below the sharp ceiling, the radial family contains exactly two distinct potentials at that parameter. -/
theorem solution_two_scale_classification (n : ℕ) (y : ℝ) :
    (0 < y ∧ y < peak n) ↔
      ∃ a b : ℝ, a < criticalScale n ∧ criticalScale n < b ∧
        solution n a ≠ solution n b ∧ parameter n a = y ∧ parameter n b = y ∧
        ∀ t : ℝ, parameter n t = y ↔
          solution n t = solution n a ∨ solution n t = solution n b := by
  rw [parameter_two_scale_classification]
  constructor
  · rintro ⟨a, b, ha, hb, hpa, hpb, hr⟩
    refine ⟨a, b, ha, hb, ?_, hpa, hpb, ?_⟩
    · intro he
      exact (lt_trans ha hb).ne ((solution_injective n) he)
    · intro t
      simpa only [(solution_injective n).eq_iff] using hr t
  · rintro ⟨a, b, ha, hb, _, hpa, hpb, hr⟩
    refine ⟨a, b, ha, hb, hpa, hpb, ?_⟩
    intro t
    simpa only [(solution_injective n).eq_iff] using hr t

#print axioms fderiv_solution_apply
#print axioms solution_injective
#print axioms solution_two_scale_classification
#print axioms solutionHessian_eq
#print axioms solutionLevi_eq
#print axioms solutionLevi_pos_iff
#print axioms solutionMatrix_quadratic
#print axioms det_solutionMatrix
#print axioms solution_eq_zero_iff
#print axioms exp_neg_solution
#print axioms solution_mongeAmpere
end GaloisForLFunctions.HilbertMetric.RadialKahler
