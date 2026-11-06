import GaloisForLFunctions.ArithmeticInnerFunctionTheory.TheArithmeticBernsteinTheorem

/-!
# The `{2, 3}` rung of the insertion cone

The arithmetic Bernstein theorem says that torus positivity at all primes and all base points is the Laplace cone. On a fixed prime set the cone is strictly larger.

* **Steep amplitudes** (`torusSum_two_three_nonneg`). If `f(x + y) ≤ f(x)e^{−3y}` from `x` on, the torus sum on `{2, 3}` is nonnegative at `x`.
* **The Gaussian** (`gaussian_torus_positive`, `not_isExpConvexFrom_gaussian`). `e^{−x²}` is torus positive on `{2, 3}` at every `x ≥ 3/2`, and it is exponentially convex from no point: it is strictly log-concave.

So finite prime sets do not see the Laplace wall: only the full set of primes, with the base point moved to the left, forces it. A proof that `S ≥ 0` by
rungs on prime sets cannot pass through the Laplace cone. The cost of a rung is measured by the steepness needed at its base point: this is the
log-concavity wall (`sum_sq_le_of_logConcave`), where the admissible first coefficients are bounded in `ℓ²` as the prime set grows.
-/

open Finset

namespace GaloisForLFunctions.ArithmeticInnerFunctionTheory

noncomputable section

/-- The steps of the rung `{2, 3}`. -/
def twoThree : Fin 2 → ℝ := ![Real.log 2, Real.log 3]

theorem twoThree_pos (i : Fin 2) : 0 ≤ twoThree i := by
  fin_cases i
  · exact (Real.log_pos (by norm_num)).le
  · exact (Real.log_pos (by norm_num)).le

/-- **The steep part of the cone.** -/
theorem torusSum_two_three_nonneg {f : ℝ → ℝ} {x : ℝ} (hx : 0 ≤ f x)
    (hf : ∀ y, 0 ≤ y → |f (x + y)| ≤ f x * Real.exp (-3 * y)) (θ : Fin 2 → ℝ) :
    0 ≤ torusSum (ampl f twoThree x) θ := by
  set r : Fin 2 → ℝ := ![1 / 8, 1 / 27] with hr
  have hr_exp : ∀ i, r i = Real.exp (-3 * twoThree i) := fun i => by
    fin_cases i
    · have e : -3 * Real.log 2 = Real.log (1 / 8) := by
        rw [show (1 / 8 : ℝ) = (2 ^ 3)⁻¹ by norm_num, Real.log_inv, Real.log_pow]
        norm_num
      simp only [hr, twoThree, Matrix.cons_val_zero, Fin.zero_eta]
      rw [e, Real.exp_log (by norm_num)]
    · have e : -3 * Real.log 3 = Real.log (1 / 27) := by
        rw [show (1 / 27 : ℝ) = (3 ^ 3)⁻¹ by norm_num, Real.log_inv, Real.log_pow]
        norm_num
      simp only [hr, twoThree, Matrix.cons_val_one, Fin.mk_one, Matrix.cons_val_fin_one]
      rw [e, Real.exp_log (by norm_num)]
  refine torusSum_nonneg_of_geometric (r := r) ?_ (fun i => ?_) (fun i => ?_) (fun k => ?_) ?_ θ
  · rw [ampl_zero]
    exact hx
  · rw [hr_exp]
    exact (Real.exp_pos _).le
  · fin_cases i <;> simp [hr] <;> norm_num
  · have hS : 0 ≤ ∑ i, (k i : ℝ) * twoThree i :=
      Finset.sum_nonneg fun i _ => mul_nonneg (Nat.cast_nonneg _) (twoThree_pos i)
    have hprod : ∏ i, r i ^ k i = Real.exp (-3 * ∑ i, (k i : ℝ) * twoThree i) := by
      rw [Finset.mul_sum, Real.exp_sum]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [hr_exp, ← Real.exp_nat_mul]
      congr 1
      ring
    rw [ampl_zero, hprod]
    exact hf _ hS
  · simp only [Fin.prod_univ_two, hr, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    norm_num

/-- The Gaussian amplitude. -/
def gaussian (x : ℝ) : ℝ := Real.exp (-x ^ 2)

/-- **The Gaussian lies in the `{2, 3}` cone** at every base point `x ≥ 3/2`. -/
theorem gaussian_torus_positive {x : ℝ} (hx : 3 / 2 ≤ x) (θ : Fin 2 → ℝ) :
    0 ≤ torusSum (ampl gaussian twoThree x) θ := by
  refine torusSum_two_three_nonneg (f := gaussian) (Real.exp_pos _).le (fun y hy => ?_) θ
  simp only [gaussian]
  rw [abs_of_pos (Real.exp_pos _), ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith [sq_nonneg y, mul_nonneg hy (by linarith : (0 : ℝ) ≤ x - 3 / 2)]

/-- An exponentially convex amplitude is log-convex along arithmetic progressions. -/
theorem IsExpConvexFrom.sq_le {x₀ : ℝ} {f : ℝ → ℝ} (hf : IsExpConvexFrom x₀ f) {t : ℝ} (ht : 0 ≤ t) :
    f x₀ * (f x₀ * f (x₀ + 2 * t) - f (x₀ + t) ^ 2) ≥ 0 := by
  have h := hf (Fin 2) Finset.univ ![0, t] ![(f (x₀ + t) : ℂ), -(f x₀ : ℂ)]
    (fun i _ => by fin_cases i <;> simp [ht])
  have e0 : x₀ + 0 + 0 = x₀ := by ring
  have e1 : x₀ + 0 + t = x₀ + t := by ring
  have e2 : x₀ + t + 0 = x₀ + t := by ring
  have e3 : x₀ + t + t = x₀ + 2 * t := by ring
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, e0, e1,
    e2, e3] at h
  have h2 : ((f (x₀ + t) : ℂ) * (starRingEnd ℂ) (f (x₀ + t) : ℂ) * (f x₀ : ℂ) +
      (f (x₀ + t) : ℂ) * (starRingEnd ℂ) (-(f x₀ : ℂ)) * (f (x₀ + t) : ℂ) +
      (-(f x₀ : ℂ) * (starRingEnd ℂ) (f (x₀ + t) : ℂ) * (f (x₀ + t) : ℂ) +
        -(f x₀ : ℂ) * (starRingEnd ℂ) (-(f x₀ : ℂ)) * (f (x₀ + 2 * t) : ℂ))) =
      ((f x₀ * (f x₀ * f (x₀ + 2 * t) - f (x₀ + t) ^ 2) : ℝ) : ℂ) := by
    simp only [map_neg, Complex.conj_ofReal]
    push_cast
    ring
  rw [h2, Complex.ofReal_re] at h
  exact h

/-- **The Gaussian is exponentially convex from no point.** -/
theorem not_isExpConvexFrom_gaussian (x₀ : ℝ) : ¬IsExpConvexFrom x₀ gaussian := by
  intro h
  have h1 := IsExpConvexFrom.sq_le h (t := 1) zero_le_one
  have hpos : 0 < gaussian x₀ := Real.exp_pos _
  have h2 : gaussian x₀ * gaussian (x₀ + 2 * 1) - gaussian (x₀ + 1) ^ 2 ≥ 0 :=
    nonneg_of_mul_nonneg_right h1 hpos
  have h3 : gaussian x₀ * gaussian (x₀ + 2 * 1) < gaussian (x₀ + 1) ^ 2 := by
    simp only [gaussian]
    rw [← Real.exp_add, ← Real.exp_nat_mul]
    apply Real.exp_lt_exp.mpr
    push_cast
    nlinarith
  linarith

end

end GaloisForLFunctions.ArithmeticInnerFunctionTheory
