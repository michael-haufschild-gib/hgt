import GaloisForLFunctions.RHTower.WeilLogShiftProjectedExponentialLimit

/-! A quadratic exponential is a standard Gaussian average of linear
exponentials. Finite atomic expectations commute with this average. -/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace RHTower

theorem finiteWeil_exp_quadratic_gaussian_average (c : NNReal) (x : ℝ) :
    (∫ z : ℝ, Real.exp ((Real.sqrt (2 * (c : ℝ)) * z) * x) ∂(gaussianReal 0 1)) =
      Real.exp ((c : ℝ) * x ^ 2) := by
  have h := congrFun (mgf_fun_id_gaussianReal (μ := 0) (v := 1))
    (Real.sqrt (2 * (c : ℝ)) * x)
  have hmgf : (∫ z : ℝ, Real.exp ((Real.sqrt (2 * (c : ℝ)) * x) * z)
      ∂(gaussianReal 0 1)) = Real.exp ((Real.sqrt (2 * (c : ℝ)) * x) ^ 2 / 2) := by
    simpa [mgf] using h
  calc
    _ = ∫ z : ℝ, Real.exp ((Real.sqrt (2 * (c : ℝ)) * x) * z) ∂(gaussianReal 0 1) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun z => by
        dsimp only
        congr 1
        ring
    _ = Real.exp ((Real.sqrt (2 * (c : ℝ)) * x) ^ 2 / 2) := hmgf
    _ = _ := by
      rw [mul_pow, Real.sq_sqrt (by positivity)]
      congr 1
      ring

theorem finiteWeilCanonicalObservableLaw_quadratic_gaussian_average
    (r k : ℕ) (f : Fin (r + 1) → ℝ) (c : NNReal) :
    (∫ x : ℝ, Real.exp ((c : ℝ) * x ^ 2)
      ∂(finiteWeilCanonicalObservableLaw r k f : Measure ℝ)) =
      ∫ z : ℝ, (∫ x : ℝ, Real.exp ((Real.sqrt (2 * (c : ℝ)) * z) * x)
        ∂(finiteWeilCanonicalObservableLaw r k f : Measure ℝ)) ∂(gaussianReal 0 1) := by
  have hi (i : Fin (r + 1)) :
      Integrable (fun z : ℝ => Real.exp ((Real.sqrt (2 * (c : ℝ)) * z) * f i))
        (gaussianReal 0 1) := by
    convert integrable_exp_mul_gaussianReal (μ := 0) (v := 1)
      (Real.sqrt (2 * (c : ℝ)) * f i) using 1
    ext z
    congr 1
    ring
  simp_rw [finiteWeilCanonicalObservableLaw_integral_real]
  rw [integral_finsetSum _ (fun i _ => (hi i).const_mul (finiteWeilCanonicalEdgeMass r k i))]
  simp_rw [integral_const_mul, finiteWeil_exp_quadratic_gaussian_average]

theorem finiteWeilCanonicalProjectedIndex_quadratic_gaussian_average
    (r k : ℕ) (c : NNReal) :
    (∫ x : ℝ, Real.exp ((c : ℝ) * x ^ 2)
      ∂(finiteWeilCanonicalProjectedProbabilityLaw r k 1 0 : Measure ℝ)) =
      ∫ z : ℝ, (∫ x : ℝ, Real.exp ((Real.sqrt (2 * (c : ℝ)) * z) * x)
        ∂(finiteWeilCanonicalProjectedProbabilityLaw r k 1 0 : Measure ℝ)) ∂(gaussianReal 0 1) := by
  unfold finiteWeilCanonicalProjectedProbabilityLaw
  exact finiteWeilCanonicalObservableLaw_quadratic_gaussian_average r k _ c

end RHTower
