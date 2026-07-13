import GaloisForLFunctions.HTGeometry.BernsteinSzegoMeanValue

/-!
# The Bernstein--Szegő moment form

This module turns the reciprocal-square analytic density into an explicit two-sided moment
sequence. It proves that its finite Toeplitz form is exactly weighted circle integration and that
the original top OPUC vector remains normalized and orthogonal to every lower coefficient vector.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex Matrix Polynomial
open scoped ComplexConjugate ComplexOrder

noncomputable section

/-- The complex-valued form of the positive Bernstein--Szegő weight. -/
def bernsteinSzegoComplexWeight {N : ℕ} (c : ℤ → ℂ)
    (hG : (circleToeplitzGram N c).PosDef) (z : ℂ) : ℂ :=
  (Complex.normSq ((finiteOPUCReversedPolynomial c hG).eval z) : ℂ)⁻¹

/-- The two-sided Fourier moment sequence of the Bernstein--Szegő weight, with the project Toeplitz
orientation. -/
def bernsteinSzegoMoment {N : ℕ} (c : ℤ → ℂ)
    (hG : (circleToeplitzGram N c).PosDef) (k : ℤ) : ℂ :=
  Real.circleAverage (fun z : ℂ => z ^ (-k) * bernsteinSzegoComplexWeight c hG z) 0 1

theorem bernsteinSzegoComplexWeight_continuousOn_sphere {N : ℕ} (c : ℤ → ℂ)
    (hG : (circleToeplitzGram N c).PosDef) :
    ContinuousOn (bernsteinSzegoComplexWeight c hG) (Metric.sphere (0 : ℂ) 1) := by
  apply ContinuousOn.inv₀ (by fun_prop)
  intro z hz
  have hznorm : ‖z‖ = 1 := by
    simpa [Metric.mem_sphere, dist_zero_right] using hz
  have hq : (finiteOPUCReversedPolynomial c hG).eval z ≠ 0 :=
    finiteOPUCReversedPolynomial_ne_zero_on_closedBall c hG (by linarith)
  exact Complex.ofReal_ne_zero.mpr (Complex.normSq_eq_zero.not.mpr hq)

/-- Integer Toeplitz exponents become the corresponding monomial/conjugate-monomial product on the
unit circle. -/
theorem unitCircle_zpow_neg_sub (i j : ℕ) {z : ℂ} (hz : ‖z‖ = 1) :
    z ^ (-((i : ℤ) - (j : ℤ))) = z ^ j * star (z ^ i) := by
  have hz0 : z ≠ 0 := norm_ne_zero_iff.mp (by simp [hz])
  rw [show -((i : ℤ) - (j : ℤ)) = (j : ℤ) - (i : ℤ) by omega,
    zpow_natCast_sub_natCast₀ hz0]
  rw [show star (z ^ i) = (z⁻¹) ^ i by
    calc
      star (z ^ i) = star z ^ i := map_pow (starRingEnd ℂ) z i
      _ = (z⁻¹) ^ i := congrArg (fun w : ℂ => w ^ i) (Complex.inv_eq_conj hz).symm]
  simp [div_eq_mul_inv]

theorem bernsteinSzegoMoment_mul_coeff
    {N : ℕ} (c : ℤ → ℂ) (hG : (circleToeplitzGram N c).PosDef)
    (i j : ℕ) (a : ℂ) :
    bernsteinSzegoMoment c hG ((i : ℤ) - (j : ℤ)) * a =
      Real.circleAverage
        (fun z : ℂ => a * (z ^ j * star (z ^ i) * bernsteinSzegoComplexWeight c hG z))
        0 1 := by
  rw [mul_comm, bernsteinSzegoMoment]
  change a • Real.circleAverage
      (fun z : ℂ => z ^ (-((i : ℤ) - (j : ℤ))) * bernsteinSzegoComplexWeight c hG z)
      0 1 = _
  rw [← Real.circleAverage_fun_smul]
  apply Real.circleAverage_congr_sphere
  intro z hz
  have hznorm : ‖z‖ = 1 := by
    simpa [Metric.mem_sphere, dist_zero_right] using hz
  simp only [smul_eq_mul]
  rw [unitCircle_zpow_neg_sub i j hznorm]

def finiteCoefficientPolynomialEval {N : ℕ} (u : Fin (N + 1) → ℂ) (z : ℂ) : ℂ :=
  ∑ i, u i * z ^ (i : ℕ)

theorem bernsteinSzego_term_circleIntegrable
    {N : ℕ} (c : ℤ → ℂ) (hG : (circleToeplitzGram N c).PosDef)
    (i j : Fin (N + 1)) (a : ℂ) :
    CircleIntegrable
      (fun z : ℂ => a *
        (z ^ (j : ℕ) * star (z ^ (i : ℕ)) * bernsteinSzegoComplexWeight c hG z))
      0 1 := by
  apply ContinuousOn.circleIntegrable zero_le_one
  have hj : ContinuousOn (fun z : ℂ => z ^ (j : ℕ)) (Metric.sphere 0 1) :=
    (continuous_id.pow (j : ℕ)).continuousOn
  have hi : ContinuousOn (fun z : ℂ => star (z ^ (i : ℕ))) (Metric.sphere 0 1) :=
    (continuous_star.comp (continuous_id.pow (i : ℕ))).continuousOn
  exact continuousOn_const.mul ((hj.mul hi).mul
    (bernsteinSzegoComplexWeight_continuousOn_sphere c hG))

/-- The finite Toeplitz form of the model moments is literal weighted circle integration. -/
theorem finiteToeplitzInner_bernsteinSzegoMoment
    {N : ℕ} (c : ℤ → ℂ) (hG : (circleToeplitzGram N c).PosDef)
    (u v : Fin (N + 1) → ℂ) :
    finiteToeplitzInner (bernsteinSzegoMoment c hG) u v =
      Real.circleAverage
        (fun z : ℂ => finiteCoefficientPolynomialEval v z *
          star (finiteCoefficientPolynomialEval u z) *
          bernsteinSzegoComplexWeight c hG z) 0 1 := by
  calc
    finiteToeplitzInner (bernsteinSzegoMoment c hG) u v =
        ∑ i : Fin (N + 1), ∑ j : Fin (N + 1),
          bernsteinSzegoMoment c hG ((i : ℤ) - (j : ℤ)) *
            (v j * star (u i)) := by
      simp only [finiteToeplitzInner, dotProduct, Matrix.mulVec, circleToeplitzGram]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j hj
      ring_nf
      rfl
    _ = ∑ i : Fin (N + 1), ∑ j : Fin (N + 1),
        Real.circleAverage
          (fun z : ℂ => (v j * star (u i)) *
            (z ^ (j : ℕ) * star (z ^ (i : ℕ)) * bernsteinSzegoComplexWeight c hG z))
          0 1 := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      exact bernsteinSzegoMoment_mul_coeff c hG (i : ℕ) (j : ℕ)
        (v j * star (u i))
    _ = Real.circleAverage
        (fun z : ℂ => ∑ i : Fin (N + 1), ∑ j : Fin (N + 1),
          (v j * star (u i)) *
            (z ^ (j : ℕ) * star (z ^ (i : ℕ)) * bernsteinSzegoComplexWeight c hG z))
        0 1 := by
      rw [Real.circleAverage_fun_sum]
      · apply Finset.sum_congr rfl
        intro i hi
        rw [Real.circleAverage_fun_sum]
        intro j hj
        exact bernsteinSzego_term_circleIntegrable c hG i j (v j * star (u i))
      · intro i hi
        exact CircleIntegrable.fun_sum Finset.univ (fun j hj =>
          bernsteinSzego_term_circleIntegrable c hG i j (v j * star (u i)))
    _ = Real.circleAverage
        (fun z : ℂ => finiteCoefficientPolynomialEval v z *
          star (finiteCoefficientPolynomialEval u z) *
          bernsteinSzegoComplexWeight c hG z) 0 1 := by
      apply congrArg (fun f : ℂ → ℂ => Real.circleAverage f 0 1)
      funext z
      simp only [finiteCoefficientPolynomialEval]
      have hstar : star (∑ i : Fin (N + 1), u i * z ^ (i : ℕ)) =
          ∑ i : Fin (N + 1), star (u i) * star (z ^ (i : ℕ)) := by
        change (starRingEnd ℂ) (∑ i : Fin (N + 1), u i * z ^ (i : ℕ)) = _
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro i hi
        rw [map_mul]
        rfl
      rw [hstar]
      calc
        (∑ i : Fin (N + 1), ∑ j : Fin (N + 1),
          (v j * star (u i)) *
            (z ^ (j : ℕ) * star (z ^ (i : ℕ)) * bernsteinSzegoComplexWeight c hG z)) =
            ∑ j : Fin (N + 1), ∑ i : Fin (N + 1),
              (v j * star (u i)) *
                (z ^ (j : ℕ) * star (z ^ (i : ℕ)) *
                  bernsteinSzegoComplexWeight c hG z) := Finset.sum_comm
        _ = (∑ j : Fin (N + 1), v j * z ^ (j : ℕ) *
              (∑ i : Fin (N + 1), star (u i) * star (z ^ (i : ℕ)))) *
              bernsteinSzegoComplexWeight c hG z := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro j hj
          rw [Finset.mul_sum, Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro i hi
          ring
        _ = ((∑ i : Fin (N + 1), v i * z ^ (i : ℕ)) *
              (∑ i : Fin (N + 1), star (u i) * star (z ^ (i : ℕ)))) *
              bernsteinSzegoComplexWeight c hG z := by
          rw [← Finset.sum_mul]

theorem finiteCoefficientPolynomialEval_finiteOPUCVector
    {N : ℕ} (c : ℤ → ℂ) (hG : (circleToeplitzGram N c).PosDef) (z : ℂ) :
    finiteCoefficientPolynomialEval (finiteOPUCVector c hG) z =
      (finiteOPUCPolynomial c hG).eval z := by
  rw [finiteOPUCPolynomial, Polynomial.ofFn_eq_sum_monomial]
  symm
  change Polynomial.eval z
      (Finset.sum (Finset.univ : Finset (Fin (N + 1)))
        (fun i => Polynomial.monomial (i : ℕ) (finiteOPUCVector c hG i))) =
    Finset.sum (Finset.univ : Finset (Fin (N + 1)))
      (fun i => finiteOPUCVector c hG i * z ^ (i : ℕ))
  simpa using Polynomial.eval_finsetSum (Finset.univ : Finset (Fin (N + 1)))
    (fun i : Fin (N + 1) => Polynomial.monomial (i : ℕ) (finiteOPUCVector c hG i)) z

theorem finiteCoefficientPolynomialEval_opucHead
    {N : ℕ} (q : Fin N → ℂ) (z : ℂ) :
    finiteCoefficientPolynomialEval (opucHead q) z =
      ∑ i : Fin N, q i * z ^ (i : ℕ) := by
  simp only [finiteCoefficientPolynomialEval]
  rw [Fin.sum_univ_castSucc]
  simp

theorem bernsteinSzego_polynomial_monomial_term_circleIntegrable
    {N : ℕ} (c : ℤ → ℂ) (hG : (circleToeplitzGram N c).PosDef)
    (q : Fin N → ℂ) (i : Fin N) :
    CircleIntegrable
      (fun z : ℂ => star (q i) *
        ((finiteOPUCPolynomial c hG).eval z * star (z ^ (i : ℕ)) *
          bernsteinSzegoComplexWeight c hG z)) 0 1 := by
  apply ContinuousOn.circleIntegrable zero_le_one
  have hp : ContinuousOn (fun z : ℂ => (finiteOPUCPolynomial c hG).eval z)
      (Metric.sphere 0 1) := by fun_prop
  have hi : ContinuousOn (fun z : ℂ => star (z ^ (i : ℕ)))
      (Metric.sphere 0 1) :=
    (continuous_star.comp (continuous_id.pow (i : ℕ))).continuousOn
  exact continuousOn_const.mul ((hp.mul hi).mul
    (bernsteinSzegoComplexWeight_continuousOn_sphere c hG))

/-- The top OPUC vector remains orthogonal to every lower coefficient vector for the model
moments. -/
theorem finiteToeplitzInner_bernsteinSzegoMoment_head_zero
    {N : ℕ} (c : ℤ → ℂ) (hG : (circleToeplitzGram N c).PosDef)
    (q : Fin N → ℂ) :
    finiteToeplitzInner (bernsteinSzegoMoment c hG) (opucHead q)
      (finiteOPUCVector c hG) = 0 := by
  rw [finiteToeplitzInner_bernsteinSzegoMoment]
  simp_rw [finiteCoefficientPolynomialEval_finiteOPUCVector,
    finiteCoefficientPolynomialEval_opucHead]
  have hstar (z : ℂ) : star (∑ i : Fin N, q i * z ^ (i : ℕ)) =
      ∑ i : Fin N, star (q i) * star (z ^ (i : ℕ)) := by
    change (starRingEnd ℂ) (∑ i : Fin N, q i * z ^ (i : ℕ)) = _
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [map_mul]
    rfl
  calc
    Real.circleAverage
        (fun z : ℂ => (finiteOPUCPolynomial c hG).eval z *
          star (∑ i : Fin N, q i * z ^ (i : ℕ)) *
          bernsteinSzegoComplexWeight c hG z) 0 1 =
      Real.circleAverage
        (fun z : ℂ => ∑ i : Fin N, star (q i) *
          ((finiteOPUCPolynomial c hG).eval z * star (z ^ (i : ℕ)) *
            bernsteinSzegoComplexWeight c hG z)) 0 1 := by
        apply congrArg (fun f : ℂ → ℂ => Real.circleAverage f 0 1)
        funext z
        rw [hstar, Finset.mul_sum, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i hi
        ring
    _ = ∑ i : Fin N, Real.circleAverage
        (fun z : ℂ => star (q i) *
          ((finiteOPUCPolynomial c hG).eval z * star (z ^ (i : ℕ)) *
            bernsteinSzegoComplexWeight c hG z)) 0 1 := by
      rw [Real.circleAverage_fun_sum]
      intro i hi
      exact bernsteinSzego_polynomial_monomial_term_circleIntegrable c hG q i
    _ = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      change Real.circleAverage (fun z : ℂ => star (q i) •
        ((finiteOPUCPolynomial c hG).eval z * star (z ^ (i : ℕ)) *
          bernsteinSzegoComplexWeight c hG z)) 0 1 = 0
      rw [Real.circleAverage_fun_smul]
      change star (q i) • Real.circleAverage
        (fun z : ℂ => (finiteOPUCPolynomial c hG).eval z * star (z ^ (i : ℕ)) *
          ((Complex.normSq
            ((finiteOPUCReversedPolynomial c hG).eval z) : ℂ)⁻¹)) 0 1 = 0
      rw [bernsteinSzego_monomial_orthogonal i.isLt c hG]
      simp

/-- The top OPUC vector remains normalized for the model moments. -/
theorem finiteToeplitzInner_bernsteinSzegoMoment_self
    {N : ℕ} (c : ℤ → ℂ) (hG : (circleToeplitzGram N c).PosDef) :
    finiteToeplitzInner (bernsteinSzegoMoment c hG)
      (finiteOPUCVector c hG) (finiteOPUCVector c hG) = 1 := by
  rw [finiteToeplitzInner_bernsteinSzegoMoment]
  simp_rw [finiteCoefficientPolynomialEval_finiteOPUCVector]
  exact bernsteinSzego_polynomial_normalized c hG

end
end GaloisForLFunctions.HTGeometry
