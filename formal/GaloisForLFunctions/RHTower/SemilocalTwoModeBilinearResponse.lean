import GaloisForLFunctions.RHTower.SemilocalCosineModeFirstOrderResponse

/-!
# The bilinear (`ε₁ε₂`) response of the semilocal Hankel determinants to two cosine modes

Multiply the archimedean Gamma measure by `(1 + 2ε₁ cos(δ₁ s))(1 + 2ε₂ cos(δ₂ s))`.  In the
orthonormal archimedean Jacobi basis the Gram matrix is

`1 + ε₁ T(δ₁) + ε₂ T(δ₂) + ε₁ε₂ (T(δ₁+δ₂) + T(δ₁−δ₂))`

(product-to-sum), and the mixed second derivative of `log det` at the origin is

`∂₁∂₂ log D_n = tr T(δ₁+δ₂) + tr T(δ₁−δ₂) − tr(T(δ₁) T(δ₂))`

= (first-order jet of the sum mode) + (first-order jet of the beat mode) − (truncation defect).
This is the covariance of the two linear statistics in the `n+1`-point archimedean Jacobi ensemble,
`tr(K f₁ (1−K) f₂ K)`: the product-mode first-order response is cancelled exactly by the diagonal
part of the bilinear term, and what remains is the off-diagonal block pairing of the two boost
matrices.  For `δ_a = log p_a` this is the exact structure of the two-prime cross term of the
semilocal measure (report §3.5).
-/

open Matrix Real MeasureTheory Filter Topology
open scoped BigOperators

namespace RHTower
namespace CosineModeResponse

open GaloisForLFunctions.HilbertMetric

/-- Gram matrix of the archimedean orthonormal polynomials for the two-mode measure
`(1 + 2ε₁ cos(δ₁ s))(1 + 2ε₂ cos(δ₂ s)) μ`. -/
noncomputable def twoModeGram (δ₁ δ₂ ε₁ ε₂ : ℝ) (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  fun i j => ∫ s : ℝ, (semilocalArchimedeanJacobiPolynomial i).eval s *
    (semilocalArchimedeanJacobiPolynomial j).eval s *
    ((1 + 2 * ε₁ * Real.cos (δ₁ * s)) * (1 + 2 * ε₂ * Real.cos (δ₂ * s)))
    ∂semilocalArchimedeanGammaMeasure

/-- The affine-bilinear matrix family `1 + ε₁ T₁ + ε₂ T₂ + ε₁ε₂ (T₊ + T₋)`. -/
noncomputable def twoModeMatrix (δ₁ δ₂ : ℝ) (n : ℕ) (ε₁ ε₂ : ℝ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  1 + ε₁ • cosineModeTangent δ₁ n + ε₂ • cosineModeTangent δ₂ n +
    (ε₁ * ε₂) • (cosineModeTangent (δ₁ + δ₂) n + cosineModeTangent (δ₁ - δ₂) n)

theorem cos_add_add_cos_sub (a b s : ℝ) :
    Real.cos ((a + b) * s) + Real.cos ((a - b) * s) = 2 * Real.cos (a * s) * Real.cos (b * s) := by
  rw [add_mul, sub_mul, Real.cos_add, Real.cos_sub]
  ring

/-- **The two-mode Gram matrix is `1 + ε₁ T₁ + ε₂ T₂ + ε₁ε₂ (T₊ + T₋)`.** -/
theorem twoModeGram_eq (δ₁ δ₂ ε₁ ε₂ : ℝ) (n : ℕ) :
    twoModeGram δ₁ δ₂ ε₁ ε₂ n = twoModeMatrix δ₁ δ₂ n ε₁ ε₂ := by
  ext i j
  unfold twoModeGram
  set P : ℝ → ℝ := fun s => (semilocalArchimedeanJacobiPolynomial i).eval s *
    (semilocalArchimedeanJacobiPolynomial j).eval s with hP
  have h0 : Integrable P semilocalArchimedeanGammaMeasure :=
    integrable_eval_mul_eval_semilocalArchimedeanGammaMeasure
      (semilocalArchimedeanJacobiPolynomial i) (semilocalArchimedeanJacobiPolynomial j)
  have h1 : Integrable (fun s => P s * Real.cos (δ₁ * s)) semilocalArchimedeanGammaMeasure :=
    integrable_eval_mul_eval_mul_cos i j δ₁
  have h2 : Integrable (fun s => P s * Real.cos (δ₂ * s)) semilocalArchimedeanGammaMeasure :=
    integrable_eval_mul_eval_mul_cos i j δ₂
  have h3 : Integrable (fun s => P s * Real.cos ((δ₁ + δ₂) * s)) semilocalArchimedeanGammaMeasure :=
    integrable_eval_mul_eval_mul_cos i j (δ₁ + δ₂)
  have h4 : Integrable (fun s => P s * Real.cos ((δ₁ - δ₂) * s)) semilocalArchimedeanGammaMeasure :=
    integrable_eval_mul_eval_mul_cos i j (δ₁ - δ₂)
  have hsplit : (fun s : ℝ => (semilocalArchimedeanJacobiPolynomial i).eval s *
      (semilocalArchimedeanJacobiPolynomial j).eval s *
      ((1 + 2 * ε₁ * Real.cos (δ₁ * s)) * (1 + 2 * ε₂ * Real.cos (δ₂ * s)))) =
      fun s => P s + (2 * ε₁) * (P s * Real.cos (δ₁ * s)) + (2 * ε₂) * (P s * Real.cos (δ₂ * s)) +
        (2 * ε₁ * ε₂) * (P s * Real.cos ((δ₁ + δ₂) * s)) +
        (2 * ε₁ * ε₂) * (P s * Real.cos ((δ₁ - δ₂) * s)) := by
    funext s
    have h := cos_add_add_cos_sub δ₁ δ₂ s
    simp only [hP]
    linear_combination (-2 * ε₁ * ε₂ * ((semilocalArchimedeanJacobiPolynomial i).eval s *
      (semilocalArchimedeanJacobiPolynomial j).eval s)) * h
  have hA : Integrable (fun s => P s + (2 * ε₁) * (P s * Real.cos (δ₁ * s)))
      semilocalArchimedeanGammaMeasure := h0.add (h1.const_mul _)
  have hB : Integrable (fun s => P s + (2 * ε₁) * (P s * Real.cos (δ₁ * s)) +
      (2 * ε₂) * (P s * Real.cos (δ₂ * s))) semilocalArchimedeanGammaMeasure :=
    hA.add (h2.const_mul _)
  have hC : Integrable (fun s => P s + (2 * ε₁) * (P s * Real.cos (δ₁ * s)) +
      (2 * ε₂) * (P s * Real.cos (δ₂ * s)) + (2 * ε₁ * ε₂) * (P s * Real.cos ((δ₁ + δ₂) * s)))
      semilocalArchimedeanGammaMeasure := hB.add (h3.const_mul _)
  rw [hsplit, integral_add hC (h4.const_mul _), integral_add hB (h3.const_mul _),
    integral_add hA (h2.const_mul _), integral_add h0 (h1.const_mul _),
    integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul]
  have hgram : ∫ s : ℝ, P s ∂semilocalArchimedeanGammaMeasure = if (i : ℕ) = j then 1 else 0 :=
    semilocalArchimedeanJacobiGram_eq_ite i j
  rw [hgram]
  simp only [twoModeMatrix, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul,
    cosineModeTangent, hP]
  by_cases hij : i = j
  · subst hij; simp; ring
  · have hij' : (i : ℕ) ≠ j := fun h => hij (Fin.ext h)
    simp [hij, hij']; ring

/-- The two-mode determinant path. -/
noncomputable def twoModeDeterminant (δ₁ δ₂ : ℝ) (n : ℕ) (ε₁ ε₂ : ℝ) : ℝ :=
  (twoModeGram δ₁ δ₂ ε₁ ε₂ n).det

/-- The bilinear jet: sum-mode jet + beat-mode jet − truncation defect `tr(T(δ₁) T(δ₂))`. -/
noncomputable def bilinearDeterminantJet (δ₁ δ₂ : ℝ) (n : ℕ) : ℝ :=
  cosineModeDeterminantJet (δ₁ + δ₂) n + cosineModeDeterminantJet (δ₁ - δ₂) n -
    Matrix.trace (cosineModeTangent δ₁ n * cosineModeTangent δ₂ n)

section calculus

variable (δ₁ δ₂ : ℝ) (n : ℕ)

theorem twoModeMatrix_zero_left (ε₂ : ℝ) :
    twoModeMatrix δ₁ δ₂ n 0 ε₂ = 1 + ε₂ • cosineModeTangent δ₂ n := by
  unfold twoModeMatrix
  simp

theorem hasDerivAt_twoModeMatrix_entry (ε₂ : ℝ) (i j : Fin (n + 1)) :
    HasDerivAt (fun ε₁ => twoModeMatrix δ₁ δ₂ n ε₁ ε₂ i j)
      ((cosineModeTangent δ₁ n +
        ε₂ • (cosineModeTangent (δ₁ + δ₂) n + cosineModeTangent (δ₁ - δ₂) n)) i j) 0 := by
  have hfun : (fun ε₁ => twoModeMatrix δ₁ δ₂ n ε₁ ε₂ i j) =
      fun ε₁ => ((1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) i j + ε₂ * cosineModeTangent δ₂ n i j) +
        ε₁ * (cosineModeTangent δ₁ n i j +
          ε₂ * (cosineModeTangent (δ₁ + δ₂) n i j + cosineModeTangent (δ₁ - δ₂) n i j)) := by
    funext ε₁
    simp only [twoModeMatrix, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  rw [hfun]
  have h := ((hasDerivAt_id (0 : ℝ)).mul_const (cosineModeTangent δ₁ n i j +
    ε₂ * (cosineModeTangent (δ₁ + δ₂) n i j + cosineModeTangent (δ₁ - δ₂) n i j))).const_add
    ((1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) i j + ε₂ * cosineModeTangent δ₂ n i j)
  convert h using 1
  simp [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]

theorem hasDerivAt_det_twoModeMatrix (ε₂ : ℝ) :
    HasDerivAt (fun ε₁ => (twoModeMatrix δ₁ δ₂ n ε₁ ε₂).det)
      (detFirstJet (1 + ε₂ • cosineModeTangent δ₂ n)
        (cosineModeTangent δ₁ n +
          ε₂ • (cosineModeTangent (δ₁ + δ₂) n + cosineModeTangent (δ₁ - δ₂) n))) 0 := by
  have h := hasDerivAt_matrixDet (fun ε₁ => twoModeMatrix δ₁ δ₂ n ε₁ ε₂)
    (cosineModeTangent δ₁ n +
      ε₂ • (cosineModeTangent (δ₁ + δ₂) n + cosineModeTangent (δ₁ - δ₂) n)) 0
    (fun i j => hasDerivAt_twoModeMatrix_entry δ₁ δ₂ n ε₂ i j)
  rwa [twoModeMatrix_zero_left] at h

/-- The inner derivative at a base point where the single-mode Gram determinant is nonzero. -/
theorem deriv_log_det_twoModeMatrix (ε₂ : ℝ) (hdet : (1 + ε₂ • cosineModeTangent δ₂ n).det ≠ 0) :
    deriv (fun ε₁ => Real.log (twoModeMatrix δ₁ δ₂ n ε₁ ε₂).det) 0 =
      Matrix.trace ((1 + ε₂ • cosineModeTangent δ₂ n)⁻¹ *
        (cosineModeTangent δ₁ n +
          ε₂ • (cosineModeTangent (δ₁ + δ₂) n + cosineModeTangent (δ₁ - δ₂) n))) := by
  have h := hasDerivAt_det_twoModeMatrix δ₁ δ₂ n ε₂
  have h0 : (twoModeMatrix δ₁ δ₂ n 0 ε₂).det ≠ 0 := by rw [twoModeMatrix_zero_left]; exact hdet
  have hlog := h.log h0
  rw [hlog.deriv, twoModeMatrix_zero_left, detFirstJet_eq_det_mul_trace_inv_mul _ _ hdet]
  field_simp

theorem hasDerivAt_inv_one_add_smul (T : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (i j : Fin (n + 1)) :
    HasDerivAt (fun t : ℝ => (1 + t • T)⁻¹ i j) (-(T i j)) 0 := by
  have hent : ∀ i j, HasDerivAt (fun t : ℝ => (1 + t • T) i j) (T i j) 0 := by
    intro i j
    have hfun : (fun t : ℝ => (1 + t • T) i j) =
        fun t => (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) i j + t * T i j := by
      funext t
      simp [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    rw [hfun]
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (T i j)).const_add
      ((1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) i j)
  have h := hasDerivAt_matrix_inv (fun t : ℝ => 1 + t • T) T 0 hent (by simp) i j
  simpa using h

/-- Derivative of `ε₂ ↦ tr((1 + ε₂T₂)⁻¹ (T₁ + ε₂ T₁₂))` at `0`: `tr(−T₂T₁ + T₁₂)`. -/
theorem hasDerivAt_traceInvMul (T₁ T₂ T₁₂ : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    HasDerivAt (fun ε₂ : ℝ => Matrix.trace ((1 + ε₂ • T₂)⁻¹ * (T₁ + ε₂ • T₁₂)))
      (Matrix.trace (-(T₂ * T₁) + T₁₂)) 0 := by
  have hN : ∀ k i, HasDerivAt (fun t : ℝ => (T₁ + t • T₁₂) k i) (T₁₂ k i) 0 := by
    intro k i
    have hfun : (fun t : ℝ => (T₁ + t • T₁₂) k i) = fun t => T₁ k i + t * T₁₂ k i := by
      funext t
      simp [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    rw [hfun]
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (T₁₂ k i)).const_add (T₁ k i)
  have hfun : (fun ε₂ : ℝ => Matrix.trace ((1 + ε₂ • T₂)⁻¹ * (T₁ + ε₂ • T₁₂))) =
      fun ε₂ => ∑ i, ∑ k, (1 + ε₂ • T₂)⁻¹ i k * (T₁ + ε₂ • T₁₂) k i := by
    funext ε₂
    simp [Matrix.trace, Matrix.mul_apply]
  rw [hfun]
  have hterm : ∀ i k : Fin (n + 1), HasDerivAt (fun ε₂ : ℝ => (1 + ε₂ • T₂)⁻¹ i k * (T₁ + ε₂ • T₁₂) k i)
      (-(T₂ i k) * T₁ k i + (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) i k * T₁₂ k i) 0 := by
    intro i k
    have hM := hasDerivAt_inv_one_add_smul n T₂ i k
    have := hM.mul (hN k i)
    convert this using 1
    simp
  have hrow : ∀ i : Fin (n + 1), HasDerivAt (fun ε₂ : ℝ => ∑ k, (1 + ε₂ • T₂)⁻¹ i k * (T₁ + ε₂ • T₁₂) k i)
      (∑ k, (-(T₂ i k) * T₁ k i + (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) i k * T₁₂ k i)) 0 :=
    fun i => HasDerivAt.fun_sum (𝕜 := ℝ) (u := (Finset.univ : Finset (Fin (n + 1))))
      (fun k _ => hterm i k)
  have h := HasDerivAt.fun_sum (𝕜 := ℝ) (u := (Finset.univ : Finset (Fin (n + 1))))
    (fun i _ => hrow i)
  refine h.congr_deriv ?_
  have hval : (∑ i, ∑ k, (-(T₂ i k) * T₁ k i + (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) i k * T₁₂ k i)) =
      Matrix.trace (-(T₂ * T₁) + T₁₂) := by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.add_apply, Matrix.neg_apply, Matrix.mul_apply,
      Finset.sum_add_distrib, Finset.sum_neg_distrib, neg_mul]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [Matrix.one_apply]
  exact hval

end calculus

/-- **The bilinear response of the semilocal Hankel determinant.**
`∂₁∂₂ log D_n(ε₁, ε₂)|₀ = tr T(δ₁+δ₂) + tr T(δ₁−δ₂) − tr(T(δ₁) T(δ₂))`. -/
theorem deriv_deriv_log_twoModeDeterminant (δ₁ δ₂ : ℝ) (n : ℕ) :
    deriv (fun ε₂ => deriv (fun ε₁ => Real.log (twoModeDeterminant δ₁ δ₂ n ε₁ ε₂)) 0) 0 =
      bilinearDeterminantJet δ₁ δ₂ n := by
  have hG := hasDerivAt_traceInvMul n (cosineModeTangent δ₁ n) (cosineModeTangent δ₂ n)
    (cosineModeTangent (δ₁ + δ₂) n + cosineModeTangent (δ₁ - δ₂) n)
  have hcont : Continuous (fun ε₂ : ℝ => (1 + ε₂ • cosineModeTangent δ₂ n).det) :=
    Continuous.matrix_det (continuous_const.add (continuous_id.smul continuous_const))
  have hev : ∀ᶠ ε₂ in 𝓝 (0 : ℝ), (1 + ε₂ • cosineModeTangent δ₂ n).det ≠ 0 :=
    hcont.continuousAt.eventually_ne (by simp)
  have heq : (fun ε₂ => deriv (fun ε₁ => Real.log (twoModeDeterminant δ₁ δ₂ n ε₁ ε₂)) 0) =ᶠ[𝓝 0]
      fun ε₂ => Matrix.trace ((1 + ε₂ • cosineModeTangent δ₂ n)⁻¹ *
        (cosineModeTangent δ₁ n +
          ε₂ • (cosineModeTangent (δ₁ + δ₂) n + cosineModeTangent (δ₁ - δ₂) n))) := by
    filter_upwards [hev] with ε₂ h
    unfold twoModeDeterminant
    simp_rw [twoModeGram_eq]
    exact deriv_log_det_twoModeMatrix δ₁ δ₂ n ε₂ h
  have hD := hG.congr_of_eventuallyEq heq
  rw [hD.deriv]
  unfold bilinearDeterminantJet
  rw [Matrix.trace_add, Matrix.trace_neg, Matrix.trace_mul_comm, Matrix.trace_add,
    trace_cosineModeTangent, trace_cosineModeTangent]
  unfold cosineModeDeterminantJet
  ring

end CosineModeResponse
end RHTower
