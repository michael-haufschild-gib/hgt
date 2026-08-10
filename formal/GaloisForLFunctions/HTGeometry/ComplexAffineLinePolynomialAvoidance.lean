import GaloisForLFunctions.HTGeometry.AffineLinePolynomialAvoidance

/-!
# Countable affine-line avoidance for complex obstruction polynomials

Spectral obstruction polynomials carry complex coefficients even though their parameters are real.
Splitting a complex polynomial into its coefficientwise real and imaginary parts turns each
obstruction into a real polynomial with the same real zero set contained in its own, so the real
affine-line avoidance layer applies verbatim: for almost every affine line, a countable family of
nonzero complex obstructions vanishes only on a countable set of parameters.
-/

open MeasureTheory

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {σ : Type*}

/-- Coefficientwise real part of a complex multivariate polynomial. -/
def mvPolynomialRealPart (Q : MvPolynomial σ ℂ) : MvPolynomial σ ℝ :=
  ∑ d ∈ Q.support, MvPolynomial.monomial d (Q.coeff d).re

/-- Coefficientwise imaginary part of a complex multivariate polynomial. -/
def mvPolynomialImagPart (Q : MvPolynomial σ ℂ) : MvPolynomial σ ℝ :=
  ∑ d ∈ Q.support, MvPolynomial.monomial d (Q.coeff d).im

@[simp] theorem coeff_mvPolynomialRealPart (Q : MvPolynomial σ ℂ) (d : σ →₀ ℕ) :
    MvPolynomial.coeff d (mvPolynomialRealPart Q) = (Q.coeff d).re := by
  classical
  rw [mvPolynomialRealPart, MvPolynomial.coeff_sum]
  by_cases hd : d ∈ Q.support
  · rw [Finset.sum_eq_single d]
    · rw [MvPolynomial.coeff_monomial, if_pos rfl]
    · intro e _ hed
      rw [MvPolynomial.coeff_monomial, if_neg hed]
    · intro hnot
      exact absurd hd hnot
  · have hzero : Q.coeff d = 0 := by
      simpa [MvPolynomial.mem_support_iff] using hd
    rw [hzero]
    refine Finset.sum_eq_zero fun e he => ?_
    rw [MvPolynomial.coeff_monomial, if_neg]
    intro h
    exact hd (h ▸ he)

@[simp] theorem coeff_mvPolynomialImagPart (Q : MvPolynomial σ ℂ) (d : σ →₀ ℕ) :
    MvPolynomial.coeff d (mvPolynomialImagPart Q) = (Q.coeff d).im := by
  classical
  rw [mvPolynomialImagPart, MvPolynomial.coeff_sum]
  by_cases hd : d ∈ Q.support
  · rw [Finset.sum_eq_single d]
    · rw [MvPolynomial.coeff_monomial, if_pos rfl]
    · intro e _ hed
      rw [MvPolynomial.coeff_monomial, if_neg hed]
    · intro hnot
      exact absurd hd hnot
  · have hzero : Q.coeff d = 0 := by
      simpa [MvPolynomial.mem_support_iff] using hd
    rw [hzero]
    refine Finset.sum_eq_zero fun e he => ?_
    rw [MvPolynomial.coeff_monomial, if_neg]
    intro h
    exact hd (h ▸ he)

/-- A complex polynomial with vanishing real and imaginary parts is zero. -/
theorem mvPolynomial_eq_zero_of_parts (Q : MvPolynomial σ ℂ)
    (hre : mvPolynomialRealPart Q = 0) (him : mvPolynomialImagPart Q = 0) : Q = 0 := by
  ext d
  have h1 : (Q.coeff d).re = 0 := by
    rw [← coeff_mvPolynomialRealPart Q d, hre, MvPolynomial.coeff_zero]
  have h2 : (Q.coeff d).im = 0 := by
    rw [← coeff_mvPolynomialImagPart Q d, him, MvPolynomial.coeff_zero]
  rw [MvPolynomial.coeff_zero]
  exact Complex.ext h1 h2

/-- Evaluation of the real part at a real point is the real part of the evaluation. -/
theorem eval_mvPolynomialRealPart (Q : MvPolynomial σ ℂ) (p : σ → ℝ) :
    MvPolynomial.eval p (mvPolynomialRealPart Q) =
      (MvPolynomial.eval₂ (RingHom.id ℂ) (fun t => (p t : ℂ)) Q).re := by
  classical
  rw [mvPolynomialRealPart, map_sum, MvPolynomial.eval₂_eq, Complex.re_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [MvPolynomial.eval_monomial]
  have hprod : (∏ i ∈ d.support, ((p i : ℂ)) ^ d i) =
      (((∏ i ∈ d.support, p i ^ d i : ℝ)) : ℂ) := by
    push_cast
    rfl
  have hre : (∏ i ∈ d.support, ((p i : ℂ)) ^ d i).re = ∏ i ∈ d.support, p i ^ d i := by
    rw [hprod, Complex.ofReal_re]
  have him : (∏ i ∈ d.support, ((p i : ℂ)) ^ d i).im = 0 := by
    rw [hprod, Complex.ofReal_im]
  simp [Complex.mul_re, hre, him, Finsupp.prod]

/-- Evaluation of the imaginary part at a real point is the imaginary part of the evaluation. -/
theorem eval_mvPolynomialImagPart (Q : MvPolynomial σ ℂ) (p : σ → ℝ) :
    MvPolynomial.eval p (mvPolynomialImagPart Q) =
      (MvPolynomial.eval₂ (RingHom.id ℂ) (fun t => (p t : ℂ)) Q).im := by
  classical
  rw [mvPolynomialImagPart, map_sum, MvPolynomial.eval₂_eq, Complex.im_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [MvPolynomial.eval_monomial]
  have hprod : (∏ i ∈ d.support, ((p i : ℂ)) ^ d i) =
      (((∏ i ∈ d.support, p i ^ d i : ℝ)) : ℂ) := by
    push_cast
    rfl
  have hre : (∏ i ∈ d.support, ((p i : ℂ)) ^ d i).re = ∏ i ∈ d.support, p i ^ d i := by
    rw [hprod, Complex.ofReal_re]
  have him : (∏ i ∈ d.support, ((p i : ℂ)) ^ d i).im = 0 := by
    rw [hprod, Complex.ofReal_im]
  simp [Complex.mul_im, hre, him, Finsupp.prod]

/-- A real witness for a nonzero complex polynomial: one of its two parts is a nonzero real
polynomial whose nonvanishing forces the complex polynomial to be nonzero. -/
def mvPolynomialRealShadow (Q : MvPolynomial σ ℂ) : MvPolynomial σ ℝ := by
  classical
  exact if mvPolynomialRealPart Q = 0 then mvPolynomialImagPart Q else mvPolynomialRealPart Q

theorem mvPolynomialRealShadow_ne_zero {Q : MvPolynomial σ ℂ} (hQ : Q ≠ 0) :
    mvPolynomialRealShadow Q ≠ 0 := by
  classical
  rw [mvPolynomialRealShadow]
  split_ifs with hre
  · intro him
    exact hQ (mvPolynomial_eq_zero_of_parts Q hre him)
  · exact hre

theorem eval₂_ne_zero_of_eval_mvPolynomialRealShadow_ne_zero {Q : MvPolynomial σ ℂ}
    {p : σ → ℝ} (h : MvPolynomial.eval p (mvPolynomialRealShadow Q) ≠ 0) :
    MvPolynomial.eval₂ (RingHom.id ℂ) (fun t => (p t : ℂ)) Q ≠ 0 := by
  classical
  intro hzero
  rw [mvPolynomialRealShadow] at h
  split_ifs at h with hre
  · rw [eval_mvPolynomialImagPart, hzero] at h
    exact h rfl
  · rw [eval_mvPolynomialRealPart, hzero] at h
    exact h rfl

/-- **Countable affine-line avoidance for complex obstructions.**  For almost every affine line,
a countable family of nonzero complex polynomials vanishes only on a countable set of real
parameters. -/
theorem countable_complexMvPolynomialAffineLineAvoidance_ae_pair {n : ℕ}
    (Q : ℕ → MvPolynomial (Fin n) ℂ) (hQ : ∀ r, Q r ≠ 0) :
    ∀ᵐ av : (Fin n → ℝ) × (Fin n → ℝ) ∂(volume.prod volume),
      ∃ C : Set ℝ, C.Countable ∧
        ∀ g ∉ C, ∀ r,
          MvPolynomial.eval₂ (RingHom.id ℂ)
            (fun i => ((av.1 i + g * av.2 i : ℝ) : ℂ)) (Q r) ≠ 0 := by
  have hshadow : ∀ r, mvPolynomialRealShadow (Q r) ≠ 0 := fun r =>
    mvPolynomialRealShadow_ne_zero (hQ r)
  filter_upwards [countable_mvPolynomialAffineLineAvoidance_ae_pair
    (fun r => mvPolynomialRealShadow (Q r)) hshadow] with av hav
  obtain ⟨C, hC, hgC⟩ := hav
  refine ⟨C, hC, fun g hg r => ?_⟩
  exact eval₂_ne_zero_of_eval_mvPolynomialRealShadow_ne_zero (hgC g hg r)

end

end GaloisForLFunctions.HTGeometry
