/-
# Complex contour integrals on affine parallelograms

This file supplies a parallelogram version of the Cauchy--Goursat theorem. The proof pulls the
contour back to the real unit square and applies the two-dimensional divergence theorem. Complex
differentiability makes the resulting divergence vanish.
-/
import Mathlib.Analysis.Complex.CauchyIntegral

open Complex Set MeasureTheory intervalIntegral

namespace GaloisForLFunctions

noncomputable section

/-- The positively oriented contour integral of `g` around the affine parallelogram with vertices
`a`, `a + 1`, `a + 1 + τ`, and `a + τ`. -/
def parallelogramIntegral (g : ℂ → ℂ) (τ a : ℂ) : ℂ :=
    (∫ x : ℝ in 0..1, g (a + x)) +
      τ * (∫ y : ℝ in 0..1, g (a + 1 + y * τ)) -
      (∫ x : ℝ in 0..1, g (a + τ + x)) -
      τ * (∫ y : ℝ in 0..1, g (a + y * τ))

/-- The real-linear parametrization of the two edge directions `1` and `τ`. -/
def parallelogramCLM (τ : ℂ) : ℝ × ℝ →L[ℝ] ℂ :=
  Complex.ofRealCLM.comp (ContinuousLinearMap.fst ℝ ℝ ℝ) +
    (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight τ

@[simp]
theorem parallelogramCLM_apply (τ : ℂ) (p : ℝ × ℝ) :
    parallelogramCLM τ p = (p.1 : ℂ) + (p.2 : ℂ) * τ := by
  rfl

/-- **Cauchy--Goursat for an affine parallelogram.** The contour integral of an entire function
around an arbitrary affine parallelogram vanishes. -/
theorem parallelogramIntegral_eq_zero_of_differentiable (g : ℂ → ℂ) (τ a : ℂ)
    (hg : Differentiable ℂ g) : parallelogramIntegral g τ a = 0 := by
  let A : ℝ × ℝ → ℂ := fun p => a + parallelogramCLM τ p
  let dg : ℝ × ℝ → ℝ × ℝ →L[ℝ] ℂ := fun p =>
    (ContinuousLinearMap.restrictScalars ℝ
      (ContinuousLinearMap.toSpanSingleton ℂ (deriv g (A p)))).comp (parallelogramCLM τ)
  let f : ℝ × ℝ → ℂ := fun p => τ * g (A p)
  let q : ℝ × ℝ → ℂ := fun p => -g (A p)
  let f' : ℝ × ℝ → ℝ × ℝ →L[ℝ] ℂ := fun p => τ • dg p
  let q' : ℝ × ℝ → ℝ × ℝ →L[ℝ] ℂ := fun p => -(dg p)
  have hA : ∀ p, HasFDerivAt A (parallelogramCLM τ) p := by
    intro p
    exact (parallelogramCLM τ).hasFDerivAt.const_add a
  have hdg : ∀ p, HasFDerivAt (fun p => g (A p)) (dg p) p := by
    intro p
    simpa only [Function.comp_apply] using
      (((hg (A p)).hasDerivAt.hasFDerivAt.restrictScalars ℝ).comp p (hA p))
  have hf : ∀ p, HasFDerivAt f (f' p) p := by
    intro p
    exact (hdg p).const_mul τ
  have hq : ∀ p, HasFDerivAt q (q' p) p := by
    intro p
    exact (hdg p).neg
  have hdiv : ∀ p, f' p (1, 0) + q' p (0, 1) = 0 := by
    intro p
    simp only [f', q', dg, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.neg_apply, ContinuousLinearMap.comp_apply,
      parallelogramCLM_apply]
    have hspan (z : ℂ) :
        (ContinuousLinearMap.restrictScalars ℝ
          (ContinuousLinearMap.toSpanSingleton ℂ (deriv g (A p)))) z =
            deriv g (A p) * z := by
      simp [mul_comm]
    rw [hspan, hspan]
    simp only [ofReal_one, ofReal_zero, zero_mul, add_zero, one_mul, zero_add, smul_eq_mul]
    ring
  have hfc : Continuous f := continuous_iff_continuousAt.mpr fun p => (hf p).continuousAt
  have hqc : Continuous q := continuous_iff_continuousAt.mpr fun p => (hq p).continuousAt
  have hzeroInt : IntegrableOn (fun _ : ℝ × ℝ => (0 : ℂ))
      (uIcc (0 : ℝ) 1 ×ˢ uIcc (0 : ℝ) 1) volume := MeasureTheory.integrableOn_zero
  have hmain := MeasureTheory.integral2_divergence_prod_of_hasFDerivAt_off_countable
    f q f' q' 0 0 1 1 ∅ countable_empty
    hfc.continuousOn hqc.continuousOn
    (fun p _ => hf p) (fun p _ => hq p)
    (by simpa only [hdiv] using hzeroInt)
  have hleft :
      (∫ x : ℝ in 0..1, ∫ y : ℝ in 0..1,
        f' (x, y) (1, 0) + q' (x, y) (0, 1)) = 0 := by
    simp only [hdiv, intervalIntegral.integral_zero]
  rw [hleft] at hmain
  have hm := hmain.symm
  simp [f, q, A, parallelogramCLM_apply, intervalIntegral.integral_neg,
    intervalIntegral.integral_const_mul, add_assoc, add_comm, add_left_comm] at hm
  have hrightArg :
      (∫ y : ℝ in 0..1, g (a + ((y : ℂ) * τ + 1))) =
        ∫ y : ℝ in 0..1, g (a + 1 + (y : ℂ) * τ) := by
    apply integral_congr
    intro y _
    apply congrArg g
    ring
  have htopArg :
      (∫ x : ℝ in 0..1, g (τ + (a + (x : ℂ)))) =
        ∫ x : ℝ in 0..1, g (a + τ + (x : ℂ)) := by
    apply integral_congr
    intro x _
    apply congrArg g
    ring
  rw [hrightArg, htopArg] at hm
  rw [parallelogramIntegral]
  linear_combination hm

end

end GaloisForLFunctions

namespace GaloisForLFunctions

noncomputable section

def parallelogramSquare : Set (ℝ × ℝ) := Icc 0 1 ×ˢ Icc 0 1

def parallelogramOpenSquare : Set (ℝ × ℝ) := Ioo 0 1 ×ˢ Ioo 0 1

theorem parallelogramIntegral_eq_zero_of_continuousOn_of_differentiableAt
    (g : ℂ → ℂ) (τ a : ℂ)
    (hgc : ContinuousOn (fun p : ℝ × ℝ => g (a + parallelogramCLM τ p)) parallelogramSquare)
    (hgd : ∀ p ∈ parallelogramOpenSquare, DifferentiableAt ℂ g (a + parallelogramCLM τ p)) :
    parallelogramIntegral g τ a = 0 := by
  let A : ℝ × ℝ → ℂ := fun p => a + parallelogramCLM τ p
  let dg : ℝ × ℝ → ℝ × ℝ →L[ℝ] ℂ := fun p =>
    (ContinuousLinearMap.restrictScalars ℝ
      (ContinuousLinearMap.toSpanSingleton ℂ (deriv g (A p)))).comp (parallelogramCLM τ)
  let f : ℝ × ℝ → ℂ := fun p => τ * g (A p)
  let q : ℝ × ℝ → ℂ := fun p => -g (A p)
  let f' : ℝ × ℝ → ℝ × ℝ →L[ℝ] ℂ := fun p => τ • dg p
  let q' : ℝ × ℝ → ℝ × ℝ →L[ℝ] ℂ := fun p => -(dg p)
  have hA : ∀ p, HasFDerivAt A (parallelogramCLM τ) p := by
    intro p
    exact (parallelogramCLM τ).hasFDerivAt.const_add a
  have hdg : ∀ p ∈ parallelogramOpenSquare,
      HasFDerivAt (fun p => g (A p)) (dg p) p := by
    intro p hp
    simpa only [Function.comp_apply] using
      ((((hgd p hp).hasDerivAt.hasFDerivAt.restrictScalars ℝ)).comp p (hA p))
  have hf : ∀ p ∈ parallelogramOpenSquare, HasFDerivAt f (f' p) p := by
    intro p hp
    exact (hdg p hp).const_mul τ
  have hq : ∀ p ∈ parallelogramOpenSquare, HasFDerivAt q (q' p) p := by
    intro p hp
    exact (hdg p hp).neg
  have hdiv : ∀ p, f' p (1, 0) + q' p (0, 1) = 0 := by
    intro p
    simp only [f', q', dg, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.neg_apply, ContinuousLinearMap.comp_apply,
      parallelogramCLM_apply]
    have hspan (z : ℂ) :
        (ContinuousLinearMap.restrictScalars ℝ
          (ContinuousLinearMap.toSpanSingleton ℂ (deriv g (A p)))) z = deriv g (A p) * z := by
      simp [mul_comm]
    rw [hspan, hspan]
    simp only [ofReal_one, ofReal_zero, zero_mul, add_zero, one_mul, zero_add, smul_eq_mul]
    ring
  have hfc : ContinuousOn f parallelogramSquare := by
    simpa [f, A] using (continuousOn_const.mul hgc)
  have hqc : ContinuousOn q parallelogramSquare := by
    simpa [q, A] using hgc.neg
  have hzeroInt : IntegrableOn (fun _ : ℝ × ℝ => (0 : ℂ))
      (uIcc (0 : ℝ) 1 ×ˢ uIcc (0 : ℝ) 1) volume := MeasureTheory.integrableOn_zero
  have hmain := MeasureTheory.integral2_divergence_prod_of_hasFDerivAt_off_countable
    f q f' q' 0 0 1 1 ∅ countable_empty
    (by simpa [parallelogramSquare] using hfc) (by simpa [parallelogramSquare] using hqc)
    (by
      intro p hp
      apply hf p
      simpa [parallelogramOpenSquare] using hp.1)
    (by
      intro p hp
      apply hq p
      simpa [parallelogramOpenSquare] using hp.1)
    (by simpa only [hdiv] using hzeroInt)
  have hleft :
      (∫ x : ℝ in 0..1, ∫ y : ℝ in 0..1,
        f' (x, y) (1, 0) + q' (x, y) (0, 1)) = 0 := by
    simp only [hdiv, intervalIntegral.integral_zero]
  rw [hleft] at hmain
  have hm := hmain.symm
  simp [f, q, A, parallelogramCLM_apply, intervalIntegral.integral_neg,
    intervalIntegral.integral_const_mul, add_assoc, add_comm, add_left_comm] at hm
  have hrightArg :
      (∫ y : ℝ in 0..1, g (a + ((y : ℂ) * τ + 1))) =
        ∫ y : ℝ in 0..1, g (a + 1 + (y : ℂ) * τ) := by
    apply integral_congr
    intro y _
    apply congrArg g
    ring
  have htopArg :
      (∫ x : ℝ in 0..1, g (τ + (a + (x : ℂ)))) =
        ∫ x : ℝ in 0..1, g (a + τ + (x : ℂ)) := by
    apply integral_congr
    intro x _
    apply congrArg g
    ring
  rw [hrightArg, htopArg] at hm
  rw [parallelogramIntegral]
  linear_combination hm

end

end GaloisForLFunctions
