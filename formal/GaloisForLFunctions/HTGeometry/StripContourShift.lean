import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# The horizontal contour shift on a strip

If a function is holomorphic on a closed horizontal strip, is integrable on the two boundary lines,
and its vertical segments at `±R` contribute nothing in the limit, then its integrals along the two
boundary lines agree.  This is Cauchy's theorem for rectangles together with the exhaustion of the
line by `[-R, R]`.
-/

open Complex MeasureTheory Filter Set

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

omit [CompleteSpace X] in
/-- **The horizontal contour shift.**  A holomorphic function with vanishing vertical contribution
has the same integral on the two boundary lines of a strip. -/
theorem integral_line_shift {G : ℂ → X} {a b : ℝ}
    (hG : ∀ z : ℂ, z.im ∈ uIcc a b → DifferentiableAt ℂ G z)
    (hintA : Integrable (fun x : ℝ => G ((x : ℂ) + (a : ℂ) * I)))
    (hintB : Integrable (fun x : ℝ => G ((x : ℂ) + (b : ℂ) * I)))
    (hvert : Tendsto (fun R : ℝ => ‖∫ y in a..b, G ((R : ℂ) + (y : ℂ) * I)‖
        + ‖∫ y in a..b, G (-(R : ℂ) + (y : ℂ) * I)‖) atTop (nhds 0)) :
    (∫ x : ℝ, G ((x : ℂ) + (a : ℂ) * I)) = ∫ x : ℝ, G ((x : ℂ) + (b : ℂ) * I) := by
  have hrect : ∀ R : ℝ,
      (((∫ x in (-R)..R, G ((x : ℂ) + (a : ℂ) * I))
            - ∫ x in (-R)..R, G ((x : ℂ) + (b : ℂ) * I))
          + I • ∫ y in a..b, G ((R : ℂ) + (y : ℂ) * I))
        - I • ∫ y in a..b, G (-(R : ℂ) + (y : ℂ) * I) = 0 := by
    intro R
    have hdiff : DifferentiableOn ℂ G
        (uIcc (-(R : ℂ) + (a : ℂ) * I).re ((R : ℂ) + (b : ℂ) * I).re ×ℂ
          uIcc (-(R : ℂ) + (a : ℂ) * I).im ((R : ℂ) + (b : ℂ) * I).im) := by
      intro z hz
      refine (hG z ?_).differentiableWithinAt
      have him : z.im ∈ uIcc (-(R : ℂ) + (a : ℂ) * I).im ((R : ℂ) + (b : ℂ) * I).im := hz.2
      simpa using him
    have hzero := Complex.integral_boundary_rect_eq_zero_of_differentiableOn G
      (-(R : ℂ) + (a : ℂ) * I) ((R : ℂ) + (b : ℂ) * I) hdiff
    simp only [Complex.add_re, Complex.add_im, Complex.neg_re, Complex.neg_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re,
      Complex.I_im, mul_zero, mul_one, sub_zero, zero_add, add_zero,
      neg_zero, Complex.ofReal_neg] at hzero
    exact hzero
  have hAlim : Tendsto (fun R : ℝ => ∫ x in (-R)..R, G ((x : ℂ) + (a : ℂ) * I)) atTop
      (nhds (∫ x : ℝ, G ((x : ℂ) + (a : ℂ) * I))) :=
    intervalIntegral_tendsto_integral hintA
      (tendsto_neg_atTop_atBot.comp tendsto_id) tendsto_id
  have hBlim : Tendsto (fun R : ℝ => ∫ x in (-R)..R, G ((x : ℂ) + (b : ℂ) * I)) atTop
      (nhds (∫ x : ℝ, G ((x : ℂ) + (b : ℂ) * I))) :=
    intervalIntegral_tendsto_integral hintB
      (tendsto_neg_atTop_atBot.comp tendsto_id) tendsto_id
  have hVlim : Tendsto (fun R : ℝ => (I • ∫ y in a..b, G ((R : ℂ) + (y : ℂ) * I))
      - I • ∫ y in a..b, G (-(R : ℂ) + (y : ℂ) * I)) atTop (nhds 0) := by
    refine squeeze_zero_norm (fun R => ?_) hvert
    refine le_trans (norm_sub_le _ _) ?_
    rw [norm_smul, norm_smul, Complex.norm_I, one_mul, one_mul]
  have hsum : Tendsto (fun R : ℝ =>
      (((∫ x in (-R)..R, G ((x : ℂ) + (a : ℂ) * I))
            - ∫ x in (-R)..R, G ((x : ℂ) + (b : ℂ) * I))
          + I • ∫ y in a..b, G ((R : ℂ) + (y : ℂ) * I))
        - I • ∫ y in a..b, G (-(R : ℂ) + (y : ℂ) * I)) atTop
      (nhds ((∫ x : ℝ, G ((x : ℂ) + (a : ℂ) * I)) - ∫ x : ℝ, G ((x : ℂ) + (b : ℂ) * I))) := by
    have hcomb := (hAlim.sub hBlim).add hVlim
    have hfun : (fun R : ℝ => ((∫ x in (-R)..R, G ((x : ℂ) + (a : ℂ) * I))
          - ∫ x in (-R)..R, G ((x : ℂ) + (b : ℂ) * I))
        + ((I • ∫ y in a..b, G ((R : ℂ) + (y : ℂ) * I))
          - I • ∫ y in a..b, G (-(R : ℂ) + (y : ℂ) * I)))
        = fun R : ℝ => (((∫ x in (-R)..R, G ((x : ℂ) + (a : ℂ) * I))
              - ∫ x in (-R)..R, G ((x : ℂ) + (b : ℂ) * I))
            + I • ∫ y in a..b, G ((R : ℂ) + (y : ℂ) * I))
          - I • ∫ y in a..b, G (-(R : ℂ) + (y : ℂ) * I) := by
      funext R
      rw [add_sub_assoc]
    rw [hfun] at hcomb
    simpa using hcomb
  have hzerolim : Tendsto (fun R : ℝ =>
      (((∫ x in (-R)..R, G ((x : ℂ) + (a : ℂ) * I))
            - ∫ x in (-R)..R, G ((x : ℂ) + (b : ℂ) * I))
          + I • ∫ y in a..b, G ((R : ℂ) + (y : ℂ) * I))
        - I • ∫ y in a..b, G (-(R : ℂ) + (y : ℂ) * I)) atTop (nhds 0) := by
    simp only [hrect]
    exact tendsto_const_nhds
  exact sub_eq_zero.mp (tendsto_nhds_unique hsum hzerolim)

end

end GaloisForLFunctions.HTGeometry
