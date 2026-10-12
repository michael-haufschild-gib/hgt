import GaloisForLFunctions.HTGeometry.PaperHalfLineOrder
import GaloisForLFunctions.HTGeometry.PaperCayleySourceBounds

/-! # Sign-faithful bounded observables of full continuous source tails -/

namespace GaloisForLFunctions.HTGeometry
noncomputable section
open MeasureTheory Set

private abbrev H := Lp ℂ 2 halfLineMeasure

/-- The signed imaginary coordinate of the invertible Cayley encoding. -/
def paperSignedCayley (x : ℝ) : ℝ := -(realCayley x).im

theorem paperSignedCayley_formula (x : ℝ) :
    paperSignedCayley x = 2 * x / (1 + x ^ 2) := by
  rw [paperSignedCayley, realCayley, Complex.div_im]
  simp only [Complex.sub_re, Complex.ofReal_re, Complex.I_re, sub_zero,
    Complex.add_re, add_zero, Complex.sub_im, Complex.ofReal_im, Complex.I_im,
    zero_sub, Complex.add_im, zero_add, Complex.normSq_apply]
  ring

theorem continuous_paperSignedCayley : Continuous paperSignedCayley :=
  (Complex.continuous_im.comp continuous_realCayley).neg

theorem paperSignedCayley_abs_le (x : ℝ) : |paperSignedCayley x| ≤ 1 := by
  simpa only [paperSignedCayley, abs_neg, norm_realCayley] using
    Complex.abs_im_le_norm (realCayley x)

theorem paperSignedCayley_mul_nonneg_iff (ε x : ℝ) :
    0 ≤ ε * paperSignedCayley x ↔ 0 ≤ ε * x := by
  rw [paperSignedCayley_formula, ← mul_div_assoc,
    le_div_iff₀ (show 0 < 1 + x ^ 2 by positivity), zero_mul]
  constructor <;> intro h <;> nlinarith

def paperHalfLineSignedSymbol (F : C(ℝ, ℝ)) (T ε : ℝ) : C(ℝ, ℝ) :=
  ⟨fun x => ε * paperSignedCayley (F (T + x)),
    continuous_const.mul (continuous_paperSignedCayley.comp
      (F.continuous.comp (continuous_const.add continuous_id)))⟩

theorem paperHalfLineSignedSymbol_bound (F : C(ℝ, ℝ)) (T ε x : ℝ) :
    ‖(paperHalfLineSignedSymbol F T ε x : ℂ)‖ ≤ |ε| := by
  rw [Complex.norm_real, Real.norm_eq_abs]
  change |ε * paperSignedCayley (F (T + x))| ≤ |ε|
  rw [abs_mul]
  exact (mul_le_mul_of_nonneg_left (paperSignedCayley_abs_le _) (abs_nonneg ε)).trans_eq
    (mul_one _)

def paperHalfLineSignedCayley (F : C(ℝ, ℝ)) (T ε : ℝ) : H →L[ℂ] H :=
  lpBoundedMulCLM (Complex.continuous_ofReal.comp
    (paperHalfLineSignedSymbol F T ε).continuous).measurable (abs_nonneg ε)
    (paperHalfLineSignedSymbol_bound F T ε)

theorem paperHalfLineSignedCayley_coeFn (F : C(ℝ, ℝ)) (T ε : ℝ) (f : H) :
    (paperHalfLineSignedCayley F T ε f : ℝ → ℂ) =ᵐ[halfLineMeasure]
      fun x => ((ε * paperSignedCayley (F (T + x)) : ℝ) : ℂ) * f x :=
  lpBoundedMulCLM_coeFn _ _ _ f

theorem paperHalfLineSignedCayley_selfAdjoint (F : C(ℝ, ℝ)) (T ε : ℝ) :
    IsSelfAdjoint (paperHalfLineSignedCayley F T ε) :=
  paperHalfLineRealMul_selfAdjoint (paperHalfLineSignedSymbol F T ε).continuous
    (abs_nonneg ε) (paperHalfLineSignedSymbol_bound F T ε)

theorem paperHalfLineSignedCayley_neg (F : C(ℝ, ℝ)) (T ε : ℝ) :
    paperHalfLineSignedCayley F T (-ε) = -paperHalfLineSignedCayley F T ε := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [paperHalfLineSignedCayley_coeFn F T (-ε) f,
    Lp.coeFn_neg (paperHalfLineSignedCayley F T ε f),
    paperHalfLineSignedCayley_coeFn F T ε f] with x hM hN hP
  change (paperHalfLineSignedCayley F T (-ε) f : ℝ → ℂ) x =
    ((-(paperHalfLineSignedCayley F T ε f) : H) : ℝ → ℂ) x
  rw [hM, hN, Pi.neg_apply, hP]
  push_cast
  ring

/-- Compact positivity repair is equivalent to the literal sign condition on the whole tail. -/
theorem paperHalfLineSignedCayley_compact_positive_iff (F : C(ℝ, ℝ)) (T ε : ℝ) :
    (∃ K : compactOperatorStarAlgebra H,
      (paperHalfLineSignedCayley F T ε + K.1).IsPositive) ↔
        ∀ t ≥ T, 0 ≤ ε * F t := by
  rw [paperHalfLineSignedCayley,
    paperHalfLineRealMul_compact_positive_iff (paperHalfLineSignedSymbol F T ε).continuous
      (abs_nonneg ε) (paperHalfLineSignedSymbol_bound F T ε)]
  change (∀ x ≥ 0, 0 ≤ ε * paperSignedCayley (F (T + x))) ↔ _
  simp only [paperSignedCayley_mul_nonneg_iff]
  constructor
  · intro h t ht
    simpa only [add_sub_cancel] using h (t - T) (by linarith)
  · intro h x hx
    exact h (T + x) (by linarith)

/-- A full source interval obstructs every nonzero scalar orientation of compact repair. -/
theorem paperHalfLineSignedCayley_no_repair_of_interval (F : C(ℝ, ℝ)) (T : ℝ)
    {δ : ℝ} (hδ : 0 < δ) (hI : Icc (-δ) δ ⊆ F '' Ioi T) (ε : ℝˣ) :
    ¬ ∃ K : compactOperatorStarAlgebra H,
      (paperHalfLineSignedCayley F T (ε : ℝ) + K.1).IsPositive := by
  rw [paperHalfLineSignedCayley_compact_positive_iff]
  intro h
  rcases lt_or_gt_of_ne (Units.ne_zero ε) with hn | hp
  · obtain ⟨t, ht, hF⟩ := hI (show δ ∈ Icc (-δ) δ by constructor <;> linarith)
    have hz := h t ht.le
    rw [hF] at hz
    exact (not_le_of_gt (mul_neg_of_neg_of_pos hn hδ)) hz
  · obtain ⟨t, ht, hF⟩ := hI (show -δ ∈ Icc (-δ) δ by constructor <;> linarith)
    have hz := h t ht.le
    rw [hF] at hz
    exact (not_le_of_gt (mul_neg_of_pos_of_neg hp (neg_neg_of_pos hδ))) hz

end
end GaloisForLFunctions.HTGeometry
