import GaloisForLFunctions.RHTower.DeningerMeyerHilbertFlow
import GaloisForLFunctions.HTGeometry.LieTrotterProduct

/-! # Whole-line convolution by every original Meyer source

The all-weight source condition admits Bochner averages of the actual
full-Jordan flow on the whole time line. No support or sign restriction
and no uniform bound on Xi multiplicities is imposed.
-/

noncomputable section
open Complex MeasureTheory Filter ContinuousLinearMap
open GaloisForLFunctions.HTGeometry

namespace RHTower

theorem deningerMeyerHilbertFlowBound_le (t : ℝ) :
    deningerMeyerHilbertFlowBound t ≤ Real.exp (2*|t|) := by
  have hs : ‖deningerHasseShiftEvolution t‖ ≤ Real.exp |t| := by
    rcases subsingleton_or_nontrivial DeningerArithmeticJetHilbert with h | h
    · haveI := h
      rw [show deningerHasseShiftEvolution t = 0 from Subsingleton.elim _ _, norm_zero]
      exact (Real.exp_pos _).le
    · haveI := h
      apply (GaloisForLFunctions.HTGeometry.norm_exp_le_exp_norm
        ((t : ℂ) • deningerHasseHilbertShift)).trans
      apply Real.exp_le_exp.mpr
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
      simpa using mul_le_mul_of_nonneg_left norm_deningerHasseHilbertShift_le (abs_nonneg t)
  calc deningerMeyerHilbertFlowBound t ≤ Real.exp |t| * Real.exp |t| :=
      mul_le_mul_of_nonneg_left hs (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem integrable_deningerMeyerHilbertConvolution
    (g : DeningerMeyerStrongLogTarget) (x : DeningerArithmeticJetHilbert) :
    Integrable (fun t : ℝ => g.val t • deningerMeyerHilbertFlow t x) := by
  apply ((integrable_deningerMeyerHasseSourceMass g).mul_const ‖x‖).mono'
    ((g.property.smooth.continuous.smul
      (continuous_deningerMeyerHilbertFlow_orbit x)).aestronglyMeasurable)
  filter_upwards with t
  change ‖g.val t • deningerMeyerHilbertFlow t x‖ ≤ _
  rw [norm_smul]
  calc ‖g.val t‖ * ‖deningerMeyerHilbertFlow t x‖ ≤
      ‖g.val t‖ * (Real.exp (2*|t|)*‖x‖) :=
        mul_le_mul_of_nonneg_left
          ((norm_deningerMeyerHilbertFlow_apply t x).trans
            (mul_le_mul_of_nonneg_right (deningerMeyerHilbertFlowBound_le t) (norm_nonneg x)))
          (norm_nonneg _)
    _ = _ := by ring

def deningerMeyerHilbertConvolutionAverage
    (g : DeningerMeyerStrongLogTarget) (x : DeningerArithmeticJetHilbert) :
    DeningerArithmeticJetHilbert := ∫ t : ℝ, g.val t • deningerMeyerHilbertFlow t x

theorem norm_deningerMeyerHilbertConvolutionAverage
    (g : DeningerMeyerStrongLogTarget) (x : DeningerArithmeticJetHilbert) :
    ‖deningerMeyerHilbertConvolutionAverage g x‖ ≤ deningerMeyerHasseSourceMass g * ‖x‖ := by
  have hb (t : ℝ) : ‖g.val t • deningerMeyerHilbertFlow t x‖ ≤
      (Real.exp (2*|t|)*‖g.val t‖)*‖x‖ := by
    rw [norm_smul]
    calc ‖g.val t‖ * ‖deningerMeyerHilbertFlow t x‖ ≤
        ‖g.val t‖ * (Real.exp (2*|t|)*‖x‖) :=
          mul_le_mul_of_nonneg_left
            ((norm_deningerMeyerHilbertFlow_apply t x).trans
              (mul_le_mul_of_nonneg_right (deningerMeyerHilbertFlowBound_le t) (norm_nonneg x)))
            (norm_nonneg _)
      _ = _ := by ring
  simpa only [deningerMeyerHilbertConvolutionAverage, integral_mul_const,
    deningerMeyerHasseSourceMass] using
      norm_integral_le_of_norm_le ((integrable_deningerMeyerHasseSourceMass g).mul_const ‖x‖)
        (Eventually.of_forall hb)

def deningerMeyerHilbertConvolutionLM (g : DeningerMeyerStrongLogTarget) :
    DeningerArithmeticJetHilbert →ₗ[ℂ] DeningerArithmeticJetHilbert where
  toFun := deningerMeyerHilbertConvolutionAverage g
  map_add' x y := by
    simp only [deningerMeyerHilbertConvolutionAverage, map_add, smul_add]
    exact integral_add (integrable_deningerMeyerHilbertConvolution g x)
      (integrable_deningerMeyerHilbertConvolution g y)
  map_smul' c x := by
    change (∫ t : ℝ, g.val t • deningerMeyerHilbertFlow t (c • x)) =
      c • ∫ t : ℝ, g.val t • deningerMeyerHilbertFlow t x
    calc _ = ∫ t : ℝ, c • (g.val t • deningerMeyerHilbertFlow t x) :=
        integral_congr_ae (Eventually.of_forall fun t => by rw [map_smul, smul_comm])
      _ = _ := integral_smul c _

/-- Literal convolution of the full flow by an arbitrary original source. -/
def deningerMeyerHilbertConvolution (g : DeningerMeyerStrongLogTarget) :
    DeningerArithmeticJetHilbert →L[ℂ] DeningerArithmeticJetHilbert :=
  (deningerMeyerHilbertConvolutionLM g).mkContinuous (deningerMeyerHasseSourceMass g)
    (norm_deningerMeyerHilbertConvolutionAverage g)

theorem deningerMeyerHilbertConvolution_apply (g : DeningerMeyerStrongLogTarget)
    (x : DeningerArithmeticJetHilbert) :
    deningerMeyerHilbertConvolution g x =
      ∫ t : ℝ, g.val t • deningerMeyerHilbertFlow t x := rfl

theorem deningerMeyerHilbertConvolution_coordinate (g : DeningerMeyerStrongLogTarget)
    (x : DeningerArithmeticJetHilbert) (q : DeningerArithmeticJetCoordinate) :
    deningerMeyerHilbertConvolution g x q =
      ∫ t : ℝ, g.val t * deningerMeyerHilbertFlow t x q := by
  exact ((lp.evalCLM ℂ (fun _ : DeningerArithmeticJetCoordinate => ℂ) 2 q).integral_comp_comm
    (integrable_deningerMeyerHilbertConvolution g x)).symm

theorem deningerMeyerHilbertConvolution_add (g h : DeningerMeyerStrongLogTarget) :
    deningerMeyerHilbertConvolution (g+h) =
      deningerMeyerHilbertConvolution g + deningerMeyerHilbertConvolution h := by
  apply ContinuousLinearMap.ext
  intro x
  simp only [deningerMeyerHilbertConvolution_apply, Submodule.coe_add,
    Pi.add_apply, add_smul, add_apply]
  exact integral_add (integrable_deningerMeyerHilbertConvolution g x)
    (integrable_deningerMeyerHilbertConvolution h x)

theorem deningerMeyerHilbertConvolution_smul (c : ℂ) (g : DeningerMeyerStrongLogTarget) :
    deningerMeyerHilbertConvolution (c • g) = c • deningerMeyerHilbertConvolution g := by
  apply ContinuousLinearMap.ext
  intro x
  change (∫ t : ℝ, (c*g.val t) • deningerMeyerHilbertFlow t x) =
    c • ∫ t : ℝ, g.val t • deningerMeyerHilbertFlow t x
  simp only [mul_smul]
  exact integral_smul c _

end RHTower
