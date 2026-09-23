import GaloisForLFunctions.RHTower.DeningerZetaLeftLine
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.MellinTransform

/-!
# Right-line inverse data for the zero-damping sewn Green scalar

The centered Gaussian divided by the two reflected zeta factors is absolutely
integrable on `Re s = 2`.  The proof uses the corpus's uniform reciprocal-zeta
bounds on `Re s = 2` and `Re s = -1`, and a Gaussian majorant.  This supplies a
convergent inverse-Mellin datum at zero damping.  Its identification with a
completion of the literal damped Green source, including residue transport
across damping poles, remains a separate source-domain problem.
-/

open Complex MeasureTheory
namespace RHTower
noncomputable section

/-- Explicit centered Gaussian Mellin factor of the reflected source. -/
def deningerOriginalGreenCenteredGaussianMellin (s : ℂ) : ℂ :=
  Complex.exp ((s - 1 / 2) ^ 2 / (4 * (Real.pi : ℂ)))

/-- Prime-independent zero-damping scalar after sewing the original prime Green denominator. -/
def deningerOriginalGreenZeroDampingSewnSymbol (s : ℂ) : ℂ :=
  deningerOriginalGreenCenteredGaussianMellin s /
    (riemannZeta s * riemannZeta (1 - s))

private theorem norm_inv_zeta_left_le (t : ℝ) :
    ‖(riemannZeta (-1 + (t : ℂ) * I))⁻¹‖ ≤ 8 * Real.pi ^ 2 := by
  have hpi : (0 : ℝ) < 8 * Real.pi ^ 2 := by positivity
  have hlower := norm_riemannZeta_left_line_ge_const t
  have hpos : 0 < ‖riemannZeta (-1 + (t : ℂ) * I)‖ :=
    lt_of_lt_of_le (div_pos one_pos hpi) hlower
  rw [norm_inv]
  exact (inv_le_iff_one_le_mul₀ hpos).2 (by
    have h : 1 ≤ ‖riemannZeta (-1 + (t : ℂ) * I)‖ * (8 * Real.pi ^ 2) := by
      exact (div_le_iff₀ hpi).1 hlower
    nlinarith)

private theorem norm_gaussian_line (t : ℝ) :
    ‖deningerOriginalGreenCenteredGaussianMellin (2 + (t : ℂ) * I)‖ =
      Real.exp (((9 / 4 : ℝ) - t ^ 2) / (4 * Real.pi)) := by
  rw [deningerOriginalGreenCenteredGaussianMellin, Complex.norm_exp]
  congr 1
  have harg : (2 + (t : ℂ) * I) - 1 / 2 = (3 / 2 : ℂ) + (t : ℂ) * I := by ring
  rw [harg]
  have hcast : (4 : ℂ) * (Real.pi : ℂ) = ((4 * Real.pi : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hcast, Complex.div_ofReal_re]
  have hsq : (((3 / 2 : ℂ) + (t : ℂ) * I) ^ (2 : ℕ)).re = 9 / 4 - t ^ 2 := by
    simp [pow_two, Complex.mul_re]
    ring
  rw [hsq]

private theorem norm_inv_zeta_right_le (t : ℝ) :
    ‖(riemannZeta (2 + (t : ℂ) * I))⁻¹‖ ≤ 4 := by
  have hlower : (1 : ℝ) / 4 ≤ ‖riemannZeta (2 + (t : ℂ) * I)‖ :=
    norm_riemannZeta_ge_of_two_le_re (by simp)
  have hpos : 0 < ‖riemannZeta (2 + (t : ℂ) * I)‖ :=
    lt_of_lt_of_le (by norm_num) hlower
  rw [norm_inv]
  exact (inv_le_iff_one_le_mul₀ hpos).2 (by nlinarith [hlower])

private theorem integrable_gaussian_line :
    Integrable (fun t : ℝ => Real.exp (((9 / 4 : ℝ) - t ^ 2) / (4 * Real.pi))) := by
  have hcoef : (0 : ℝ) < 1 / (4 * Real.pi) := by positivity
  have hint : Integrable (fun t : ℝ => Real.exp (-(1 / (4 * Real.pi)) * t ^ 2)) :=
    integrable_exp_neg_mul_sq hcoef
  have heq : (fun t : ℝ => Real.exp (((9 / 4 : ℝ) - t ^ 2) / (4 * Real.pi))) =
      (fun t : ℝ => Real.exp ((9 / 4 : ℝ) / (4 * Real.pi)) *
        Real.exp (-(1 / (4 * Real.pi)) * t ^ 2)) := by
    funext t
    rw [← Real.exp_add]
    congr 1
    ring
  rw [heq]
  exact hint.const_mul _

/-- Uniform Gaussian majorant of the zero-damping symbol on the safe right line. -/
theorem deningerOriginalGreenZeroDampingSewnSymbol_norm_line_two_le (t : ℝ) :
    ‖deningerOriginalGreenZeroDampingSewnSymbol (2 + (t : ℂ) * I)‖ ≤
      (32 * Real.pi ^ 2) *
        Real.exp (((9 / 4 : ℝ) - t ^ 2) / (4 * Real.pi)) := by
  have hright := norm_inv_zeta_right_le t
  have hleft := norm_inv_zeta_left_le (-t)
  have harg : (1 : ℂ) - (2 + (t : ℂ) * I) = -1 + ((-t : ℝ) : ℂ) * I := by
    push_cast
    ring
  unfold deningerOriginalGreenZeroDampingSewnSymbol
  rw [harg]
  simp only [div_eq_mul_inv, mul_inv_rev, norm_mul]
  rw [norm_gaussian_line]
  have hprod :
      ‖(riemannZeta (-1 + ((-t : ℝ) : ℂ) * I))⁻¹‖ *
          ‖(riemannZeta (2 + (t : ℂ) * I))⁻¹‖ ≤
        (8 * Real.pi ^ 2) * 4 := by
    calc
      _ ≤ (8 * Real.pi ^ 2) * ‖(riemannZeta (2 + (t : ℂ) * I))⁻¹‖ :=
        mul_le_mul_of_nonneg_right hleft (norm_nonneg _)
      _ ≤ (8 * Real.pi ^ 2) * 4 :=
        mul_le_mul_of_nonneg_left hright (by positivity)
  calc
    _ ≤ Real.exp (((9 / 4 : ℝ) - t ^ 2) / (4 * Real.pi)) *
          ((8 * Real.pi ^ 2) * 4) :=
      mul_le_mul_of_nonneg_left hprod (Real.exp_nonneg _)
    _ = _ := by ring

private theorem continuous_zeta_line (σ : ℝ) (hσ : σ ≠ 1) :
    Continuous (fun t : ℝ => riemannZeta ((σ : ℂ) + (t : ℂ) * I)) := by
  have hpath : Continuous (fun t : ℝ => (σ : ℂ) + (t : ℂ) * I) := by fun_prop
  apply continuous_iff_continuousAt.mpr
  intro t
  have hs1 : ((σ : ℂ) + (t : ℂ) * I) ≠ 1 := by
    intro heq
    have hre := congrArg Complex.re heq
    simp at hre
    exact hσ hre
  exact ContinuousAt.comp (g := riemannZeta)
    (f := fun u : ℝ => (σ : ℂ) + (u : ℂ) * I) (x := t)
    (differentiableAt_riemannZeta hs1).continuousAt hpath.continuousAt

private theorem continuous_symbol_line :
    Continuous (fun t : ℝ =>
      deningerOriginalGreenZeroDampingSewnSymbol (2 + (t : ℂ) * I)) := by
  have hgauss : Continuous (fun t : ℝ =>
      deningerOriginalGreenCenteredGaussianMellin (2 + (t : ℂ) * I)) := by
    unfold deningerOriginalGreenCenteredGaussianMellin
    fun_prop
  have hright : Continuous (fun t : ℝ => riemannZeta (2 + (t : ℂ) * I)) :=
    continuous_zeta_line 2 (by norm_num)
  have hleft : Continuous (fun t : ℝ => riemannZeta (1 - (2 + (t : ℂ) * I))) := by
    convert (continuous_zeta_line (-1) (by norm_num)).comp continuous_neg using 1
    funext t
    congr 1
    push_cast
    ring
  have hright0 (t : ℝ) : riemannZeta (2 + (t : ℂ) * I) ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re (by simp)
  have hleft0 (t : ℝ) : riemannZeta (1 - (2 + (t : ℂ) * I)) ≠ 0 := by
    have harg : (1 : ℂ) - (2 + (t : ℂ) * I) = -1 + ((-t : ℝ) : ℂ) * I := by
      push_cast
      ring
    rw [harg]
    have hbound := norm_riemannZeta_left_line_ge_const (-t)
    intro hz
    rw [hz, norm_zero] at hbound
    have hpos : (0 : ℝ) < 1 / (8 * Real.pi ^ 2) := by positivity
    linarith
  change Continuous (fun t : ℝ =>
    deningerOriginalGreenCenteredGaussianMellin (2 + (t : ℂ) * I) /
      (riemannZeta (2 + (t : ℂ) * I) *
        riemannZeta (1 - (2 + (t : ℂ) * I))))
  exact hgauss.div (hright.mul hleft) (fun t => mul_ne_zero (hright0 t) (hleft0 t))

/-- The sewn zero-damping scalar is absolutely integrable on `Re s = 2`. -/
theorem deningerOriginalGreenZeroDampingSewnSymbol_verticalIntegrable_two :
    VerticalIntegrable deningerOriginalGreenZeroDampingSewnSymbol 2 := by
  have hmajor : Integrable (fun t : ℝ => (32 * Real.pi ^ 2) *
      Real.exp (((9 / 4 : ℝ) - t ^ 2) / (4 * Real.pi))) :=
    integrable_gaussian_line.const_mul _
  refine Integrable.mono' hmajor continuous_symbol_line.aestronglyMeasurable ?_
  filter_upwards with t
  exact deningerOriginalGreenZeroDampingSewnSymbol_norm_line_two_le t

/-- Reflection of the zero-damping sewn scalar exchanges the two safe lines. -/
theorem deningerOriginalGreenZeroDampingSewnSymbol_reflect (s : ℂ) :
    deningerOriginalGreenZeroDampingSewnSymbol (1 - s) =
      deningerOriginalGreenZeroDampingSewnSymbol s := by
  have hsq : ((1 - s) - 1 / 2) ^ 2 = (s - 1 / 2) ^ 2 := by ring
  have hsub : (1 : ℂ) - (1 - s) = s := by ring
  unfold deningerOriginalGreenZeroDampingSewnSymbol
    deningerOriginalGreenCenteredGaussianMellin
  rw [hsub, hsq, mul_comm (riemannZeta (1 - s)) (riemannZeta s)]

private theorem deningerOriginalGreenZeroDampingSewnSymbol_left_eq_right_neg (t : ℝ) :
    deningerOriginalGreenZeroDampingSewnSymbol (-1 + (t : ℂ) * I) =
      deningerOriginalGreenZeroDampingSewnSymbol (2 + ((-t : ℝ) : ℂ) * I) := by
  have harg : (-1 : ℂ) + (t : ℂ) * I =
      1 - (2 + ((-t : ℝ) : ℂ) * I) := by
    push_cast
    ring_nf
  rw [harg, deningerOriginalGreenZeroDampingSewnSymbol_reflect]

/-- The reflected safe line has the same Gaussian integrability bound. -/
theorem deningerOriginalGreenZeroDampingSewnSymbol_verticalIntegrable_neg_one :
    VerticalIntegrable deningerOriginalGreenZeroDampingSewnSymbol (-1) := by
  have hmajor : Integrable (fun t : ℝ => (32 * Real.pi ^ 2) *
      Real.exp (((9 / 4 : ℝ) - t ^ 2) / (4 * Real.pi))) :=
    integrable_gaussian_line.const_mul _
  have hcont : Continuous (fun t : ℝ =>
      deningerOriginalGreenZeroDampingSewnSymbol (-1 + (t : ℂ) * I)) := by
    convert continuous_symbol_line.comp continuous_neg using 1
    funext t
    exact deningerOriginalGreenZeroDampingSewnSymbol_left_eq_right_neg t
  have hleft : Integrable (fun t : ℝ =>
      deningerOriginalGreenZeroDampingSewnSymbol (-1 + (t : ℂ) * I)) := by
    refine Integrable.mono' hmajor hcont.aestronglyMeasurable ?_
    filter_upwards with t
    rw [deningerOriginalGreenZeroDampingSewnSymbol_left_eq_right_neg]
    simpa only [neg_sq] using
      deningerOriginalGreenZeroDampingSewnSymbol_norm_line_two_le (-t)
  simpa [VerticalIntegrable] using hleft

/-- An inverse-Mellin source datum on the safe right line. -/
def deningerOriginalGreenZeroDampingRightLineSource (x : ℝ) : ℂ :=
  mellinInv 2 deningerOriginalGreenZeroDampingSewnSymbol x

end
end RHTower
