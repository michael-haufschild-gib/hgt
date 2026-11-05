import GaloisForLFunctions.SignedWindowCriticality.TheWindowReadsTheOutsideChargesOfAThetaGauge
import GaloisForLFunctions.ArithmeticCriticalityTheory.ShiftedGroundStateKernelBounds

/-!
# Signed theta gauges reverse the even deficit

A theta gauge `ω = Σ_j α_jτ_{b_j}` is exact on the line, and on a window `S = (−c, c)` the even sector
reads it through (SWC `fullZeroForm_evenThetaGauge_window`)

  `Ẑ(Φωu) = J_{Φω}(u) − 2V_c^S(u) − 2τ_c^S ∫u²Φω cosh(x/2)`,   `τ_c^S = A/2 − ∫_SΦω cosh(x/2)`,

the outside cosh charge `τ_c^S` entering with the pole's sign. For a nonnegative even theta gauge
`τ_c^S > 0`: an outside deficit (SWC `evenThetaGauge_coshChargedDefect_neg`). This module is the
positive survivor of that no-go, for review §2.7 Q3.

* **The deficit is an artifact of nonnegative gauges** (`exists_signedThetaGauge`). For every window
  there is an even three-translate gauge `ω = τ_0 − ¼(τ_b + τ_{−b})`, `b ≥ max(2c, 4)`, whose
  coordinate `Φω` is positive on the window and whose outside cosh charge is negative.
* **In such a gauge the potential term of the even sector is a credit**
  (`fullZeroForm_signedThetaGauge_eq`): `Ẑ(Φωu) = J_{Φω}(u) − 2V_c^S(u) + 2|τ_c^S|∫u²Φω cosh(x/2)`.

The pole's cost does not disappear: the lobes `−¼Φ(· ∓ b)` make the jump conductances
`Φω(x)Φω(x + t)` negative for jumps from the window into the lobes, and the theta functional equation
pays the charge back exactly through those jumps. A gauge family with a pointwise nonnegative even
remainder must therefore control the jumps toward its outside charges, not the sign of the charge.
-/

open MeasureTheory Set Filter Topology
open scoped Real

noncomputable section

namespace GaloisForLFunctions.FrustratedArithmeticDirichletForms

open _root_.RHTower
open GaloisForLFunctions.ArithmeticCriticalityTheory
open GaloisForLFunctions.SignedWindowCriticality

/-- The weights `(1, −¼, −¼)` of the signed gauge. -/
def lobeWeights : Fin 3 → ℝ := ![1, -(1 / 4), -(1 / 4)]

/-- The shifts `(0, b, −b)` of the signed gauge. -/
def lobeShifts (b : ℝ) : Fin 3 → ℝ := ![0, b, -b]

theorem coordinate_signedThetaGauge (b x : ℝ) :
    riemannKernelReal x * translateSpan Finset.univ lobeWeights (lobeShifts b) x =
      riemannKernelReal x - (1 / 4) * (riemannKernelReal (x - b) + riemannKernelReal (x + b)) := by
  rw [thetaGauge_coordinate, Fin.sum_univ_three]
  simp only [lobeWeights, lobeShifts, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, sub_zero, sub_neg_eq_add]
  ring

theorem sinhCoefficient_signedThetaGauge (b : ℝ) :
    translateSinhCoefficient Finset.univ lobeWeights (lobeShifts b) = 0 := by
  unfold translateSinhCoefficient
  rw [Fin.sum_univ_three]
  simp only [lobeWeights, lobeShifts, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, zero_div, Real.sinh_zero,
    show -b / 2 = -(b / 2) by ring, Real.sinh_neg]
  ring

theorem coshCoefficient_signedThetaGauge (b : ℝ) :
    translateCoshCoefficient Finset.univ lobeWeights (lobeShifts b) = 1 - Real.cosh (b / 2) / 2 := by
  unfold translateCoshCoefficient
  rw [Fin.sum_univ_three]
  simp only [lobeWeights, lobeShifts, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, zero_div, Real.cosh_zero,
    show -b / 2 = -(b / 2) by ring, Real.cosh_neg]
  ring

theorem coordinate_signedThetaGauge_even (b x : ℝ) :
    riemannKernelReal (-x) * translateSpan Finset.univ lobeWeights (lobeShifts b) (-x) =
      riemannKernelReal x * translateSpan Finset.univ lobeWeights (lobeShifts b) x := by
  rw [coordinate_signedThetaGauge, coordinate_signedThetaGauge, riemannKernelReal_neg',
    show -x - b = -(x + b) by ring, show -x + b = -(x - b) by ring, riemannKernelReal_neg',
    riemannKernelReal_neg']
  ring

/-- The lobes never exceed the kernel on the window: `Φ(x − s) ≤ Φ(x)` for `|x| ≤ c`, `|s| = b ≥ 2c`. -/
theorem riemannKernelReal_shift_le {b c x : ℝ} (hbc : 2 * c ≤ b) (hx : |x| ≤ c) (s : ℝ)
    (hs : |s| = b) : riemannKernelReal (x - s) ≤ riemannKernelReal x := by
  rw [← riemannKernelReal_abs' (x - s), ← riemannKernelReal_abs' x]
  refine riemannKernelReal_antitone_of_nonneg (abs_nonneg x) ?_
  have h := abs_sub_abs_le_abs_sub s x
  rw [abs_sub_comm s x, hs] at h
  linarith

theorem cosh_two_gt_two : 2 < Real.cosh 2 := by
  have h := Real.quadratic_le_exp_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num)
  rw [Real.cosh_eq]
  have : 0 < Real.exp (-2) := Real.exp_pos _
  linarith

/-- **A signed theta gauge positive on the window with negative outside cosh charge.** For every
`c > 0` and `b ≥ max(2c, 4)`, the gauge `ω = τ_0 − ¼(τ_b + τ_{−b})` has `Φω ≥ Φ/2 > 0` on `[−c, c]`,
vanishing odd pole coefficient, and outside cosh charge `A/2 − ∫_{(−c,c)}Φω cosh(x/2) < 0`. -/
theorem exists_signedThetaGauge {c b : ℝ} (hc : 0 < c) (hbc : 2 * c ≤ b) (hb4 : 4 ≤ b) :
    (∀ x, |x| ≤ c → riemannKernelReal x / 2 ≤
      riemannKernelReal x * translateSpan Finset.univ lobeWeights (lobeShifts b) x) ∧
    translateSinhCoefficient Finset.univ lobeWeights (lobeShifts b) = 0 ∧
    translateCoshCoefficient Finset.univ lobeWeights (lobeShifts b) / 2 -
      coshCharge (translateSpan Finset.univ lobeWeights (lobeShifts b)) (Ioo (-c) c) < 0 := by
  have hpos : ∀ x, |x| ≤ c → riemannKernelReal x / 2 ≤
      riemannKernelReal x * translateSpan Finset.univ lobeWeights (lobeShifts b) x := by
    intro x hx
    rw [coordinate_signedThetaGauge]
    have hb0 : 0 ≤ b := by linarith
    have h1 := riemannKernelReal_shift_le hbc hx b (abs_of_nonneg hb0)
    have h2 := riemannKernelReal_shift_le hbc hx (-b) (by rw [abs_neg, abs_of_nonneg hb0])
    rw [sub_neg_eq_add] at h2
    linarith
  refine ⟨hpos, sinhCoefficient_signedThetaGauge b, ?_⟩
  rw [coshCoefficient_signedThetaGauge]
  have hcharge : 0 ≤ coshCharge (translateSpan Finset.univ lobeWeights (lobeShifts b)) (Ioo (-c) c) := by
    unfold coshCharge
    refine setIntegral_nonneg measurableSet_Ioo fun x hx => ?_
    have hx' : |x| ≤ c := abs_le.mpr ⟨hx.1.le, hx.2.le⟩
    have := hpos x hx'
    have hΦ := riemannKernelReal_pos x
    exact mul_nonneg (by linarith) (Real.cosh_pos _).le
  have hcosh : Real.cosh 2 ≤ Real.cosh (b / 2) := by
    rw [Real.cosh_le_cosh, abs_of_pos (by norm_num), abs_of_pos (by linarith)]
    linarith
  have := cosh_two_gt_two
  linarith

/-- **In the signed gauge the even potential term is a credit.** For every even `C²_c` profile `u`,
`Ẑ(Φωu) = J_{Φω}(u) − 2V_c(u) + 2|τ_c|∫u²Φω cosh(x/2)`. -/
theorem fullZeroForm_signedThetaGauge_eq {c b : ℝ} (hc : 0 < c) (hbc : 2 * c ≤ b) (hb4 : 4 ≤ b)
    {u : ℝ → ℝ} (hu : ContDiff ℝ 2 u) (huc : HasCompactSupport u) (heven : ∀ x, u (-x) = u x) :
    fullZeroForm (phiDoobTest fun y => translateSpan Finset.univ lobeWeights (lobeShifts b) y * u y) =
      signedJumpEnergy (fun y => riemannKernelReal y *
          translateSpan Finset.univ lobeWeights (lobeShifts b) y) u -
        2 * chargeVariance (fun x => riemannKernelReal x *
          translateSpan Finset.univ lobeWeights (lobeShifts b) x * Real.cosh (x / 2)) (Ioo (-c) c) u +
        2 * |translateCoshCoefficient Finset.univ lobeWeights (lobeShifts b) / 2 -
            coshCharge (translateSpan Finset.univ lobeWeights (lobeShifts b)) (Ioo (-c) c)| *
          ∫ x, u x ^ 2 * (riemannKernelReal x *
            translateSpan Finset.univ lobeWeights (lobeShifts b) x * Real.cosh (x / 2)) := by
  obtain ⟨-, hB, hneg⟩ := exists_signedThetaGauge hc hbc hb4
  rw [fullZeroForm_evenThetaGauge_window Finset.univ lobeWeights (lobeShifts b) hc.le
    (coordinate_signedThetaGauge_even b) hB hu huc heven, abs_of_neg hneg]
  ring

end GaloisForLFunctions.FrustratedArithmeticDirichletForms
