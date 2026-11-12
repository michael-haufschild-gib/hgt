import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.CriticalPowerContactCoefficientIsTheRealResidue
import GaloisForLFunctions.HTGeometry.MeromorphicSimplePoleDifferentialOperator

/-!
# The finite part of the critical contact symbol

Harmonic subtraction cancels the real zeta pole. Writing the remaining
symbol as the residue unit times a divided difference gives an analytic
extension, whose value at zero is the derivative of the contact factor.
-/

noncomputable section

open Complex Set

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

/-- The critical contact factor is analytic at the real origin. -/
theorem analyticAt_criticalPowerContactFactor :
    AnalyticAt ℂ criticalPowerContactFactor 0 := by
  have hζ : riemannZeta (1 / 2) ≠ 0 := by
    simpa only [ofReal_div, ofReal_one, ofReal_ofNat] using
      _root_.RHTower.riemannZeta_ne_zero_of_ofReal_mem_Ioo
        (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
  have hζan : AnalyticAt ℂ riemannZeta (1 / 2) := by
    have hd : DifferentiableOn ℂ riemannZeta ({1}ᶜ) := fun z hz =>
      (differentiableAt_riemannZeta
        (by simpa only [mem_compl_iff, mem_singleton_iff] using hz)).differentiableWithinAt
    exact (hd.analyticOnNhd isOpen_compl_singleton) _ (by norm_num)
  have hB : AnalyticAt ℂ
      (fun z : ℂ => -deriv riemannZeta z / riemannZeta z - riemannZeta z)
      (1 / 2) := (hζan.deriv.neg.div hζan hζ).sub hζan
  have hh : AnalyticAt ℂ
      (fun z : ℂ => -deriv riemannZeta z / riemannZeta z - riemannZeta z)
      ((fun s : ℂ => s + 1 / 2) 0) := by
    simpa only [zero_add] using hB
  exact hh.comp (f := fun s : ℂ => s + 1 / 2) (x := 0)
    (analyticAt_id.add analyticAt_const)

/-- Analytic extension of the critical contact symbol after harmonic
subtraction. -/
def criticalPowerContactRegularPart (s : ℂ) : ℂ :=
  _root_.RHTower.zetaResidueUnit (s + 1) * dslope criticalPowerContactFactor 0 s

/-- A residue unit times a divided difference removes the singularity. -/
theorem analyticAt_criticalPowerContactRegularPart :
    AnalyticAt ℂ criticalPowerContactRegularPart 0 := by
  have hR : AnalyticAt ℂ _root_.RHTower.zetaResidueUnit
      ((fun s : ℂ => s + 1) 0) := by
    simpa only [zero_add] using _root_.RHTower.zetaResidueUnit_analyticAt
  exact (hR.comp (f := fun s : ℂ => s + 1) (x := 0)
    (analyticAt_id.add analyticAt_const)).mul
      (analyticAt_dslope_zero_of_analyticAt analyticAt_criticalPowerContactFactor)

/-- The removed pole leaves the derivative of the analytic contact factor. -/
theorem criticalPowerContactRegularPart_zero :
    criticalPowerContactRegularPart 0 = deriv criticalPowerContactFactor 0 := by
  rw [criticalPowerContactRegularPart, zero_add,
    _root_.RHTower.zetaResidueUnit_one, one_mul, dslope_same]

/-- Away from zero the extension equals the harmonically subtracted symbol. -/
theorem criticalPowerContactRegularPart_eq {s : ℂ} (hs : s ≠ 0) :
    criticalPowerContactRegularPart s = riemannZeta (s + 1) *
      (criticalPowerContactFactor s - (criticalPowerContactCoefficient : ℂ)) := by
  have hs1 : s + 1 ≠ 1 := by
    intro he
    exact hs (add_right_cancel (he.trans (zero_add (1 : ℂ)).symm))
  have hd : s * dslope criticalPowerContactFactor 0 s =
      criticalPowerContactFactor s - criticalPowerContactFactor 0 := by
    simpa only [sub_zero, smul_eq_mul] using
      (sub_smul_dslope criticalPowerContactFactor 0 s)
  rw [criticalPowerContactRegularPart, _root_.RHTower.zetaResidueUnit,
    Function.update_of_ne hs1, add_sub_cancel_right,
    criticalPowerContactCoefficient_eq_realResidue, ← hd]
  ring

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
