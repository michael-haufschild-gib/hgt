import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMCuspPositiveRows

/-! Measurability of the unchanged windowed orbit sums and their positive majorants. -/
open Set Filter Topology MeasureTheory UpperHalfPlane ModularGroup
open GaloisForLFunctions.HTGeometry
namespace RHTower.D4BMModularCore
noncomputable section

/-- A measurable height profile gives the original measurable windowed seed. -/
theorem cuspHeightSeed_measurable (h : ℝ → ℂ) (hh : Measurable h) : Measurable (cuspHeightSeed h) := by
  have hw : Continuous (fun z : UpperHalfPlane => (cuspWindow z.re:ℂ)) := by
    unfold cuspWindow
    fun_prop
  exact hw.measurable.mul (hh.comp continuous_im.measurable)

/-- The literal countable modular periodization preserves measurability. -/
theorem periodize_measurable (f : UpperHalfPlane → ℂ) (hf : Measurable f) : Measurable (periodize f) :=
  Measurable.tsum (fun γ : PSL2Z => hf.comp (measurable_const_smul γ))

theorem lowCuspPower_measurable (P : D4BMEisensteinAbsoluteConvergenceParameter) :
    Measurable (lowCuspPower P.s) :=
  Measurable.ite measurableSet_Iic
    (Complex.continuous_ofReal_cpow_const (by linarith [P.re_gt_one])).measurable measurable_const

theorem lowCuspPower_periodize_measurable (P : D4BMEisensteinAbsoluteConvergenceParameter) :
    Measurable (periodize (cuspHeightSeed (lowCuspPower P.s))) :=
  periodize_measurable _ (cuspHeightSeed_measurable _ (lowCuspPower_measurable P))

theorem positiveCuspRows_measurable (r : ℝ) : Measurable (positiveCuspRows r) := by
  apply Measurable.tsum
  intro v
  exact ((continuous_im.comp (by
      have hc : Continuous (fun z : UpperHalfPlane => (QuotientGroup.mk (gammaSetMatrix v.1) : PSL2Z) • z) := continuous_const_smul _
      simp_rw [PSL2Z_mk_smul] at hc
      exact hc)).rpow_const
    (fun z => Or.inl (gammaSetMatrix v.1 • z).im_pos.ne')).measurable

theorem positiveLowCuspRows_measurable (r : ℝ) : Measurable (positiveLowCuspRows r) := by
  apply Measurable.tsum
  intro v
  have hc : Continuous (fun z : UpperHalfPlane => (gammaSetMatrix v.1 • z).im) :=
    continuous_im.comp (by
      have hc : Continuous (fun z : UpperHalfPlane => (QuotientGroup.mk (gammaSetMatrix v.1) : PSL2Z) • z) := continuous_const_smul _
      simp_rw [PSL2Z_mk_smul] at hc
      exact hc)
  exact Measurable.ite (measurableSet_Iic.preimage hc.measurable)
    (hc.rpow_const (fun z => Or.inl (gammaSetMatrix v.1 • z).im_pos.ne')).measurable measurable_const

end
end RHTower.D4BMModularCore
