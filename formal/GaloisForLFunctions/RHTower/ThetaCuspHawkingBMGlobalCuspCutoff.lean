import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMCellGermExtension

/-!
The original complete cusp cutoff has a globally smooth modular extension. Its full germ agrees on every closed-cell chart, so every differential cutoff contribution is retained.
-/

open MeasureTheory Set Filter Topology UpperHalfPlane ModularGroup
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HTGeometry.ScalarTwoJet
open scoped MatrixGroups ContDiff
namespace RHTower.D4BMModularCore
open D4BMGlobalAngularResponse D4BMAngularSeries D4BMQuadraticMixedSource
noncomputable section

/-- The original full cusp cutoff response is smooth throughout positive height. -/
theorem cutoffResponse_contDiffOn (q : XiZeroCopy) (branch : Bool) :
    ContDiffOn ℝ ∞ (cutoffResponse q branch) domain := by
  have hc : ContDiffOn ℝ ∞ (cuspResponse q branch) domain := by
    unfold cuspResponse cuspPowerResponse powerResponse
    exact contDiffOn_const.mul (((contDiffOn_const.mul (height_cpow_contDiffOn _ ∞)).add
      (contDiffOn_const.mul (height_cpow_contDiffOn _ ∞))).add
      (contDiffOn_const.mul (height_cpow_contDiffOn _ ∞)))
  have hk : ContDiff ℝ ∞ cutoff := by
    let Y : (Fin 2 → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj 1
    exact Complex.ofRealCLM.contDiff.comp (Real.smoothTransition.contDiff.comp
      (Y.contDiff.sub contDiff_const))
  exact hk.contDiffOn.mul hc

private theorem cutoffResponse_chartSmooth (q : XiZeroCopy) (branch : Bool) :
    ChartSmooth (fun z => cutoffResponse q branch (coordinates z)) := by
  have hC : ContDiff ℝ ∞ (fun z : ℂ => ![z.re,z.im]) := by
    apply contDiff_pi.mpr
    intro i
    fin_cases i
    · exact Complex.reCLM.contDiff
    · exact Complex.imCLM.contDiff
  have hf : ContDiffOn ℝ ∞ (fun z : ℂ => cutoffResponse q branch ![z.re,z.im])
      {z : ℂ | 0 < z.im} :=
    (cutoffResponse_contDiffOn q branch).comp hC.contDiffOn (fun _ hz => hz)
  intro z
  apply (hf.contDiffAt (isOpen_upperHalfPlaneSet.mem_nhds z.im_pos)).congr_of_eventuallyEq
  filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds z.im_pos] with w hw
  simp only [Function.comp_apply,coordinates,ofComplex_apply_of_im_pos hw]
  rfl

private theorem cutoffResponse_cell_germ (q : XiZeroCopy) (branch : Bool) :
    CellGermCompatible (fun z => cutoffResponse q branch (coordinates z)) := by
  intro γ z hz hγ
  induction γ using QuotientGroup.induction_on with
  | H A =>
    simp only [PSL2Z_mk_smul] at hγ ⊢
    by_cases hc : A 1 0 = 0
    · obtain ⟨n,hn⟩ := exists_eq_T_zpow_of_c_eq_zero hc
      apply Filter.Eventually.of_forall
      intro w
      change cutoffResponse q branch (coordinates (A • w)) = cutoffResponse q branch (coordinates w)
      rw [hn]
      simp only [coordinates,cutoffResponse,cutoff,cuspResponse,cuspPowerResponse,powerResponse,
        Matrix.cons_val_one,ModularGroup.im_T_zpow_smul]
    · obtain ⟨hl,hr⟩ := nonparabolic_cell_overlap_low A hc z hz hγ
      have hleft : ∀ᶠ w : UpperHalfPlane in 𝓝 z, w.im < 2 :=
        (isOpen_lt UpperHalfPlane.continuous_im continuous_const).mem_nhds hl
      have hright : ∀ᶠ w : UpperHalfPlane in 𝓝 z, (A • w).im < 2 :=
        (isOpen_lt (UpperHalfPlane.continuous_im.comp
          (show Continuous (fun w : UpperHalfPlane => A • w) from by
            simp_rw [sl_moeb]; exact continuous_const_smul _)) continuous_const).mem_nhds hr
      filter_upwards [hleft,hright] with w hw hAw
      rw [cutoffResponse_zero q branch _ hAw.le,cutoffResponse_zero q branch _ hw.le]

/-- The globally glued original cusp cutoff response, retaining its complete closed-cell germs. -/
def globalCuspCutoff (q : XiZeroCopy) (branch : Bool) : UpperHalfPlane → ℂ :=
  cellGermExtension (fun z => cutoffResponse q branch (coordinates z))

/-- The original cusp cutoff extends to a globally smooth upper-half-plane field. -/
theorem globalCuspCutoff_smooth (q : XiZeroCopy) (branch : Bool) :
    ChartSmooth (globalCuspCutoff q branch) :=
  cellGermExtension_smooth _ (cutoffResponse_cell_germ q branch) (cutoffResponse_chartSmooth q branch)

/-- The constructed global cusp cutoff is invariant under every actual modular element. -/
theorem globalCuspCutoff_invariant (q : XiZeroCopy) (branch : Bool) (γ : PSL2Z)
    (z : UpperHalfPlane) : globalCuspCutoff q branch (γ • z) = globalCuspCutoff q branch z :=
  cellGermExtension_invariant _ (cutoffResponse_cell_germ q branch) γ z

/-- Full germ agreement preserves every cutoff derivative in each closed-cell chart. -/
theorem globalCuspCutoff_germ (q : XiZeroCopy) (branch : Bool) (z : UpperHalfPlane)
    (hz : z ∈ fd) : globalCuspCutoff q branch =ᶠ[𝓝 z]
      (fun w => cutoffResponse q branch (coordinates w)) :=
  cellGermExtension_germ _ (cutoffResponse_cell_germ q branch) z hz

/-- The global cusp cutoff equals the original full cutoff response on the closed modular cell. -/
theorem globalCuspCutoff_eq_on_fd (q : XiZeroCopy) (branch : Bool) (z : UpperHalfPlane)
    (hz : z ∈ fd) : globalCuspCutoff q branch z = cutoffResponse q branch (coordinates z) :=
  (globalCuspCutoff_germ q branch z hz).eq_of_nhds

end
end RHTower.D4BMModularCore
