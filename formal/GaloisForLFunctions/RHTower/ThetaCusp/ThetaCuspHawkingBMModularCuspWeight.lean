import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMCuspWeightProfile
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMModularEnergyDomain

/-! Smooth bounded cusp weights on the actual modular quotient, including their full cell germs. -/
open Set Filter Topology UpperHalfPlane ModularGroup
open GaloisForLFunctions.HTGeometry
open scoped MatrixGroups ContDiff ComplexConjugate
namespace RHTower.D4BMJointWave
open D4BMModularCore
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

private theorem height_cell_germ (h : ℝ → ℂ) (c : ℂ) (hl : ∀ y ≤ 2, h y = c) :
    CellGermCompatible (fun z : UpperHalfPlane => h z.im) := by
  intro γ z hz hγ
  induction γ using QuotientGroup.induction_on with
  | H A =>
    simp only [PSL2Z_mk_smul] at hγ ⊢
    by_cases hc : A 1 0 = 0
    · obtain ⟨n,hn⟩ := exists_eq_T_zpow_of_c_eq_zero hc
      apply Filter.Eventually.of_forall
      intro w
      change h (A • w).im = h w.im
      rw [hn w,ModularGroup.im_T_zpow_smul]
    · obtain ⟨hlow,hr⟩ := nonparabolic_cell_overlap_low A hc z hz hγ
      have hleft : ∀ᶠ w : UpperHalfPlane in 𝓝 z, w.im < 2 :=
        (isOpen_lt UpperHalfPlane.continuous_im continuous_const).mem_nhds hlow
      have hright : ∀ᶠ w : UpperHalfPlane in 𝓝 z, (A • w).im < 2 :=
        (isOpen_lt (UpperHalfPlane.continuous_im.comp
          (show Continuous (fun w : UpperHalfPlane => A • w) from by
            simp_rw [sl_moeb]; exact continuous_const_smul _)) continuous_const).mem_nhds hr
      filter_upwards [hleft,hright] with w hw hAw
      rw [hl _ hAw.le,hl _ hw.le]

private theorem profile_compatible (N : ℝ) :
    CellGermCompatible (fun z : UpperHalfPlane => (cuspWeightProfile N z.im : ℂ)) :=
  height_cell_germ (fun y : ℝ => (cuspWeightProfile N y:ℂ)) cuspWeightBase
    (fun y hy => by rw [cuspWeightProfile_low N y hy])

def modularCuspWeight (N : ℝ) : UpperHalfPlane → ℂ :=
  cellGermExtension (fun z : UpperHalfPlane => (cuspWeightProfile N z.im : ℂ))

theorem modularCuspWeight_invariant (N : ℝ) (γ : PSL2Z) (z : UpperHalfPlane) :
    modularCuspWeight N (γ • z) = modularCuspWeight N z :=
  cellGermExtension_invariant _ (profile_compatible N) γ z

theorem modularCuspWeight_germ (N : ℝ) (z : UpperHalfPlane) (hz : z ∈ fd) :
    modularCuspWeight N =ᶠ[𝓝 z] fun w => (cuspWeightProfile N w.im : ℂ) :=
  cellGermExtension_germ _ (profile_compatible N) z hz

theorem modularCuspWeight_smooth (N : ℝ) (hN : 0 < N) : ChartSmooth (modularCuspWeight N) := by
  apply cellGermExtension_smooth _ (profile_compatible N)
  intro z
  have h : ContDiffAt ℝ ∞ (fun w : ℂ => (cuspWeightProfile N w.im : ℂ)) (z:ℂ) :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp (z:ℂ)
      ((cuspWeightProfile_contDiffAt N z.im hN z.im_pos).comp (z:ℂ) Complex.imCLM.contDiff.contDiffAt)
  apply h.congr_of_eventuallyEq
  filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds z.im_pos] with w hw
  simp only [Function.comp_apply,ofComplex_apply_of_im_pos hw]
  rfl

theorem modularCuspWeight_real (N : ℝ) (z : UpperHalfPlane) :
    conj (modularCuspWeight N z) = modularCuspWeight N z := by
  simp only [modularCuspWeight,cellGermExtension,Complex.conj_ofReal]

theorem modularCuspWeight_re_bounds (N : ℝ) (hN : 0 < N) (z : UpperHalfPlane) :
    cuspWeightBase ≤ (modularCuspWeight N z).re ∧
      (modularCuspWeight N z).re ≤ cuspWeightBase+N := by
  simp only [modularCuspWeight,cellGermExtension,Complex.ofReal_re]
  exact cuspWeightProfile_bounds N _ hN (UpperHalfPlane.im_pos _)

theorem modularCuspWeight_norm_bound (N : ℝ) (hN : 0 < N) (z : UpperHalfPlane) :
    ‖modularCuspWeight N z‖ ≤ cuspWeightBase+N := by
  simp only [modularCuspWeight,cellGermExtension,Complex.norm_real,Real.norm_eq_abs]
  have hb := modularCuspWeight_re_bounds N hN z
  simp only [modularCuspWeight,cellGermExtension,Complex.ofReal_re] at hb
  rw [abs_of_nonneg (le_trans (by linarith [cuspWeightBase_one_le]) hb.1)]
  exact hb.2

/-- The full cell germ gives the literal derivative, including the cutoff transition. -/
theorem modularCuspWeight_weightedDeriv (N : ℝ) (hN : 0 < N) (z : UpperHalfPlane)
    (hz : z ∈ fd) (v : ℂ) :
    weightedDeriv v (modularCuspWeight N) z =
      (z.im:ℂ)*((deriv (cuspWeightProfile N) z.im:ℝ):ℂ)*(v.im:ℂ) := by
  have hc := (UpperHalfPlane.contMDiffAt_ofComplex (n := 0) z.im_pos).continuousAt
  have hg : modularCuspWeight N ∘ ofComplex =ᶠ[𝓝 (z:ℂ)]
      fun w : ℂ => (cuspWeightProfile N w.im:ℂ) := by
    have he : ∀ᶠ w : ℂ in 𝓝 (z:ℂ), modularCuspWeight N (ofComplex w) =
        (cuspWeightProfile N (ofComplex w).im:ℂ) := by
      apply hc.eventually (p := fun u : UpperHalfPlane =>
        modularCuspWeight N u = (cuspWeightProfile N u.im:ℂ))
      rw [ofComplex_apply]
      exact modularCuspWeight_germ N z hz
    filter_upwards [he,isOpen_upperHalfPlaneSet.mem_nhds z.im_pos] with w hw hp
    simpa only [Function.comp_apply,ofComplex_apply_of_im_pos hp,UpperHalfPlane.im] using! hw
  have hp := (cuspWeightProfile_hasDerivAt N z.im hN z.im_pos).hasFDerivAt
  have hF := Complex.ofRealCLM.hasFDerivAt.comp (z:ℂ)
    (hp.comp (z:ℂ) Complex.imCLM.hasFDerivAt)
  unfold weightedDeriv
  rw [hg.fderiv_eq]
  change (z.im:ℂ)*(fderiv ℝ (Complex.ofRealCLM ∘ cuspWeightProfile N ∘ Complex.im) (z:ℂ)) v = _
  rw [hF.fderiv]
  rw [(cuspWeightProfile_hasDerivAt N z.im hN z.im_pos).deriv]
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.toSpanSingleton_apply,
    Complex.imCLM_apply,Complex.ofRealCLM_apply,smul_eq_mul]
  push_cast
  ring

theorem modularCuspWeight_horizontal_zero (N : ℝ) (hN : 0 < N) (z : UpperHalfPlane)
    (hz : z ∈ fd) : weightedDeriv 1 (modularCuspWeight N) z = 0 := by
  simp only [modularCuspWeight_weightedDeriv N hN z hz,Complex.one_im,Complex.ofReal_zero,mul_zero]

/-- The uniform cusp slope survives the actual modular extension on the original cell. -/
theorem modularCuspWeight_vertical_bound (N : ℝ) (hN : 0 < N) (z : UpperHalfPlane)
    (hz : z ∈ fd) :
    ‖weightedDeriv Complex.I (modularCuspWeight N) z‖ ≤ (3/2:ℝ)*‖modularCuspWeight N z‖ := by
  rw [modularCuspWeight_weightedDeriv N hN z hz,
    (modularCuspWeight_germ N z hz).eq_of_nhds]
  have hp : 0 ≤ cuspWeightProfile N z.im :=
    le_trans (by linarith [cuspWeightBase_one_le]) (cuspWeightProfile_bounds N z.im hN z.im_pos).1
  simpa only [Complex.I_im,Complex.ofReal_one,mul_one,← Complex.ofReal_mul,
    Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hp] using
    cuspWeightProfile_gradient_bound N z.im hN z.im_pos

end
end RHTower.D4BMJointWave
