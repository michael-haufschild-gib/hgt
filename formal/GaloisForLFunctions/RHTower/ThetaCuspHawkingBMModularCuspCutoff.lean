import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMCuspCutoffProfile

/-! Compact smooth cutoffs on the full modular quotient at growing cusp scale. -/
open Set Filter Topology UpperHalfPlane ModularGroup
open GaloisForLFunctions.HTGeometry
open scoped MatrixGroups ContDiff ComplexConjugate
namespace RHTower.D4BMJointWave
open D4BMModularCore
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

private theorem cutoff_compatible (N : ℝ) (hN : 1 ≤ N) :
    CellGermCompatible (fun z : UpperHalfPlane => (scaledCuspCutoff N z.im:ℂ)) := by
  have hl (y : ℝ) (hy : y ≤ 2) : scaledCuspCutoff N y = 1 :=
    scaledCuspCutoff_low N y (by linarith) (by linarith)
  intro γ z hz hγ
  induction γ using QuotientGroup.induction_on with
  | H A =>
    simp only [PSL2Z_mk_smul] at hγ ⊢
    by_cases hc : A 1 0 = 0
    · obtain ⟨n,hn⟩ := exists_eq_T_zpow_of_c_eq_zero hc
      apply Filter.Eventually.of_forall
      intro w
      change (scaledCuspCutoff N (A • w).im:ℂ) = (scaledCuspCutoff N w.im:ℂ)
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

def modularCuspCutoff (N : ℝ) : UpperHalfPlane → ℂ :=
  cellGermExtension (fun z : UpperHalfPlane => (scaledCuspCutoff N z.im:ℂ))

theorem modularCuspCutoff_invariant (N : ℝ) (hN : 1 ≤ N) (γ : PSL2Z) (z : UpperHalfPlane) :
    modularCuspCutoff N (γ • z) = modularCuspCutoff N z :=
  cellGermExtension_invariant _ (cutoff_compatible N hN) γ z

/-- The entire scaled cutoff germ survives every seam of the original closed cell. -/
theorem modularCuspCutoff_germ (N : ℝ) (hN : 1 ≤ N) (z : UpperHalfPlane) (hz : z ∈ fd) :
    modularCuspCutoff N =ᶠ[𝓝 z] fun w => (scaledCuspCutoff N w.im:ℂ) :=
  cellGermExtension_germ _ (cutoff_compatible N hN) z hz

theorem modularCuspCutoff_smooth (N : ℝ) (hN : 1 ≤ N) : ChartSmooth (modularCuspCutoff N) := by
  apply cellGermExtension_smooth _ (cutoff_compatible N hN)
  intro z
  have h : ContDiffAt ℝ ∞ (fun w : ℂ => (scaledCuspCutoff N w.im:ℂ)) (z:ℂ) :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp (z:ℂ)
      ((scaledCuspCutoff_smooth N).contDiffAt.comp (z:ℂ) Complex.imCLM.contDiff.contDiffAt)
  apply h.congr_of_eventuallyEq
  filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds z.im_pos] with w hw
  simp only [Function.comp_apply,ofComplex_apply_of_im_pos hw]
  rfl

theorem modularCuspCutoff_real (N : ℝ) (z : UpperHalfPlane) :
    conj (modularCuspCutoff N z) = modularCuspCutoff N z := by
  simp only [modularCuspCutoff,cellGermExtension,Complex.conj_ofReal]

theorem modularCuspCutoff_norm_le_one (N : ℝ) (z : UpperHalfPlane) :
    ‖modularCuspCutoff N z‖ ≤ 1 := by
  simp only [modularCuspCutoff,cellGermExtension,scaledCuspCutoff,Complex.norm_real,Real.norm_eq_abs]
  rw [abs_of_nonneg (baseCuspCutoff_bounds _).1]
  exact (baseCuspCutoff_bounds _).2

/-- This is compact quotient support on the original cell, without imposing extra seam conditions. -/
theorem modularCuspCutoff_compact (N : ℝ) (hN : 1 ≤ N) : CellCompact (modularCuspCutoff N) := by
  refine ⟨{z : UpperHalfPlane | z ∈ fd ∧ z.im ≤ 3*N},truncated_cell_compact (3*N),?_⟩
  intro z hz hn
  rw [(modularCuspCutoff_germ N hN z hz).eq_of_nhds]
  rw [scaledCuspCutoff_high N z.im (by linarith) (by
    have : ¬ z.im ≤ 3*N := fun he => hn ⟨hz,he⟩
    linarith),Complex.ofReal_zero]

/-- Every fixed cell point eventually lies inside the region where the complete cutoff germ is one. -/
theorem modularCuspCutoff_eventually_one (z : UpperHalfPlane) (hz : z ∈ fd) :
    ∀ᶠ n : ℕ in atTop, modularCuspCutoff ((n:ℝ)+1) =ᶠ[𝓝 z] fun _ => (1:ℂ) := by
  obtain ⟨m,hm⟩ := exists_nat_gt z.im
  filter_upwards [eventually_ge_atTop m] with n hn
  have hN : (1:ℝ) ≤ (n:ℝ)+1 := by
    have : (0:ℝ) ≤ n := by positivity
    linarith
  have hy : z.im < 2*((n:ℝ)+1) := by
    have hmn : (m:ℝ) ≤ n := by exact_mod_cast hn
    have hn0 : (0:ℝ) ≤ n := by positivity
    linarith
  apply (modularCuspCutoff_germ _ hN z hz).trans
  filter_upwards [(isOpen_lt UpperHalfPlane.continuous_im continuous_const).mem_nhds hy] with w hw
  rw [scaledCuspCutoff_low _ _ (by positivity) hw.le,Complex.ofReal_one]

end
end RHTower.D4BMJointWave
