import GaloisForLFunctions.RHTower.SelbergScatteringQuarterShiftSource
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMCellGermExtension
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMCuspPeriodization
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMCompactModularPeriodization

/-!
# Original Xi field with a genuine modular cusp subtraction

The complete scattering field retains its physical parameter. Its full Weyl
principal part is subtracted only above the original smooth cutoff. Compatible
cell germs produce a smooth invariant extension, identified with the complete
cutoff orbit sum. Uniform full-tail control gives boundedness, and the original
nonzero horizontal mean proves nonvanishing. The exact differential forcing is
retained and vanishes outside the cutoff transition band.
-/

open Set Filter Topology MeasureTheory UpperHalfPlane ModularGroup
open GaloisForLFunctions.HTGeometry
open scoped MatrixGroups ContDiff
namespace RHTower.SelbergScatteringCuspSubtraction
open D4BMModularCore D4BMGlobalAngularResponse D4BMAngularSeries D4BMJointSource
noncomputable section

private theorem physicalScalar_S (q : XiZeroCopy) (z : UpperHalfPlane) :
    scalar (physicalAngularParameter q) (coordinates (S • z)) =
      scalar (physicalAngularParameter q) (coordinates z) := by
  have h := physicalScalar_invert q ⟨z.re,z.im,z.im_pos⟩
  rw [UpperHalfPlane.modular_S_smul]
  simpa [coordinates,d4BMEisensteinInvertCoordinate,
    Complex.inv_re,Complex.inv_im,Complex.normSq_apply,sq,neg_div] using h

private theorem physicalScalar_T (q : XiZeroCopy) (z : UpperHalfPlane) :
    scalar (physicalAngularParameter q) (coordinates (T • z)) =
      scalar (physicalAngularParameter q) (coordinates z) := by
  simp only [coordinates,ModularGroup.re_T_smul,ModularGroup.im_T_smul]
  simpa [scalar] using
    d4BM_completedEisensteinCuspLeg_scalar_periodic (physicalAngularParameter q) z.im z.re

/-- The complete physical scattering field is invariant under the entire integral modular group. -/
theorem physicalScalar_modular (q : XiZeroCopy) (A : SL(2, ℤ)) (z : UpperHalfPlane) :
    scalar (physicalAngularParameter q) (coordinates (A • z)) =
      scalar (physicalAngularParameter q) (coordinates z) := by
  have hA : A ∈ Subgroup.closure {S,T} := by simp [SpecialLinearGroup.SL2Z_generators]
  suffices ∀ z : UpperHalfPlane, scalar (physicalAngularParameter q) (coordinates (A • z)) =
      scalar (physicalAngularParameter q) (coordinates z) from this z
  induction hA using Subgroup.closure_induction with
  | mem g hg =>
    simp only [mem_insert_iff,mem_singleton_iff] at hg
    rcases hg with rfl | rfl
    · exact physicalScalar_S q
    · exact physicalScalar_T q
  | one => intro w; simp
  | mul g h _ _ ig ih => intro w; rw [mul_smul,ig,ih]
  | inv g _ ig => intro w; simpa using (ig (g⁻¹ • w)).symm

/-- The original linear field minus its complete smooth cusp principal subtraction. -/
def residual (q : XiZeroCopy) (z : Fin 2 → ℝ) : ℂ :=
  scalar (physicalAngularParameter q) z - cutoff z*principal (physicalAngularParameter q) z

/-- Below the cutoff the original source is retained literally. -/
theorem residual_low (q : XiZeroCopy) (z : Fin 2 → ℝ) (hz : z 1 ≤ 2) :
    residual q z = scalar (physicalAngularParameter q) z := by
  unfold residual cutoff
  rw [Real.smoothTransition.zero_of_nonpos (by linarith)]
  simp

/-- Above the cutoff every nonconstant Fourier mode remains, with its original normalization. -/
theorem residual_high (q : XiZeroCopy) (z : Fin 2 → ℝ) (hz : 3 ≤ z 1) :
    residual q z = tail (physicalAngularParameter q) z := by
  unfold residual cutoff
  rw [Real.smoothTransition.one_of_one_le (by linarith)]
  dsimp [scalar,D4BMGlobalAngularResponse.principal,tail,d4BMCompletedEisensteinCuspLeg]
  ring

/-- Integer translations preserve the literal cusp-subtracted source. -/
theorem residual_translate (q : XiZeroCopy) (n : ℤ) (z : UpperHalfPlane) :
    residual q (coordinates (T^n • z)) = residual q (coordinates z) := by
  simp only [residual,physicalScalar_modular]
  congr 1
  simp only [cutoff,D4BMGlobalAngularResponse.principal,d4BMCompletedEisensteinCuspConstantPart,
    d4BMCompletedEisensteinCuspConstantTerm,d4BMCompletedEisensteinCuspConstantMaassFactor,
    coordinates,ModularGroup.im_T_zpow_smul]
  rfl

/-- Full source germs agree across every closed-cell overlap, including the elliptic corners. -/
theorem residual_cell_compatible (q : XiZeroCopy) :
    CellGermCompatible (fun z => residual q (coordinates z)) := by
  intro γ z hz hγ
  induction γ using QuotientGroup.induction_on with
  | H A =>
    simp only [PSL2Z_mk_smul] at hγ ⊢
    by_cases hc : A 1 0 = 0
    · obtain ⟨n,hn⟩ := exists_eq_T_zpow_of_c_eq_zero hc
      apply Filter.Eventually.of_forall
      intro w
      dsimp only
      rw [hn]
      exact residual_translate q n w
    · obtain ⟨hl,hr⟩ := nonparabolic_cell_overlap_low A hc z hz hγ
      have hleft : ∀ᶠ w : UpperHalfPlane in 𝓝 z, w.im < 2 :=
        (isOpen_lt UpperHalfPlane.continuous_im continuous_const).mem_nhds hl
      have hright : ∀ᶠ w : UpperHalfPlane in 𝓝 z, (A • w).im < 2 :=
        (isOpen_lt (UpperHalfPlane.continuous_im.comp (show Continuous (fun w : UpperHalfPlane => A • w) from by
          simp_rw [sl_moeb]; exact continuous_const_smul _)) continuous_const).mem_nhds hr
      filter_upwards [hleft,hright] with w hw hAw
      rw [residual_low q _ hAw.le,residual_low q _ hw.le,physicalScalar_modular]

private theorem residual_smooth (q : XiZeroCopy) : ContDiffOn ℝ ∞ (residual q) domain := by
  exact (cuspLeg_contDiffOn .scalar (physicalAngularParameter q)).sub
    (sourceCutoff_smooth.contDiffOn.mul (cuspConstantPart_contDiffOn .scalar (physicalAngularParameter q)))

private theorem residual_chartSmooth (q : XiZeroCopy) :
    ChartSmooth (fun z => residual q (coordinates z)) := by
  have hc : ContDiff ℝ ∞ (fun w : ℂ => (![w.re,w.im] : Fin 2 → ℝ)) := by
    apply contDiff_pi.mpr
    intro i
    fin_cases i
    · exact Complex.reCLM.contDiff
    · exact Complex.imCLM.contDiff
  intro z
  have hf := (residual_smooth q).contDiffAt
    ((isOpen_lt (continuous_const : Continuous (fun _ : Fin 2 → ℝ => (0:ℝ)))
      (continuous_apply 1)).mem_nhds (show coordinates z ∈ domain from z.im_pos))
  apply (hf.comp (z:ℂ) hc.contDiffAt).congr_of_eventuallyEq
  filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds z.im_pos] with w hw
  simp only [Function.comp_def,coordinates,ofComplex_apply_of_im_pos hw]
  rfl

/-- The genuine modular extension of the original cusp-subtracted linear field. -/
def globalResidual (q : XiZeroCopy) : UpperHalfPlane → ℂ :=
  cellGermExtension (fun z => residual q (coordinates z))

theorem globalResidual_eq_on_fd (q : XiZeroCopy) (z : UpperHalfPlane) (hz : z ∈ fd) :
    globalResidual q z = residual q (coordinates z) := by
  simpa only [one_smul,globalResidual] using
    cellGermExtension_eq _ (residual_cell_compatible q) 1 z (by simpa using hz)

theorem globalResidual_invariant (q : XiZeroCopy) (γ : PSL2Z) (z : UpperHalfPlane) :
    globalResidual q (γ • z) = globalResidual q z :=
  cellGermExtension_invariant _ (residual_cell_compatible q) γ z

theorem globalResidual_smooth (q : XiZeroCopy) : ChartSmooth (globalResidual q) :=
  cellGermExtension_smooth _ (residual_cell_compatible q) (residual_chartSmooth q)

/-- The original height subtraction with its unchanged translation partition. -/
def cutoffSeed (q : XiZeroCopy) (z : UpperHalfPlane) : ℂ :=
  (cuspWindow z.re:ℂ)*(cutoff ![0,z.im]*principal (physicalAngularParameter q) ![0,z.im])

theorem cutoffSeed_periodize_cell (q : XiZeroCopy) (z : UpperHalfPlane) (hz : z ∈ fd) :
    periodize (cutoffSeed q) z = cutoff (coordinates z)*principal (physicalAngularParameter q) (coordinates z) := by
  refine periodize_cuspWindow (fun y : ℝ => cutoff ![0,y]*principal (physicalAngularParameter q) ![0,y]) ?_ z hz
  intro y hy
  unfold cutoff
  rw [Real.smoothTransition.zero_of_nonpos (by change y-2 ≤ 0; linarith)]
  simp

/-- Full orbit periodization identifies the extension with an explicit original-source correction. -/
theorem globalResidual_eq_periodized (q : XiZeroCopy) (z : UpperHalfPlane) :
    globalResidual q z = scalar (physicalAngularParameter q) (coordinates z)-periodize (cutoffSeed q) z := by
  obtain ⟨A,hA⟩ := exists_smul_mem_fd z
  have hi := globalResidual_invariant q (QuotientGroup.mk A) z
  have hp := periodize_invariant (cutoffSeed q) (QuotientGroup.mk A) z
  simp only [PSL2Z_mk_smul] at hi hp
  rw [← hi,globalResidual_eq_on_fd q _ hA,residual,← cutoffSeed_periodize_cell q _ hA,hp,
    physicalScalar_modular]

/-- Compact lower-cell control and the complete Fourier tail give a uniform bound. -/
theorem residual_cell_bound (q : XiZeroCopy) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : UpperHalfPlane, z ∈ fd → ‖residual q (coordinates z)‖ ≤ C := by
  have hc := (residual_chartSmooth q).continuous
  obtain ⟨A,hA⟩ := (truncated_cell_compact 4).exists_bound_of_continuousOn hc.continuousOn
  obtain ⟨B,hB,hb⟩ := weighted_tail_bounded (physicalAngularParameter q) 0 3 (by norm_num)
  refine ⟨max 0 (max A B),le_max_left _ _,?_⟩
  intro z hz
  by_cases hy : z.im ≤ 4
  · exact (hA z ⟨hz,hy⟩).trans ((le_max_left _ _).trans (le_max_right _ _))
  · have h3 : 3 ≤ z.im := by linarith
    rw [residual_high q _ h3]
    have hh := hb (coordinates z) h3
    simp only [Complex.cpow_zero,one_mul] at hh
    exact hh.trans ((le_max_right _ _).trans (le_max_right _ _))

/-- The constructed modular source is bounded on the whole upper half-plane. -/
theorem globalResidual_bounded (q : XiZeroCopy) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : UpperHalfPlane, ‖globalResidual q z‖ ≤ C := by
  obtain ⟨C,hC,hb⟩ := residual_cell_bound q
  refine ⟨C,hC,?_⟩
  intro z
  obtain ⟨A,hA⟩ := exists_smul_mem_fd z
  have he := globalResidual_invariant q (QuotientGroup.mk A) z
  simp only [PSL2Z_mk_smul] at he
  rw [← he,globalResidual_eq_on_fd q _ hA]
  exact hb _ hA

/-- Every actual Xi copy supplies a nonzero value of the corrected field on the original closed cell. -/
theorem globalResidual_nonzero_on_fd (q : XiZeroCopy) :
    ∃ z : UpperHalfPlane, z ∈ fd ∧ globalResidual q z ≠ 0 := by
  obtain ⟨x,hx⟩ := SelbergScatteringHeightConjugation.scalarSource_xi_nonzero_on_every_height q (3/2) (by norm_num)
  let z : UpperHalfPlane := ⟨⟨x,3/2⟩,by norm_num⟩
  obtain ⟨A,hA⟩ := exists_smul_mem_fd z
  refine ⟨A • z,hA,?_⟩
  have hy := modular_orbit_height_le (QuotientGroup.mk A) z
  simp only [PSL2Z_mk_smul] at hy
  have hlow : (A • z).im ≤ 2 := by
    change (A • z).im ≤ max (3/2:ℝ) (1/(3/2:ℝ)) at hy
    exact hy.trans (by norm_num)
  rw [globalResidual_eq_on_fd q _ hA,residual_low q _ hlow,physicalScalar_modular]
  exact hx


/-- The full cutoff differential expression; no derivative of the cutoff is discarded. -/
def cutoffForcing (q : XiZeroCopy) (z : Fin 2 → ℝ) : ℂ :=
  hyperbolicLaplacian (fun w => cutoff w*principal (physicalAngularParameter q) w) z -
    ((physicalAngularParameter q)^2-1/4)*(cutoff z*principal (physicalAngularParameter q) z)

/-- The actual corrected source solves the original scattering equation with its retained forcing. -/
theorem residual_equation (q : XiZeroCopy) (z : Fin 2 → ℝ) (hz : 0 < z 1) :
    -hyperbolicLaplacian (residual q) z -
      (((q.1:ℂ)/2)*(1-(q.1:ℂ)/2))*residual q z = cutoffForcing q z := by
  have hn : domain ∈ 𝓝 z :=
    (isOpen_lt continuous_const (continuous_apply 1)).mem_nhds hz
  have hp := ((contDiffOn_infty.mp (cuspConstantPart_contDiffOn .scalar (physicalAngularParameter q))) 2).contDiffAt hn
  change ContDiffAt ℝ 2 (principal (physicalAngularParameter q)) z at hp
  have hc : ContDiffAt ℝ 2 cutoff z := (contDiff_infty.mp sourceCutoff_smooth 2).contDiffAt
  have hf : ContDiffAt ℝ 2 (scalar (physicalAngularParameter q)) z :=
    cuspLeg_contDiffAt .scalar (physicalAngularParameter q) 2 z hz
  have he : residual q = fun w => scalar (physicalAngularParameter q) w +
      (-1:ℂ)*(cutoff w*principal (physicalAngularParameter q) w) := by
    funext w
    dsimp [residual]
    ring
  rw [he,hyperbolicLaplacian_add hf ((contDiffAt_const (c := (-1:ℂ))).mul (hc.mul hp)),
    hyperbolicLaplacian_const_mul (hc.mul hp)]
  have hs := scalarCusp_hyperbolicLaplacian (physicalAngularParameter q) z hz
  change hyperbolicLaplacian (scalar (physicalAngularParameter q)) z =
    ((physicalAngularParameter q)^2-1/4)*scalar (physicalAngularParameter q) z at hs
  rw [hs]
  dsimp [cutoffForcing]
  rw [physicalAngularParameter_eq]
  ring

private theorem principal_equation (u : ℂ) (z : Fin 2 → ℝ) (hz : 0 < z 1) :
    hyperbolicLaplacian (principal u) z = (u^2-1/4)*principal u z := by
  have hn : domain ∈ 𝓝 z :=
    (isOpen_lt continuous_const (continuous_apply 1)).mem_nhds hz
  have hf (e : Bool) := ((contDiffOn_infty.mp (cuspConstantTerm_contDiffOn .scalar u e)) 2).contDiffAt hn
  change hyperbolicLaplacian (fun w =>
    d4BMCompletedEisensteinCuspConstantTerm .scalar u false (w 1) +
    d4BMCompletedEisensteinCuspConstantTerm .scalar u true (w 1)) z = _
  rw [hyperbolicLaplacian_add (hf false) (hf true),cuspConstantTerm_hyperbolicLaplacian u false z hz,
    cuspConstantTerm_hyperbolicLaplacian u true z hz]
  dsimp [D4BMGlobalAngularResponse.principal,d4BMCompletedEisensteinCuspConstantPart]
  ring

/-- The retained forcing vanishes below the cutoff, on an actual open neighborhood. -/
theorem cutoffForcing_low (q : XiZeroCopy) (z : Fin 2 → ℝ) (hz : z 1 < 2) :
    cutoffForcing q z = 0 := by
  have he : (fun w => cutoff w*principal (physicalAngularParameter q) w) =ᶠ[𝓝 z] (fun _ => (0:ℂ)) := by
    filter_upwards [(isOpen_lt (continuous_apply 1) continuous_const).mem_nhds hz] with w hw
    unfold cutoff
    rw [Real.smoothTransition.zero_of_nonpos (by linarith)]
    simp
  rw [cutoffForcing,hyperbolicLaplacian_congr he,he.eq_of_nhds]
  have hzero : hyperbolicLaplacian (fun _ : Fin 2 → ℝ => (0:ℂ)) z = 0 := by
    simpa only [zero_mul] using
      hyperbolicLaplacian_const_mul (z := z) (contDiffAt_const (c := (1:ℂ))) (0:ℂ)
  simp only [hzero,mul_zero,sub_zero]

/-- Beyond the transition band, the complete corrected field again solves the homogeneous equation. -/
theorem cutoffForcing_high (q : XiZeroCopy) (z : Fin 2 → ℝ) (hz : 3 < z 1) :
    cutoffForcing q z = 0 := by
  have he : (fun w => cutoff w*principal (physicalAngularParameter q) w) =ᶠ[𝓝 z]
      principal (physicalAngularParameter q) := by
    filter_upwards [(isOpen_lt continuous_const (continuous_apply 1)).mem_nhds hz] with w hw
    unfold cutoff
    rw [Real.smoothTransition.one_of_one_le (by linarith)]
    simp
  rw [cutoffForcing,hyperbolicLaplacian_congr he,he.eq_of_nhds,
    principal_equation _ z (by linarith),sub_self]

end
end RHTower.SelbergScatteringCuspSubtraction
