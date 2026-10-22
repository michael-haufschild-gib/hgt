import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMQuarticCutoffContact

/-! Actual smooth modular cores for the original principal-subtracted quartic source, with both cutoff derivatives and physical Green transposition. -/

open Set Filter Topology MeasureTheory UpperHalfPlane ModularGroup
open scoped ContDiff MatrixGroups ComplexConjugate
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HTGeometry.ScalarTwoJet
namespace RHTower.D4BMQuarticResidualCore
open D4BMAngularSeries D4BMGlobalAngularResponse D4BMSquareCuspJets
open D4BMJointSource D4BMQuarticPrincipalExpansion D4BMQuarticCutoffMellin
open D4BMModularCore D4BMJointWave D4BMQuarticCutoffContact
noncomputable section
set_option autoImplicit false

private def principalHeight (q : XiZeroCopy) (slot : Fin 6) (y : ℝ) : ℂ :=
  ∑ j : Fin 5, quarticPrincipalCoefficient q slot j*powerCutoffHeight (quarticPrincipalExponent q j) y

private theorem principalHeight_smooth (q : XiZeroCopy) (slot : Fin 6) :
    ContDiff ℝ ∞ (principalHeight q slot) :=
  ContDiff.sum (fun _ _ => contDiff_const.mul (powerCutoffHeight_smooth _))

private theorem principalHeight_low (q : XiZeroCopy) (slot : Fin 6) (y : ℝ) (hy : y ≤ 2) :
    principalHeight q slot y=0 := by
  apply Finset.sum_eq_zero
  intro j _
  rw [powerCutoffHeight,cutoffPower_low _ _ hy,mul_zero]

private theorem principalHeight_eq (q : XiZeroCopy) (slot : Fin 6) (z : UpperHalfPlane) :
    principalHeight q slot z.im=cutoff (coordinates z)*quarticContactPrincipal q slot (coordinates z) := by
  rw [quarticContactPrincipal_eq_power_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  change quarticPrincipalCoefficient q slot j*(cutoff (coordinates z)*
    (z.im:ℂ)^(quarticPrincipalExponent q j))=_
  ring

private theorem residual_height (q : XiZeroCopy) (slot : Fin 6)
    (z : Fin 2 → ℝ) (hz : 0<z 1) :
    quarticContactResidual q slot z=quarticContactField q slot z-principalHeight q slot (z 1) := by
  let Z : UpperHalfPlane := ⟨⟨z 0,z 1⟩,hz⟩
  have hc : coordinates Z=z := by
    funext i
    fin_cases i <;> rfl
  have h := principalHeight_eq q slot Z
  change principalHeight q slot (z 1)=_ at h
  rw [hc] at h
  unfold quarticContactResidual
  rw [h]

/-- The literal principal-subtracted quartic source is smooth on the entire original chart. -/
theorem quarticContactResidual_smooth (q : XiZeroCopy) (slot : Fin 6) :
    ContDiffOn ℝ ∞ (quarticContactResidual q slot) domain := by
  have hh : ContDiff ℝ ∞ (fun z : Fin 2 → ℝ => principalHeight q slot (z 1)) :=
    (principalHeight_smooth q slot).comp (contDiff_apply ℝ ℝ (1 : Fin 2))
  exact ((quarticContactField_smooth q slot).sub hh.contDiffOn).congr
    (fun z hz => residual_height q slot z hz)

private theorem height_compatible (h : ℝ → ℂ) (hl : ∀ y ≤ 2, h y=0) :
    CellGermCompatible (fun z : UpperHalfPlane => h z.im) := by
  intro γ z hz hγ
  induction γ using QuotientGroup.induction_on with
  | H A =>
    simp only [PSL2Z_mk_smul] at hγ ⊢
    by_cases hc : A 1 0=0
    · obtain ⟨n,hn⟩ := exists_eq_T_zpow_of_c_eq_zero hc
      apply Filter.Eventually.of_forall
      intro w
      change h (A • w).im=h w.im
      rw [hn w,ModularGroup.im_T_zpow_smul]
    · obtain ⟨hlow,hr⟩ := nonparabolic_cell_overlap_low A hc z hz hγ
      have hleft : ∀ᶠ w : UpperHalfPlane in 𝓝 z, w.im < 2 :=
        (isOpen_lt UpperHalfPlane.continuous_im continuous_const).mem_nhds hlow
      have hright : ∀ᶠ w : UpperHalfPlane in 𝓝 z, (A • w).im < 2 :=
        (isOpen_lt (UpperHalfPlane.continuous_im.comp
          (show Continuous (fun w : UpperHalfPlane => A • w) from by
            simp_rw [sl_moeb]; exact continuous_const_smul _)) continuous_const).mem_nhds hr
      filter_upwards [hleft,hright] with w hw hAw
      exact (hl _ hAw.le).trans (hl _ hw.le).symm

private theorem height_chart_smooth (h : ℝ → ℂ) (hs : ContDiff ℝ ∞ h) :
    ChartSmooth (fun z : UpperHalfPlane => h z.im) := by
  intro z
  have hc := hs.contDiffAt.comp (z:ℂ) Complex.imCLM.contDiff.contDiffAt
  apply hc.congr_of_eventuallyEq
  filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds z.im_pos] with w hw
  simp only [Function.comp_apply,ofComplex_apply_of_im_pos hw]
  rfl

private theorem coordinates_chart_smooth {f : (Fin 2 → ℝ) → ℂ}
    (hf : ContDiffOn ℝ ∞ f domain) : ChartSmooth (fun z => f (coordinates z)) := by
  intro z
  have hn : domain ∈ 𝓝 (coordinates z) :=
    (isOpen_lt continuous_const (continuous_apply 1)).mem_nhds z.im_pos
  have hs := hf.contDiffAt hn
  have he : (fun z : UpperHalfPlane => f (coordinates z)) ∘ ofComplex =ᶠ[𝓝 (z:ℂ)]
      f ∘ angularCoordinates := by
    filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds z.im_pos] with w hw
    simp only [Function.comp_apply,coordinates,ofComplex_apply_of_im_pos hw,angularCoordinates]
    rfl
  exact (hs.comp (z:ℂ) angularCoordinates.contDiff.contDiffAt).congr_of_eventuallyEq he

/-- The actual quartic residual extended across every original modular seam. -/
def quarticResidualModular (q : XiZeroCopy) (slot : Fin 6) (z : UpperHalfPlane) : ℂ :=
  quarticContactField q slot (coordinates z)-cellGermExtension (fun w => principalHeight q slot w.im) z

/-- The complete residual germ, including the original cutoff derivatives, is unchanged on the closed cell. -/
theorem quarticResidualModular_germ (q : XiZeroCopy) (slot : Fin 6)
    (z : UpperHalfPlane) (hz : z ∈ fd) :
    quarticResidualModular q slot =ᶠ[𝓝 z] fun w => quarticContactResidual q slot (coordinates w) := by
  filter_upwards [cellGermExtension_germ _
    (height_compatible _ (principalHeight_low q slot)) z hz] with w hw
  change quarticContactField q slot (coordinates w)-_=_
  rw [hw,principalHeight_eq]
  rfl

private theorem residual_modular_smooth (q : XiZeroCopy) (slot : Fin 6) :
    ChartSmooth (quarticResidualModular q slot) := by
  intro z
  exact (coordinates_chart_smooth (quarticContactField_smooth q slot) z).sub
    (cellGermExtension_smooth _ (height_compatible _ (principalHeight_low q slot))
      (height_chart_smooth _ (principalHeight_smooth q slot)) z)

private theorem residual_modular_invariant (q : XiZeroCopy) (slot : Fin 6)
    (γ : PSL2Z) (z : UpperHalfPlane) :
    quarticResidualModular q slot (γ • z)=quarticResidualModular q slot z := by
  unfold quarticResidualModular
  rw [quarticContactField_modular,
    cellGermExtension_invariant _ (height_compatible _ (principalHeight_low q slot))]

private theorem scale_one_le (n : ℕ) : (1:ℝ) ≤ (n:ℝ)+1 := by
  have hn : (0:ℝ) ≤ n := by positivity
  linarith

/-- An actual compact modular core for the principal-subtracted source, at the unchanged cusp scale. -/
def quarticResidualCoreCutoff (q : XiZeroCopy) (slot : Fin 6) (n : ℕ) : CoreField where
  field z := modularCuspCutoff ((n:ℝ)+1) z*quarticResidualModular q slot z
  smooth z := (modularCuspCutoff_smooth _ (scale_one_le n) z).mul (residual_modular_smooth q slot z)
  invariant γ z := by
    rw [modularCuspCutoff_invariant _ (scale_one_le n),residual_modular_invariant]
  compact := by
    obtain ⟨K,hK,hc⟩ := modularCuspCutoff_compact ((n:ℝ)+1) (scale_one_le n)
    refine ⟨K,hK,?_⟩
    intro z hz hn
    change modularCuspCutoff ((n:ℝ)+1) z*_=0
    rw [hc z hz hn,zero_mul]

/-- Every finite core is the original cutoff times the actual residual, as a full closed-cell germ. -/
theorem quarticResidualCoreCutoff_germ (q : XiZeroCopy) (slot : Fin 6) (n : ℕ)
    (z : UpperHalfPlane) (hz : z ∈ fd) :
    (quarticResidualCoreCutoff q slot n).field =ᶠ[𝓝 z] fun w =>
      (scaledCuspCutoff ((n:ℝ)+1) w.im:ℂ)*quarticContactResidual q slot (coordinates w) := by
  filter_upwards [modularCuspCutoff_germ _ (scale_one_le n) z hz,
    quarticResidualModular_germ q slot z hz] with w hc hr
  change modularCuspCutoff ((n:ℝ)+1) w*quarticResidualModular q slot w=_
  rw [hc,hr]

private theorem residual_core_zero_germ (q : XiZeroCopy) (slot : Fin 6) (n : ℕ)
    (z : UpperHalfPlane) (hz : z ∈ fd) (hy : 3*((n:ℝ)+1) < z.im) :
    (quarticResidualCoreCutoff q slot n).field =ᶠ[𝓝 z] fun _ => 0 := by
  filter_upwards [modularCuspCutoff_germ _ (scale_one_le n) z hz,
    (isOpen_lt continuous_const UpperHalfPlane.continuous_im).mem_nhds hy] with w hw hwy
  change modularCuspCutoff ((n:ℝ)+1) w*_=0
  rw [hw,scaledCuspCutoff_high _ _ (by positivity) hwy.le,Complex.ofReal_zero,zero_mul]

private theorem outer_physical_test_germ (r : XiZeroCopy) (n : ℕ) (z : UpperHalfPlane)
    (hz : z ∈ fd) (hy : z.im ≤ 3*((n:ℝ)+1)) :
    (physicalCoreCutoff r (3*n+2)).field =ᶠ[𝓝 z] physicalTestField r := by
  have hy' : z.im < 2*(((3*n+2:ℕ):ℝ)+1) := by
    push_cast
    have hn : (0:ℝ) ≤ n := by positivity
    linarith
  filter_upwards [modularCuspCutoff_germ _ (scale_one_le (3*n+2)) z hz,
    (isOpen_lt UpperHalfPlane.continuous_im continuous_const).mem_nhds hy'] with w hw hwy
  change modularCuspCutoff (((3*n+2:ℕ):ℝ)+1) w*physicalTestField r w=physicalTestField r w
  rw [hw,scaledCuspCutoff_low _ _ (by positivity) hwy.le,Complex.ofReal_one,one_mul]

private theorem core_inner_integral (f g : CoreField) :
    Integrable (fun z => conj (f.field z)*g.field z) D4BMModularCore.measure ∧
    inner ℂ (fieldVector f) (fieldVector g) =
      ∫ z, conj (f.field z)*g.field z ∂D4BMModularCore.measure := by
  have he : (fun z => inner ℂ (fieldVector f z) (fieldVector g z)) =ᵐ[D4BMModularCore.measure]
      (fun z => conj (f.field z)*g.field z) := by
    filter_upwards [(core_field_memLp f.field f.smooth f.compact).coeFn_toLp,
      (core_field_memLp g.field g.smooth g.compact).coeFn_toLp] with z hf hg
    change fieldVector f z = _ at hf
    change fieldVector g z = _ at hg
    rw [hf,hg]
    simp only [RCLike.inner_apply,mul_comm]
  exact ⟨(L2.integrable_inner (𝕜 := ℂ) (fieldVector f) (fieldVector g)).congr he,
    (L2.inner_def _ _).trans (integral_congr_ae he)⟩

private theorem core_second_green (f g : CoreField) :
    inner ℂ (fieldVector f.laplacian) (fieldVector g) =
      inner ℂ (fieldVector f) (fieldVector g.laplacian) := by
  have hf := f.completed_green ⟨frameGraph g,frameGraph_mem g⟩
  have hg := g.completed_green ⟨frameGraph f,frameGraph_mem f⟩
  change inner ℂ (derivativeVector f 1) (derivativeVector g 1)+
    inner ℂ (derivativeVector f Complex.I) (derivativeVector g Complex.I) =
      -inner ℂ (fieldVector f.laplacian) (fieldVector g) at hf
  change inner ℂ (derivativeVector g 1) (derivativeVector f 1)+
    inner ℂ (derivativeVector g Complex.I) (derivativeVector f Complex.I) =
      -inner ℂ (fieldVector g.laplacian) (fieldVector f) at hg
  have hc := congrArg conj hg
  simp only [map_add,map_neg,inner_conj_symm] at hc
  exact neg_injective (hf.symm.trans hc)

/-- The actual physical QNM angular test transposes against every constructed
quartic source cutoff. All modular seams are included by the original core
Green theorem; no test-domain or Green identity premise is supplied. -/
theorem quarticResidualCoreCutoff_physical_green (q r : XiZeroCopy) (slot : Fin 6) (n : ℕ) :
    Integrable (fun z : UpperHalfPlane => scalar (physicalAngularParameter r) (coordinates z)*
      (quarticResidualCoreCutoff q slot n).field z) D4BMModularCore.measure ∧
    Integrable (fun z : UpperHalfPlane => scalar (physicalAngularParameter r) (coordinates z)*
      (quarticResidualCoreCutoff q slot n).laplacian.field z) D4BMModularCore.measure ∧
    (∫ z : UpperHalfPlane, scalar (physicalAngularParameter r) (coordinates z)*
      (quarticResidualCoreCutoff q slot n).laplacian.field z ∂D4BMModularCore.measure) =
      (physicalAngularParameter r^(2 : ℕ)-1/4)*∫ z : UpperHalfPlane,
        scalar (physicalAngularParameter r) (coordinates z)*
          (quarticResidualCoreCutoff q slot n).field z ∂D4BMModularCore.measure := by
  let F := physicalCoreCutoff r (3*n+2)
  let G := quarticResidualCoreCutoff q slot n
  have hzero (z : UpperHalfPlane) (hz : z ∈ fd) (hy : 3*((n:ℝ)+1)<z.im) :
      G.field z=0 ∧ G.laplacian.field z=0 := by
    have he := residual_core_zero_germ q slot n z hz hy
    refine ⟨he.eq_of_nhds,?_⟩
    rw [CoreField.laplacian_field,chartLaplacian_congr he]
    simp [chartLaplacian,planarLaplacian,Function.comp_def]
  have he₀ : (fun z => conj (F.field z)*G.field z) =ᵐ[D4BMModularCore.measure]
      (fun z => scalar (physicalAngularParameter r) (coordinates z)*G.field z) := by
    filter_upwards [ae_restrict_mem ModularGroup.isClosed_fd.measurableSet] with z hz
    by_cases hy : z.im ≤ 3*((n:ℝ)+1)
    · rw [(outer_physical_test_germ r n z hz hy).eq_of_nhds]
      simp only [physicalTestField,starRingEnd_self_apply]
    · rw [(hzero z hz (lt_of_not_ge hy)).1,mul_zero,mul_zero]
  have he₁ : (fun z => conj (F.laplacian.field z)*G.field z) =ᵐ[D4BMModularCore.measure]
      (fun z => (physicalAngularParameter r^(2 : ℕ)-1/4)*
        (scalar (physicalAngularParameter r) (coordinates z)*G.field z)) := by
    filter_upwards [ae_restrict_mem ModularGroup.isClosed_fd.measurableSet] with z hz
    by_cases hy : z.im ≤ 3*((n:ℝ)+1)
    · rw [CoreField.laplacian_field,
        chartLaplacian_congr (outer_physical_test_germ r n z hz hy),
        physicalTestField_laplacian,starRingEnd_self_apply,mul_assoc]
    · rw [(hzero z hz (lt_of_not_ge hy)).1,mul_zero,mul_zero,mul_zero]
  have he₂ : (fun z => conj (F.field z)*G.laplacian.field z) =ᵐ[D4BMModularCore.measure]
      (fun z => scalar (physicalAngularParameter r) (coordinates z)*G.laplacian.field z) := by
    filter_upwards [ae_restrict_mem ModularGroup.isClosed_fd.measurableSet] with z hz
    by_cases hy : z.im ≤ 3*((n:ℝ)+1)
    · rw [(outer_physical_test_germ r n z hz hy).eq_of_nhds]
      simp only [physicalTestField,starRingEnd_self_apply]
    · rw [(hzero z hz (lt_of_not_ge hy)).2,mul_zero,mul_zero]
  have h₀ := core_inner_integral F G
  have h₁ := core_inner_integral F.laplacian G
  have h₂ := core_inner_integral F G.laplacian
  refine ⟨h₀.1.congr he₀,h₂.1.congr he₂,?_⟩
  change (∫ z, scalar (physicalAngularParameter r) (coordinates z)*G.laplacian.field z
    ∂D4BMModularCore.measure)=_
  rw [← integral_congr_ae he₂,← h₂.2,← core_second_green F G,h₁.2,
    integral_congr_ae he₁,integral_const_mul]


/-- Both derivatives of the outer cutoff survive in the residual's actual modular Laplacian. -/
theorem quarticResidualCoreCutoff_laplacian (q : XiZeroCopy) (slot : Fin 6) (n : ℕ)
    (z : UpperHalfPlane) (hz : z ∈ fd) :
    (quarticResidualCoreCutoff q slot n).laplacian.field z=
      (scaledCuspCutoff ((n:ℝ)+1) z.im:ℂ)*
        hyperbolicLaplacian (quarticContactResidual q slot) (coordinates z)+
      2*(z.im:ℂ)^(2 : ℕ)*((deriv (scaledCuspCutoff ((n:ℝ)+1)) z.im:ℝ):ℂ)*
        coordDeriv 1 (quarticContactResidual q slot) (coordinates z)+
      (z.im:ℂ)^(2 : ℕ)*((deriv (deriv (scaledCuspCutoff ((n:ℝ)+1))) z.im:ℝ):ℂ)*
        quarticContactResidual q slot (coordinates z) := by
  rw [CoreField.laplacian_field,chartLaplacian_congr (quarticResidualCoreCutoff_germ q slot n z hz)]
  change chartLaplacian (fun w =>
    (fun x : Fin 2 → ℝ => (scaledCuspCutoff ((n:ℝ)+1) (x 1):ℂ)*
      quarticContactResidual q slot x) (coordinates w)) z=_
  rw [chartLaplacian_coordinates (fun x : Fin 2 → ℝ =>
    (scaledCuspCutoff ((n:ℝ)+1) (x 1):ℂ)*quarticContactResidual q slot x) z]
  have hn : domain ∈ 𝓝 (coordinates z) :=
    (isOpen_lt continuous_const (continuous_apply 1)).mem_nhds z.im_pos
  exact hyperbolicLaplacian_height_mul _ (scaledCuspCutoff_smooth _) _ _
    (((quarticContactResidual_smooth q slot).contDiffAt hn).of_le (by norm_cast))

/-- Every point eventually retains the entire uncut residual germ, not just its value. -/
theorem quarticResidualCoreCutoff_eventually_germ (q : XiZeroCopy) (slot : Fin 6)
    (z : UpperHalfPlane) (hz : z ∈ fd) :
    ∀ᶠ n : ℕ in atTop, (quarticResidualCoreCutoff q slot n).field =ᶠ[𝓝 z]
      fun w => quarticContactResidual q slot (coordinates w) := by
  filter_upwards [modularCuspCutoff_eventually_one z hz] with n hn
  filter_upwards [hn,quarticResidualModular_germ q slot z hz] with w hc hr
  change modularCuspCutoff ((n:ℝ)+1) w*quarticResidualModular q slot w=_
  rw [hc,one_mul,hr]

end
end RHTower.D4BMQuarticResidualCore
