import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMQuarticResidualCore

/-! Native physical Green transport for the actual quartic residual, with every original Mellin and cutoff contact retained. -/

open Set Filter Topology MeasureTheory UpperHalfPlane ModularGroup
open scoped ContDiff MatrixGroups ComplexConjugate
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HTGeometry.ScalarTwoJet
namespace RHTower.D4BMQuarticResidualGreen
open D4BMAngularSeries D4BMGlobalAngularResponse D4BMSquareCuspJets
open D4BMJointSource D4BMQuarticPrincipalExpansion D4BMQuarticCutoffMellin
open D4BMModularCore D4BMJointWave D4BMQuarticCutoffContact D4BMQuarticResidualCore
noncomputable section
set_option autoImplicit false

private theorem jet_smooth {f : (Fin 2 → ℝ) → ℂ} (hf : ContDiffOn ℝ ∞ f domain)
    (word : List (Fin 2)) : ContDiffOn ℝ ∞ (coordinateJet word f) domain := by
  induction word with
  | nil => exact hf
  | cons i word ih =>
    intro z hz
    exact (((ih.contDiffAt ((isOpen_lt continuous_const (continuous_apply 1)).mem_nhds hz)).fderiv_right
      (m := ∞) (by simp)).clm_apply contDiffAt_const).contDiffWithinAt

private theorem jet_germ {f g : (Fin 2 → ℝ) → ℂ} {z : Fin 2 → ℝ}
    (he : f =ᶠ[𝓝 z] g) (word : List (Fin 2)) :
    coordinateJet word f =ᶠ[𝓝 z] coordinateJet word g := by
  induction word with
  | nil => exact he
  | cons i word ih =>
    filter_upwards [ih.fderiv (𝕜 := ℝ)] with w hw
    change fderiv ℝ (coordinateJet word f) w (Pi.single i 1)=
      fderiv ℝ (coordinateJet word g) w (Pi.single i 1)
    rw [hw]

/-- Every actual derivative of the original cutoff residual admits every complex height weight. -/
theorem quarticContactResidual_weighted_jet_memLp (q : XiZeroCopy) (slot : Fin 6)
    (word : List (Fin 2)) (w : ℂ) :
    MemLp (fun z : UpperHalfPlane => (z.im:ℂ)^w*
      coordinateJet word (quarticContactResidual q slot) (coordinates z)) 2 D4BMModularCore.measure := by
  obtain ⟨C,-,hC⟩ := quarticContact_remainder_jet_bound q slot w word ⟨3,by norm_num⟩
  apply cuspBound_memLp _ ((height_cpow_contDiffOn w 0).continuousOn.mul
    (jet_smooth (quarticContactResidual_smooth q slot) word).continuousOn) C
  intro z hz
  have he : quarticContactResidual q slot =ᶠ[𝓝 z] fun v =>
      quarticContactField q slot v-quarticContactPrincipal q slot v := by
    filter_upwards [(isOpen_lt continuous_const (continuous_apply 1)).mem_nhds hz] with v hv
    have hc : cutoff v=1 := by
      unfold cutoff
      rw [Real.smoothTransition.one_of_one_le (by linarith)]
      simp
    rw [quarticContactResidual,hc,one_mul]
  change ‖(z 1:ℂ)^w*coordinateJet word (quarticContactResidual q slot) z‖ ≤ C
  rw [(jet_germ he word).eq_of_nhds]
  exact hC z hz.le

/-- The actual first-derivative cutoff error pairs absolutely with the complete physical scalar. -/
theorem quarticResidual_vertical_pairing_integrable (q r : XiZeroCopy) (slot : Fin 6) :
    Integrable (fun z : UpperHalfPlane => scalar (physicalAngularParameter r) (coordinates z)*
      (z.im:ℂ)*coordDeriv 1 (quarticContactResidual q slot) (coordinates z)) D4BMModularCore.measure := by
  have hh : MemLp (fun z : UpperHalfPlane => (z.im:ℂ)^2*
      coordDeriv 1 (quarticContactResidual q slot) (coordinates z)) 2 D4BMModularCore.measure := by
    simpa only [coordinateJet,Complex.cpow_ofNat] using
      quarticContactResidual_weighted_jet_memLp q slot [1] 2
  apply ((physicalDualDensity_memLp r).integrable_mul hh).congr
  exact Filter.Eventually.of_forall (fun z => by
    change ((z.im:ℂ)⁻¹*scalar (physicalAngularParameter r) (coordinates z))*
      ((z.im:ℂ)^2*coordDeriv 1 (quarticContactResidual q slot) (coordinates z))=_
    have hy : (z.im:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr z.im_pos.ne'
    field_simp [hy])

/-- The actual complete-scalar core pairings converge to the admitted original residual pairing. -/
theorem quarticResidualCoreCutoff_physical_pairing_tendsto (q r : XiZeroCopy) (slot : Fin 6) :
    Tendsto (fun n : ℕ => ∫ z : UpperHalfPlane,
      scalar (physicalAngularParameter r) (coordinates z)*(quarticResidualCoreCutoff q slot n).field z
        ∂D4BMModularCore.measure) atTop (𝓝 (∫ z : UpperHalfPlane,
          scalar (physicalAngularParameter r) (coordinates z)*quarticContactResidual q slot (coordinates z)
            ∂D4BMModularCore.measure)) := by
  let P : UpperHalfPlane → ℂ := fun z =>
    scalar (physicalAngularParameter r) (coordinates z)*quarticContactResidual q slot (coordinates z)
  apply tendsto_integral_of_dominated_convergence (fun z => ‖P z‖)
  · intro n
    exact (quarticResidualCoreCutoff_physical_green q r slot n).1.aestronglyMeasurable
  · exact (quarticContactResidual_scalar_integrable q slot (physicalAngularParameter r)).norm
  · intro n
    filter_upwards [ae_restrict_mem ModularGroup.isClosed_fd.measurableSet] with z hz
    change ‖scalar (physicalAngularParameter r) (coordinates z)*
      (modularCuspCutoff ((n:ℝ)+1) z*quarticResidualModular q slot z)‖ ≤ _
    rw [(quarticResidualModular_germ q slot z hz).eq_of_nhds,mul_left_comm,norm_mul]
    exact (mul_le_mul_of_nonneg_right (modularCuspCutoff_norm_le_one _ z) (norm_nonneg _)).trans_eq
      (one_mul _)
  · filter_upwards [ae_restrict_mem ModularGroup.isClosed_fd.measurableSet] with z hz
    apply tendsto_const_nhds.congr'
    filter_upwards [quarticResidualCoreCutoff_eventually_germ q slot z hz] with n hn
    rw [hn.eq_of_nhds]

private theorem scaled_norm_le_one (N y : ℝ) : ‖(scaledCuspCutoff N y:ℂ)‖ ≤ 1 := by
  change ‖(baseCuspCutoff (y/N):ℂ)‖ ≤ 1
  rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (baseCuspCutoff_bounds _).1]
  exact (baseCuspCutoff_bounds _).2

/-- Both differentiated outer-cutoff contributions disappear in the admitted physical Laplacian limit. -/
theorem quarticResidualCoreCutoff_H_physical_laplacian_tendsto (q r : XiZeroCopy) :
    Tendsto (fun n : ℕ => ∫ z : UpperHalfPlane,
      scalar (physicalAngularParameter r) (coordinates z)*(quarticResidualCoreCutoff q 4 n).laplacian.field z
        ∂D4BMModularCore.measure) atTop (𝓝 (∫ z : UpperHalfPlane,
          scalar (physicalAngularParameter r) (coordinates z)*
            hyperbolicLaplacian (quarticContactResidual q 4) (coordinates z) ∂D4BMModularCore.measure)) := by
  obtain ⟨C,-,hb⟩ := scaledCuspCutoff_derivative_bounds
  let P : UpperHalfPlane → ℂ := fun z =>
    scalar (physicalAngularParameter r) (coordinates z)*quarticContactResidual q 4 (coordinates z)
  let V : UpperHalfPlane → ℂ := fun z => scalar (physicalAngularParameter r) (coordinates z)*
    (z.im:ℂ)*coordDeriv 1 (quarticContactResidual q 4) (coordinates z)
  let L : UpperHalfPlane → ℂ := fun z => scalar (physicalAngularParameter r) (coordinates z)*
    hyperbolicLaplacian (quarticContactResidual q 4) (coordinates z)
  let B : UpperHalfPlane → ℝ := fun z => ‖L z‖+2*C*‖V z‖+C*‖P z‖
  apply tendsto_integral_of_dominated_convergence B
  · intro n
    exact (quarticResidualCoreCutoff_physical_green q r 4 n).2.1.aestronglyMeasurable
  · exact (((quarticContactResidual_H_laplacian_scalar_integrable q (physicalAngularParameter r)).norm).add
      ((quarticResidual_vertical_pairing_integrable q r 4).norm.const_mul (2*C))).add
        ((quarticContactResidual_scalar_integrable q 4 (physicalAngularParameter r)).norm.const_mul C)
  · intro n
    filter_upwards [ae_restrict_mem ModularGroup.isClosed_fd.measurableSet] with z hz
    let N : ℝ := (n:ℝ)+1
    have h1 : ‖(z.im:ℂ)*((deriv (scaledCuspCutoff N) z.im:ℝ):ℂ)‖ ≤ C := by
      rw [← Complex.ofReal_mul,Complex.norm_real,Real.norm_eq_abs]
      exact (hb N z.im).1
    have h2 : ‖(z.im:ℂ)^2*((deriv (deriv (scaledCuspCutoff N)) z.im:ℝ):ℂ)‖ ≤ C := by
      rw [← Complex.ofReal_pow,← Complex.ofReal_mul,Complex.norm_real,Real.norm_eq_abs]
      exact (hb N z.im).2
    have he : scalar (physicalAngularParameter r) (coordinates z)*
        (quarticResidualCoreCutoff q 4 n).laplacian.field z=
        (scaledCuspCutoff N z.im:ℂ)*L z+
          (2:ℂ)*((z.im:ℂ)*((deriv (scaledCuspCutoff N) z.im:ℝ):ℂ))*V z+
            ((z.im:ℂ)^2*((deriv (deriv (scaledCuspCutoff N)) z.im:ℝ):ℂ))*P z := by
      rw [quarticResidualCoreCutoff_laplacian q 4 n z hz]
      dsimp only [L,V,P,N]
      ring
    have h0b : ‖(scaledCuspCutoff N z.im:ℂ)*L z‖ ≤ ‖L z‖ := by
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_right (scaled_norm_le_one N z.im) (norm_nonneg _)).trans_eq (one_mul _)
    have h1b : ‖(2:ℂ)*((z.im:ℂ)*((deriv (scaledCuspCutoff N) z.im:ℝ):ℂ))*V z‖ ≤ 2*C*‖V z‖ := by
      rw [norm_mul,norm_mul,Complex.norm_ofNat]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 (by norm_num)) (norm_nonneg _)
    have h2b : ‖((z.im:ℂ)^2*((deriv (deriv (scaledCuspCutoff N)) z.im:ℝ):ℂ))*P z‖ ≤ C*‖P z‖ := by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
    rw [he]
    calc
      _ ≤ ‖(scaledCuspCutoff N z.im:ℂ)*L z‖+
          ‖(2:ℂ)*((z.im:ℂ)*((deriv (scaledCuspCutoff N) z.im:ℝ):ℂ))*V z‖+
            ‖((z.im:ℂ)^2*((deriv (deriv (scaledCuspCutoff N)) z.im:ℝ):ℂ))*P z‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ ≤ ‖L z‖+2*C*‖V z‖+C*‖P z‖ := add_le_add (add_le_add h0b h1b) h2b
  · filter_upwards [ae_restrict_mem ModularGroup.isClosed_fd.measurableSet] with z hz
    apply tendsto_const_nhds.congr'
    filter_upwards [quarticResidualCoreCutoff_eventually_germ q 4 z hz] with n hn
    rw [CoreField.laplacian_field,chartLaplacian_congr hn,
      chartLaplacian_coordinates (quarticContactResidual q 4) z]

/-- Native Green transport for the actual principal-subtracted H and the original physical QNM test. -/
theorem quarticContactResidual_H_physical_green (q r : XiZeroCopy) :
    (∫ z : UpperHalfPlane, scalar (physicalAngularParameter r) (coordinates z)*
      hyperbolicLaplacian (quarticContactResidual q 4) (coordinates z) ∂D4BMModularCore.measure)=
      (physicalAngularParameter r^2-1/4)*∫ z : UpperHalfPlane,
        scalar (physicalAngularParameter r) (coordinates z)*quarticContactResidual q 4 (coordinates z)
          ∂D4BMModularCore.measure := by
  have h := (quarticResidualCoreCutoff_physical_pairing_tendsto q r 4).const_mul
    (physicalAngularParameter r^2-1/4)
  have he : (fun n : ℕ => ∫ z : UpperHalfPlane, scalar (physicalAngularParameter r) (coordinates z)*
      (quarticResidualCoreCutoff q 4 n).laplacian.field z ∂D4BMModularCore.measure)=
      fun n => (physicalAngularParameter r^2-1/4)*∫ z : UpperHalfPlane,
        scalar (physicalAngularParameter r) (coordinates z)*(quarticResidualCoreCutoff q 4 n).field z
          ∂D4BMModularCore.measure := funext (fun n => (quarticResidualCoreCutoff_physical_green q r 4 n).2.2)
  rw [← he] at h
  exact tendsto_nhds_unique (quarticResidualCoreCutoff_H_physical_laplacian_tendsto q r) h

/-- The original physical finite part, retaining its unchanged native Mellin subtraction. -/
def quarticNativePhysicalPeriod (q : XiZeroCopy) (slot : Fin 6) : ℂ :=
  (∫ z : UpperHalfPlane, scalar (physicalAngularParameter q) (coordinates z)*
    quarticContactResidual q slot (coordinates z) ∂D4BMModularCore.measure)-
    reflectedCompletedLambda ((q.1:ℂ)-1)*∑ j : Fin 5, quarticPrincipalCoefficient q slot j*
      nativeCutoffMellinContinuation (quarticPhysicalMellinExponent q j)

/-- Exact native physical Green transport of H: all original cusp and source-cutoff contacts are included. -/
theorem quarticNativePhysicalPeriod_H_green (q : XiZeroCopy) :
    quarticNativePhysicalPeriod q 5=(physicalAngularParameter q^2-1/4)*quarticNativePhysicalPeriod q 4 := by
  let mu : ℂ := physicalAngularParameter q^2-1/4
  have hmu : mu=(q.1:ℂ)*((q.1:ℂ)-2)/4 := by
    dsimp only [mu]
    rw [physicalAngularParameter_eq]
    ring
  have hc (j : Fin 5) : quarticPrincipalCoefficient q 5 j=
      quarticPrincipalExponent q j*(quarticPrincipalExponent q j-1)*quarticPrincipalCoefficient q 4 j := rfl
  have hs : (∑ j : Fin 5, quarticPrincipalCoefficient q 4 j*
      (quarticPrincipalExponent q j*(quarticPrincipalExponent q j-1)-mu)*
        nativeCutoffMellinContinuation (quarticPhysicalMellinExponent q j))=
      (∑ j : Fin 5, quarticPrincipalCoefficient q 5 j*
        nativeCutoffMellinContinuation (quarticPhysicalMellinExponent q j))-
      mu*(∑ j : Fin 5, quarticPrincipalCoefficient q 4 j*
        nativeCutoffMellinContinuation (quarticPhysicalMellinExponent q j)) := by
    rw [Finset.mul_sum,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rw [hc]
    ring
  have hk := quarticPrincipalCutoffContact_physical_integral q 4
  rw [← hmu,hs] at hk
  have hg := quarticContactResidual_H_physical_green q q
  simp_rw [quarticContactResidual_H_laplacian,mul_sub] at hg
  rw [integral_sub (quarticContactResidual_scalar_integrable q 5 (physicalAngularParameter q))
    (quarticPrincipalCutoffContact_scalar_integrable q 4 (physicalAngularParameter q)),hk] at hg
  unfold quarticNativePhysicalPeriod
  dsimp only [mu] at hg
  linear_combination hg

end
end RHTower.D4BMQuarticResidualGreen
