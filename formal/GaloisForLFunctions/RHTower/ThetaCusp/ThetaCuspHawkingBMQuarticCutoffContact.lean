import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMQuarticPrincipalExpansion
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMCutoffMismatchMellin

/-! Exact native Mellin contact of all six original quartic principal fields, with the full residual Laplacian retained. -/

open Set Filter Topology MeasureTheory
open scoped ContDiff
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HTGeometry.ScalarTwoJet
namespace RHTower.D4BMQuarticCutoffContact
open D4BMAngularSeries D4BMGlobalAngularResponse D4BMSquareCuspJets
open D4BMJointSource D4BMQuarticPrincipalExpansion D4BMQuarticCutoffMellin
noncomputable section
set_option autoImplicit false

private abbrev Field := (Fin 2 → ℝ) → ℂ
private def point (z : Fin 2 → ℝ) (hz : 0<z 1) : UpperHalfPlane := ⟨⟨z 0,z 1⟩,hz⟩
private theorem coordinates_point (z : Fin 2 → ℝ) (hz : 0<z 1) :
    coordinates (point z hz)=z := by
  funext i
  fin_cases i <;> rfl
private theorem principal_value (q : XiZeroCopy) (slot : Fin 6)
    (z : Fin 2 → ℝ) (hz : 0<z 1) :
    quarticContactPrincipal q slot z=∑ j : Fin 5,
      quarticPrincipalCoefficient q slot j*(z 1:ℂ)^(quarticPrincipalExponent q j) := by
  have h := quarticContactPrincipal_eq_power_sum q slot (point z hz)
  rw [coordinates_point] at h
  exact h
private theorem principal_germ (q : XiZeroCopy) (slot : Fin 6)
    (z : Fin 2 → ℝ) (hz : 0<z 1) :
    quarticContactPrincipal q slot =ᶠ[𝓝 z] fun w => ∑ j : Fin 5,
      quarticPrincipalCoefficient q slot j*(w 1:ℂ)^(quarticPrincipalExponent q j) := by
  filter_upwards [(isOpen_lt continuous_const (continuous_apply 1)).mem_nhds hz] with w hw
  exact principal_value q slot w hw
private theorem principal_smooth (q : XiZeroCopy) (slot : Fin 6)
    (z : Fin 2 → ℝ) (hz : 0<z 1) (n : ℕ) :
    ContDiffAt ℝ n (quarticContactPrincipal q slot) z := by
  have hn : domain ∈ 𝓝 z := (isOpen_lt continuous_const (continuous_apply 1)).mem_nhds hz
  have hs : ContDiffAt ℝ n (fun w => ∑ j : Fin 5,
      quarticPrincipalCoefficient q slot j*(w 1:ℂ)^(quarticPrincipalExponent q j)) z :=
    ContDiffAt.sum (fun j _ => contDiffAt_const.mul
      ((height_cpow_contDiffOn (quarticPrincipalExponent q j) n).contDiffAt hn))
  exact hs.congr_of_eventuallyEq (principal_germ q slot z hz)
private theorem cutoff_power_smooth (k : ℂ) (z : Fin 2 → ℝ) (hz : 0<z 1) :
    ContDiffAt ℝ 2 (cutoffPower k) z :=
  ((sourceCutoff_smooth.contDiffAt).of_le (by norm_cast)).mul ((height_cpow_contDiffOn k 2).contDiffAt
    ((isOpen_lt continuous_const (continuous_apply 1)).mem_nhds hz))
private theorem lap_sum {ι : Type*} (s : Finset ι) (f : ι → Field)
    (z : Fin 2 → ℝ) (hf : ∀ i ∈ s, ContDiffAt ℝ 2 (f i) z) :
    hyperbolicLaplacian (fun x => ∑ i ∈ s, f i x) z=∑ i ∈ s, hyperbolicLaplacian (f i) z := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa only [Finset.sum_empty,zero_mul] using
        (hyperbolicLaplacian_const_mul (f := fun _ : Fin 2 → ℝ => (1:ℂ)) (z := z) contDiffAt_const (0:ℂ))
  | @insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      rw [hyperbolicLaplacian_add (hf i (Finset.mem_insert_self _ _))
        (ContDiffAt.sum (fun j hj => hf j (Finset.mem_insert_of_mem hj))),
        ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))]

/-- The actual differential contact of the original cutoff with each full principal field. -/
def quarticPrincipalCutoffContact (q : XiZeroCopy) (slot : Fin 6) (z : Fin 2 → ℝ) : ℂ :=
  hyperbolicLaplacian (fun w => cutoff w*quarticContactPrincipal q slot w) z-
    cutoff z*hyperbolicLaplacian (quarticContactPrincipal q slot) z

/-- Both derivatives of the original cutoff survive in the exact five-term contact sum. -/
theorem quarticPrincipalCutoffContact_eq_sum (q : XiZeroCopy) (slot : Fin 6) (z : UpperHalfPlane) :
    quarticPrincipalCutoffContact q slot (coordinates z)=∑ j : Fin 5,
      quarticPrincipalCoefficient q slot j*cutoffCommutator (quarticPrincipalExponent q j) (coordinates z) := by
  have he : (fun w => cutoff w*quarticContactPrincipal q slot w) =ᶠ[𝓝 (coordinates z)]
      fun w => ∑ j : Fin 5, quarticPrincipalCoefficient q slot j*cutoffPower (quarticPrincipalExponent q j) w := by
    filter_upwards [principal_germ q slot (coordinates z) z.im_pos] with w hw
    rw [hw,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    unfold cutoffPower
    ring
  unfold quarticPrincipalCutoffContact
  rw [hyperbolicLaplacian_congr he,
    lap_sum _ _ _ (fun j _ => contDiffAt_const.mul (cutoff_power_smooth _ _ z.im_pos)),
    quarticContactPrincipal_laplacian_eq_power_sum,Finset.mul_sum,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [hyperbolicLaplacian_const_mul (cutoff_power_smooth _ _ z.im_pos)]
  unfold D4BMJointSource.cutoffCommutator
  change _=quarticPrincipalCoefficient q slot j*
    (hyperbolicLaplacian (cutoffPower (quarticPrincipalExponent q j)) (coordinates z)-
      cutoff (coordinates z)*(quarticPrincipalExponent q j*(quarticPrincipalExponent q j-1)*
        (z.im:ℂ)^(quarticPrincipalExponent q j)))
  ring

private theorem scalar_contact_sum (q : XiZeroCopy) (slot : Fin 6) (u : ℂ) (z : UpperHalfPlane) :
    scalar u (coordinates z)*quarticPrincipalCutoffContact q slot (coordinates z)=
      ∑ j : Fin 5, quarticPrincipalCoefficient q slot j*
        (scalar u (coordinates z)*cutoffCommutator (quarticPrincipalExponent q j) (coordinates z)) := by
  rw [quarticPrincipalCutoffContact_eq_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Actual native absolute admission of every full-scalar cutoff-contact pairing. -/
theorem quarticPrincipalCutoffContact_scalar_integrable (q : XiZeroCopy) (slot : Fin 6) (u : ℂ) :
    Integrable (fun z : UpperHalfPlane =>
      scalar u (coordinates z)*quarticPrincipalCutoffContact q slot (coordinates z)) D4BMModularCore.measure := by
  have h : Integrable (fun z : UpperHalfPlane => ∑ j : Fin 5, quarticPrincipalCoefficient q slot j*
      (scalar u (coordinates z)*cutoffCommutator (quarticPrincipalExponent q j) (coordinates z)))
      D4BMModularCore.measure :=
    integrable_finsetSum _ (fun j _ => (scalar_cutoffCommutator_integrable u _).const_mul _)
  exact h.congr (Filter.Eventually.of_forall (fun z => (scalar_contact_sum q slot u z).symm))

private theorem physical_cutoff_moment (q : XiZeroCopy) (j : Fin 5) :
    scalarCutoffPeriod (physicalAngularParameter q) (quarticPrincipalExponent q j)=
      reflectedCompletedLambda ((q.1:ℂ)-1)*
        (quarticPrincipalExponent q j*(quarticPrincipalExponent q j-1)-((q.1:ℂ)*((q.1:ℂ)-2)/4))*
        nativeCutoffMellinContinuation (quarticPhysicalMellinExponent q j) := by
  have hm : d4BMCompletedEisensteinCuspWeylExponent (physicalAngularParameter q) false = 1-(q.1:ℂ)/2 := by
    rw [physicalAngularParameter_eq]
    norm_num [d4BMCompletedEisensteinCuspWeylExponent,d4BMCuspSign]
    ring
  have hcm : d4BMCompletedEisensteinCuspConstantCoefficient (physicalAngularParameter q) false =
      reflectedCompletedLambda ((q.1:ℂ)-1) := by
    rw [physicalAngularParameter_eq]
    simp only [d4BMCompletedEisensteinCuspConstantCoefficient,Bool.false_eq_true,↓reduceIte]
    congr 1
    ring
  have hcp : d4BMCompletedEisensteinCuspConstantCoefficient (physicalAngularParameter q) true = 0 := by
    rw [physicalAngularParameter_eq]
    simp only [d4BMCompletedEisensteinCuspConstantCoefficient,↓reduceIte]
    rw [show 1+2*(((q.1:ℂ)-1)/2)=(q.1:ℂ) by ring,nativeCompletedLambda_at_xi]
  have hw : (1-(q.1:ℂ)/2)+quarticPrincipalExponent q j-1=quarticPhysicalMellinExponent q j := by
    unfold quarticPhysicalMellinExponent
    ring
  have hv : (1-(q.1:ℂ)/2)+quarticPrincipalExponent q j-1≠0 :=
    hw ▸ quarticPhysicalMellinExponent_ne_zero q j
  rw [scalarCutoffPeriod_eq_moments,hcm,hcp,hm,zero_mul,add_zero,
    cutoffPowerMoment_eq_gap_mul_nativeMellin _ _ hv,hw]
  ring

/-- The actual physical cutoff-contact integral equals its full original Mellin correction. -/
theorem quarticPrincipalCutoffContact_physical_integral (q : XiZeroCopy) (slot : Fin 6) :
    (∫ z : UpperHalfPlane, scalar (physicalAngularParameter q) (coordinates z)*
      quarticPrincipalCutoffContact q slot (coordinates z) ∂D4BMModularCore.measure)=
      reflectedCompletedLambda ((q.1:ℂ)-1)*∑ j : Fin 5, quarticPrincipalCoefficient q slot j*
        (quarticPrincipalExponent q j*(quarticPrincipalExponent q j-1)-((q.1:ℂ)*((q.1:ℂ)-2)/4))*
        nativeCutoffMellinContinuation (quarticPhysicalMellinExponent q j) := by
  rw [integral_congr_ae (Filter.Eventually.of_forall (scalar_contact_sum q slot (physicalAngularParameter q)))]
  rw [integral_finsetSum _ (fun j _ =>
    (scalar_cutoffCommutator_integrable (physicalAngularParameter q) _).const_mul _)]
  simp_rw [integral_const_mul]
  change (∑ j : Fin 5, quarticPrincipalCoefficient q slot j*
    scalarCutoffPeriod (physicalAngularParameter q) (quarticPrincipalExponent q j))=_
  simp_rw [physical_cutoff_moment]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The actual principal-subtracted H retains the full cutoff contact in its Laplacian. -/
theorem quarticContactResidual_H_laplacian (q : XiZeroCopy) (z : UpperHalfPlane) :
    hyperbolicLaplacian (quarticContactResidual q 4) (coordinates z)=
      quarticContactResidual q 5 (coordinates z)-quarticPrincipalCutoffContact q 4 (coordinates z) := by
  have hn : domain ∈ 𝓝 (coordinates z) :=
    (isOpen_lt continuous_const (continuous_apply 1)).mem_nhds z.im_pos
  have hf : ContDiffAt ℝ 2 (quarticContactField q 4) (coordinates z) :=
    ((quarticContactField_smooth q 4).contDiffAt hn).of_le (by norm_cast)
  have hc : ContDiffAt ℝ 2 cutoff (coordinates z) :=
    sourceCutoff_smooth.contDiffAt.of_le (by norm_cast)
  have hp := hc.mul (principal_smooth q 4 (coordinates z) z.im_pos 2)
  have he : quarticContactResidual q 4=fun w => quarticContactField q 4 w+
      (-1:ℂ)*(cutoff w*quarticContactPrincipal q 4 w) := by
    funext w
    unfold quarticContactResidual
    ring
  rw [he,hyperbolicLaplacian_add hf (contDiffAt_const.mul hp),hyperbolicLaplacian_const_mul hp]
  have hf' : hyperbolicLaplacian (quarticContactField q 4) (coordinates z)=
      quarticContactField q 5 (coordinates z) := rfl
  have hp' : hyperbolicLaplacian (quarticContactPrincipal q 4) (coordinates z)=
      quarticContactPrincipal q 5 (coordinates z) := rfl
  rw [hf']
  unfold quarticContactResidual quarticPrincipalCutoffContact
  rw [hp']
  ring

/-- The full physical Laplacian pairing of the residual H is absolutely admitted. -/
theorem quarticContactResidual_H_laplacian_scalar_integrable (q : XiZeroCopy) (u : ℂ) :
    Integrable (fun z : UpperHalfPlane => scalar u (coordinates z)*
      hyperbolicLaplacian (quarticContactResidual q 4) (coordinates z)) D4BMModularCore.measure := by
  have h := (quarticContactResidual_scalar_integrable q 5 u).sub
    (quarticPrincipalCutoffContact_scalar_integrable q 4 u)
  apply h.congr
  exact Filter.Eventually.of_forall (fun z => by
    change scalar u (coordinates z)*quarticContactResidual q 5 (coordinates z)-
      scalar u (coordinates z)*quarticPrincipalCutoffContact q 4 (coordinates z)=_
    dsimp only
    rw [quarticContactResidual_H_laplacian,mul_sub])

end
end RHTower.D4BMQuarticCutoffContact
