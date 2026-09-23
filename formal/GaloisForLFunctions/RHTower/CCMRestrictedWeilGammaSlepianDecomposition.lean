import GaloisForLFunctions.RHTower.CCMRestrictedWeilActualBirmanSchwinger
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# Gamma--Slepian decomposition of the exact restricted-Weil ground

The compact injective Gram `J_a† J_a` supplies the canonical spectral basis of the complete CCM
archimedean form domain.  Its Rayleigh energy is literal physical aperture mass, its eigenspaces
form a complete Hilbert sum, and its zero eigenspace vanishes.  Projecting the actual compact
Birman--Schwinger ground equation against every Gamma--Slepian eigenspace gives an exact modal
balance with the full compressed prime--polar remainder intact.
-/

open MeasureTheory
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

/-- Positive compact Gamma--Slepian Gram operator on the exact complete form domain. -/
def ccmArchimedeanGammaSlepianGram (a : SuzukiPositiveAperture) :
    CCMArchimedeanFormDomain a →L[ℂ] CCMArchimedeanFormDomain a :=
  (ccmArchimedeanFormToAperture a).adjoint ∘L
    ccmArchimedeanFormToAperture a

theorem ccmArchimedeanGammaSlepianGram_isPositive
    (a : SuzukiPositiveAperture) :
    (ccmArchimedeanGammaSlepianGram a).IsPositive := by
  exact ContinuousLinearMap.isPositive_adjoint_comp_self
    (ccmArchimedeanFormToAperture a)

theorem ccmArchimedeanGammaSlepianGram_isSelfAdjoint
    (a : SuzukiPositiveAperture) :
    IsSelfAdjoint (ccmArchimedeanGammaSlepianGram a) := by
  exact ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
    (ccmArchimedeanGammaSlepianGram_isPositive a).1

theorem isCompactOperator_ccmArchimedeanGammaSlepianGram
    (a : SuzukiPositiveAperture) :
    IsCompactOperator (ccmArchimedeanGammaSlepianGram a) := by
  exact (isCompactOperator_ccmArchimedeanFormToAperture a).clm_comp
    (ccmArchimedeanFormToAperture a).adjoint

theorem ccmArchimedeanGammaSlepianGram_injective
    (a : SuzukiPositiveAperture) :
    Function.Injective (ccmArchimedeanGammaSlepianGram a) := by
  exact (ccmArchimedeanFormToAperture a).adjoint_comp_self_injective_iff.mpr
    (ccmArchimedeanFormToAperture_injective a)

/-- Gamma--Slepian Gram energy is exactly literal physical aperture mass. -/
theorem ccmArchimedeanGammaSlepianGram_reApplyInnerSelf
    (a : SuzukiPositiveAperture) (u : CCMArchimedeanFormDomain a) :
    (ccmArchimedeanGammaSlepianGram a).reApplyInnerSelf u =
      ‖ccmArchimedeanFormToAperture a u‖ ^ (2 : ℕ) := by
  rw [ContinuousLinearMap.reApplyInnerSelf_apply]
  change (inner ℂ
    ((ccmArchimedeanFormToAperture a).adjoint
      (ccmArchimedeanFormToAperture a u)) u).re = _
  rw [ContinuousLinearMap.adjoint_inner_left, inner_self_eq_norm_sq_to_K]
  norm_cast

/-- Kernel presentation of one Gamma--Slepian eigenspace. -/
def ccmGammaSlepianEigenCLM (a : SuzukiPositiveAperture) (mu : ℂ) :
    CCMArchimedeanFormDomain a →L[ℂ] CCMArchimedeanFormDomain a :=
  ccmArchimedeanGammaSlepianGram a -
    mu • ContinuousLinearMap.id ℂ (CCMArchimedeanFormDomain a)

def ccmGammaSlepianEigenspace (a : SuzukiPositiveAperture) (mu : ℂ) :
    Submodule ℂ (CCMArchimedeanFormDomain a) :=
  LinearMap.ker ((ccmGammaSlepianEigenCLM a mu :
    CCMArchimedeanFormDomain a →L[ℂ] CCMArchimedeanFormDomain a) :
      CCMArchimedeanFormDomain a →ₗ[ℂ] CCMArchimedeanFormDomain a)

theorem mem_ccmGammaSlepianEigenspace_iff
    {a : SuzukiPositiveAperture} {mu : ℂ}
    {u : CCMArchimedeanFormDomain a} :
    u ∈ ccmGammaSlepianEigenspace a mu ↔
      ccmArchimedeanGammaSlepianGram a u = mu • u := by
  rw [ccmGammaSlepianEigenspace, LinearMap.mem_ker]
  show ccmGammaSlepianEigenCLM a mu u = 0 ↔ _
  rw [ccmGammaSlepianEigenCLM]
  simp [sub_eq_zero]

/-- The exact Gamma--Slepian Gram has no invisible zero mode. -/
theorem ccmGammaSlepianEigenspace_zero_eq_bot
    (a : SuzukiPositiveAperture) :
    ccmGammaSlepianEigenspace a 0 = ⊥ := by
  ext u
  rw [mem_ccmGammaSlepianEigenspace_iff]
  simp only [zero_smul, Submodule.mem_bot]
  constructor
  · intro hu
    apply ccmArchimedeanGammaSlepianGram_injective a
    simpa using hu
  · rintro rfl
    simp

theorem completeSpace_ccmGammaSlepianEigenspace
    (a : SuzukiPositiveAperture) (mu : ℂ) :
    CompleteSpace (ccmGammaSlepianEigenspace a mu) := by
  have hclosed : IsClosed
      ((ccmGammaSlepianEigenspace a mu :
        Submodule ℂ (CCMArchimedeanFormDomain a)) :
          Set (CCMArchimedeanFormDomain a)) :=
    (ccmGammaSlepianEigenCLM a mu).isClosed_ker
  exact hclosed.completeSpace_coe

theorem ccmGammaSlepianEigenspace_eq_eigenspace
    (a : SuzukiPositiveAperture) (mu : ℂ) :
    ccmGammaSlepianEigenspace a mu =
      Module.End.eigenspace
        ((ccmArchimedeanGammaSlepianGram a :
          CCMArchimedeanFormDomain a →L[ℂ] CCMArchimedeanFormDomain a) :
          Module.End ℂ (CCMArchimedeanFormDomain a)) mu := by
  ext u
  rw [mem_ccmGammaSlepianEigenspace_iff, Module.End.mem_eigenspace_iff]
  exact Iff.rfl

theorem completeSpace_ccmGammaSlepian_operator_eigenspace
    (a : SuzukiPositiveAperture) (mu : ℂ) :
    CompleteSpace (Module.End.eigenspace
      ((ccmArchimedeanGammaSlepianGram a :
        CCMArchimedeanFormDomain a →L[ℂ] CCMArchimedeanFormDomain a) :
        Module.End ℂ (CCMArchimedeanFormDomain a)) mu) := by
  rw [← ccmGammaSlepianEigenspace_eq_eigenspace]
  exact completeSpace_ccmGammaSlepianEigenspace a mu

theorem isSymmetric_ccmArchimedeanGammaSlepianGram
    (a : SuzukiPositiveAperture) :
    ((ccmArchimedeanGammaSlepianGram a :
      CCMArchimedeanFormDomain a →L[ℂ] CCMArchimedeanFormDomain a) :
      Module.End ℂ (CCMArchimedeanFormDomain a)).IsSymmetric := by
  exact ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
    (ccmArchimedeanGammaSlepianGram_isSelfAdjoint a)

/-- Gamma--Slepian eigenspaces span the complete CCM form domain. -/
theorem ccmGammaSlepianEigenspaces_topologicalClosure
    (a : SuzukiPositiveAperture) :
    (⊤ : Submodule ℂ (CCMArchimedeanFormDomain a)) ≤
      (⨆ mu : ℂ, Module.End.eigenspace
        ((ccmArchimedeanGammaSlepianGram a :
          CCMArchimedeanFormDomain a →L[ℂ] CCMArchimedeanFormDomain a) :
          Module.End ℂ (CCMArchimedeanFormDomain a)) mu).topologicalClosure := by
  have hbot := ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot
    (isCompactOperator_ccmArchimedeanGammaSlepianGram a)
    (isSymmetric_ccmArchimedeanGammaSlepianGram a)
  exact (Submodule.topologicalClosure_eq_top_iff.mpr hbot).ge

/-- Exact complete Hilbert sum of the actual Gamma--Slepian eigenspaces. -/
theorem isHilbertSum_ccmGammaSlepianEigenspaces
    (a : SuzukiPositiveAperture) :
    IsHilbertSum ℂ
      (fun mu : ℂ => (Module.End.eigenspace
        ((ccmArchimedeanGammaSlepianGram a :
          CCMArchimedeanFormDomain a →L[ℂ] CCMArchimedeanFormDomain a) :
          Module.End ℂ (CCMArchimedeanFormDomain a)) mu :
        Submodule ℂ (CCMArchimedeanFormDomain a)))
      (fun mu : ℂ => (Module.End.eigenspace
        ((ccmArchimedeanGammaSlepianGram a :
          CCMArchimedeanFormDomain a →L[ℂ] CCMArchimedeanFormDomain a) :
          Module.End ℂ (CCMArchimedeanFormDomain a)) mu).subtypeₗᵢ) := by
  haveI : ∀ mu : ℂ, CompleteSpace (Module.End.eigenspace
      ((ccmArchimedeanGammaSlepianGram a :
        CCMArchimedeanFormDomain a →L[ℂ] CCMArchimedeanFormDomain a) :
        Module.End ℂ (CCMArchimedeanFormDomain a)) mu) :=
    fun mu => completeSpace_ccmGammaSlepian_operator_eigenspace a mu
  exact IsHilbertSum.mkInternal _
    ((isSymmetric_ccmArchimedeanGammaSlepianGram a).orthogonalFamily_eigenspaces)
    (ccmGammaSlepianEigenspaces_topologicalClosure a)

/-- Actual Gamma--Slepian spectral component of a complete CCM form vector. -/
def ccmGammaSlepianComponent (a : SuzukiPositiveAperture)
    (u : CCMArchimedeanFormDomain a) (mu : ℂ) :
    CCMArchimedeanFormDomain a :=
  (((isHilbertSum_ccmGammaSlepianEigenspaces a).linearIsometryEquiv u mu :
    Module.End.eigenspace
      ((ccmArchimedeanGammaSlepianGram a :
        CCMArchimedeanFormDomain a →L[ℂ] CCMArchimedeanFormDomain a) :
        Module.End ℂ (CCMArchimedeanFormDomain a)) mu) :
    CCMArchimedeanFormDomain a)

theorem ccmGammaSlepianComponent_mem (a : SuzukiPositiveAperture)
    (u : CCMArchimedeanFormDomain a) (mu : ℂ) :
    ccmGammaSlepianComponent a u mu ∈ ccmGammaSlepianEigenspace a mu := by
  rw [ccmGammaSlepianEigenspace_eq_eigenspace]
  exact ((isHilbertSum_ccmGammaSlepianEigenspaces a).linearIsometryEquiv u mu).2

/-- Every complete CCM form vector is the unconditional sum of its actual Gamma--Slepian
components. -/
theorem hasSum_ccmGammaSlepianComponent (a : SuzukiPositiveAperture)
    (u : CCMArchimedeanFormDomain a) :
    HasSum (ccmGammaSlepianComponent a u) u := by
  have h := (isHilbertSum_ccmGammaSlepianEigenspaces a).hasSum_linearIsometryEquiv_symm
    ((isHilbertSum_ccmGammaSlepianEigenspaces a).linearIsometryEquiv u)
  rw [LinearIsometryEquiv.symm_apply_apply] at h
  exact h

/-- Prime--polar remainder compressed to the exact Gamma form domain. -/
def ccmRestrictedWeilFormRemainder (a : SuzukiPositiveAperture) :
    CCMArchimedeanFormDomain a →L[ℂ] CCMArchimedeanFormDomain a :=
  (ccmArchimedeanFormToAperture a).adjoint ∘L
    ccmRestrictedWeilBoundedRemainder a ∘L
      ccmArchimedeanFormToAperture a

theorem ccmRestrictedWeilFormBirmanSchwinger_eq_gammaSlepian_sub_remainder
    (a : SuzukiPositiveAperture) (E : ℝ) :
    ccmRestrictedWeilFormBirmanSchwinger a E =
      (E : ℂ) • ccmArchimedeanGammaSlepianGram a -
        ccmRestrictedWeilFormRemainder a := by
  apply ContinuousLinearMap.ext
  intro u
  change (ccmArchimedeanFormToAperture a).adjoint
      ((E : ℂ) • ccmArchimedeanFormToAperture a u -
        ccmRestrictedWeilBoundedRemainder a
          (ccmArchimedeanFormToAperture a u)) = _
  rw [map_sub, map_smul]
  rfl

/-- **Exact all-mode whole-ground balance.** Against every actual Gamma--Slepian eigenmode, the
true restricted-Weil ground equation reduces to a scalar diagonal Gamma factor plus the intact
compressed prime--polar coupling. -/
theorem ccmRestrictedWeilCanonicalGround_gammaSlepian_mode_balance
    (a : SuzukiPositiveAperture) (mu : ℂ)
    (w : ccmGammaSlepianEigenspace a mu) :
    ((1 : ℂ) - (ccmRestrictedWeilGroundEnergy a : ℂ) * mu) *
          inner ℂ (ccmRestrictedWeilCanonicalGroundFormLift a)
            (w : CCMArchimedeanFormDomain a) +
        inner ℂ
          (ccmRestrictedWeilFormRemainder a
            (ccmRestrictedWeilCanonicalGroundFormLift a))
          (w : CCMArchimedeanFormDomain a) = 0 := by
  let u := ccmRestrictedWeilCanonicalGroundFormLift a
  let G := ccmArchimedeanGammaSlepianGram a
  let D := ccmRestrictedWeilFormRemainder a
  let E : ℂ := ccmRestrictedWeilGroundEnergy a
  have hfixed := ccmRestrictedWeilCanonicalGroundFormLift_birmanSchwinger_fixed a
  rw [ccmRestrictedWeilFormBirmanSchwinger_eq_gammaSlepian_sub_remainder] at hfixed
  change E • G u - D u = u at hfixed
  have heig : G (w : CCMArchimedeanFormDomain a) = mu • w :=
    mem_ccmGammaSlepianEigenspace_iff.mp w.property
  have hsym := isSymmetric_ccmArchimedeanGammaSlepianGram a u
    (w : CCMArchimedeanFormDomain a)
  change inner ℂ (G u) w = inner ℂ u (G w) at hsym
  rw [heig, inner_smul_right u (w : CCMArchimedeanFormDomain a) mu] at hsym
  have hp := congrArg
    (fun z : CCMArchimedeanFormDomain a => inner ℂ z w) hfixed
  simp only [inner_sub_left] at hp
  rw [inner_smul_left (G u) w E, Complex.conj_ofReal] at hp
  rw [hsym] at hp
  change ((1 : ℂ) - E * mu) * inner ℂ u w + inner ℂ (D u) w = 0
  linear_combination -hp

end RHTower
