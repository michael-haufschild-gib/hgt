import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMFullSourceOverlap

/-!
Compatible germs on the closed modular cell extend to an actual globally smooth invariant field. Proper discontinuity controls all nearby cell representatives, including elliptic corners.
-/

open MeasureTheory Set Filter Topology UpperHalfPlane ModularGroup
open GaloisForLFunctions.HTGeometry
open scoped MatrixGroups ContDiff
namespace RHTower.D4BMModularCore
noncomputable section

private theorem exists_cell_element (z : UpperHalfPlane) : ∃ γ : PSL2Z, γ • z ∈ fd := by
  obtain ⟨A,hA⟩ := exists_smul_mem_fd z
  exact ⟨QuotientGroup.mk A,by simpa only [PSL2Z_mk_smul] using hA⟩

private def cellElement (z : UpperHalfPlane) : PSL2Z := (exists_cell_element z).choose

private theorem cellElement_mem (z : UpperHalfPlane) : cellElement z • z ∈ fd :=
  (exists_cell_element z).choose_spec

/-- Compatibility of full function germs at every closed-cell modular overlap. -/
def CellGermCompatible (f : UpperHalfPlane → ℂ) : Prop :=
  ∀ γ : PSL2Z, ∀ z ∈ fd, γ • z ∈ fd → (fun w => f (γ • w)) =ᶠ[𝓝 z] f

/-- The extension obtained by evaluating a chosen closed-cell orbit representative. -/
def cellGermExtension (f : UpperHalfPlane → ℂ) (z : UpperHalfPlane) : ℂ :=
  f (cellElement z • z)

/-- Every admissible closed-cell representative gives the same extension value. -/
theorem cellGermExtension_eq (f : UpperHalfPlane → ℂ) (hf : CellGermCompatible f)
    (γ : PSL2Z) (z : UpperHalfPlane) (hγ : γ • z ∈ fd) :
    cellGermExtension f z = f (γ • z) := by
  have hh : (cellElement z * γ⁻¹) • (γ • z) ∈ fd := by
    simpa only [mul_smul,inv_smul_smul] using cellElement_mem z
  have he := (hf (cellElement z * γ⁻¹) (γ • z) hγ hh).eq_of_nhds
  simpa only [mul_smul,inv_smul_smul,cellGermExtension] using he

/-- Compatible cell germs give a pointwise modular-invariant extension. -/
theorem cellGermExtension_invariant (f : UpperHalfPlane → ℂ) (hf : CellGermCompatible f)
    (γ : PSL2Z) (z : UpperHalfPlane) : cellGermExtension f (γ • z) = cellGermExtension f z := by
  have hh : (cellElement z * γ⁻¹) • (γ • z) ∈ fd := by
    simpa only [mul_smul,inv_smul_smul] using cellElement_mem z
  simpa only [mul_smul,inv_smul_smul,cellGermExtension] using
    cellGermExtension_eq f hf (cellElement z * γ⁻¹) (γ • z) hh

/-- The extension retains the entire original function germ at every closed-cell point. -/
theorem cellGermExtension_germ (f : UpperHalfPlane → ℂ) (hf : CellGermCompatible f)
    (z : UpperHalfPlane) (hz : z ∈ fd) : cellGermExtension f =ᶠ[𝓝 z] f := by
  classical
  obtain ⟨K,hK,hKz⟩ := exists_compact_mem_nhds z
  obtain ⟨s,hs⟩ := compact_cell_pullbacks_finite K hK
  have he (γ : PSL2Z) : ∀ᶠ w in 𝓝 z, γ • w ∈ fd → f (γ • w) = f w := by
    by_cases hγ : γ • z ∈ fd
    · filter_upwards [hf γ z hz hγ] with w hw
      exact fun _ => hw
    · have ho : ∀ᶠ w in 𝓝 z, γ • w ∉ fd :=
        (isClosed_fd.isOpen_compl.preimage (continuous_const_smul γ)).mem_nhds hγ
      filter_upwards [ho] with w hw
      exact fun hc => (hw hc).elim
  have hall : ∀ᶠ w in 𝓝 z, ∀ γ ∈ s, γ • w ∈ fd → f (γ • w) = f w :=
    (Filter.eventually_all_finset s).mpr (fun γ _ => he γ)
  filter_upwards [hKz,hall] with w hw hlocal
  have hm : cellElement w ∈ s := by
    by_contra hn
    exact hs (cellElement w) hn w hw (cellElement_mem w)
  exact hlocal (cellElement w) hm (cellElement_mem w)

/-- Compatible smooth cell germs extend smoothly across all modular seams and elliptic points. -/
theorem cellGermExtension_smooth (f : UpperHalfPlane → ℂ) (hf : CellGermCompatible f)
    (hs : ChartSmooth f) : ChartSmooth (cellGermExtension f) := by
  intro z
  let γ := cellElement z
  have he := cellGermExtension_germ f hf (γ • z) (cellElement_mem z)
  have hp : cellGermExtension f =ᶠ[𝓝 z] (fun w => f (γ • w)) := by
    have ht := (continuous_const_smul γ).continuousAt.eventually he
    filter_upwards [ht] with w hw
    simpa only [cellGermExtension_invariant f hf γ w] using hw
  have hc := (UpperHalfPlane.contMDiffAt_ofComplex (n := 0) z.im_pos).continuousAt
  have hpc : cellGermExtension f ∘ ofComplex =ᶠ[𝓝 (z:ℂ)] (fun w => f (γ • ofComplex w)) := by
    change ∀ᶠ w in 𝓝 (z:ℂ), cellGermExtension f (ofComplex w) = f (γ • ofComplex w)
    apply hc.eventually (p := fun w => cellGermExtension f w = f (γ • w))
    rw [ofComplex_apply]
    filter_upwards [hp] with w hw
    exact hw
  exact (hs.modular_pullback γ z).congr_of_eventuallyEq hpc

end
end RHTower.D4BMModularCore
