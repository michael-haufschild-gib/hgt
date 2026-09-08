import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMFullSourceOverlap

/-!
Compatible closed-cell germs construct a globally smooth modular forcing representing the original lifted L² source.
-/

open MeasureTheory Set Filter Topology UpperHalfPlane ModularGroup
open GaloisForLFunctions.HTGeometry
open scoped MatrixGroups ContDiff
namespace RHTower.D4BMModularCore
open D4BMGlobalAngularResponse
noncomputable section

private theorem exists_cell_element (z : UpperHalfPlane) : ∃ γ : PSL2Z, γ • z ∈ fd := by
  obtain ⟨A,hA⟩ := exists_smul_mem_fd z
  exact ⟨QuotientGroup.mk A,by simpa only [PSL2Z_mk_smul] using hA⟩

private def cellElement (z : UpperHalfPlane) : PSL2Z := (exists_cell_element z).choose

private theorem cellElement_mem (z : UpperHalfPlane) : cellElement z • z ∈ fd :=
  (exists_cell_element z).choose_spec

private def CellCompatible (f : UpperHalfPlane → ℂ) : Prop :=
  ∀ γ : PSL2Z, ∀ z ∈ fd, γ • z ∈ fd → (fun w => f (γ • w)) =ᶠ[𝓝 z] f

private def smoothCellLift (f : UpperHalfPlane → ℂ) (z : UpperHalfPlane) : ℂ :=
  f (cellElement z • z)

private theorem smoothCellLift_eq (f : UpperHalfPlane → ℂ) (hf : CellCompatible f)
    (γ : PSL2Z) (z : UpperHalfPlane) (hγ : γ • z ∈ fd) :
    smoothCellLift f z = f (γ • z) := by
  have hh : (cellElement z * γ⁻¹) • (γ • z) ∈ fd := by
    simpa only [mul_smul,inv_smul_smul] using cellElement_mem z
  have he := (hf (cellElement z * γ⁻¹) (γ • z) hγ hh).eq_of_nhds
  simpa only [mul_smul,inv_smul_smul,smoothCellLift] using he

private theorem smoothCellLift_invariant (f : UpperHalfPlane → ℂ) (hf : CellCompatible f)
    (γ : PSL2Z) (z : UpperHalfPlane) : smoothCellLift f (γ • z) = smoothCellLift f z := by
  have hh : (cellElement z * γ⁻¹) • (γ • z) ∈ fd := by
    simpa only [mul_smul,inv_smul_smul] using cellElement_mem z
  simpa only [mul_smul,inv_smul_smul,smoothCellLift] using
    smoothCellLift_eq f hf (cellElement z * γ⁻¹) (γ • z) hh

private theorem smoothCellLift_germ (f : UpperHalfPlane → ℂ) (hf : CellCompatible f)
    (z : UpperHalfPlane) (hz : z ∈ fd) : smoothCellLift f =ᶠ[𝓝 z] f := by
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

private theorem smoothCellLift_smooth (f : UpperHalfPlane → ℂ) (hf : CellCompatible f)
    (hs : ChartSmooth f) : ChartSmooth (smoothCellLift f) := by
  intro z
  let γ := cellElement z
  have he := smoothCellLift_germ f hf (γ • z) (cellElement_mem z)
  have hp : smoothCellLift f =ᶠ[𝓝 z] (fun w => f (γ • w)) := by
    have ht := (continuous_const_smul γ).continuousAt.eventually he
    filter_upwards [ht] with w hw
    simpa only [smoothCellLift_invariant f hf γ w] using hw
  have hc := (UpperHalfPlane.contMDiffAt_ofComplex (n := 0) z.im_pos).continuousAt
  have hpc : smoothCellLift f ∘ ofComplex =ᶠ[𝓝 (z:ℂ)] (fun w => f (γ • ofComplex w)) := by
    change ∀ᶠ w in 𝓝 (z:ℂ), smoothCellLift f (ofComplex w) = f (γ • ofComplex w)
    apply hc.eventually (p := fun w => smoothCellLift f w = f (γ • w))
    rw [ofComplex_apply]
    filter_upwards [hp] with w hw
    exact hw
  exact (hs.modular_pullback γ z).congr_of_eventuallyEq hpc

private theorem forcing_compatible (q : XiZeroCopy) (branch : Bool) :
    CellCompatible (fun z => forcing q branch (coordinates z)) := by
  intro γ z hz hγ
  induction γ using QuotientGroup.induction_on with
  | H A =>
    simp only [PSL2Z_mk_smul] at hγ ⊢
    exact forcing_cell_overlap_germ q branch A z hz hγ

/-- The actual forcing glued by its compatible closed-cell germs, including every seam point. -/
def globalForcing (q : XiZeroCopy) (branch : Bool) : UpperHalfPlane → ℂ :=
  smoothCellLift (fun z => forcing q branch (coordinates z))

/-- The glued source equals the literal full forcing at every point of the closed cell. -/
theorem globalForcing_eq_on_fd (q : XiZeroCopy) (branch : Bool) (z : UpperHalfPlane)
    (hz : z ∈ fd) : globalForcing q branch z = forcing q branch (coordinates z) := by
  simpa only [one_smul,globalForcing] using
    smoothCellLift_eq _ (forcing_compatible q branch) 1 z (by simpa using hz)

/-- The globally glued original forcing is pointwise modular invariant. -/
theorem globalForcing_invariant (q : XiZeroCopy) (branch : Bool) (γ : PSL2Z)
    (z : UpperHalfPlane) : globalForcing q branch (γ • z) = globalForcing q branch z :=
  smoothCellLift_invariant _ (forcing_compatible q branch) γ z

/-- The actual full forcing is globally smooth in every positive-height chart. -/
theorem globalForcing_smooth (q : XiZeroCopy) (branch : Bool) :
    ChartSmooth (globalForcing q branch) :=
  smoothCellLift_smooth _ (forcing_compatible q branch) (forcing_chartSmooth q branch)

private theorem invariant_ae_eq_of_native {f g : UpperHalfPlane → ℂ}
    (hf : ∀ γ : PSL2Z, ∀ z, f (γ • z) = f z)
    (hg : ∀ γ : PSL2Z, ∀ z, g (γ • z) = g z) (he : f =ᵐ[measure] g) :
    f =ᵐ[(volume : Measure UpperHalfPlane)] g := by
  have hn : ∀ᵐ z : UpperHalfPlane ∂volume, z ∈ fd → f z = g z :=
    (ae_restrict_iff' isClosed_fd.measurableSet).mp he
  have ht (γ : PSL2Z) : ∀ᵐ z : UpperHalfPlane ∂volume, γ • z ∈ fd → f z = g z := by
    have hh := (measurePreserving_smul γ (volume : Measure UpperHalfPlane)).quasiMeasurePreserving.ae hn
    filter_upwards [hh] with z hz hmem
    simpa only [hf γ z,hg γ z] using hz hmem
  have hall : ∀ᵐ z : UpperHalfPlane ∂volume, ∀ γ : PSL2Z, γ • z ∈ fd → f z = g z :=
    ae_all_iff.mpr ht
  filter_upwards [hall] with z hz
  exact hz (cellElement z) (cellElement_mem z)

/-- The globally smooth source is the actual modular lift of the original native L² forcing vector. -/
theorem globalForcing_ae_lift (q : XiZeroCopy) (branch : Bool) :
    globalForcing q branch =ᵐ[(volume : Measure UpperHalfPlane)]
      globalLift (forcingVector q branch) := by
  apply invariant_ae_eq_of_native (globalForcing_invariant q branch)
    (globalLift_invariant (forcingVector q branch))
  filter_upwards [ae_mem_interior,forcingVector_coe q branch,
    globalLift_ae_eq (forcingVector q branch)] with z hz hF hL
  rw [globalForcing_eq_on_fd q branch z (fdo_subset_fd hz),hL,hF]

end
end RHTower.D4BMModularCore
