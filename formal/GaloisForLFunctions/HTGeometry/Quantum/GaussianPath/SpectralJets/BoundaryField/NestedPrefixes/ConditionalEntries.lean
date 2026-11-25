import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.BoundaryField.NestedPrefixes.ConditionalLaw
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.BoundaryField.FirstReturnDates

/-! # Conditional law of actual scalar entry dates on an unmodified chain -/

open Set MeasureTheory Real Filter
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpectralJets.BoundaryField.NestedPrefixes
open PrecisionReturns
noncomputable section

/-- Reciprocal scaling sends a null family of positive dates to a null
family of nonzero spectral actions. Its graph is expressed by the inverse
map so that joint measurability is retained. -/
private theorem reciprocal_section (S : Set (PathPauliDisorder × ℝ)) (η : PathPauliDisorder)
    (hS : volume (Prod.mk η ⁻¹' S)=0) {c : ℝ} (hc : c≠0) :
    volume {u : ℝ | u≠0 ∧ (η,c/u)∈S}=0 := by
  let V := Prod.mk η ⁻¹' S ∩ ({0}:Set ℝ)ᶜ
  have hz : volume V=0 := measure_mono_null inter_subset_left hS
  have hi : volume ((fun t : ℝ => c/t) '' V)=0 := by
    apply addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume _ hz
    intro t ht
    have ht₀ : t≠0 := ht.2
    apply DifferentiableAt.differentiableWithinAt
    fun_prop (disch := exact ht₀)
  apply measure_mono_null _ hi
  intro u hu
  exact ⟨c/u,⟨hu.2,div_ne_zero hc hu.1⟩,by field_simp⟩

/-- All genuine scalar entries on this register avoid every prescribed
measurable null family based on all remaining couplings. The exterior
origin may be chosen using the complete Hamiltonian. -/
theorem gaussian_conditional_entries (k : ℕ) {ε : ℝ} (he : ε∈Ioo (0:ℝ) (sqrt 2))
    (S : Set (PathPauliDisorder × ℝ)) (hm : MeasurableSet S)
    (hS : ∀ η : PathPauliDisorder, volume (Prod.mk η ⁻¹' S)=0) :
    ∀ᵐ ω ∂pathPauliDisorderLaw,
      let H : selfAdjoint (Matrix (Config k) (Config k) ℂ) := ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),
        isSelfAdjoint_pathHamiltonian _⟩
      ∀ a : ℝ, 0<a → ε<orbitCircuitDistance H 0 a →
        (eraseTerminal k ω,firstVisit H a 0 ε)∉S := by
  let c (n : ℤ) := (2*π)*((n:ℝ)+SharpOccupation.physicalArc ε)
  have hx := (SharpOccupation.physicalArc_spec he.1 he.2).1
  have hn (n : ℤ) : c n≠0 := by
    apply mul_ne_zero (mul_ne_zero (by norm_num) pi_ne_zero)
    by_cases hp : 0≤n
    · exact (add_pos_of_nonneg_of_pos (by exact_mod_cast hp : (0:ℝ)≤n) hx.1).ne'
    · have hu : (n:ℝ)≤-1 := by exact_mod_cast (show n≤-1 by omega)
      linarith only [hu,hx.2]
  let B (n : ℤ) := {p : PathPauliDisorder × ℝ | p.2≠0 ∧ (p.1,c n/p.2)∈S}
  have hb (n : ℤ) : MeasurableSet (B n) :=
    (measurableSet_eq_fun measurable_snd measurable_const).compl.inter
      (hm.preimage (measurable_fst.prodMk (measurable_const.div measurable_snd)))
  have hnull (n : ℤ) (η : PathPauliDisorder) : volume (Prod.mk η ⁻¹' B n)=0 :=
    reciprocal_section S η (hS η) (hn n)
  filter_upwards [ae_all_iff.mpr (fun n => gaussian_native_null k (B n) (hb n) (hnull n))] with ω hω
  intro H a ha hfar hbad
  obtain ⟨hv,m,n,hm',hbal,hw⟩ := first_entry_action H ha he.1 he.2 hfar
  let v := firstVisit H a 0 ε
  have heq : (∑ i, (m i:ℝ)*H.2.isHermitian.eigenvalues i)=c n/v := hw
  apply hω n m hm' hbal
  change (∑ i, (m i:ℝ)*H.2.isHermitian.eigenvalues i)≠0 ∧
    (eraseTerminal k ω,c n/(∑ i, (m i:ℝ)*H.2.isHermitian.eigenvalues i))∈S
  rw [heq]
  refine ⟨div_ne_zero (hn n) hv.ne',?_⟩
  rwa [show c n/(c n/v)=v by field_simp [hn n,hv.ne']]

#print axioms gaussian_conditional_entries
end
end GaloisForLFunctions.HTGeometry.SpectralJets.BoundaryField.NestedPrefixes
