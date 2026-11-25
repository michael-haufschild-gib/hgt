import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.BoundaryField.NestedPrefixes.JointDates.Candidates

/-! # Joint absolute continuity of genuine scalar entry dates on nested prefixes -/

open MeasureTheory Set Real
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpectralJets.BoundaryField.NestedPrefixes.JointDates
open PrecisionReturns
noncomputable section

/-- A planar null set misses every pair of genuine first scalar entry dates
on the two registers, even for observation origins selected with joint access
to both Hamiltonians. -/
theorem gaussian_joint_entry_dates {j k : ℕ} (hjk : j<k) {e f : ℝ}
    (he : e∈Ioo (0:ℝ) (sqrt 2)) (hf : f∈Ioo (0:ℝ) (sqrt 2))
    (S : Set (ℝ × ℝ)) (hm : MeasurableSet S) (hn : volume S=0) :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ a b : ℝ, 0<a → 0<b →
      e<orbitCircuitDistance (generator j ω) 0 a → f<orbitCircuitDistance (generator k ω) 0 b →
      (firstVisit (generator j ω) a 0 e,firstVisit (generator k ω) b 0 f)∉S := by
  let U := {t : ℝ | volume (Prod.mk t ⁻¹' S)≠0}
  have hmU : MeasurableSet U := (measurableSet_eq_fun (measurable_measure_prodMk_left hm)
    measurable_const).compl
  have hU : volume U=0 := measure_eq_zero_iff_ae_notMem.mpr
    ((Measure.measure_prod_null hm).mp hn |>.mono fun _ h => not_not_intro h)
  let B (g : PathPauliDisorder → ℝ) := {p : PathPauliDisorder × ℝ | g p.1∉U ∧ (g p.1,p.2)∈S}
  have hb {g : PathPauliDisorder → ℝ} (hg : Measurable g) : MeasurableSet (B g) :=
    ((hmU.preimage (hg.comp measurable_fst)).compl).inter (hm.preimage ((hg.comp measurable_fst).prodMk measurable_snd))
  have hz (g : PathPauliDisorder → ℝ) (η : PathPauliDisorder) : volume (Prod.mk η ⁻¹' B g)=0 := by
    by_cases h : g η∈U
    · have hzero : Prod.mk η ⁻¹' B g=∅ := eq_empty_iff_forall_notMem.mpr fun _ ht => ht.1 h
      rw [hzero,measure_empty]
    · exact measure_mono_null (fun _ ht => ht.2) (not_not.mp h : volume (Prod.mk (g η) ⁻¹' S)=0)
  have h1 := gaussian_conditional_entries j he (Prod.snd ⁻¹' U) (hmU.preimage measurable_snd) (fun _ => hU)
  have h2 (n : ℤ) (m : Config j → ℤ) := gaussian_conditional_entries k hf (B (candidate j e n m))
    (hb (measurable_candidate j e n m)) (hz _)
  filter_upwards [h1,ae_all_iff.mpr (fun n => ae_all_iff.mpr (h2 n))] with ω hsmall hlarge
  intro a b ha hb' hA hB hbad
  obtain ⟨n,m,hc⟩ := entry_candidate j ω ha he hA
  have h := hlarge n m b hb' hB
  change ¬ (candidate j e n m (eraseTerminal k ω)∉U ∧
    (candidate j e n m (eraseTerminal k ω),firstVisit (generator k ω) b 0 f)∈S) at h
  rw [candidate_before hjk,hc] at h
  exact h ⟨hsmall a ha hA,hbad⟩

#print axioms gaussian_joint_entry_dates
end
end GaloisForLFunctions.HTGeometry.SpectralJets.BoundaryField.NestedPrefixes.JointDates
