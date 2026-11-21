import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnLevels.FirstVisits
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.LocalSimulation.CrossingWidth
import Mathlib.MeasureTheory.Measure.Prod

/-! # Choosing the physical tolerance before the Hamiltonian is drawn -/
open MeasureTheory Set Filter Topology
open scoped Matrix.Norms.L2Operator ENNReal NNReal
namespace GaloisForLFunctions.HTGeometry.ReturnLevels
noncomputable section
open PrecisionReturns

private theorem measurable_time_projection {X : Type*} [TopologicalSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X] {Z : Set (X × ℝ)} (hZ : IsClosed Z) :
    MeasurableSet {x : X | ∃ t : ℝ, (x,t) ∈ Z} := by
  let K (m : ℕ) := Icc (-(m:ℝ)) m
  let F (m : ℕ) := {x : X | ∃ t ∈ K m, (x,t) ∈ Z}
  have hF (m : ℕ) : IsClosed (F m) := by
    letI : CompactSpace ↥(K m) := inferInstanceAs (CompactSpace (Icc (-(m:ℝ)) m))
    let S := (fun p : X × ↥(K m) => (p.1,p.2.val)) ⁻¹' Z
    have hs : IsClosed S := hZ.preimage (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
    have he : F m=Prod.fst '' S := by
      ext x
      exact ⟨fun ⟨t,ht,h⟩ => ⟨(x,⟨t,ht⟩),h,rfl⟩,fun ⟨⟨_,t⟩,ht,rfl⟩ => ⟨t.val,t.property,ht⟩⟩
    exact he ▸ isClosedMap_fst_of_compactSpace _ hs
  have he : {x : X | ∃ t : ℝ, (x,t) ∈ Z}=⋃ m, F m := by
    ext x
    constructor
    · rintro ⟨t,ht⟩
      obtain ⟨m,hm⟩ := exists_nat_gt |t|
      exact mem_iUnion.mpr ⟨m,t,abs_le.mp hm.le,ht⟩
    · intro h
      obtain ⟨m,t,_,ht⟩ := mem_iUnion.mp h
      exact ⟨t,ht⟩
  rw [he]
  exact MeasurableSet.iUnion fun m => (hF m).measurableSet

private abbrev chainH (ω : PathPauliDisorder) (n : ℕ) : selfAdjoint (Register (n+2)) :=
  ⟨pathHamiltonian (pathPauliDisorderShell ω n),isSelfAdjoint_pathHamiltonian _⟩

private theorem continuous_chain_distance (n s : ℕ) :
    Continuous (fun p : PathPauliDisorder × ℝ => orbitCircuitDistance (chainH p.1 n) s p.2) := by
  have hH : Continuous (fun ω : PathPauliDisorder => pathHamiltonian (pathPauliDisorderShell ω n)) := by
    simp_rw [pathHamiltonian_eq_sum]
    apply continuous_finset_sum
    intro l _
    cases l with
    | inl i => exact (Complex.continuous_ofReal.comp (continuous_apply _)).smul continuous_const
    | inr i => exact (Complex.continuous_ofReal.comp (continuous_apply _)).smul continuous_const
  exact (Metric.continuous_infDist_pt _).comp
    (continuous_unitaryEvolution.comp ((hH.comp continuous_fst).prodMk continuous_snd))

private theorem measurable_levels_graph (n : ℕ) :
    MeasurableSet {p : PathPauliDisorder × ℝ | p.2 ∈ sharedLevels (pathPauliDisorderShell p.1 n)} := by
  let Z (s : ℕ) := {p : (PathPauliDisorder × ℝ) × ℝ |
    orbitCircuitDistance (chainH p.1.1 n) s p.2=orbitCircuitDistance (chainH p.1.1 n) (s+Fintype.card (PathLabel n)) p.2 ∧
    orbitCircuitDistance (chainH p.1.1 n) s p.2=p.1.2}
  have hf (s : ℕ) : Continuous (fun p : (PathPauliDisorder × ℝ) × ℝ => orbitCircuitDistance (chainH p.1.1 n) s p.2) :=
    (continuous_chain_distance n s).comp ((continuous_fst.comp continuous_fst).prodMk continuous_snd)
  have hc (s : ℕ) : IsClosed (Z s) := (isClosed_eq (hf s) (hf _)).inter (isClosed_eq (hf s) (continuous_snd.comp continuous_fst))
  have he : {p : PathPauliDisorder × ℝ | p.2 ∈ sharedLevels (pathPauliDisorderShell p.1 n)} =
      ⋃ s : ℕ, {p | ∃ t : ℝ, (p,t) ∈ Z s} := by
    ext p
    exact Iff.rfl.trans (by simp only [sharedLevels,mem_setOf_eq,mem_iUnion,mem_image,Z,chainH])
  rw [he]
  exact MeasurableSet.iUnion fun s => measurable_time_projection (hc s)

/-- For almost every deterministic choice of error, the whole Gaussian
chain avoids the exceptional levels almost surely. The choice of error
comes before the draw and works simultaneously on all prefix lengths. -/
theorem gaussian_prescribed_levels :
    ∀ᵐ ε : ℝ ∂volume, ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ n, ε ∉ sharedLevels (pathPauliDisorderShell ω n) := by
  letI : IsProbabilityMeasure pathPauliDisorderLaw := by unfold pathPauliDisorderLaw; infer_instance
  have h (n : ℕ) : ∀ᵐ ε : ℝ ∂volume, ∀ᵐ ω ∂pathPauliDisorderLaw, ε ∉ sharedLevels (pathPauliDisorderShell ω n) := by
    apply (Measure.ae_ae_comm (measurable_levels_graph n).compl).mp
    apply Filter.Eventually.of_forall
    intro ω
    let x := pathPauliDisorderShell ω n
    have hd : dimH (sharedLevels x) < ((1:ℝ≥0):ℝ≥0∞) := (sharedLevels_dimension x).trans_lt (by norm_num)
    have hz := hausdorffMeasure_of_dimH_lt hd
    simpa only [ae_iff,not_not,Set.setOf_mem_eq,NNReal.coe_one,MeasureTheory.hausdorffMeasure_real] using hz
  filter_upwards [ae_all_iff.mpr h] with ε hε
  exact ae_all_iff.mpr hε

#print axioms gaussian_prescribed_levels
end
end GaloisForLFunctions.HTGeometry.ReturnLevels
