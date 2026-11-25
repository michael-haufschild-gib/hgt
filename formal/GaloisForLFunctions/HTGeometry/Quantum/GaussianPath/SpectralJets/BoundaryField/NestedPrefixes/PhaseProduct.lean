import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.BoundaryField.NestedPrefixes.JointActions
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.BoundaryField.JointHaar

/-! # Joint Haar law of all nested phase packets on one laboratory clock -/

open MeasureTheory Filter Topology
namespace GaloisForLFunctions.HTGeometry.SpectralJets.BoundaryField.NestedPrefixes
noncomputable section

/-- The physical frequencies from the first n registers of at least three
spins share one time parameter and have no joint integer resonance. -/
theorem gaussian_nested_phase_product :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ (n : ℕ) (r : (j : Fin n) → Config j.val),
      let E (j : Fin n) := (isSelfAdjoint_pathHamiltonian (pathPauliDisorderShell ω (j.val+1))).isHermitian.eigenvalues
      let f (a : (j : Fin n) × {i : Config j.val // i≠r j}) :=
        projectiveFrequency (fun i => -E a.1 i) (r a.1) a.2
      RationallyIndependentFrequency f ∧
        Tendsto (clockPhaseWindowLaw f) atTop (𝓝 (finiteTorusHaarProbabilityMeasure _)) := by
  classical
  filter_upwards [gaussian_nested_actions] with ω hω
  intro n r E f
  suffices h : RationallyIndependentFrequency f from ⟨h,clockPhaseWindowLaw_tendsto_haar f h⟩
  intro m hm
  choose b hsort using fun j : Fin n => ordered_at_zero j.val ω
  let c (j : Fin n) := liftPacket (r j) (fun i => m ⟨j,i⟩)
  let q (j : Fin n) (i : Config j.val) := -c j (b j i)
  have hb (j : Fin n) : (∑ i, q j i)=0 := by
    change (∑ i, -c j (b j i))=0
    rw [Finset.sum_neg_distrib,Equiv.sum_comp (b j) (c j),lift_sum,neg_zero]
  have hA (j : Fin n) : action j.val (q j) ω =
      ∑ i, (m ⟨j,i⟩:ℝ)*projectiveFrequency (fun a => -E j a) (r j) i := by
    unfold action
    rw [hsort j]
    calc
      _ = ∑ i, (c j (b j i):ℝ)*(-E j (b j i)) := by
        apply Finset.sum_congr rfl
        intro i _
        simp only [q,Int.cast_neg,neg_mul,mul_neg,E,Function.comp_apply]
      _ = ∑ i, (c j i:ℝ)*(-E j i) := Equiv.sum_comp (b j) _
      _ = _ := lift_energy (r j) _ (fun i => -E j i)
  have hzero : (∑ j, action j.val (q j) ω)=0 := by
    simpa only [hA,finiteTorusCharacterDetuning,Fintype.sum_sigma,f] using hm
  have hq := hω n q hb hzero
  funext a
  obtain ⟨j,i⟩ := a
  have h := congrFun (hq j) ((b j).symm i.val)
  simpa only [q,c,Equiv.apply_symm_apply,lift_off_anchor,Pi.zero_apply,neg_eq_zero] using h

#print axioms gaussian_nested_phase_product
end
end GaloisForLFunctions.HTGeometry.SpectralJets.BoundaryField.NestedPrefixes
