import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.FirstGate.PhysicalDescent
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.FirstGate.GaussianContacts
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrecisionReturns.FirstVisit
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.LocalSimulation.CrossingWidth
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.EmptyVisitFlux.GaussianLaw

/-! # The first affordable one-gate return precedes the first scalar return -/
open Matrix MeasureTheory Real Filter Topology Set
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.FirstGate
noncomputable section
open PrecisionReturns EmptyVisitFlux

/-- At any positive origin outside the scalar tube, its next entry admits
a strictly earlier one-gate visit at the same physical accuracy. The
statement holds simultaneously for every origin on the entire chain. -/
theorem gaussian_first_one_gate_window (ε : ℝ) (hε : 0 < ε) (hs : ε < sqrt 2) :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ k : ℕ,
      let p := pathPauliDisorderShell ω (k+1)
      let N := k+3
      let H : selfAdjoint (Register N) := ⟨pathHamiltonian p,isSelfAdjoint_pathHamiltonian p⟩
      ∀ A > (0:ℝ), ε < orbitCircuitDistance H 0 A →
        ∃ t ∈ Ioo A (firstVisit H A 0 ε), orbitCircuitDistance H 1 t < ε ∧ ε < orbitCircuitDistance H 0 t := by
  filter_upwards [gaussian_fixed_contacts (SharpOccupation.physicalArc ε),gaussian_path_all_prefixes_maximally_projective] with ω hc hg k
  intro p N H A hA hfar
  let E := fun j => -H.2.isHermitian.eigenvalues j
  let f := fun j => E j/(2*π)
  let x := SharpOccupation.physicalArc ε
  let v := firstVisit H A 0 ε
  have hleast := firstVisit_isLeast H A 0 hε
  have hAv : A < v := hleast.1.1.lt_of_ne (by
    intro h
    have hv := (hasProjectiveCircuitApproximation_iff_infDist _ 0 ε).mp hleast.1.2
    change orbitCircuitDistance H 0 v ≤ ε at hv
    exact (h ▸ hfar : ε < orbitCircuitDistance H 0 v).not_ge hv)
  have hentry : visitEntry f x v := by
    refine ⟨(physical_visit H hε hs v).mpr hleast.1.2,v-A,sub_pos.mpr hAv,?_⟩
    intro t hh ht
    have htA : A ≤ t := by linarith only [hh.1]
    exact hh.2.not_ge (hleast.2 ⟨htA,(physical_visit H hε hs t).mp ht⟩)
  obtain ⟨z,hz,C,hC,he⟩ := strict_gate_at_entry p hε hs (hA.trans hAv)
    (maximallyProjectiveEnergy_neg (hg k)).injective (hc k).1 (hc k).2 hentry
  let err := ‖unitaryEvolution H.val v-z • (C.eval : Register N)‖
  have hnear : orbitCircuitDistance H 1 v < ε :=
    ((hasProjectiveCircuitApproximation_iff_infDist _ 1 err).mp ⟨z,hz,C,hC.le,le_rfl⟩).trans_lt he
  have hopen := ((orbitCircuitDistance_lipschitz H 1).continuous.continuousAt.eventually_lt continuousAt_const hnear).filter_mono
    (nhdsWithin_le_nhds : 𝓝[<] v ≤ 𝓝 v)
  have hstart : ∀ᶠ t : ℝ in 𝓝[<] v, A < t := (lt_mem_nhds hAv).filter_mono nhdsWithin_le_nhds
  obtain ⟨t,ht,ha,hv⟩ := (hopen.and (hstart.and self_mem_nhdsWithin)).exists
  refine ⟨t,⟨ha,hv⟩,ht,lt_of_not_ge ?_⟩
  intro h
  exact (show t < v from hv).not_ge (hleast.2 ⟨ha.le,(hasProjectiveCircuitApproximation_iff_infDist _ 0 ε).mpr h⟩)

/-- From the actual first near-Hilbert crossing on every sufficiently
long prefix, one gate returns strictly before the empty circuit at 1/10. -/
theorem gaussian_first_crossing_one_gate :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop,
      let N := k+3
      let H : selfAdjoint (Register N) := ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),isSelfAdjoint_pathHamiltonian _⟩
      let P := nearHilbertContinuousCircuitBudget N
      ∃ σ > (0:ℝ), orbitCircuitDistance H P σ=9/80 ∧
        (∀ t ∈ Ico 0 σ, orbitCircuitDistance H P t < 9/80) ∧
        firstVisit H σ 1 (1/10) < firstVisit H σ 0 (1/10) := by
  have hs : (1/10:ℝ)<sqrt 2 := by nlinarith only [sq_sqrt (by norm_num : (0:ℝ)≤2),sqrt_nonneg 2]
  filter_upwards [gaussian_first_one_gate_window (1/10) (by norm_num) hs,
    LocalPatches.gaussian_first_crossing_local_width] with ω hone hcross
  filter_upwards [hcross] with k hk
  intro N H P
  obtain ⟨σ,hσ,he,hbefore,hafter⟩ := hk
  have hwidth : 0 ≤ LocalPatches.localCrossingWidth N := by unfold LocalPatches.localCrossingWidth; positivity
  have hpos := hwidth.trans_lt hσ
  have hfar : 1/10 < orbitCircuitDistance H 0 σ := by
    by_contra! h
    have hscalar := (hasProjectiveCircuitApproximation_iff_infDist _ 0 (1/10:ℝ)).mpr h
    obtain ⟨v,hv,hleast⟩ := hafter 0 (Nat.zero_le _)
    have hv' : v≤σ := hleast.2 ⟨le_rfl,hscalar⟩
    linarith only [hv,hv',hwidth]
  obtain ⟨t,ht,hcheap,_⟩ := hone k σ hpos hfar
  exact ⟨σ,hpos,he,hbefore,((firstVisit_isLeast H σ 1 (by norm_num : 0 < (1/10:ℝ))).2
    ⟨ht.1.le,(hasProjectiveCircuitApproximation_iff_infDist _ 1 _).mpr hcheap.le⟩).trans_lt ht.2⟩

#print axioms gaussian_first_one_gate_window
#print axioms gaussian_first_crossing_one_gate
end
end GaloisForLFunctions.HTGeometry.FirstGate
