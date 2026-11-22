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

/-- Immediately before every positive scalar entry the exact minimum
gate count is one, at the same physical tolerance as the scalar entry. -/
theorem gaussian_one_gate_before_entry (ε : ℝ) (hε : 0 < ε) (hs : ε < sqrt 2) :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ k : ℕ,
      let p := pathPauliDisorderShell ω (k+1)
      let H : selfAdjoint (Register (k+3)) := ⟨pathHamiltonian p,isSelfAdjoint_pathHamiltonian p⟩
      let f := fun j => -H.2.isHermitian.eigenvalues j/(2*π)
      ∀ v > (0:ℝ), visitEntry f (SharpOccupation.physicalArc ε) v →
        ∀ᶠ t : ℝ in 𝓝[<] v, orbitCircuitDistance H 1 t < ε ∧ ε < orbitCircuitDistance H 0 t := by
  filter_upwards [gaussian_fixed_contacts (SharpOccupation.physicalArc ε),
    gaussian_path_all_prefixes_maximally_projective] with ω hc hg k
  intro p H f v hv he
  obtain ⟨z,hz,C,hC,hd⟩ := strict_gate_at_entry p hε hs hv
    (maximallyProjectiveEnergy_neg (hg k)).injective (hc k).1 (hc k).2 he
  let err := ‖unitaryEvolution H.val v-z • (C.eval : Register (k+3))‖
  have hnear : orbitCircuitDistance H 1 v < ε :=
    ((hasProjectiveCircuitApproximation_iff_infDist _ 1 err).mp ⟨z,hz,C,hC.le,le_rfl⟩).trans_lt hd
  obtain ⟨_,δ,hδ,hgap⟩ := he
  have h1 : ∀ᶠ t : ℝ in 𝓝[<] v, orbitCircuitDistance H 1 t < ε :=
    ((orbitCircuitDistance_lipschitz H 1).continuous.continuousAt.eventually_lt continuousAt_const hnear).filter_mono
      nhdsWithin_le_nhds
  have hleft : ∀ᶠ t : ℝ in 𝓝[<] v, v-δ < t := (lt_mem_nhds (sub_lt_self v hδ)).filter_mono nhdsWithin_le_nhds
  filter_upwards [h1,hleft,self_mem_nhdsWithin] with t ht hlo hhi
  refine ⟨ht,lt_of_not_ge fun h => hgap t ⟨hlo,hhi⟩ ?_⟩
  exact (physical_visit H hε hs t).mpr ((hasProjectiveCircuitApproximation_iff_infDist _ 0 _).mpr h)

/-- The first empty visit following an outside time is an incoming scalar
entry, with the whole interval from that time to the visit outside. -/
theorem first_empty_entry_of_outside {N : ℕ} (H : selfAdjoint (Register N)) {A ε : ℝ}
    (hε : 0 < ε) (hs : ε < sqrt 2) (hfar : ε < orbitCircuitDistance H 0 A) :
    let v := firstVisit H A 0 ε
    A < v ∧ visitEntry (fun j => -H.2.isHermitian.eigenvalues j/(2*π))
      (SharpOccupation.physicalArc ε) v := by
  intro v
  have hleast := firstVisit_isLeast H A 0 hε
  have hAv : A < v := hleast.1.1.lt_of_ne (by
    intro h
    have hv := (hasProjectiveCircuitApproximation_iff_infDist _ 0 ε).mp hleast.1.2
    change orbitCircuitDistance H 0 v ≤ ε at hv
    exact hfar.not_ge ((congrArg (orbitCircuitDistance H 0) h).le.trans hv))
  refine ⟨hAv,?_⟩
  refine ⟨(physical_visit H hε hs v).mpr hleast.1.2,v-A,sub_pos.mpr hAv,?_⟩
  intro t hh ht
  have htA : A ≤ t := by linarith only [hh.1]
  exact hh.2.not_ge (hleast.2 ⟨htA,(physical_visit H hε hs t).mp ht⟩)

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
  filter_upwards [gaussian_one_gate_before_entry ε hε hs] with ω hentryWindow k
  intro p N H A hA hfar
  let v := firstVisit H A 0 ε
  obtain ⟨hAv,hentry⟩ := first_empty_entry_of_outside H hε hs hfar
  have hopen := hentryWindow k v (hA.trans hAv) hentry
  have hstart : ∀ᶠ t : ℝ in 𝓝[<] v, A < t := (lt_mem_nhds hAv).filter_mono nhdsWithin_le_nhds
  obtain ⟨t,ht,ha,hv⟩ := (hopen.and (hstart.and self_mem_nhdsWithin)).exists
  exact ⟨t,⟨ha,hv⟩,ht⟩

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

#print axioms gaussian_one_gate_before_entry
#print axioms gaussian_first_one_gate_window
#print axioms gaussian_first_crossing_one_gate
end
end GaloisForLFunctions.HTGeometry.FirstGate
