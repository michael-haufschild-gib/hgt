import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.FirstGate.Boundary.GaussianDistinction
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.FirstGate.FirstVisit
import GaloisForLFunctions.HTGeometry.JointHardEventMeasurability

/-! # A rotation on the first spin at every empty-circuit entry -/
open Matrix MeasureTheory Real Filter Topology
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.FirstGate.Boundary
noncomputable section
open EmptyVisitFlux PrecisionReturns Set

/-- At each positive empty-circuit entry a rotation of the same first-site Z
strictly improves the approximation. Its angle and phase work throughout a
neighbourhood of the entry, including a left interval of exact cost one. -/
theorem gaussian_firstZ_entry_window (ε : ℝ) (hε : 0<ε) (hs : ε<sqrt 2) :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ k : ℕ,
      let p := pathPauliDisorderShell ω (k+1)
      let H : selfAdjoint (Register (k+3)) := ⟨pathHamiltonian p,isSelfAdjoint_pathHamiltonian p⟩
      let Z := finitePauliMatrix (pauliZLabel (0:Fin (k+3)))
      let f := fun j => -H.2.isHermitian.eigenvalues j/(2*π)
      ∀ v > (0:ℝ), visitEntry f (SharpOccupation.physicalArc ε) v →
        ∃ θ : ℝ, ∃ z : ℂ, ‖z‖=1 ∧
          (∀ᶠ t in 𝓝 v, ‖unitaryEvolution H.val t-z • unitaryEvolution Z θ‖ < ε) ∧
          ∀ᶠ t in 𝓝[<] v, orbitCircuitDistance H 1 t < ε ∧ ε < orbitCircuitDistance H 0 t := by
  filter_upwards [gaussian_firstZ_distinguishes,gaussian_fixed_contacts (SharpOccupation.physicalArc ε),
    gaussian_path_all_prefixes_maximally_projective,gaussian_one_gate_before_entry ε hε hs] with ω hd hc hg hw k
  intro p H Z f v hv he
  obtain ⟨a,b,hab,hr⟩ := strict_rotation_at_entry p hε hs hv
    (maximallyProjectiveEnergy_neg (hg k)).injective (hc k).1 (hc k).2 he
  let P : selfAdjoint (Register (k+3)) := ⟨Z,finitePauliMatrix_isHermitian _⟩
  obtain ⟨θ,z,hz,herr⟩ := hr P ((hd (k+1)).ne hab)
  have ht : Continuous (fun t : ℝ => unitaryEvolution H.val t) :=
    continuous_unitaryEvolution.comp (continuous_const.prodMk continuous_id)
  refine ⟨θ,z,hz,?_,hw k v hv he⟩
  exact (ht.sub continuous_const).norm.continuousAt.eventually_lt continuousAt_const herr

/-- At physical error 1/10 the first-site Z rotation already works before
the first empty return from the actual near-Hilbert crossing. -/
theorem gaussian_firstZ_first_crossing :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop,
      let N := k+3
      let H : selfAdjoint (Register N) := ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),
        isSelfAdjoint_pathHamiltonian _⟩
      let P := nearHilbertContinuousCircuitBudget N
      let Z := finitePauliMatrix (pauliZLabel (0:Fin N))
      ∃ σ > (0:ℝ), orbitCircuitDistance H P σ=9/80 ∧
        (∀ t ∈ Ico 0 σ, orbitCircuitDistance H P t < 9/80) ∧
        ∃ θ : ℝ, ∃ z : ℂ, ‖z‖=1 ∧ ∃ t ∈ Ioo σ (firstVisit H σ 0 (1/10)),
          ‖unitaryEvolution H.val t-z • unitaryEvolution Z θ‖ < 1/10 ∧
          1/10 < orbitCircuitDistance H 0 t := by
  have hs : (1/10:ℝ)<sqrt 2 := by nlinarith only [sq_sqrt (by norm_num : (0:ℝ)≤2),sqrt_nonneg 2]
  filter_upwards [gaussian_firstZ_entry_window (1/10) (by norm_num) hs,gaussian_first_crossing_one_gate]
    with ω hw hc
  filter_upwards [hc] with k hk
  intro N H P Z
  obtain ⟨σ,hσ,he,hbefore,_⟩ := hk
  have hfar : 1/10 < orbitCircuitDistance H 0 σ := by
    by_contra! h
    obtain ⟨z,hz,C,hC,herr⟩ := (hasProjectiveCircuitApproximation_iff_infDist _ 0 _).mpr h
    have hh := (hasProjectiveCircuitApproximation_iff_infDist _ P (1/10)).mp
      ⟨z,hz,C,hC.trans (Nat.zero_le _),herr⟩
    change orbitCircuitDistance H P σ ≤ 1/10 at hh
    linarith only [he,hh]
  let v := firstVisit H σ 0 (1/10)
  obtain ⟨hav,hentry⟩ := first_empty_entry_of_outside H (by norm_num) hs hfar
  obtain ⟨θ,z,hz,hh,hl⟩ := hw k v (hσ.trans hav) hentry
  have ha : ∀ᶠ t : ℝ in 𝓝[<] v, σ<t := (lt_mem_nhds hav).filter_mono nhdsWithin_le_nhds
  obtain ⟨t,ht,hm,ha',hv⟩ :=
    ((hh.filter_mono nhdsWithin_le_nhds).and (hl.and (ha.and self_mem_nhdsWithin))).exists
  exact ⟨σ,hσ,he,hbefore,θ,z,hz,t,⟨ha',hv⟩,ht,hm.2⟩

#print axioms gaussian_firstZ_entry_window
#print axioms gaussian_firstZ_first_crossing
end
end GaloisForLFunctions.HTGeometry.FirstGate.Boundary
