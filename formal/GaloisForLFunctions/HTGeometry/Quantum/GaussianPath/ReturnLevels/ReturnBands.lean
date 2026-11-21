import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnLevels.CrossingVisits
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.FirstGate.Occupation

/-! # Positive occupation in each gate-count band on the return from the first crossing -/
open Set Filter MeasureTheory Topology
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.ReturnLevels
noncomputable section
open PrecisionReturns

/-- Just before the genuine return to each gate budget, the cost lies
in the next one-sweep band on a whole interval. Each of these bands
also has positive lower time density from every fixed observation origin. -/
theorem gaussian_return_bands :
    ∀ᵐ ε : ℝ ∂volume, ε ∈ Ioo (0:ℝ) (9/80) →
      ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop,
        let x := pathPauliDisorderShell ω (k+1)
        let N := k+3
        let H : selfAdjoint (Register N) := ⟨pathHamiltonian x,isSelfAdjoint_pathHamiltonian x⟩
        let P := nearHilbertContinuousCircuitBudget N
        let J := Fintype.card (PathLabel (k+1))
        ∃ σ > (0:ℝ), orbitCircuitDistance H P σ=9/80 ∧
          (∀ t ∈ Ico 0 σ, orbitCircuitDistance H P t < 9/80) ∧
          ∀ s ≤ P, let v := firstVisit H σ s ε
            (∃ a ∈ Ico σ v, ∀ u ∈ Ioo a v,
              orbitCircuitDistance H (s+J) u < ε ∧ ε < orbitCircuitDistance H s u) ∧
            ∃ c > (0:ℝ), ∀ A : ℝ, ∀ᶠ T : ℝ in atTop,
              c < volume.real ((SharpOccupation.visitSet H (s+J) ε \
                SharpOccupation.visitSet H s ε) ∩ Icc A T)/(T-A) := by
  filter_upwards [gaussian_crossing_first_visit_order,gaussian_prescribed_levels] with ε hcross hreg ht
  filter_upwards [hcross ht,hreg,gaussian_path_all_prefixes_maximally_projective] with ω hc hr hg
  filter_upwards [hc] with k hk
  intro x N H P J
  obtain ⟨σ,hσ,he,hbefore,horder⟩ := hk
  refine ⟨σ,hσ,he,hbefore,?_⟩
  intro s hs v
  have hv := firstVisit_isLeast H σ s ht.1
  have hσv : σ<v := (firstVisit_isLeast H σ (s+J) ht.1).1.1.trans_lt (horder s hs)
  have hd : orbitCircuitDistance H s v ≤ ε := (hasProjectiveCircuitApproximation_iff_infDist _ s ε).mp hv.1.2
  have hle : orbitCircuitDistance H (s+J) v ≤ orbitCircuitDistance H s v := by
    simpa only [sub_self,abs_zero,zero_pow (by decide : 2≠0),mul_zero,add_zero] using path_increment x s v v
  have hlt : orbitCircuitDistance H (s+J) v < ε := (hle.trans hd).lt_of_ne fun eq =>
    let h := le_antisymm hd (eq.ge.trans hle)
    hr (k+1) (mem_iUnion.mpr ⟨s,v,h.trans eq.symm,h⟩)
  have hh : ∀ᶠ u : ℝ in 𝓝[<] v, orbitCircuitDistance H (s+J) u < ε ∧ ε < orbitCircuitDistance H s u := by
    have hhigh := (orbitCircuitDistance_lipschitz H (s+J)).continuous.continuousAt.eventually_lt continuousAt_const hlt
    filter_upwards [hhigh.filter_mono nhdsWithin_le_nhds,(lt_mem_nhds hσv).filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with u hu hlu huv
    refine ⟨hu,lt_of_not_ge fun ha => huv.not_ge (hv.2 ⟨hlu.le,?_⟩)⟩
    exact (hasProjectiveCircuitApproximation_iff_infDist _ s _).mpr ha
  obtain ⟨a,ha,hi⟩ := mem_nhdsLT_iff_exists_Ioo_subset.mp hh
  refine ⟨⟨max a σ,⟨le_max_right ..,max_lt ha hσv⟩,fun u hu => hi ⟨(le_max_left ..).trans_lt hu.1,hu.2⟩⟩,?_⟩
  obtain ⟨u,hu⟩ := exists_between (show a<v from ha)
  have hpair := hi (show u ∈ Ioo a v from hu)
  have hroot : ε < Real.sqrt 2 := ht.2.trans (by
    nlinarith only [Real.sq_sqrt (by norm_num : (0:ℝ)≤2),Real.sqrt_nonneg 2])
  exact FirstGate.translated_strict_window H (hg k) ht.1 hroot hpair.1 hpair.2

#print axioms gaussian_return_bands
end
end GaloisForLFunctions.HTGeometry.ReturnLevels
