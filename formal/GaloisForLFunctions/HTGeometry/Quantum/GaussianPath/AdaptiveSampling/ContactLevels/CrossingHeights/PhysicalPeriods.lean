import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.AdaptiveSampling.ContactLevels.CrossingHeights.ExceptionalValues
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.AdaptiveSampling.ContactLevels.VisitParameter
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.AdaptiveSampling.ShiftedWaits.SortedPhases

/-! # Nonresonant first waits at a fixed physical return error -/

open Set MeasureTheory
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.AdaptiveSampling.ContactLevels.CrossingHeights
open PrescribedTimes PrecisionReturns
noncomputable section

private abbrev Point (k : ℕ) := PrefixIndex (k+1) → ℝ
private def frequencies (k : ℕ) (x : Point k) :=
  RHTower.zeroProjectiveFrequency (sortedEnsembleSpectrum (chainPauliFin_isHermitian (k+3)) x ∘
    (prefixPhaseEnergyEquiv k).symm)

private theorem prefix_heights (k : ℕ) (ε : ℝ) (hε : 0<ε) :
    ∃ B : Set ℝ, B.Countable ∧ ∀ r ∉ B, ∀ᵐ x ∂centredProductGaussian (PrefixIndex (k+1)) 1,
      RationallyIndependentFrequency (frequencies k x) → ∀ (s j : ℕ) (a u : ℝ),
        let H := prefixGenerator (k+1) x
        ε<orbitCircuitDistance H s a → orbitCircuitDistance H j u=r →
          FreeAtStep (frequencies k x) (firstVisit H a s ε-u) := by
  let J := ℕ × ℕ × ℚ
  let v (b : J) (x : Point k) := visitParameter (k+1) b.1 b.2.2 (x,ε)
  let f (b : J) (p : Point k × ℝ) := pathGateDistance (k+1) b.2.1 p.1 p.2
  have hw : Measurable (frequencies k) := by
    let h := (continuous_sortedEnsembleSpectrum (chainPauliFin_isHermitian (k+3))).measurable
    exact measurable_pi_lambda _ fun i => ((measurable_pi_apply _).comp h).sub ((measurable_pi_apply _).comp h)
  have hv (b : J) : Measurable (v b) := (measurable_visitParameter ..).comp
    (measurable_id.prodMk measurable_const)
  obtain ⟨B,hB,h⟩ := exceptional_clock_heights (centredProductGaussian (PrefixIndex (k+1)) 1)
    (frequencies k) hw v hv f (fun b => (continuous_distance (k+1) b.2.1).measurable)
  refine ⟨B,hB,fun r hr => ?_⟩
  filter_upwards [h r hr] with x hx hi s j a u
  intro H hout hu
  obtain ⟨q,_,hq⟩ := rational_visit_origin H a s hε hout
  have hh := hx hi (s,j,q) u hu
  simpa only [v,visitParameter,if_pos hε,hq,H] using hh

private abbrev shellPoint (k : ℕ) (ω : PathPauliDisorder) : Point k :=
  fun i => pathPauliDisorderShell ω (k+1) (pathCoeffEquiv (k+1) i)

private abbrev generator (k : ℕ) (ω : PathPauliDisorder) : selfAdjoint (Register (k+3)) :=
  ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),isSelfAdjoint_pathHamiltonian _⟩

private theorem sorted_frequencies (k : ℕ) (ω : PathPauliDisorder)
    (hm : MaximallyProjectiveEnergy (generator k ω).2.isHermitian.eigenvalues) :
    ∃ e : (Fin (k+3) → Bool) ≃ Fin ((2^(k+3)-1)+1),
      RHTower.zeroProjectiveFrequency ((generator k ω).2.isHermitian.eigenvalues ∘ e.symm)
        = frequencies k (shellPoint k ω) ∧
      RationallyIndependentFrequency (frequencies k (shellPoint k ω)) := by
  let p := prefixPhaseEnergyEquiv k
  obtain ⟨q,hq⟩ := SpectralJets.physical_sorted_order k ω hm.injective
  let e := q.trans p
  have he : (generator k ω).2.isHermitian.eigenvalues ∘ e.symm =
      sortedEnsembleSpectrum (chainPauliFin_isHermitian (k+3)) (shellPoint k ω) ∘ p.symm := by
    funext i
    simpa only [e,Function.comp_apply,Equiv.symm_trans_apply,q.apply_symm_apply] using hq (q.symm (p.symm i))
  have hw : RHTower.zeroProjectiveFrequency ((generator k ω).2.isHermitian.eigenvalues ∘ e.symm) =
      frequencies k (shellPoint k ω) := congrArg RHTower.zeroProjectiveFrequency he
  refine ⟨e,hw,?_⟩
  rw [←hw]
  exact RHTower.maximallyProjectiveEnergy_zeroProjectiveFrequency_independent _ (hm.comp_equiv e.symm)

private def Waits {n d : ℕ} (H : selfAdjoint (Register n)) (w : Fin d → ℝ) (ε r : ℝ) : Prop :=
  ∀ (s j : ℕ) (a u : ℝ), ε<orbitCircuitDistance H s a → orbitCircuitDistance H j u=r →
    FreeAtStep w (firstVisit H a s ε-u)

/-- Outside a deterministic countable set of crossing heights, all
prefixes have nonresonant elapsed times from any such crossing to
every first return at the prescribed physical error from outside. -/
theorem gaussian_fixed_return_error_free_waits (ε : ℝ) (hε : 0<ε) :
    ∃ B : Set ℝ, B.Countable ∧ ∀ r ∉ B, ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ k : ℕ,
      let N := k+3
      let H : selfAdjoint (Register N) := ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),isSelfAdjoint_pathHamiltonian _⟩
      ∃ e : (Fin N → Bool) ≃ Fin ((2^N-1)+1), ∀ (s j : ℕ) (a u : ℝ),
        ε<orbitCircuitDistance H s a → orbitCircuitDistance H j u=r →
          FreeAtStep (RHTower.zeroProjectiveFrequency (H.2.isHermitian.eigenvalues ∘ e.symm))
            (firstVisit H a s ε-u) := by
  choose B hB h using fun k => prefix_heights k ε hε
  refine ⟨⋃ k, B k,countable_iUnion hB,?_⟩
  intro r hr
  have hb (k : ℕ) : r∉B k := fun h => hr (mem_iUnion.mpr ⟨k,h⟩)
  have ha (k : ℕ) : ∀ᵐ ω ∂pathPauliDisorderLaw,
      RationallyIndependentFrequency (frequencies k (shellPoint k ω)) →
        Waits (prefixGenerator (k+1) (shellPoint k ω)) (frequencies k (shellPoint k ω)) ε r :=
    (gaussian_pauli_prefix_coordinates_law (k+1)).quasiMeasurePreserving.ae (h k r (hb k))
  filter_upwards [ae_all_iff.mpr ha,gaussian_path_all_prefixes_maximally_projective] with ω hw hm k
  intro N H
  obtain ⟨e,he,hi⟩ := sorted_frequencies k ω (hm k)
  refine ⟨e,?_⟩
  change Waits (generator k ω) _ ε r
  rw [he]
  have heq : prefixGenerator (k+1) (shellPoint k ω)=generator k ω :=
    Subtype.ext (numberedGenerator_shell (pathPauliDisorderShell ω (k+1)))
  rw [←heq]
  exact hw k hi

#print axioms gaussian_fixed_return_error_free_waits
end
end GaloisForLFunctions.HTGeometry.AdaptiveSampling.ContactLevels.CrossingHeights
