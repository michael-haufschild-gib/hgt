import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.FirstGate.EntryTransitions
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.ShortTimeProducts.ScalarDensity
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.MaximumOccupation

/-! # Positive time density of strict one-gate improvements -/
open Real Matrix Set MeasureTheory Filter Topology
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.FirstGate
noncomputable section
open SharpOccupation

/-- Translating a sufficiently accurate empty-circuit visit preserves the
two strict error margins at u. Times lying between the two gate budgets have a
positive lower density from every observation origin. -/
theorem translated_strict_window {N : ℕ} (H : selfAdjoint (Register N))
    (hi : MaximallyProjectiveEnergy H.2.isHermitian.eigenvalues)
    {j s : ℕ} {ε u : ℝ} (hε : 0 < ε) (hs : ε < sqrt 2) (h1 : orbitCircuitDistance H j u < ε)
    (h0 : ε < orbitCircuitDistance H s u) :
    ∃ c > (0:ℝ), ∀ a : ℝ, ∀ᶠ T : ℝ in atTop,
      c < volume.real ((visitSet H j ε \ visitSet H s ε) ∩ Icc a T)/(T-a) := by
  let δ := min ε (min (ε-orbitCircuitDistance H j u) (orbitCircuitDistance H s u-ε))/2
  have hδ : 0 < δ := half_pos (lt_min hε (lt_min (sub_pos.mpr h1) (sub_pos.mpr h0)))
  have hδε : δ < ε := (half_lt_self (lt_min hε (lt_min (sub_pos.mpr h1) (sub_pos.mpr h0)))).trans_le (min_le_left ..)
  have h₁ := (half_lt_self (lt_min hε (lt_min (sub_pos.mpr h1) (sub_pos.mpr h0)))).trans_le
    ((min_le_right ..).trans (min_le_left _ _))
  have h₀ := (half_lt_self (lt_min hε (lt_min (sub_pos.mpr h1) (sub_pos.mpr h0)))).trans_le
    ((min_le_right ..).trans (min_le_right _ _))
  change δ < ε-orbitCircuitDistance H j u at h₁
  change δ < orbitCircuitDistance H s u-ε at h₀
  let p := ((2^N:ℕ):ℝ)*(physicalArc δ)^(2^N-1:ℕ)
  have hp : 0 < p := mul_pos (Nat.cast_pos.mpr (pow_pos (by decide) _)) (pow_pos (physicalArc_spec hδ (hδε.trans hs)).1.1 _)
  refine ⟨p/2,half_pos hp,?_⟩
  intro a
  have htend : Tendsto (fun T : ℝ => T-u) atTop atTop := tendsto_atTop.mpr fun b =>
    (eventually_ge_atTop (b+u)).mono fun _ h => (le_sub_iff_add_le).mpr h
  have hlim := (ShortTimeProducts.scalar_fraction H hi hδ (hδε.trans hs) (a-u)).comp htend
  filter_upwards [hlim.eventually_const_lt (half_lt_self hp),eventually_gt_atTop a] with T hT hTa
  let F := visitSet H 0 δ ∩ Icc (a-u) (T-u)
  let G := (fun t : ℝ => t+(-u)) ⁻¹' F
  have hm : MeasurableSet F := by
    have hc : IsClosed (visitSet H 0 δ) := by
      change IsClosed {t | HasProjectiveCircuitApproximation N δ 0 (unitaryEvolution H.val t)}
      simp only [hasProjectiveCircuitApproximation_iff_infDist]
      exact isClosed_le (orbitCircuitDistance_lipschitz H 0).continuous continuous_const
    exact hc.measurableSet.inter measurableSet_Icc
  have he : volume.real G=volume.real F :=
    congrArg ENNReal.toReal ((measurePreserving_add_right volume (-u)).measure_preimage hm.nullMeasurableSet)
  have hsub : G ⊆ (visitSet H j ε \ visitSet H s ε) ∩ Icc a T := by
    intro t hh
    have hnear : HasProjectiveCircuitApproximation N δ 0 (unitaryEvolution H.val (t+-u)) := hh.1
    have hh' : t+-u ∈ Icc (a-u) (T-u) := hh.2
    refine ⟨⟨?_,?_⟩,by constructor <;> linarith only [hh'.1,hh'.2]⟩
    · have hu := (hasProjectiveCircuitApproximation_iff_infDist (unitaryEvolution H.val u) j (ε-δ)).mpr
        (show orbitCircuitDistance H j u ≤ ε-δ by linarith only [h₁])
      have h := affordable_add_time H hnear hu
      rwa [show t+-u+u=t by ring,show δ+(ε-δ)=ε by ring,zero_add] at h
    · intro hcheap
      have hh' := affordable_add_time H hcheap (hnear.neg_time H)
      rw [show t+ -(t+-u)=u by ring] at hh'
      have h := (hasProjectiveCircuitApproximation_iff_infDist _ s _).mp hh'
      change orbitCircuitDistance H s u ≤ _ at h
      linarith only [h,h₀]
  change p/2 < volume.real F/(T-u-(a-u)) at hT
  rw [show T-u-(a-u)=T-a by ring,←he] at hT
  exact hT.trans_le (div_le_div_of_nonneg_right
    (measureReal_mono hsub (measure_ne_top_of_subset inter_subset_right measure_Icc_lt_top.ne)) (sub_nonneg.mpr hTa.le))

/-- At the prescribed physical error, already one gate buys a positive
fraction of time outside the entire empty-circuit tube on each sufficiently
long fixed prefix. The gain can depend on the draw and the prefix. -/
theorem gaussian_one_gate_exclusive_occupation :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop,
      let N := k+3
      let H : selfAdjoint (Register N) := ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),isSelfAdjoint_pathHamiltonian _⟩
      ∃ c > (0:ℝ), ∀ a : ℝ, ∀ᶠ T : ℝ in atTop,
        c < volume.real ((visitSet H 1 (1/10) \ visitSet H 0 (1/10)) ∩ Icc a T)/(T-a) := by
  have hε : (0:ℝ)<1/10 := by norm_num
  have hs : (1/10:ℝ)<sqrt 2 := by nlinarith only [sq_sqrt (by norm_num : (0:ℝ)≤2),sqrt_nonneg 2]
  filter_upwards [gaussian_first_crossing_one_gate,gaussian_first_one_gate_window _ hε hs,
    gaussian_path_all_prefixes_maximally_projective] with ω hcross hwin hgen
  filter_upwards [hcross] with k hk
  intro N H
  obtain ⟨σ,hσ,_,_,hd⟩ := hk
  have hfar : 1/10 < orbitCircuitDistance H 0 σ := by
    by_contra! h
    have hle := (PrecisionReturns.firstVisit_isLeast H σ 0 hε).2
      ⟨le_rfl,(hasProjectiveCircuitApproximation_iff_infDist _ 0 _).mpr h⟩
    exact hd.not_ge (hle.trans (PrecisionReturns.firstVisit_isLeast H σ 1 hε).1.1)
  obtain ⟨u,_,h1,h0⟩ := hwin k σ hσ hfar
  exact translated_strict_window H (hgen k) hε hs h1 h0

#print axioms gaussian_one_gate_exclusive_occupation
end
end GaloisForLFunctions.HTGeometry.FirstGate
