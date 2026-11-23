import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.LocalSimulation.PhysicalSpeed.FirstTravel
import GaloisForLFunctions.HTGeometry.GaussianBoxMass

/-! # Gaussian probability of an early near-Hilbert onset or first return -/
open Set Filter MeasureTheory ProbabilityTheory Real
namespace GaloisForLFunctions.HTGeometry.LocalPatches.PhysicalSpeed
open PrescribedTimes ShortWindows
noncomputable section

/-- Uniform in the deadline, an early onset or an early first return at any
budget through half the crossing budget requires an exceptionally large
individual coupling. The exponent is quadratic in inverse time. -/
theorem gaussian_early_first_passage_tail :
    ∀ᶠ k : ℕ in atTop, ∀ t : ℝ, 0 < t →
      let N := k+3
      let P := nearHilbertContinuousCircuitBudget N
      let m := Fintype.card (ChainLabel N)
      pathPauliDisorderLaw.real {ω | crossingOrigin (k+1) P (9/80) (prefixPoint k ω) ≤ t ∨
        ∃ s ≤ P/2, crossingWait (k+1) P s (prefixPoint k ω) ≤ t} ≤
          2*(m:ℝ)*exp (-(travelProduct N/t)^2/2) := by
  let μ := pathPauliDisorderLaw
  letI : IsProbabilityMeasure μ := by dsimp [μ,pathPauliDisorderLaw]; infer_instance
  filter_upwards [gaussian_capped_first_passage] with k hk
  intro t ht N P m
  let I := PrefixIndex (k+1)
  let R := travelProduct N/t
  have hprod : 0 < travelProduct N := by dsimp [travelProduct,localCrossingWidth,N]; positivity
  have hR : 0 < R := div_pos hprod ht
  have htime : travelProduct N/R=t := by dsimp only [R]; field_simp [hprod.ne',ht.ne']
  let A (i : I) := {ω | R ≤ |prefixPoint k ω i|}
  have hm (i : I) : μ.real (A i) ≤ 2*exp (-R^2/2) := by
    have hmap := (measurePreserving_eval (fun _ : I => gaussianReal 0 1) i).comp
      (gaussian_pauli_prefix_coordinates_law (k+1))
    exact measureReal_abs_ge_le_of_standardGaussian hmap.measurable.aemeasurable hmap.map_eq hR.le
  apply le_trans (b:=μ.real (⋃ i, A i))
  · apply ENNReal.toReal_mono (measure_ne_top _ _)
    apply measure_mono_ae
    filter_upwards [hk] with ω hw
    intro he
    by_contra h
    have hcap (i : I) : |prefixPoint k ω i| ≤ R := le_of_lt (lt_of_not_ge
      (fun hi => h (mem_iUnion.mpr ⟨i,hi⟩)))
    have hh := hw R hR hcap
    rw [htime,lt_min_iff] at hh
    rcases he with hσ|⟨s,hs,hΔ⟩
    · exact hh.1.not_ge hσ
    · exact hh.2.not_ge ((crossingWait_antitone hs _).trans hΔ)
  · apply (measureReal_iUnion_fintype_le A).trans
    apply (Finset.sum_le_sum (s:=Finset.univ) (fun i _ => hm i)).trans_eq
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,I,Fintype.card_fin]
    ring

#print axioms gaussian_early_first_passage_tail
end
end GaloisForLFunctions.HTGeometry.LocalPatches.PhysicalSpeed
