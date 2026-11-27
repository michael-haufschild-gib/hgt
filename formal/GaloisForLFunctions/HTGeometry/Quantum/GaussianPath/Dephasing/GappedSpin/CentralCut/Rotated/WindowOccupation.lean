import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.WeakBonds.NearDiagonal.PhysicalCutoff
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.PhaseBoundary.GaussianOccupation
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.MaximumOccupation

/-! # Occupation of entire windows around moving observation dates -/
open Filter Set MeasureTheory Topology Real
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.Dephasing.GappedSpin.CentralCut
open SharpOccupation
noncomputable section

/-- Centers with a visit anywhere within radius R. -/
def nearbyVisit {K : ℕ} (H : selfAdjoint (SharpOccupation.Register K)) (s : ℕ) (R : ℝ) : Set ℝ :=
  {v | ∃ t ∈ Icc (v-R) (v+R), t ∈ visitSet H s (1/10)}

/-- A cheap increment moves any nearby half-budget visit to the center
at error 11/100. This covers the whole window without a time mesh. -/
theorem nearbyVisit_subset {K P B : ℕ} (H : selfAdjoint (SharpOccupation.Register K))
    {R : ℝ} (hB : 2*B ≤ P)
    (hfit : ∀ t : ℝ, |t| ≤ R → HasProjectiveCircuitApproximation K (1/100) B
      (unitaryEvolution H.val t)) :
    nearbyVisit H (P/2) R ⊆ visitSet H P (11/100) := by
  rintro v ⟨t,ht,hv⟩
  have hlag : |v-t| ≤ R := abs_le.mpr ⟨by linarith only [ht.2],by linarith only [ht.1]⟩
  obtain ⟨z,hz,C,hC,herr⟩ := affordable_add_time H hv (hfit (v-t) hlag)
  rw [show t+(v-t)=v by ring] at herr
  exact ⟨z,hz,C,hC.trans (by omega),herr.trans_eq (by norm_num)⟩

/-- The size cutoff precedes the disorder quantifier. On each prefix
the window origin may depend on the sample and the observation length. -/
theorem cheap_window_occupation :
    ∃ b ∈ Ioo (0:ℝ) 1, ∀ᶠ k : ℕ in atTop, ∀ᵐ ω ∂pathPauliDisorderLaw,
      let n := k+1
      let K := n+2
      let P := nearHilbertContinuousCircuitBudget K
      let u := pathPauliDisorderShell ω n
      let H : selfAdjoint (SharpOccupation.Register K) := ⟨pathHamiltonian u,isSelfAdjoint_pathHamiltonian u⟩
      ∀ R : ℝ, ∀ B : ℕ, 2*B ≤ P →
        (∀ t : ℝ, |t| ≤ R → HasProjectiveCircuitApproximation K (1/100) B
          (unitaryEvolution H.val t)) →
        ∀ a : ℝ→ℝ, ∀ᶠ L : ℝ in atTop,
          volume.real (nearbyVisit H (P/2) R ∩ Icc (a L) (a L+L))/L < b^(2^K:ℕ) := by
  let ε : ℝ := 11/100
  obtain ⟨b,hb,hcut⟩ := WeakBonds.NearDiagonal.physical_record_cutoff ε (by norm_num [ε])
    (lt_of_lt_of_le (by norm_num [ε] : ε<1) (one_le_sqrt.mpr (by norm_num)))
  let c := (b+1)/2
  have hbc : b<c := by dsimp only [c]; linarith only [hb.2]
  refine ⟨c,⟨hb.1.trans hbc,by dsimp only [c]; linarith only [hb.2]⟩,?_⟩
  filter_upwards [(tendsto_add_atTop_nat 3).eventually hcut] with k hk
  filter_upwards [gaussian_path_all_prefixes_maximally_projective,
    PhaseBoundary.gaussian_uniform_affordable_fraction] with ω hr hlim
  intro n K P u H R B hB hfit a
  have h₀ := hlim k P ε (fun _ => 0)
  simp only [zero_add] at h₀
  have hupper := le_of_tendsto h₀ ((hk H (hr k) 0).mono fun _ h => h.le)
  have hc := hupper.trans_lt (pow_lt_pow_left₀ hbc hb.1.le (Nat.two_pow_pos K).ne')
  have hlong := (hlim k P ε a).eventually_lt_const hc
  have hsub := nearbyVisit_subset H hB hfit
  filter_upwards [hlong,eventually_gt_atTop (0:ℝ)] with L hl hL
  have hm := measureReal_mono (μ:=volume) (inter_subset_inter_left (Icc (a L) (a L+L)) hsub)
    (measure_ne_top_of_subset inter_subset_right measure_Icc_lt_top.ne)
  have hfrac := div_le_div_of_nonneg_right hm hL.le
  apply hfrac.trans_lt
  simpa only [visitFraction,add_sub_cancel_left] using hl

#print axioms cheap_window_occupation
end
end GaloisForLFunctions.HTGeometry.Dephasing.GappedSpin.CentralCut
