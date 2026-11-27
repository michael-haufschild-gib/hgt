import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.WeakBonds.NearDiagonal.BlockMergers.Physical.DelayedExcursions.BlockWindow
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Dephasing.GappedSpin.CentralCut.IncrementClock
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.WeakBonds.NearDiagonal.OccupationBand
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.WeakBonds.NearDiagonal.LinearCap.GaussianSector

/-! # A long first excursion and a capped all-time maximum on the same chain -/
open Set MeasureTheory Filter Real
namespace GaloisForLFunctions.HTGeometry.WeakBonds.NearDiagonal.BlockMergers
open PrescribedTimes SharpOccupation Dephasing.GappedSpin.CentralCut
noncomputable section

/-- Reindex a balanced cut at the original prefix size. -/
private theorem prefix_window :
    ∃ A > (0:ℝ), ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 256 ≤ n+2 → ∀ T ≥ (1:ℝ),
      let K := n+2
      ∃ B : ℕ, 2*B ≤ nearHilbertContinuousCircuitBudget K ∧
        ∃ F : Set (PathLabel n→ℝ), MeasurableSet F ∧
          A*exp (-C*(K:ℝ)*((Nat.clog 2 K:ℝ)+1)) ≤ T^9*(standardLaw (PathLabel n)).real F ∧
          ∀ x ∈ F, x ∈ capEvent n (1/10) ∧ ∀ t : ℝ, |t| ≤ T →
            HasProjectiveCircuitApproximation K (1/100) B
              (unitaryEvolution (pathHamiltonian (WithLp.toLp 2 x : PathShell n)) t) := by
  obtain ⟨A,hA,C,hC,hw⟩ := physical_block_window
  refine ⟨A,hA,C,hC,?_⟩
  intro n hn T hT K
  let l := (n+2)/2-2
  let r := (n+3)/2-2
  have hsum : l+r+2=n := by dsimp only [l,r]; omega
  have hlr : l ≤ r := by dsimp only [l,r]; omega
  have hr : r ≤ l+1 := by dsimp only [l,r]; omega
  have hlarge : 128 ≤ l+2 := by dsimp only [l]; omega
  have hb := balanced_increment_budget l r hlr hr hlarge
  have hw' := hw l r (by omega) hlr hr T hT
  change 2*_ ≤ nearHilbertContinuousCircuitBudget (l+r+2+2) at hb
  rw [hsum] at hb hw'
  exact ⟨_,hb,hw'⟩

/-- For an original Gaussian prefix, both the first crossing and all
subsequent half-budget waits exceed T on a sector with finite-accuracy
maximum at most 213D. The lower survival mass has prefactor exp[-O(K log K)]. -/
theorem hierarchical_original_wait :
    ∃ A > (0:ℝ), ∃ C : ℝ, 0 ≤ C ∧ ∃ b ∈ Ioo (0:ℝ) 1, ∀ᶠ k : ℕ in atTop,
      let n := k+1
      let K := n+2
      let P := nearHilbertContinuousCircuitBudget K
      ∀ T ≥ (1:ℝ), ∃ E : Set PathPauliDisorder, MeasurableSet E ∧
        A*exp (-C*(K:ℝ)*((Nat.clog 2 K:ℝ)+1)) ≤ T^9*pathPauliDisorderLaw.real E ∧
        ∀ᵐ ω ∂pathPauliDisorderLaw, ω∈E →
          let u := pathPauliDisorderShell ω n
          let x := fun i => u (pathCoeffEquiv n i)
          let H : selfAdjoint (SharpOccupation.Register K) := ⟨pathHamiltonian u,isSelfAdjoint_pathHamiltonian u⟩
          T < crossingOrigin n P (9/80) x ∧ (∀ j ≤ P/2, T < crossingWait n P j x) ∧
            ∃ m : ℕ, P < m ∧ m ≤ 213*2^K ∧ IsRecurrentOrbitCircuitMaximumAt H (1/10) m ∧
              ∀ o : ℝ, ∀ᶠ L : ℝ in atTop, ∀ j : ℕ, j*(64*(K+1))*213 ≤ m →
                visitFraction H j (1/10) o L < b^(2^K:ℕ) := by
  obtain ⟨A,hA,C,hC,hw⟩ := prefix_window
  obtain ⟨b,hb,hband⟩ := capped_path_occupation
  refine ⟨A,hA,C,hC,b,hb,?_⟩
  filter_upwards [delay_of_cheap,hband,eventually_ge_atTop 256] with k hdelay hmax hk
  intro n K P T hT
  obtain ⟨B,hB,F,hF,hprob,hwin⟩ := hw n (by dsimp only [n]; omega) T hT
  let Y := fun (ω : PathPauliDisorder) l => pathPauliDisorderShell ω n l
  have hY := AccuracyScales.TenthPlateau.measurePreserving_pathDisorder_labels n
  refine ⟨Y ⁻¹' F,hF.preimage hY.measurable,hprob.trans_eq (congrArg (T^9*·)
    (hY.measureReal_preimage hF.nullMeasurableSet).symm),?_⟩
  filter_upwards [hdelay,gaussian_path_all_prefixes_maximally_projective] with ω hd hω
  intro he u x H
  obtain ⟨hc,hinc⟩ := hwin (Y ω) he
  obtain ⟨ho,hr⟩ := hd T (zero_lt_one.trans_le hT) B hB hinc
  refine ⟨ho,hr,hmax u (hω k) 213 (by decide) ?_⟩
  intro t
  have ht := hc t
  change pathGateDistance n (213*2^K) (fun i => u (pathCoeffEquiv n i)) t ≤ _ at ht
  rw [pathGateDistance,numberedGenerator_shell] at ht
  rw [Nat.mul_comm 213 (2^K)] at ht
  exact (hasProjectiveCircuitApproximation_iff_infDist ..).mpr ht

#print axioms hierarchical_original_wait
end
end GaloisForLFunctions.HTGeometry.WeakBonds.NearDiagonal.BlockMergers
