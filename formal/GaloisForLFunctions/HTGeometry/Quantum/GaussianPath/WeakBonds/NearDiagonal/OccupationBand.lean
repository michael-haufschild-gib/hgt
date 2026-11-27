import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.WeakBonds.NearDiagonal.PhysicalCutoff
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SharpOccupation.PhysicalTolerance
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SharpOccupation.PositiveDensityBudget
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.GaussianMaximumQuantiles

/-! # An occupation band for full-rank paths with a Hilbert-dimension gate cap -/

open Set Filter Real MeasureTheory ProbabilityTheory
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.WeakBonds.NearDiagonal
open SharpOccupation
noncomputable section

/-- An all-time cap at error one tenth bounds the loss in comparing
the recurrent maximum at that same error with the long-record gate
count. The entropy cutoff is uniform in the chosen full-rank path. -/
theorem capped_path_occupation :
    ∃ b ∈ Ioo (0:ℝ) 1, ∀ᶠ k : ℕ in atTop,
      let n := k+1
      let K := n+2
      let P := nearHilbertContinuousCircuitBudget K
      ∀ u : PathShell n,
        let H : selfAdjoint (SharpOccupation.Register K) :=
          ⟨pathHamiltonian u,isSelfAdjoint_pathHamiltonian u⟩
        MaximallyProjectiveEnergy H.2.isHermitian.eigenvalues →
        ∀ q : ℕ, 0 < q → (∀ t : ℝ, HasProjectiveCircuitApproximation K (1/10) (2^K*q)
          (unitaryEvolution H.val t)) →
        ∃ m : ℕ, P < m ∧ m ≤ q*2^K ∧ IsRecurrentOrbitCircuitMaximumAt H (1/10) m ∧
          ∀ a : ℝ, ∀ᶠ T : ℝ in atTop, ∀ s : ℕ, s*(64*(K+1))*q ≤ m →
            visitFraction H s (1/10) a T < b^(2^K:ℕ) := by
  obtain ⟨b,hb,hcut⟩ := physical_record_cutoff (1/10) (by norm_num)
    (lt_of_lt_of_le (by norm_num : (1/10:ℝ)<1) (one_le_sqrt.mpr (by norm_num)))
  refine ⟨b,hb,?_⟩
  filter_upwards [(tendsto_add_atTop_nat 3).eventually hcut] with k hk
  intro n K P u H hrank q hq hfit
  obtain ⟨m,hm⟩ := twoLocal_exists_recurrent_maximum_at (by dsimp only [K]; omega : 2 ≤ K) H
    (hasPauliWeightAtMost_pathHamiltonian u (isSelfAdjoint_pathHamiltonian u)) (1/10) (by norm_num)
  have hlow := hk H hrank
  obtain ⟨_,w,_,hw,hvisit⟩ := hm.2
  obtain ⟨v,_,hv⟩ := hvisit 0
  obtain ⟨z,hz,Cir,hCir,herr⟩ := hfit v
  have hmax : m ≤ q*2^K := (hv v ⟨le_rfl,le_add_of_nonneg_right hw.le⟩ z hz Cir herr).trans
    (hCir.trans_eq (Nat.mul_comm ..))
  refine ⟨m,?_,hmax,hm,?_⟩
  · by_contra! hle
    obtain ⟨T,hT,hsmall⟩ := ((eventually_gt_atTop (0:ℝ)).and (hlow 0)).exists
    have hall : Icc 0 T ⊆ visitSet H P (1/10) := fun t _ =>
      let ⟨z,hz,A,hA,hfit⟩ := hm.1 t
      ⟨z,hz,A,hA.trans hle,hfit⟩
    have heq : visitFraction H P (1/10) 0 T=1 := by
      rw [visitFraction,inter_eq_right.mpr hall,Real.volume_real_Icc_of_le hT.le,sub_zero,div_self hT.ne']
    change visitFraction H P (1/10) 0 T < b^(2^K:ℕ) at hsmall
    rw [heq] at hsmall
    exact (pow_lt_one₀ hb.1.le hb.2 (Nat.two_pow_pos K).ne').asymm hsmall
  · intro a
    filter_upwards [hlow a,eventually_gt_atTop a] with T hT ha
    intro s hs
    have hs' : s*(64*(K+1)) ≤ 2^K := by
      exact Nat.le_of_mul_le_mul_right (hs.trans (hmax.trans_eq (Nat.mul_comm ..))) hq
    have hP : s ≤ P := (Nat.le_div_iff_mul_le (by positivity : 0 < 64*(K+1))).mpr hs'
    exact (visitFraction_mono H hP _ a T ha.le).trans_lt hT

#print axioms capped_path_occupation
end
end GaloisForLFunctions.HTGeometry.WeakBonds.NearDiagonal
