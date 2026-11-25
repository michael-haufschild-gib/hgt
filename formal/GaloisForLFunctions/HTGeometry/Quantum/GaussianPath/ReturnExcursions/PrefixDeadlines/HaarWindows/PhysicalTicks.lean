import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.PrefixDeadlines.HaarWindows.TickCounts
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.PrefixDeadlines.HaarWindows.PhysicalLags

/-! # Affordable indices on arbitrary physical sampling clocks -/

open Set MeasureTheory
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.ReturnExcursions.PrefixDeadlines.HaarWindows
open SharpOccupation
noncomputable section

/-- Affordable ticks among indices `0,...,n-1` on one clock. -/
def affordableTicks {N : ℕ} (H : selfAdjoint (Register N)) (s : ℕ) (e h : ℝ) (n : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range n).filter (fun j => (j:ℝ)*h ∈ visitSet H s e)

/-- Every finite identity-start tick record has at least the half-resource
Haar fraction. Any record with expected count greater than one must contain
a strictly positive affordable index. The period may depend on the orbit. -/
theorem static_tick_deadline {N d : ℕ} (i : (Fin N → Bool) ≃ Fin (d+1))
    (H : selfAdjoint (Register N)) (j s : ℕ) (hj : j + j ≤ s) {e : ℝ} (he : e ∈ Ioo (0:ℝ) 2) :
    let V := hermitianEigenbasisUnitary H.2.isHermitian
    let A := projectiveContinuousCircuitCaptureTarget i V j (zeroGateArcTolerance (physicalArc e/2))
    ∀ (h : ℝ) (n : ℕ), (n:ℝ)*volume.real A ≤ ((affordableTicks H s e h n).card:ℝ) ∧
      (1 < (n:ℝ)*volume.real A → ∃ k : ℕ, 0 < k ∧ k < n ∧ (k:ℝ)*h ∈ visitSet H s e) := by
  classical
  intro V A h n
  let E := H.2.isHermitian.eigenvalues ∘ i.symm
  let φ := RHTower.projectivePhysicalPhaseFlowHom E
  let z (k : ℕ) := φ ((k:ℝ)*h)
  let Q (k : ℕ) := (k:ℝ)*h ∈ visitSet H s e
  have hd (y u v) (hvu : v ≤ u) (hu : z u+y ∈ A) (hv : z v+y ∈ A) : Q (u-v) := by
    obtain ⟨c,hc,C,hC,hfit⟩ := shifted_capture_difference i H j he y _ _ hu hv
    change ((u-v:ℕ):ℝ)*h ∈ visitSet H s e
    rw [Nat.cast_sub hvu,sub_mul]
    exact ⟨c,hc,C,hC.trans hj,hfit⟩
  have hc := translated_tick_floor z A (isClosed_projectiveContinuousCircuitCaptureTarget ..).measurableSet Q hd n
  refine ⟨hc,?_⟩
  intro hn
  have hk : 1 < (affordableTicks H s e h n).card := by
    exact_mod_cast (hn.trans_le hc)
  by_contra! hzero
  have hsub : affordableTicks H s e h n ⊆ {0} := by
    intro k hmem
    obtain ⟨hlt,ha⟩ := Finset.mem_filter.mp hmem
    apply Finset.mem_singleton.mpr
    exact Nat.eq_zero_of_not_pos fun hpos => hzero k hpos (Finset.mem_range.mp hlt) ha
  exact hk.not_ge ((Finset.card_le_card hsub).trans_eq (Finset.card_singleton _))

#print axioms static_tick_deadline
end
end GaloisForLFunctions.HTGeometry.ReturnExcursions.PrefixDeadlines.HaarWindows
