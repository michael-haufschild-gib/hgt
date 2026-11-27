import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.FixedCount.Partial.Threshold.Minimum
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.FixedCount.Peak.Ranks.Capped.Spectroscopy

/-! # First distinguishable peak-relative loss in the outgoing quantum distribution -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.FixedCount.Partial.Threshold

open Peak.Ranks.Capped _root_.HTGeometry
open scoped ComplexConjugate

variable {S : Finset Nat.Primes} (c : S → ℕ) (m : ℕ)

def thermalLosses (t : ℝ) := losses (finiteGibbsStateWeight t (fun y : State c m => energy (level y)))

def outputSpectrum (s : ℂ) := losses (fun x : State c m => outgoingShare s x)

theorem spectrum_eq (s : ℂ) : outputSpectrum c m s = thermalLosses c m (2*s.re-1) := by
  unfold outputSpectrum thermalLosses
  simp_rw [outgoing_gibbs]

theorem opposite (s : ℂ) : 2*(1-conj s).re-1 = -(2*s.re-1) := by
  rw [Complex.sub_re,Complex.one_re,Complex.conj_re]
  ring

theorem thermal_edges (w : State c m) (t : ℝ) (ht : 0 ≤ t) :
    thermalLosses c m t = scale t (lowerEdge c m) ∧
    thermalLosses c m (-t) = scale t (upperEdge c m) := by
  obtain ⟨g,u,_,_,lo,hi,ext⟩ := anchors w
  constructor
  · rw [thermalLosses,gibbs_losses _ t g (fun y => mul_le_mul_of_nonneg_left (ext y).1 ht),
      scale,lowerEdge,← Set.range_comp,lo]
    rfl
  · rw [thermalLosses,gibbs_losses _ (-t) u (fun y => mul_le_mul_of_nonpos_left (ext y).2 (neg_nonpos.mpr ht)),
      scale,upperEdge,← Set.range_comp,hi]
    apply congrArg Set.range
    funext y
    change -t*(energy (level y)-energy (level u)) = t*(-energy (level y) - -energy (level u))
    ring

theorem state_of_candidate {z : ℝ} (hz : z ∈ candidates c m) : Nonempty (State c m) := by
  rcases candidates_subset c m hz with ⟨⟨x,_⟩,_⟩ | ⟨⟨x,_⟩,_⟩ <;> exact ⟨x⟩

private theorem positive_threshold (h : (candidates c m).Nonempty) {t : ℝ} (ht : 0 < t) :
    IsLeast (differences (thermalLosses c m t) (thermalLosses c m (-t))) (t*(candidates c m).min' h) := by
  obtain ⟨w⟩ := state_of_candidate c m ((candidates c m).min'_mem h)
  obtain ⟨hl,hu⟩ := thermal_edges c m w t ht.le
  rw [hl,hu]
  exact least_scaled ht (first_unpaired c m h)

/-- At all off-line parameters the first mismatch of the two measured loss spectra
is the least greedy value multiplied by absolute damping. -/
theorem first_unpaired_output (h : (candidates c m).Nonempty) (s : ℂ) (hs : s.re ≠ 1/2) :
    IsLeast (differences (outputSpectrum c m s) (outputSpectrum c m (1-conj s)))
      (|2*s.re-1| * (candidates c m).min' h) := by
  rw [spectrum_eq,spectrum_eq,opposite]
  rcases lt_or_gt_of_ne hs with hneg | hpos
  · have h' : 2*s.re-1 < 0 := by linarith only [hneg]
    have H := positive_threshold c m h (neg_pos.mpr h')
    simpa only [neg_neg,abs_of_neg h',differences,Set.union_comm] using H
  · have h' : 0 < 2*s.re-1 := by linarith only [hpos]
    rw [abs_of_pos h']
    exact positive_threshold c m h h'

#print axioms thermal_edges
#print axioms first_unpaired_output

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.FixedCount.Partial.Threshold
