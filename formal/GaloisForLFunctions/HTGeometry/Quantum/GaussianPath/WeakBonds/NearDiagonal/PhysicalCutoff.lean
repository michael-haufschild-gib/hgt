import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SharpOccupation.PhysicalTolerance
import GaloisForLFunctions.HTGeometry.NearHilbertContinuousCircuitEntropyLaw

/-! # A uniform size cutoff for Hilbert-scale occupation below the semicircle error -/

open Set Filter Real MeasureTheory
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.WeakBonds.NearDiagonal
open SharpOccupation
noncomputable section

/-- The entropy cutoff is uniform in the eigenbasis. Maximal
projective rank is the only generator-dependent input. -/
theorem physical_record_cutoff (ε : ℝ) (hε : 0 < ε) (hε₁ : ε < sqrt 2) :
    ∃ b ∈ Ioo (0:ℝ) 1, ∀ᶠ K : ℕ in atTop, ∀ H : selfAdjoint (SharpOccupation.Register K),
      MaximallyProjectiveEnergy H.2.isHermitian.eigenvalues → ∀ a : ℝ, ∀ᶠ T : ℝ in atTop,
        visitFraction H (nearHilbertContinuousCircuitBudget K) ε a T < b^(2^K:ℕ) := by
  let x := physicalArc ε
  obtain ⟨hx,htol⟩ := physicalArc_spec hε hε₁
  change x ∈ Ioo (0:ℝ) (1/2) at hx
  let y := (x+1/2)/2
  have hxy : x < y := by dsimp only [y]; linarith only [hx.2]
  have hy : y < 1/2 := by dsimp only [y]; linarith only [hx.2]
  have hy₀ : 0 < y := hx.1.trans hxy
  let b := exp (-log 2/2)
  have h₂ := log_pos (by norm_num : (1:ℝ)<2)
  have hb : b ∈ Ioo (0:ℝ) 1 := ⟨exp_pos _,exp_lt_one_iff.mpr (by linarith only [h₂])⟩
  have hl : log y+32*log 2/(64:ℕ) < log b := by
    have h := log_lt_log hy₀ hy
    rw [log_div one_ne_zero (by norm_num),log_one,zero_sub] at h
    rw [show log b = -log 2/2 from log_exp _]
    norm_num only [Nat.cast_ofNat]
    linarith only [h]
  let δ := zeroGateArcTolerance y-zeroGateArcTolerance x
  have hδ : 0 < δ := sub_pos.mpr (strictMonoOn_zeroGateArcTolerance
    ⟨hx.1.le,hx.2.le⟩ ⟨hy₀.le,hy.le⟩ hxy)
  refine ⟨b,hb,?_⟩
  filter_upwards [positive_budget_exponent 64 (by decide) δ y b hδ hy₀ hb.1 hl] with K hK
  intro H hmax a
  have h := finite_budget_eventually_lt H hmax (nearHilbertContinuousCircuitBudget K)
    hx.1.le hxy hy a (b^(2^K:ℕ)) hK
  simpa only [x,htol] using h

#print axioms physical_record_cutoff
end
end GaloisForLFunctions.HTGeometry.WeakBonds.NearDiagonal
