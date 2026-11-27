import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.BondTransfer.MovingDates.FourthPower.PhysicalBand
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.BondTransfer.MovingDates.Passages.PowerBand
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.PhysicalBlocks.TripleSignals.FirstExcess

/-! # Budget-dependent first passages through the fourth-power band -/
open MeasureTheory Filter Set Real
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpanningDensity.BondTransfer
open RepeatedGates.PhysicalBlocks
noncomputable section
private abbrev frozen (ω : PathPauliDisorder) (n : ℕ) :
    selfAdjoint (Matrix (Fin (n+2)→Bool) (Fin (n+2)→Bool) ℂ) :=
  ⟨_,isSelfAdjoint_pathHamiltonian (pathPauliDisorderShell ω n)⟩

/-- After any tenth-error visit, the first robust above-sweep passage
takes at most the larger of the onset date and a constant times the
fourth root of the excess fraction. The lower bound is uniform even
at positive initial budget. -/
theorem gaussian_fourth_power_first_passage :
    ∃ b>0, ∃ L>0, ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop,
      let j := prefixIndex n
      let N : ℝ := (n+1:ℕ)
      ∀ (v : ℝ) (r q : ℕ), let m : ℝ := (2*r+q:ℕ)
        m≤b*N →
        HasProjectiveCircuitApproximation (n+2) (1/10) r (unitaryEvolution (frozen ω n).val v) →
        ∀ ρ∈Icc (9/80:ℝ) (1/8),
          let τ := firstExcessAfter ω n (r+q) v ρ
          let f (x : ℝ) := orbitCircuitDistance (frozen ω n) (n+1+(r+q)) (v+x)
          τ∈Icc 0 1 ∧ τ^4≤ max ((1/(j:ℝ))^48) (m/(b*N)) ∧ L≤((n+2:ℕ):ℝ)*τ^2 ∧
            f τ=ρ ∧ ∀ x∈Ico 0 τ, f x<ρ := by
  obtain ⟨b,hb,hw⟩ := gaussian_polynomial_fourth_power_band
  let s (n : ℕ) := (1/(prefixIndex n:ℝ))^12
  have h := first_passage_of_power_band s (by decide : 4≠0) hb (by
    filter_upwards [hw] with ω hω
    filter_upwards [hω] with n hn
    exact ⟨hn.1,hn.2.1,hn.2.2.2.2⟩)
  refine ⟨b,hb,?_⟩
  simpa only [s,←pow_mul] using h

/-- The same growing floor holds on the final approach to, and rebound
from, the first low visit selected after the original near-Hilbert
crossing. Reconstructing the increment uses the r gates of the visit once. -/
theorem gaussian_original_dip_fourth_band :
    ∃ b>0, ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop,
      let s := (1/(prefixIndex n:ℝ))^12
      0<s ∧ s≤1 ∧ ∀ r : ℕ, let v := firstLowAfterCrossing ω n r
        ∀ h : ℝ, |h|∈Icc s 1 → ∀ k : ℕ, HasProjectiveCircuitApproximation (n+2) (3/20) k
          (unitaryEvolution (frozen ω n).val (v+h)) →
          (1+b* |h|^4)*((n+1:ℕ):ℝ)<((r+k:ℕ):ℝ) := by
  obtain ⟨b,hb,hw⟩ := gaussian_polynomial_fourth_power_band
  refine ⟨b,hb,?_⟩
  filter_upwards [hw] with ω hω
  filter_upwards [hω] with n hn
  intro s
  obtain ⟨hs,hs₁,_,_,hfit⟩ := hn
  refine ⟨hs,hs₁,?_⟩
  intro r v h hh k hk
  let H := frozen ω n
  have hv : HasProjectiveCircuitApproximation (n+2) (1/10) r (unitaryEvolution H.val v) :=
    (PrecisionReturns.firstVisit_isLeast H _ r (by norm_num : (0:ℝ)<1/10)).1.2
  have he := affordable_add_time H (x := -v) (y := v+h) (hv.neg_time H) hk
  rw [neg_add_cancel_left,show (1/10:ℝ)+3/20=1/4 by norm_num] at he
  apply hfit |h| hh (r+k)
  rcases le_total 0 h with hpos|hneg
  · rwa [abs_of_nonneg hpos]
  · rw [abs_of_nonpos hneg]
    exact he.neg_time H

#print axioms gaussian_original_dip_fourth_band
#print axioms gaussian_fourth_power_first_passage
end
end GaloisForLFunctions.HTGeometry.SpanningDensity.BondTransfer
