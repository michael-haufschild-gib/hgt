import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.SelectedDates.AlgebraicCurves.SingleHarmonics.AntipodalHorizons.LateWindings
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli

/-! # First scalar waits on growing prefixes of a single sampled chain -/

open Filter Set MeasureTheory Real
namespace GaloisForLFunctions.HTGeometry.SpectralJets.SelectedDates.AlgebraicCurves.SingleHarmonics.AntipodalHorizons
open SharpOccupation
noncomputable section

/-- One deterministic winding cutoff per register suffices. For every
prescribed schedule above these cutoffs, almost every infinite frozen chain
eventually waits more than b^(-2^K) full-width periods after its antipodes. -/
theorem gaussian_frozen_antipodal_wait {ε b : ℝ} (hε : ε∈Ioo (0:ℝ) (sqrt 2))
    (hxb : physicalArc ε < b) (hb : b < 1) :
    ∃ N₀ : ℕ→ℕ, ∀ n : ℕ→ℕ, (∀ᶠ k : ℕ in atTop, N₀ k ≤ n k) →
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop,
      (1/b)^(2^(k+3)) < firstPeriods k (n k) ε ω := by
  classical
  let B (k n : ℕ) := {ω | firstPeriods k n ε ω ≤ (1/b)^(2^(k+3))}
  obtain ⟨c,hc,hlate⟩ := gaussian_first_wait_after_late_antipode hε hxb hb
  obtain ⟨K,hK⟩ := eventually_atTop.mp hlate
  have hex (k : ℕ) : ∃ a : ℕ, K ≤ k → ∀ n ≥ a, pathPauliDisorderLaw.real (B k n) < c^k := by
    by_cases hk : K ≤ k
    · obtain ⟨a,ha⟩ := eventually_atTop.mp (hK k hk)
      have hdim : k ≤ 2^(k+3)-3 := by
        have := Nat.lt_two_pow_self (n:=k+3)
        omega
      exact ⟨a,fun _ n hn => (ha n hn).trans_le (pow_le_pow_of_le_one hc.1.le hc.2.le hdim)⟩
    · exact ⟨0,fun h => (hk h).elim⟩
  choose A hA using hex
  refine ⟨A,?_⟩
  intro n hn
  haveI : IsProbabilityMeasure pathPauliDisorderLaw := by unfold pathPauliDisorderLaw; infer_instance
  have hsum : Summable (fun k => pathPauliDisorderLaw.real (B k (n k))) := by
    apply (summable_geometric_of_lt_one hc.1.le hc.2).of_norm_bounded_eventually_nat
    filter_upwards [eventually_ge_atTop K,hn] with k hk hnk
    rw [Real.norm_of_nonneg measureReal_nonneg]
    exact (hA k hk _ hnk).le
  have ha : ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop, ω∉B k (n k) := by
    apply ae_eventually_notMem
    simpa only [ofReal_measureReal (measure_ne_top pathPauliDisorderLaw _)] using hsum.tsum_ofReal_ne_top
  filter_upwards [ha] with ω hω
  exact hω.mono fun k hk => lt_of_not_ge hk

#print axioms gaussian_frozen_antipodal_wait
end
end GaloisForLFunctions.HTGeometry.SpectralJets.SelectedDates.AlgebraicCurves.SingleHarmonics.AntipodalHorizons
