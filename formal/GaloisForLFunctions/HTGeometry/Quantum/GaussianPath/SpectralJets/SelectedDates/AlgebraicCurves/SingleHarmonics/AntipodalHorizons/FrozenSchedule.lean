import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.SelectedDates.AlgebraicCurves.SingleHarmonics.AntipodalHorizons.LateWindings
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli

/-! # First scalar waits on growing prefixes of a single sampled chain -/

open Filter Set MeasureTheory Real
namespace GaloisForLFunctions.HTGeometry.SpectralJets.SelectedDates.AlgebraicCurves.SingleHarmonics.AntipodalHorizons
open SharpOccupation
noncomputable section

/-- Summable upper bounds at each sufficiently large winding give a single
deterministic cutoff schedule for a frozen sequence of observations. -/
theorem frozen_event_cutoff {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    (B : ℕ→ℕ→Set X) {c : ℝ} (hc : c∈Ioo (0:ℝ) 1)
    (hlate : ∀ᶠ k : ℕ in atTop, ∀ᶠ n : ℕ in atTop, μ.real (B k n)<c^k) :
    ∃ A : ℕ→ℕ, ∀ n : ℕ→ℕ, (∀ᶠ k : ℕ in atTop, A k ≤ n k) →
      ∀ᵐ ω ∂μ, ∀ᶠ k : ℕ in atTop, ω∉B k (n k) := by
  classical
  obtain ⟨K,hK⟩ := eventually_atTop.mp hlate
  have hex (k : ℕ) : ∃ a : ℕ, K ≤ k → ∀ n ≥ a, μ.real (B k n) < c^k := by
    by_cases hk : K ≤ k
    · obtain ⟨a,ha⟩ := eventually_atTop.mp (hK k hk)
      exact ⟨a,fun _ => ha⟩
    · exact ⟨0,fun h => (hk h).elim⟩
  choose A hA using hex
  refine ⟨A,?_⟩
  intro n hn
  have hsum : Summable (fun k => μ.real (B k (n k))) := by
    apply (summable_geometric_of_lt_one hc.1.le hc.2).of_norm_bounded_eventually_nat
    filter_upwards [eventually_ge_atTop K,hn] with k hk hnk
    rw [Real.norm_of_nonneg measureReal_nonneg]
    exact (hA k hk _ hnk).le
  have ha : ∀ᵐ ω ∂μ, ∀ᶠ k : ℕ in atTop, ω∉B k (n k) := by
    apply ae_eventually_notMem
    simpa only [ofReal_measureReal (measure_ne_top μ _)] using hsum.tsum_ofReal_ne_top
  exact ha

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
  haveI : IsProbabilityMeasure pathPauliDisorderLaw := by unfold pathPauliDisorderLaw; infer_instance
  have hgeo : ∀ᶠ k : ℕ in atTop, ∀ᶠ n : ℕ in atTop, pathPauliDisorderLaw.real (B k n)<c^k := by
    filter_upwards [hlate] with k hk
    have hdim : k ≤ 2^(k+3)-3 := by
      have := Nat.lt_two_pow_self (n:=k+3)
      omega
    exact hk.mono fun n hn => hn.trans_le (pow_le_pow_of_le_one hc.1.le hc.2.le hdim)
  obtain ⟨A,hA⟩ := frozen_event_cutoff pathPauliDisorderLaw B hc hgeo
  refine ⟨A,fun n hn => ?_⟩
  filter_upwards [hA n hn] with ω hω
  exact hω.mono fun k hk => lt_of_not_ge hk

#print axioms gaussian_frozen_antipodal_wait
end
end GaloisForLFunctions.HTGeometry.SpectralJets.SelectedDates.AlgebraicCurves.SingleHarmonics.AntipodalHorizons
