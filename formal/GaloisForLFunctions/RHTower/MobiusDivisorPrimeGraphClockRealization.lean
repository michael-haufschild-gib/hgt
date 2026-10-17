import GaloisForLFunctions.RHTower.MobiusDivisorClockGraphCone
import GaloisForLFunctions.RHTower.PrimePositiveClockRealization
import GaloisForLFunctions.RHTower.CHMDStationaryLocalSmoothCore
import GaloisForLFunctions.RHTower.CHMDFullJumpCoreDensity

/-! # Actual-prime synthesis in the complete arithmetic source graph

Every graph target is approximated by distinct actual prime clocks with the
literal common-scale weights and vanishing graph diagonal cost. A canonical
compact cutoff is fixed before the sufficiently large common prime scale.
-/

noncomputable section
open MeasureTheory Set Filter Topology
open GaloisForLFunctions.HTGeometry

namespace RHTower
open CHMDDoobGraph

def criticalPrimeGraphClockAtom (χ : ℝ → ℝ) (hχ : BoundedVariationOn χ univ)
    (N p : ℕ) : SourceGraph := PrimePreparation.clockAtom (criticalClockGraph χ hχ) N p

theorem eventually_exists_criticalPrimeGraphClock_compact_realization
    (χ : ℝ → ℝ) (hχ : BoundedVariationOn χ univ) (hcχ : Continuous χ)
    (hsχ : HasCompactSupport χ) (v : ℝ → ℝ) (hv : ContDiff ℝ 2 v)
    (hsv : HasCompactSupport v) (hfix : ∀ x, χ x * v x = v x) (T : ℝ)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∃ S : Finset ℕ,
      (∀ p ∈ S, p.Prime ∧ Real.sqrt N < p ∧ T < Real.log ((N : ℝ) / p)) ∧
      ‖(∑ p ∈ S, criticalPrimeGraphClockAtom χ hχ N p) - compactLift v hv hsv‖ < ε ∧
      (∑ p ∈ S, ‖criticalPrimeGraphClockAtom χ hχ N p‖ ^ 2) < ε := by
  have hbv := boundedVariationOn_of_contDiff_compact (hv.of_le (by norm_num)) hsv
  have hc := criticalClockGraph_positiveCone_contains_bvTarget χ v hχ hbv
    hcχ hv.continuous hsχ hfix T
  have he : bvLift v hbv = compactLift v hv hsv := by
    apply source_projection_injective
    rfl
  rw [he] at hc
  exact PrimePreparation.eventually_exists_prime_clock_synthesis (criticalClockGraph χ hχ)
    (continuous_criticalClockGraph χ hχ hcχ hsχ) T (compactLift v hv hsv) hc hε

def canonicalPrimeGraphClockAtom (k N p : ℕ) : SourceGraph :=
  criticalPrimeGraphClockAtom (cutoff k)
    (boundedVariationOn_of_contDiff_compact ((cutoff_contDiff k).of_le (by norm_num))
      (cutoff_hasCompactSupport k)) N p

/-- Every vector of the original complete arithmetic graph is synthesized by
distinct actual primes. The cutoff depends on the target and tolerance and is
fixed before N. No graph-admission or positive-approximation premise remains. -/
theorem exists_cutoff_eventually_criticalPrimeGraphClock_realization
    (q : SourceGraph) (T : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ k : ℕ, ∀ᶠ N : ℕ in atTop, ∃ S : Finset ℕ,
      (∀ p ∈ S, p.Prime ∧ Real.sqrt N < p ∧ T < Real.log ((N : ℝ) / p)) ∧
      ‖(∑ p ∈ S, canonicalPrimeGraphClockAtom k N p) - q‖ < ε ∧
      (∑ p ∈ S, ‖canonicalPrimeGraphClockAtom k N p‖ ^ 2) < ε := by
  obtain ⟨w, hw, hd⟩ := dense_compactTests.exists_dist_lt q
    (show (0 : ℝ) < ε / 2 by positivity)
  obtain ⟨v, hv, hsv, rfl⟩ := hw
  rw [dist_comm, dist_eq_norm] at hd
  obtain ⟨k, hfix⟩ := exists_cutoff_fix_compact hsv
  have hbv := boundedVariationOn_of_contDiff_compact
    ((cutoff_contDiff k).of_le (by norm_num)) (cutoff_hasCompactSupport k)
  have he := eventually_exists_criticalPrimeGraphClock_compact_realization (cutoff k) hbv
    (cutoff_contDiff k).continuous (cutoff_hasCompactSupport k) v hv hsv hfix T
    (show (0 : ℝ) < ε / 2 by positivity)
  refine ⟨k, ?_⟩
  filter_upwards [he] with N hN
  obtain ⟨S, hS, happ, hdiag⟩ := hN
  refine ⟨S, hS, ?_, hdiag.trans (by linarith only [hε])⟩
  calc
    _ = ‖((∑ p ∈ S, canonicalPrimeGraphClockAtom k N p) - compactLift v hv hsv) +
        (compactLift v hv hsv - q)‖ := by congr 1; abel
    _ ≤ ‖(∑ p ∈ S, canonicalPrimeGraphClockAtom k N p) - compactLift v hv hsv‖ +
        ‖compactLift v hv hsv - q‖ := norm_add_le _ _
    _ < ε := (add_lt_add happ hd).trans_eq (by ring)

end RHTower
