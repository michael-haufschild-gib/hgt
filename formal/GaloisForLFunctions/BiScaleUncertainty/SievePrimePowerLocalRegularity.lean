import GaloisForLFunctions.BiScaleUncertainty.SieveLocalVisibilityClassification
import GaloisForLFunctions.BiScaleUncertainty.SievePrimePowerVisibility
import GaloisForLFunctions.TransHorizonIncidenceMechanics.FiniteMultiplicativeObservationState
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Set.Finite.Basic

/-! Prime-factor width controls local regularity even among sources of maximal least period. -/

open scoped BigOperators Classical
open Finset
open GaloisForLFunctions.BezoutValuationIncidence
open GaloisForLFunctions.TransHorizonIncidenceMechanics
noncomputable section
namespace GaloisForLFunctions.BiScaleUncertainty.SieveMoments.LinearVisibility
open ValuationPhase ParityNeighborhood
set_option autoImplicit false

/-- Actual divisor weights retaining order one and every admitted prime power. -/
def primePowerWeights (N : ℕ) : ℕ → ℝ :=
  RHTower.pmRamanujanResidueCoeff (fun q => if q ∈ primePowerOrders N then 2 else 0) N

/-- A comparison source with every admitted coordinate equal to two. -/
def fullWeights (N : ℕ) : ℕ → ℝ :=
  RHTower.pmRamanujanResidueCoeff (fun _ => 2) N

theorem coordinate_primePowerWeights (N q : ℕ) :
    selbergMultiplesCoord N (primePowerWeights N) q =
      if q ∈ primePowerOrders N then 2 else 0 := by
  rw [primePowerWeights, selbergMultiplesCoord_ramanujan_inverse]
  by_cases hq : q ∈ Icc 1 N
  · rw [if_pos hq]
  · have hs : q ∉ primePowerOrders N := fun h => hq (mem_filter.mp h).1
    simp [hq, hs]

theorem coordinate_fullWeights (N q : ℕ) :
    selbergMultiplesCoord N (fullWeights N) q = if q ∈ Icc 1 N then 2 else 0 :=
  selbergMultiplesCoord_ramanujan_inverse N _ q

theorem activeModes_primePowerWeights (N : ℕ) :
    activeModes N (primePowerWeights N) = primePowerOrders N := by
  ext q
  simp only [activeModes, mem_filter, coordinate_primePowerWeights]
  by_cases hq : q ∈ primePowerOrders N
  · simp [hq, (mem_filter.mp hq).1]
  · simp [hq]

theorem activeModes_fullWeights (N : ℕ) : activeModes N (fullWeights N) = Icc 1 N := by
  ext q
  simp [activeModes, coordinate_fullWeights]

theorem topOrder_mem_primePowerOrders (N : ℕ) (hN : 2 ≤ N) :
    TopAnchor.topOrder N ∈ primePowerOrders N := by
  refine mem_filter.mpr ⟨TopAnchor.topOrder_mem N hN, ?_⟩
  by_cases hk : Nat.log 2 N = 0
  · simp [TopAnchor.topOrder, hk]
  · simp [TopAnchor.topOrder, Nat.primeFactors_prime_pow hk Nat.prime_two]

/-- Every missing mode is visible precisely when no admitted order has width six or more. -/
theorem prime_all_visible_iff (N : ℕ) :
    (∀ q ∈ Icc 1 N, q ∉ activeModes N (primePowerWeights N) →
      Visible N (activeModes N (primePowerWeights N)) q) ↔
    ∀ q ∈ Icc 1 N, q.primeFactors.card ≤ 5 := by
  rw [activeModes_primePowerWeights]
  constructor
  · intro h q hq
    by_cases hs : q ∈ primePowerOrders N
    · exact (mem_filter.mp hs).2.trans (by decide)
    · exact width_le_five_of_visible N q (h q hq hs)
  · intro h q hq _
    exact visible_of_width_le_five N q hq (h q hq)

/-- The exact local exponent of the actual prime-power source. -/
def primePowerExponent (N : ℕ) : ℝ :=
  if ∀ q ∈ Icc 1 N, q.primeFactors.card ≤ 5 then 1 else 1/3

/-- Full raw fifth/sixth arrays have the sharp width-dependent local inverse exponent. -/
theorem sharp_primePower_exponent (N : ℕ) (hN : 2 ≤ N) :
    LocalPairwiseHolder N (primePowerWeights N) (primePowerExponent N) ∧
      ∀ β : ℝ, primePowerExponent N < β → ¬LocalPairwiseHolder N (primePowerWeights N) β := by
  have hb : selbergMultiplesCoord N (primePowerWeights N) (TopAnchor.topOrder N) ≠ 0 := by
    rw [coordinate_primePowerWeights, if_pos (topOrder_mem_primePowerOrders N hN)]
    norm_num
  have hh := highest_stratum_sharp_exponent N hN (primePowerWeights N) hb
  by_cases hw : ∀ q ∈ Icc 1 N, q.primeFactors.card ≤ 5
  · simpa only [prime_all_visible_iff, primePowerExponent, if_pos hw] using hh
  · simpa only [prime_all_visible_iff, primePowerExponent, if_neg hw] using hh

/-- The fully supported comparison source always has sharp linear local recovery. -/
theorem sharp_full_exponent (N : ℕ) (hN : 2 ≤ N) :
    LocalPairwiseHolder N (fullWeights N) 1 ∧
      ∀ β : ℝ, 1 < β → ¬LocalPairwiseHolder N (fullWeights N) β := by
  have hb : selbergMultiplesCoord N (fullWeights N) (TopAnchor.topOrder N) ≠ 0 := by
    rw [coordinate_fullWeights, if_pos (TopAnchor.topOrder_mem N hN)]
    norm_num
  refine ⟨local_lipschitz_of_visibility N _ ?_, not_above_one N hN _ hb⟩
  intro q hq hmissing
  exact False.elim (hmissing (by rw [activeModes_fullWeights]; exact hq))

/-- Connect the existing gcd fixed-point period theorem to the actual coordinate support. -/
theorem periodic_iff_active_orders (N h : ℕ) (b : ℕ → ℝ) :
    Function.Periodic (sieveSeq N b) h ↔ ∀ q ∈ activeModes N b, q ∣ h := by
  constructor
  · intro hp q hq
    have hfix := (sieveGcdProjection_eq_zero_stride_iff N h b).mpr hp
    have hc := congrArg (fun c => selbergMultiplesCoord N c q) hfix
    rw [selbergMultiplesCoord_gcdProjection, selbergMultiplesCoord_gcdProjection,
      if_pos (dvd_zero q)] at hc
    by_contra hnot
    rw [if_neg hnot] at hc
    exact (mem_filter.mp hq).2 hc.symm
  · intro hh
    apply (sieveGcdProjection_eq_zero_stride_iff N h b).mp
    have he : ∀ d ∈ Icc 1 N, sieveGcdProjection N h b d = sieveGcdProjection N 0 b d := by
      apply (sieve_active_coefficients_eq_iff N _ _).mpr
      intro q _
      rw [selbergMultiplesCoord_gcdProjection, selbergMultiplesCoord_gcdProjection,
        if_pos (dvd_zero q)]
      by_cases hdiv : q ∣ h
      · rw [if_pos hdiv]
      · rw [if_neg hdiv, coordinate_zero_of_not_active N b q
          (fun hq => hdiv (hh q hq))]
    funext d
    by_cases hd : d ∈ Icc 1 N
    · exact he d hd
    · simp [sieveGcdProjection, hd]

/-- Retaining all primary orders forces exactly the maximal cutoff period lattice. -/
theorem periodic_iff_horizon_of_primary (N h : ℕ) (b : ℕ → ℝ)
    (hs : primePowerOrders N ⊆ activeModes N b) :
    Function.Periodic (sieveSeq N b) h ↔ horizonObservationModulus N ∣ h := by
  rw [periodic_iff_active_orders]
  constructor
  · intro hh
    exact Finset.lcm_dvd (all_orders_dvd_of_primary_orders N h (fun q hq => hh q (hs hq)))
  · intro hh q hq
    exact (Finset.dvd_lcm (f := id) (mem_filter.mp hq).1).trans hh

/-- The existing least-period invariant equals the existing full horizon modulus. -/
theorem leastPeriod_eq_horizon_of_primary (N : ℕ) (b : ℕ → ℝ)
    (hs : primePowerOrders N ⊆ activeModes N b) :
    sieveLeastPeriod N b = horizonObservationModulus N := by
  apply Nat.dvd_antisymm
  · exact (sieveSeq_periodic_iff_leastPeriod_dvd N _ b).mp
      ((periodic_iff_horizon_of_primary N _ b hs).mpr (dvd_refl _))
  · exact (periodic_iff_horizon_of_primary N _ b hs).mp
      ((sieveSeq_periodic_iff_leastPeriod_dvd N _ b).mpr (dvd_refl _))

theorem primePower_leastPeriod (N : ℕ) :
    sieveLeastPeriod N (primePowerWeights N) = horizonObservationModulus N := by
  apply leastPeriod_eq_horizon_of_primary
  rw [activeModes_primePowerWeights]

theorem full_leastPeriod (N : ℕ) :
    sieveLeastPeriod N (fullWeights N) = horizonObservationModulus N := by
  apply leastPeriod_eq_horizon_of_primary
  rw [activeModes_fullWeights]
  exact filter_subset _ _

/-- Both families retain exactly the same maximal dyadic depth. -/
theorem prime_full_same_depth (N : ℕ) (hN : 2 ≤ N) :
    activeDepth N (primePowerWeights N) = activeDepth N (fullWeights N) := by
  have hp : selbergMultiplesCoord N (primePowerWeights N) (TopAnchor.topOrder N) ≠ 0 := by
    rw [coordinate_primePowerWeights, if_pos (topOrder_mem_primePowerOrders N hN)]
    norm_num
  have hf : selbergMultiplesCoord N (fullWeights N) (TopAnchor.topOrder N) ≠ 0 := by
    rw [coordinate_fullWeights, if_pos (TopAnchor.topOrder_mem N hN)]
    norm_num
  rw [TopAnchor.activeDepth_eq_top N hN _ hp, TopAnchor.activeDepth_eq_top N hN _ hf]

private theorem exists_cutoff_width_six : ∃ N : ℕ, 2 ≤ N ∧ N.primeFactors.card = 6 := by
  obtain ⟨s, hs, hcard⟩ := Nat.infinite_setOf_prime.exists_subset_card_eq 6
  have hp : ∀ p ∈ s, p.Prime := fun p hp => hs hp
  have hfac : (∏ p ∈ s, p).primeFactors = s := Nat.primeFactors_prod hp
  have hpos : 1 < ∏ p ∈ s, p := Nat.nonempty_primeFactors.mp (by
    rw [hfac]
    exact Finset.card_pos.mp (by omega))
  exact ⟨∏ p ∈ s, p, hpos, by rw [hfac, hcard]⟩

/-- Maximal period and dyadic depth do not determine the sharp local inverse exponent. -/
theorem exists_same_period_depth_different_exponents :
    ∃ N : ℕ, 2 ≤ N ∧
      sieveLeastPeriod N (primePowerWeights N) = horizonObservationModulus N ∧
      sieveLeastPeriod N (fullWeights N) = horizonObservationModulus N ∧
      activeDepth N (primePowerWeights N) = activeDepth N (fullWeights N) ∧
      (LocalPairwiseHolder N (fullWeights N) 1 ∧
        ∀ β : ℝ, 1 < β → ¬LocalPairwiseHolder N (fullWeights N) β) ∧
      (LocalPairwiseHolder N (primePowerWeights N) (1/3) ∧
        ∀ β : ℝ, 1/3 < β → ¬LocalPairwiseHolder N (primePowerWeights N) β) := by
  obtain ⟨N, hN, hw⟩ := exists_cutoff_width_six
  have hnot : ¬∀ q ∈ Icc 1 N, q.primeFactors.card ≤ 5 := by
    intro hh
    have := hh N (mem_Icc.mpr ⟨by omega, le_refl _⟩)
    omega
  have he : primePowerExponent N = 1/3 := if_neg hnot
  refine ⟨N, hN, primePower_leastPeriod N, full_leastPeriod N,
    prime_full_same_depth N hN, sharp_full_exponent N hN, ?_⟩
  simpa only [he] using sharp_primePower_exponent N hN

end GaloisForLFunctions.BiScaleUncertainty.SieveMoments.LinearVisibility
