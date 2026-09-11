import GaloisForLFunctions.RHTower.XiGammaSixWoldJordanNegativeMassRepair

/-!
# Full-edge L1 separation from one complete coherent repair

The actual positive transposed row has zero anchor marginal. Its difference
from the original normalized row stays at full-edge variation distance at
least `(1 - 2 * K) / 3` from every complete coherent packet. Eventually the
lower bound is `1 / 6`, uniformly over all profiles and finite prime sets.

The source mechanism is the preceding negative-mass retention theorem: an L1
perturbation of a nonnegative target controls both its introduced negative
mass and its anchor error. The result strengthens exact nonmembership and
does not identify the physical domain, comparison topology, or fixed reader.
It does not prove RH.
-/

open Complex Filter Function Set Topology
open scoped BigOperators
namespace RHTower.HedenmalmThetaSource
noncomputable section

/-- Full edge variation, before the left-prime contraction can cancel coefficients. -/
def deningerBigWittEdgeVariation
    (f : DeningerCalderonWittCrossPrimePacketIndex →₀ ℂ) : ℝ :=
  ∑ i ∈ f.support, ‖f i‖

theorem deningerBigWittEdgeVariation_finset_le
    (f : DeningerCalderonWittCrossPrimePacketIndex →₀ ℂ)
    (s : Finset DeningerCalderonWittCrossPrimePacketIndex) :
    (∑ i ∈ s, ‖f i‖) ≤ deningerBigWittEdgeVariation f := by
  classical
  have heq : deningerBigWittEdgeVariation f = ∑ i ∈ f.support ∪ s, ‖f i‖ :=
    Finsupp.sum_of_support_subset f Finset.subset_union_left (fun _ z => ‖z‖) (by intros; simp)
  rw [heq]
  exact Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_right
    (fun i hi his => norm_nonneg _)

/-- A perturbation of a positive packet pays for every negative real coefficient. -/
theorem deningerBigWittNegativeRealMass_add_le_variation
    (f u : DeningerCalderonWittCrossPrimePacketIndex →₀ ℂ) (hf : ∀ i, 0 ≤ (f i).re) :
    deningerBigWittNegativeRealMass (f + u) ≤ deningerBigWittEdgeVariation u := by
  classical
  calc
    _ ≤ ∑ i ∈ (f + u).support, ‖u i‖ := by
      apply Finset.sum_le_sum
      intro i hi
      rw [Finsupp.add_apply, Complex.add_re]
      apply max_le _ (norm_nonneg _)
      have hre := Complex.re_le_norm (-u i)
      rw [Complex.neg_re, norm_neg] at hre
      linarith [hf i]
    _ ≤ _ := deningerBigWittEdgeVariation_finset_le u _

/-- Retained real marginal mass is bounded by the full edge variation. -/
theorem deningerBigWittLeftPrimeMarginal_re_le_edgeVariation
    (f : DeningerCalderonWittCrossPrimePacketIndex →₀ ℂ) (p : Nat.Primes) :
    (deningerBigWittLeftPrimeMarginal f p).re ≤ deningerBigWittEdgeVariation f := by
  classical
  have hm : primeLabelledEnergyReporter (fun q => if q = p then 1 else 0) f =
      deningerBigWittLeftPrimeMarginal f p := by
    rw [primeLabelledEnergyReporter_eq_marginal, finitePrimeMarginalEnergy_indicator]
  rw [← hm, primeLabelledEnergyReporter_re_sum]
  apply Finset.sum_le_sum
  intro i hi
  by_cases hip : i.1.1 = p
  · simpa [hip] using Complex.re_le_norm (f i)
  · simp [hip]

/-- A positive target with zero anchor cannot be approximated by one joint complete repair
without paying a full-edge variation error. -/
theorem deningerBigWittWoldPositiveTarget_coherent_distance_bound
    (a n : ℕ) (f : DeningerCalderonWittCrossPrimePacketIndex →₀ ℂ)
    (hf : ∀ i, 0 ≤ (f i).re)
    (hm : deningerBigWittLeftPrimeMarginal f (nthPrimeSubtype a) = 0)
    (b : Nat.Primes → ℂ) (s : Finset Nat.Primes) :
    1 - 2 * deningerBigWittWoldCoherentRemovalBudget a n ≤
      3 * deningerBigWittEdgeVariation
        ((deningerBigWittWoldFixedLeftRightEdgeNormalizedPacket a n - f) -
          deningerBigWittCrossPairFiniteRightLegPacket b s) := by
  let u := (deningerBigWittWoldFixedLeftRightEdgeNormalizedPacket a n - f) -
    deningerBigWittCrossPairFiniteRightLegPacket b s
  let g := deningerBigWittWoldFixedLeftRightEdgeNormalizedPacket a n -
    deningerBigWittCrossPairFiniteRightLegPacket b s
  have heq : g = f + u := by dsimp [g,u]; abel
  have hneg : deningerBigWittNegativeRealMass g ≤ deningerBigWittEdgeVariation u := by
    rw [heq]
    exact deningerBigWittNegativeRealMass_add_le_variation f u hf
  have hmargin : deningerBigWittLeftPrimeMarginal g (nthPrimeSubtype a) =
      deningerBigWittLeftPrimeMarginal u (nthPrimeSubtype a) := by
    have hadd : deningerBigWittLeftPrimeMarginal (f + u) =
        deningerBigWittLeftPrimeMarginal f + deningerBigWittLeftPrimeMarginal u :=
      Finsupp.mapDomain_add
    rw [heq, hadd, Finsupp.add_apply, hm, zero_add]
  have hvar := deningerBigWittLeftPrimeMarginal_re_le_edgeVariation u (nthPrimeSubtype a)
  have hret := (deningerBigWittWoldSignedRepair_retained_mass_bounds a n b s).1
  change 1 - 2 * (deningerBigWittWoldCoherentRemovalBudget a n + deningerBigWittNegativeRealMass g) ≤
    (deningerBigWittLeftPrimeMarginal g (nthPrimeSubtype a)).re at hret
  rw [hmargin] at hret
  change 1 - 2 * deningerBigWittWoldCoherentRemovalBudget a n ≤ 3 * deningerBigWittEdgeVariation u
  linarith

/-- The actual transposed repair is separated from every complete coherent packet in full edge L1. -/
theorem deningerBigWittWoldTransposedRepair_coherent_distance_lower
    (a n : ℕ) (b : Nat.Primes → ℂ) (s : Finset Nat.Primes) :
    (1 - 2 * deningerBigWittWoldCoherentRemovalBudget a n) / 3 ≤
      deningerBigWittEdgeVariation
        ((deningerBigWittWoldFixedLeftRightEdgeNormalizedPacket a n -
          deningerBigWittWoldTransposedRow a n) - deningerBigWittCrossPairFiniteRightLegPacket b s) := by
  apply (div_le_iff₀ (show (0 : ℝ) < 3 by norm_num)).mpr
  have hpos : ∀ i, 0 ≤ (deningerBigWittWoldTransposedRow a n i).re := by
    intro i
    obtain ⟨w,hw,hval⟩ := deningerBigWittWoldTransposedRow_nonneg a n i
    simpa only [hval, Complex.ofReal_re] using hw
  simpa only [mul_comm] using deningerBigWittWoldPositiveTarget_coherent_distance_bound
    a n (deningerBigWittWoldTransposedRow a n) hpos
    (deningerBigWittWoldTransposedRow_anchor_marginal a n) b s

/-- The eventual lower distance is uniform over every profile and every finite prime set. -/
theorem deningerBigWittWoldTransposedRepair_eventually_coherent_distance_lower (a : ℕ) :
    ∀ᶠ n in atTop, ∀ (b : Nat.Primes → ℂ) (s : Finset Nat.Primes),
      (1 / 6 : ℝ) ≤ deningerBigWittEdgeVariation
        ((deningerBigWittWoldFixedLeftRightEdgeNormalizedPacket a n -
          deningerBigWittWoldTransposedRow a n) - deningerBigWittCrossPairFiniteRightLegPacket b s) := by
  have hK := (tendsto_deningerBigWittWoldCoherentRemovalBudget a).eventually
    (gt_mem_nhds (show (0 : ℝ) < 1 / 4 by norm_num))
  filter_upwards [hK] with n hn
  intro b s
  have hbound := deningerBigWittWoldTransposedRepair_coherent_distance_lower a n b s
  nlinarith

/-- Even moving jointly complete packets cannot approximate the positive transposed repair in L1. -/
theorem deningerBigWittWoldTransposedRepair_not_tendsto_coherent_distance_zero
    (a : ℕ) (b : ℕ → Nat.Primes → ℂ) (s : ℕ → Finset Nat.Primes) :
    ¬ Tendsto (fun n => deningerBigWittEdgeVariation
      ((deningerBigWittWoldFixedLeftRightEdgeNormalizedPacket a n -
        deningerBigWittWoldTransposedRow a n) -
          deningerBigWittCrossPairFiniteRightLegPacket (b n) (s n))) atTop (nhds 0) := by
  intro hlim
  have hsmall := hlim.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / 6 by norm_num))
  have hlarge := deningerBigWittWoldTransposedRepair_eventually_coherent_distance_lower a
  obtain ⟨n,hn,hm⟩ := (hsmall.and hlarge).exists
  exact (not_lt_of_ge (hm (b n) (s n))) hn

end
end RHTower.HedenmalmThetaSource
