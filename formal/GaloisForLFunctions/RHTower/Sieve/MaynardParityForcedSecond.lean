import GaloisForLFunctions.RHTower.Sieve.MaynardDyadicBlockSelectedCount

/-!
# Parity forcing for Route-T physical packets

Spatial equation-(111) sees an amplitude band in its original cell indexing, whereas the selected
cell receiver counts reindexed even and odd fibres.  This module closes that interface exactly: a
large whole-band physical packet forces the second Maynard alternative for at least one reindexed
parity fibre, with no cardinality loss beyond the necessary half-packet threshold.
-/

noncomputable section
namespace RHTower.Sieve

/-- A large whole-band packet chooses a parity packet; its exact original/reindexed cardinality
identity then turns the corresponding two-way Route-T receiver into its second alternative. -/
theorem routeT_parity_second_alternative_of_large_packet
    {q K : ℕ} {B : Finset ℕ} {a : ℝ → ℂ}
    {lambda N R H D V T x alpha : ℝ}
    (hB : B ⊆ Finset.range (2 * K)) (ha : Continuous a)
    (hlambda : 0 < lambda) (hN : 0 < N) (hR : 0 < R) (hH : 0 < H)
    (hD : D ≤ ‖maynardFixedAmbientPhysicalDefectPacket B a lambda N R H 1‖)
    (hV : 0 < V)
    (hsource : ∀ m ∈ B, ∀ u ∈ Set.Icc (0 : ℝ) 1,
      ‖a ((m : ℝ) + u)‖ ≤ 2 * V)
    (hlog : 0 ≤ Real.log T)
    (hthreshold : 4 * V * x ^ (1 - alpha) ≤ (D / 2) * (Real.log T) ^ q)
    (heven : IsRouteTMaynardTwoAlternative q
      ((maynardEvenCellFibre B K).card : ℝ) T x alpha)
    (hodd : IsRouteTMaynardTwoAlternative q
      ((maynardOddCellFibre B K).card : ℝ) T x alpha) :
    ((maynardEvenCellFibre B K).card : ℝ) ≤
        T * x ^ (1 + routeTGapMomentNu - 2 * alpha) ∨
      ((maynardOddCellFibre B K).card : ℝ) ≤
        T * x ^ (1 + routeTGapMomentNu - 2 * alpha) := by
  have hparity := large_maynardFixedAmbientPhysicalDefectPacket_even_or_odd
    B ha hlambda hN hR hH hD
  rcases hparity with hevenLarge | hoddLarge
  · left
    have hevenSubset : maynardEvenCells B ⊆ B := Finset.filter_subset _ _
    have hevenSource : ∀ m ∈ maynardEvenCells B, ∀ u ∈ Set.Icc (0 : ℝ) 1,
        ‖a ((m : ℝ) + u)‖ ≤ 2 * V := by
      intro m hm u hu
      exact hsource m (hevenSubset hm) u hu
    have hevenUpper0 :=
      norm_maynardFixedAmbientPhysicalDefectPacket_le_two_mul_card_of_source_bound
        hlambda hN hR hH (show 0 ≤ 2 * V by positivity) hevenSource
    have hevenCard := card_maynardEvenCellFibre_eq_card_maynardEvenCells hB
    have hevenUpper :
        ‖maynardFixedAmbientPhysicalDefectPacket (maynardEvenCells B)
          a lambda N R H 1‖ ≤
          4 * V * ((maynardEvenCellFibre B K).card : ℝ) := by
      calc
        _ ≤ 2 * (2 * V) * ((maynardEvenCells B).card : ℝ) := hevenUpper0
        _ = 4 * V * ((maynardEvenCellFibre B K).card : ℝ) := by
          rw [hevenCard]
          ring
    exact routeT_second_alternative_of_large_amplitudeBand_packet
      hV hlog hevenLarge hevenUpper hthreshold heven
  · right
    have hoddSubset : maynardOddCells B ⊆ B := Finset.filter_subset _ _
    have hoddSource : ∀ m ∈ maynardOddCells B, ∀ u ∈ Set.Icc (0 : ℝ) 1,
        ‖a ((m : ℝ) + u)‖ ≤ 2 * V := by
      intro m hm u hu
      exact hsource m (hoddSubset hm) u hu
    have hoddUpper0 :=
      norm_maynardFixedAmbientPhysicalDefectPacket_le_two_mul_card_of_source_bound
        hlambda hN hR hH (show 0 ≤ 2 * V by positivity) hoddSource
    have hoddCard := card_maynardOddCellFibre_eq_card_maynardOddCells hB
    have hoddUpper :
        ‖maynardFixedAmbientPhysicalDefectPacket (maynardOddCells B)
          a lambda N R H 1‖ ≤
          4 * V * ((maynardOddCellFibre B K).card : ℝ) := by
      calc
        _ ≤ 2 * (2 * V) * ((maynardOddCells B).card : ℝ) := hoddUpper0
        _ = 4 * V * ((maynardOddCellFibre B K).card : ℝ) := by
          rw [hoddCard]
          ring
    exact routeT_second_alternative_of_large_amplitudeBand_packet
      hV hlog hoddLarge hoddUpper hthreshold hodd

end RHTower.Sieve
