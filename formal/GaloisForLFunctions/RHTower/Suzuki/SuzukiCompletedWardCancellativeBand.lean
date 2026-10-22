import GaloisForLFunctions.RHTower.Suzuki.SuzukiCompletedWardLocalCancellationWindow

/-!
# Cancellative-band rigidity for completed Suzuki Ward cross terms

The completed wall has source sign `prime - regular`.  A negative cross contribution is the
only possible energy-lowering interaction.  This file proves that such an interaction is forced
into one multiplicative lag band: neither lag can be at least twice the other.  Thus distant
regular mass cannot be part of a cancellation argument for the literal source.
-/

open Set
open scoped NNReal

namespace GaloisForLFunctions.RHTower

noncomputable section

open _root_.RHTower

private theorem reporterSecant_secondLag_lt_two_first_of_gram_pos
    (p q : ℝ≥0) (hp : p ≠ 0)
    (hgram : 0 < suzukiReporterSecantCauchyGram p q) :
    q < 2 * p := by
  have hnot : ¬ suzukiReporterSecantTransitionSeparated p q :=
    (suzukiReporterSecantCauchyGram_pos_iff_not_transitionSeparated p q).mp hgram
  by_contra hq
  have hqle : 2 * p ≤ q := le_of_not_gt hq
  have hple : p ≤ 2 * p := by
    rw [two_mul]
    exact le_add_of_nonneg_right p.property
  have hpq : p ≤ q := hple.trans hqle
  have hdepth_lt : suzukiReporterSecantTransitionDepth ⟨p, hp⟩ < 2 * p := by
    exact_mod_cast (suzukiReporterSecantTransitionDepth_mem ⟨p, hp⟩).2
  have hdepth : suzukiReporterSecantTransitionDepth ⟨p, hp⟩ ≤ q :=
    hdepth_lt.le.trans hqle
  exact hnot (Or.inr (Or.inr (Or.inl ⟨hp, hpq, hdepth⟩)))

/-- A positive raw secant Gram has comparable lags: both ratios are strictly below two. -/
theorem suzukiReporterSecantCauchyGram_pos_lagComparable
    (p q : ℝ≥0)
    (hgram : 0 < suzukiReporterSecantCauchyGram p q) :
    q < 2 * p ∧ p < 2 * q := by
  have hp : p ≠ 0 := by
    intro hp
    rw [hp, suzukiReporterSecantCauchyGram_zero_left] at hgram
    exact (lt_irrefl (0 : ℝ)) hgram
  have hq : q ≠ 0 := by
    intro hq
    rw [hq, suzukiReporterSecantCauchyGram_comm,
      suzukiReporterSecantCauchyGram_zero_left] at hgram
    exact (lt_irrefl (0 : ℝ)) hgram
  constructor
  · exact reporterSecant_secondLag_lt_two_first_of_gram_pos p q hp hgram
  · rw [suzukiReporterSecantCauchyGram_comm] at hgram
    exact reporterSecant_secondLag_lt_two_first_of_gram_pos q p hq hgram

/-- A strictly energy-lowering completed-wall cross term forces positivity of the raw secant
Gram; source signs cannot manufacture cancellation where the Cauchy geometry has none. -/
theorem suzukiReporterSecantCauchyGram_pos_of_completedWardSignedCross_neg
    {c d : ℝ} {p q : ℝ≥0}
    (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hcross : suzukiCompletedWardSignedCross c d p q < 0) :
    0 < suzukiReporterSecantCauchyGram p q := by
  unfold suzukiCompletedWardSignedCross at hcross
  by_contra hgram
  have hgram' : suzukiReporterSecantCauchyGram p q ≤ 0 := le_of_not_gt hgram
  have hnonpos : c * suzukiReporterSecantCauchyGram p q * d ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos hc hgram') hd
  linarith

/-- **Cancellative-band rigidity.**  Every negative completed Ward cross contribution lies in
the factor-two lag band. -/
theorem suzukiCompletedWardSignedCross_neg_lagComparable
    {c d : ℝ} {p q : ℝ≥0}
    (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hcross : suzukiCompletedWardSignedCross c d p q < 0) :
    q < 2 * p ∧ p < 2 * q :=
  suzukiReporterSecantCauchyGram_pos_lagComparable p q
    (suzukiReporterSecantCauchyGram_pos_of_completedWardSignedCross_neg hc hd hcross)

/-- Literal prime--regular form of cancellative-band rigidity.  If this actual source pair
lowers the completed energy, its regular lag and its prime lag are necessarily comparable within
a factor two. -/
theorem suzukiNaturalPrimeRegularSignedCross_neg_lagComparable
    (N : ℕ) (i : Fin (N + 1)) (h : ℝ)
    (hh : h ≤ Real.log (N : ℝ))
    (hbase : unitRieszSuzukiBase ≤ h)
    (hcross : suzukiCompletedWardSignedCross
      (suzukiNaturalAperturePaddedWeight N i)
      (screwRegularKernel h)
      (suzukiNaturalAperturePaddedLag N i)
      (suzukiRegularWardLag (Real.log (N : ℝ)) h hh) < 0) :
    suzukiRegularWardLag (Real.log (N : ℝ)) h hh <
        2 * suzukiNaturalAperturePaddedLag N i ∧
      suzukiNaturalAperturePaddedLag N i <
        2 * suzukiRegularWardLag (Real.log (N : ℝ)) h hh := by
  exact suzukiCompletedWardSignedCross_neg_lagComparable
    (suzukiNaturalAperturePaddedWeight_nonneg N i)
    (screwRegularKernel_pos_of_unitRieszSuzukiBase_le hbase).le hcross

end

end GaloisForLFunctions.RHTower
