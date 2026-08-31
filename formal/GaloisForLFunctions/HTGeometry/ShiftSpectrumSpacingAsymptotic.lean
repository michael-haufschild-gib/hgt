import GaloisForLFunctions.HTGeometry.ShiftSpectrumSpacing
import GaloisForLFunctions.HTGeometry.PolynomialPowerFiniteDifference

/-!
# Asymptotic spacing of the standard-twist lattice

The full standard-twist lattice has forward gap asymptotic
`q ^ (-(1 / d)) * m ^ (1 / d - 1)`.  This statement concerns the full lattice.  A
coefficient-supported spectrum can have larger gaps when intervening coefficients vanish.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Finset Set Asymptotics Topology

noncomputable section

private def forwardGapPacket : ℕ →₀ ℝ :=
  Finsupp.single 1 1 - Finsupp.single 0 1

private lemma forwardGapPacket_moment_zero :
    GaloisForLFunctions.stretchedMoment forwardGapPacket 0 = 0 := by
  rw [GaloisForLFunctions.stretchedMoment]
  unfold forwardGapPacket
  rw [Finsupp.sum_sub_index (by intros; ring)]
  simp

private lemma forwardGapPacket_moment_one :
    GaloisForLFunctions.stretchedMoment forwardGapPacket 1 = 1 := by
  rw [GaloisForLFunctions.stretchedMoment]
  unfold forwardGapPacket
  rw [Finsupp.sum_sub_index (by intros; ring)]
  norm_num

/-- The first forward difference of a nonconstant real power has its derivative as leading
asymptotic. -/
theorem realPower_forwardGap_isEquivalent {β : ℝ} (hβ : β ≠ 0) :
    (fun x : ℝ => (x + 1) ^ β - x ^ β) ~[atTop]
      (fun x : ℝ => β * x ^ (β - 1)) := by
  have h := GaloisForLFunctions.polynomialPowerFiniteDifference_isEquivalent
    (β := β) forwardGapPacket 1
      (by
        intro k hk
        interval_cases k
        exact forwardGapPacket_moment_zero)
      (by norm_num [forwardGapPacket_moment_one])
      (by simpa [descPochhammer] using hβ)
  convert h using 1
  · funext x
    rw [GaloisForLFunctions.polynomialPowerFiniteDifference]
    unfold forwardGapPacket
    rw [Finsupp.sum_sub_index (by intros; ring)]
    simp
  · funext x
    rw [GaloisForLFunctions.polynomialPowerDifferenceCoefficient,
      forwardGapPacket_moment_one]
    simp [descPochhammer]

/-- Exact leading asymptotic of the forward spacing in the full standard-twist spectral lattice. -/
theorem shiftSpectrumValue_forwardGap_isEquivalent
    {d q : ℝ} (hd : 0 < d) (hq : 0 < q) :
    (fun m : ℕ =>
        shiftSpectrumValue d q (m + 1) - shiftSpectrumValue d q m) ~[atTop]
      (fun m : ℕ => q ^ (-(1 / d)) * (m : ℝ) ^ (1 / d - 1)) := by
  have hreal := realPower_forwardGap_isEquivalent (one_div_ne_zero hd.ne')
  have hnat := hreal.comp_tendsto tendsto_natCast_atTop_atTop
  have hscaled := (IsEquivalent.refl
      (u := fun _m : ℕ => d / q ^ (1 / d))).smul hnat
  have hscaled' :
      (fun m : ℕ => d / q ^ (1 / d) *
          (((m : ℝ) + 1) ^ (1 / d) - (m : ℝ) ^ (1 / d))) ~[atTop]
        (fun m : ℕ => d / q ^ (1 / d) *
          ((1 / d) * (m : ℝ) ^ (1 / d - 1))) := by
    simpa only [Function.comp_apply, smul_eq_mul] using hscaled
  have hleft :
      (fun m : ℕ => d / q ^ (1 / d) *
          (((m : ℝ) + 1) ^ (1 / d) - (m : ℝ) ^ (1 / d))) =ᶠ[atTop]
        (fun m : ℕ =>
          shiftSpectrumValue d q (m + 1) - shiftSpectrumValue d q m) := by
    filter_upwards with m
    change d / q ^ (1 / d) *
        (((m : ℝ) + 1) ^ (1 / d) - (m : ℝ) ^ (1 / d)) =
      d * (((m + 1 : ℕ) : ℝ) / q) ^ (1 / d) -
        d * ((m : ℝ) / q) ^ (1 / d)
    rw [Real.div_rpow (Nat.cast_nonneg (m + 1)) hq.le,
      Real.div_rpow (Nat.cast_nonneg m) hq.le]
    push_cast
    ring
  have hright :
      (fun m : ℕ => d / q ^ (1 / d) *
          ((1 / d) * (m : ℝ) ^ (1 / d - 1))) =ᶠ[atTop]
        (fun m : ℕ => q ^ (-(1 / d)) * (m : ℝ) ^ (1 / d - 1)) := by
    filter_upwards with m
    rw [Real.rpow_neg hq.le]
    have hqpow : q ^ (1 / d) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hq _)
    field_simp [hd.ne', hqpow]
  exact (hscaled'.congr_left hleft).congr_right hright

end

end GaloisForLFunctions.HTGeometry
