import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheIndexAtAnApertureIsTheSumOfTheNullitiesBelowIt
import GaloisForLFunctions.HodgeTheoryOfAFixedPart.TheUnshiftedCombIndexAtItsOwnAperture
import GaloisForLFunctions.HodgeTheoryOfAFixedPart.TheRobustCombIndexCountsRightZeros
import GaloisForLFunctions.HodgeTheoryOfAFixedPart.TheApertureIndexCountsNoExtraZeros
import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.PacketMassGrams

/-!
# The null modes of the aperture path count the zeros right of the line

The far end of the aperture path. At the energy zero the index of Weil's restricted form
exhausts the zeros of `ζ` to the right of the critical line:

  `⨆_b negativeRank b 0 = #{ρ : Re ρ > ½}`   (`iSup_negativeRank_zero_eq_rightZeros`),

and by the index law of the path the same number is the total number of null modes:
`ζ` has at least `r` distinct zeros right of the line iff some finite set of apertures carries
`r` null modes in total (`nat_le_rightZeros_iff_exists_sum_nullity`).

The upper bound is the index law on smooth packets (continuation). For the lower bound, `r`
zeros right of the line give `r` robust negative directions of the comb on a window of some
integer ratio `Q` at large scales (continuation); without the margin these are at most the
index plus the nullity at the aperture `½ log Q`, which is at most the index at any larger
aperture.

**The index of step packets** (`negIndex_nestedStepGram_le_sum_nullity`). The Gram matrix of
Weil's form `𝔚_Q`, shifted by an energy, on the flat packets of nested windows inside
`(x₀, X]` has at most as many negative squares as the aperture path has null modes below any
aperture wider than `½ log(X/x₀)`: a step packet is a test of every wider aperture.
-/

open Finset Filter Zeta23

noncomputable section

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

open _root_.RHTower _root_.RHTower.PaperRestrictedWeil
open ArithmeticContinuationAndCriticalEnergy ArithmeticCastelnuovoSeveri HTGeometry
open HodgeTheoryOfAFixedPart (robustCombIndex complexCombForm combRatioAperture)

/-- A smaller margin admits more robust negative directions. -/
theorem robustCombIndex_anti {S : Finset ℕ} {η η' : ℝ} (h : η' ≤ η) :
    robustCombIndex S η ≤ robustCombIndex S η' := by
  refine iSup_le fun W => iSup_le fun hW => ?_
  refine le_iSup_of_le W (le_iSup_of_le (fun c hc hc0 => ?_) le_rfl)
  have h0 : 0 ≤ ∑ i, ‖c i‖ ^ 2 := Finset.sum_nonneg fun i _ => by positivity
  have h1 := hW c hc hc0
  have h2 := mul_le_mul_of_nonneg_right h h0
  linarith

/-- **Every zero right of the line is seen at some aperture.** -/
theorem exists_aperture_le_negativeRank {r : ℕ}
    (hr : (r : ℕ∞) ≤ (rightZeros zetaZeroConfig).encard) :
    ∃ b : SuzukiPositiveAperture, r ≤ negativeRank b 0 := by
  obtain ⟨K, hK, η, hη, hev⟩ :=
    (HodgeTheoryOfAFixedPart.nat_le_rightZeros_iff_eventual_robustCombIndex r).mp hr
  have hQ : 2 ≤ 3 * K + 1 := by omega
  obtain ⟨N, hN1, hN2⟩ :=
    (hev.and (HodgeTheoryOfAFixedPart.eventually_unshiftedCombIndex_between (3 * K + 1) hQ)).exists
  have hset : Ioc N ((3 * K + 1) * N) = Ioc N (N + 3 * K * N) := by
    congr 1
    ring
  rw [hset] at hN2
  obtain ⟨b, hbv⟩ : ∃ b : SuzukiPositiveAperture,
      b.1 = (combRatioAperture (3 * K + 1) hQ).1 + 1 :=
    ⟨⟨(combRatioAperture (3 * K + 1) hQ).1 + 1,
      by linarith [(combRatioAperture (3 * K + 1) hQ).2]⟩, rfl⟩
  have hjump := negativeRank_add_nullity_le_of_aperture_lt
    (a := combRatioAperture (3 * K + 1) hQ) (b := b) (by rw [hbv]; linarith) 0
  refine ⟨b, ENat.coe_le_coe.mp ?_⟩
  exact (hN1.trans ((robustCombIndex_anti hη.le).trans hN2.2)).trans (ENat.coe_le_coe.mpr hjump)

/-- **The far end of the aperture path.** The index at the energy zero exhausts the zeros of
`ζ` to the right of the critical line. -/
theorem iSup_negativeRank_zero_eq_rightZeros :
    ⨆ b : SuzukiPositiveAperture, (negativeRank b 0 : ℕ∞) =
      (rightZeros zetaZeroConfig).encard := by
  refine le_antisymm
    (iSup_le fun b => HodgeTheoryOfAFixedPart.negativeRank_zero_le_rightZeros b) ?_
  refine ENat.forall_natCast_le_iff_le.mp fun n hn => ?_
  obtain ⟨b, hb⟩ := exists_aperture_le_negativeRank hn
  exact le_iSup_of_le b (ENat.coe_le_coe.mpr hb)

/-- **The zeros right of the line are counted by the null modes of the aperture path.** `ζ` has
at least `r` distinct zeros right of the critical line iff some finite set of apertures carries
`r` null modes of Weil's form in total. -/
theorem nat_le_rightZeros_iff_exists_sum_nullity (r : ℕ) :
    (r : ℕ∞) ≤ (rightZeros zetaZeroConfig).encard ↔
      ∃ s : Finset SuzukiPositiveAperture, r ≤ ∑ a ∈ s, weilNullity a 0 := by
  constructor
  · intro hr
    obtain ⟨b, hb⟩ := exists_aperture_le_negativeRank hr
    exact ⟨resonantBelow b 0, by rwa [← negativeRank_eq_sum_nullity]⟩
  · rintro ⟨s, hs⟩
    -- an aperture above all members of `s`
    have hpos : 0 < 1 + ∑ a ∈ s, a.1 := by
      have : 0 ≤ ∑ a ∈ s, a.1 := Finset.sum_nonneg fun a _ => a.2.le
      linarith
    have hlt : ∀ a ∈ s, a.1 < 1 + ∑ a ∈ s, a.1 := fun a ha => by
      have := Finset.single_le_sum (f := fun a : SuzukiPositiveAperture => a.1)
        (fun a _ => a.2.le) ha
      linarith
    have h1 := sum_nullity_le_negativeRank s ⟨1 + ∑ a ∈ s, a.1, hpos⟩ 0 hlt
    exact (ENat.coe_le_coe.mpr (hs.trans h1)).trans
      (HodgeTheoryOfAFixedPart.negativeRank_zero_le_rightZeros _)

/-- The number of zeros right of the line as the supremum of the sums of the nullities. -/
theorem rightZeros_encard_eq_iSup_sum_nullity :
    (rightZeros zetaZeroConfig).encard =
      ⨆ b : SuzukiPositiveAperture, ((∑ a ∈ resonantBelow b 0, weilNullity a 0 : ℕ) : ℕ∞) := by
  rw [← iSup_negativeRank_zero_eq_rightZeros]
  exact iSup_congr fun b => by rw [negativeRank_eq_sum_nullity]

/-- **The index of step packets is bounded by the null modes of the wider apertures.** -/
theorem negIndex_nestedStepGram_le_sum_nullity {n Q x₀ X : ℕ} (hx₀ : 1 ≤ x₀) (E : ℝ)
    (x : Fin n → ℕ) (hx : ∀ i, x₀ ≤ x i ∧ x i ≤ X)
    (hQ : Real.log (X : ℝ) - Real.log x₀ < Real.log ((Q : ℝ) + 1))
    {A : SuzukiPositiveAperture} (hA : Real.log (X : ℝ) - Real.log x₀ < 2 * A.1) :
    hermNegIndex (shiftedPacketGram Q E (fun i => flatPacket x₀ (x i))) ≤
      ∑ a ∈ resonantBelow A E, weilNullity a E := by
  rw [← negativeRank_eq_sum_nullity]
  exact hermNegIndex_shiftedPacketGram_nested_le hx₀ E x hx hQ hA

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
