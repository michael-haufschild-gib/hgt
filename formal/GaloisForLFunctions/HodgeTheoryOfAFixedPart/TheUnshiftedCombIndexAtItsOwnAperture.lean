import GaloisForLFunctions.HodgeTheoryOfAFixedPart.SmoothRealPacketsCaptureTheApertureIndex
import GaloisForLFunctions.HodgeTheoryOfAFixedPart.SmoothSamplesFitTheOriginalRatio
import GaloisForLFunctions.HodgeTheoryOfAFixedPart.UnshiftedCombIndexFitsEveryWiderAperture

/-!
# The unshifted comb index at its own aperture

At every fixed integer ratio, the eventual comb index lies between the
negative and nonpositive dimensions of the exact restricted Weil form.
Away from a null mode these bounds coincide. The lower bound samples a
smooth negative family in the original window; the upper bound uses tight
block transfer and simultaneous aperture and energy stability.
-/

noncomputable section

open Finset Filter Topology Matrix Zeta23

namespace GaloisForLFunctions.HodgeTheoryOfAFixedPart

open HTGeometry AbsoluteGeometryOfSpecZ ArithmeticCastelnuovoSeveri ArithmeticIndexDescent
open ArithmeticContinuationAndCriticalEnergy
open _root_.RHTower _root_.RHTower.PaperRestrictedWeil

/-- Every restricted negative square appears eventually on the original
comb window, with no mass margin. -/
theorem eventually_negativeRank_le_originalRatio_combIndex
    {Q : ℕ} (hQ : 1 ≤ Q) (A : SuzukiPositiveAperture)
    (hA : Real.log Q = 2 * A.1) :
    ∀ᶠ N : ℕ in atTop,
      (negativeRank A 0 : ℕ∞) ≤ robustCombIndex (Ioc N (Q * N)) 0 := by
  obtain ⟨m, g, hg, hgc, hgs, hindex⟩ := exists_real_smooth_packets_capture_negativeRank A
  let f : Fin m → realTests := fun i =>
    ⟨g i, (hg i).of_le (WithTop.coe_le_coe.mpr le_top), hgc i⟩
  let c := Real.log 3 + A.1
  let F : Fin m → realTests := fun i => translatedPacketTest c (f i)
  have hQpos : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hlog : Real.log ((3 * Q : ℕ) : ℝ) = Real.log 3 + 2 * A.1 := by
    rw [Nat.cast_mul, Nat.cast_ofNat, Real.log_mul (by norm_num) hQpos.ne', hA]
  have hs : ∀ i, tsupport (F i).1 ⊆
      Set.Ioo (Real.log 3) (Real.log ((3 * Q : ℕ) : ℝ)) := by
    intro i
    have ht : tsupport (F i).1 ⊆ (fun u => u - c) ⁻¹' tsupport (f i).1 := by
      apply closure_minimal _ (isClosed_closure.preimage (continuous_id.sub continuous_const))
      intro u hu
      exact subset_closure hu
    intro u hu
    have h := hgs i (ht hu)
    rw [hlog]
    change -A.1 < u - c ∧ u - c < A.1 at h
    dsimp only [c] at h
    constructor <;> linarith only [h.1, h.2]
  have htranslation : complexWeilMixed F F = complexWeilMixed f f := by
    rw [← shiftedRealTestGram_zero, ← shiftedRealTestGram_zero]
    exact shiftedRealTestGram_translate 0 c f
  have hreal : complexWeilMixed f f =
      zeroGram zetaZeroConfig (fun i u => (g i u : ℂ)) := by
    ext i j
    exact realWeilForm_eq_zetaW (f i) (f j)
  have hfamily : negativeRank A 0 ≤ hermNegIndex (complexWeilMixed F F) := by
    rw [htranslation, hreal]
    exact hindex
  filter_upwards [eventually_realPacketIndex_le_originalRatio_combIndex hQ F hs] with N hN
  exact (ENat.coe_le_coe.mpr hfamily).trans hN

/-- The aperture belonging to a finite comb window of integer ratio `Q`. -/
def combRatioAperture (Q : ℕ) (hQ : 2 ≤ Q) : SuzukiPositiveAperture :=
  ⟨Real.log Q / 2, div_pos (Real.log_pos (by exact_mod_cast (show 1 < Q by omega)))
    (by norm_num)⟩

/-- At every fixed ratio, the eventual unshifted index lies between the
negative dimension and the full nonpositive dimension of its own aperture. -/
theorem eventually_unshiftedCombIndex_between (Q : ℕ) (hQ : 2 ≤ Q) :
    ∀ᶠ N : ℕ in atTop,
      (negativeRank (combRatioAperture Q hQ) 0 : ℕ∞) ≤
        robustCombIndex (Ioc N (Q * N)) 0 ∧
      robustCombIndex (Ioc N (Q * N)) 0 ≤
        ((negativeRank (combRatioAperture Q hQ) 0 +
          weilNullity (combRatioAperture Q hQ) 0 : ℕ) : ℕ∞) := by
  have hA : Real.log Q = 2 * (combRatioAperture Q hQ).1 := by
    dsimp only [combRatioAperture]
    ring
  exact (eventually_negativeRank_le_originalRatio_combIndex (by omega) _ hA).and
    (eventually_unshiftedCombIndex_le_rank_add_nullity (by omega) _ hA)

/-- At a nonresonant fixed ratio, the unshifted finite-comb index eventually
equals the exact restricted Weil index, without any sign assumption. -/
theorem eventually_unshiftedCombIndex_eq_of_nullity_zero (Q : ℕ) (hQ : 2 ≤ Q)
    (hnull : weilNullity (combRatioAperture Q hQ) 0 = 0) :
    ∀ᶠ N : ℕ in atTop,
      robustCombIndex (Ioc N (Q * N)) 0 =
        (negativeRank (combRatioAperture Q hQ) 0 : ℕ∞) := by
  filter_upwards [eventually_unshiftedCombIndex_between Q hQ] with N hN
  rw [hnull, add_zero] at hN
  exact le_antisymm hN.2 hN.1

end GaloisForLFunctions.HodgeTheoryOfAFixedPart
