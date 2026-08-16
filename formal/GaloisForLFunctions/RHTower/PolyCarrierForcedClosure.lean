import GaloisForLFunctions.RHTower.WallBlockSeries
import GaloisForLFunctions.RHTower.PolyDistortedHomogeneousThreshold

/-!
# The corrected direct theorem of the polynomial-carrier dimension wall

The prior Hardy claim assumed only polynomial group growth of degree `m`, which gives the
homogeneous squared density `O(|x|^{-1-2σ+2m})` — integrable exactly when `m < σ`.  An arbitrary
polynomial degree is *not* enough, and rough block forcing cannot repair a nonintegrable
homogeneous component: forcing changes only the particular solution.

The corrected statement `(15)` therefore pairs the two halves: below the Gamma shift the homogeneous
carrier is square integrable on both rays, and the particular part is square integrable by the
Gamma-wall block transfer.  Their sum is the shifted value.
-/

open MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace GaloisForLFunctions.RHTower

/-- **`(15)`: the corrected direct theorem.**  A homogeneous carrier whose polynomial group degree
is strictly below the Gamma shift is square integrable on both frequency rays, so a forced solution
whose particular part is square integrable is square integrable. -/
theorem memLp_two_of_polyCarrier_and_forced
    {X : Type*} [NormedAddCommGroup X] {u hom forced : ℝ → X} {C σ m L₀ : ℝ}
    (hL₀ : 0 < L₀) (hm : m < σ)
    (hsplit : ∀ x : ℝ, u x = hom x + forced x)
    (hu : AEStronglyMeasurable u (volume : Measure ℝ))
    (hhom : AEStronglyMeasurable hom (volume : Measure ℝ))
    (hposray : ∀ x ∈ Ioi L₀, ‖hom x‖ ≤ C * x ^ (-(1 / 2 + σ - m)))
    (hnegray : ∀ x ∈ Ioi L₀, ‖hom (-x)‖ ≤ C * x ^ (-(1 / 2 + σ - m)))
    (hmid : (∫⁻ x in Ioo (-L₀) L₀, ‖hom x‖ₑ ^ 2) ≠ ⊤)
    (hforced : MemLp forced 2 (volume : Measure ℝ)) :
    MemLp u 2 (volume : Measure ℝ) := by
  have hray : (∫⁻ x in Ioi L₀, ‖hom x‖ₑ ^ 2) ≠ ⊤ :=
    lintegral_sq_polyDistorted_ne_top hL₀ hm hposray
  have hneg : (∫⁻ x in Iio (-L₀), ‖hom x‖ₑ ^ 2) ≠ ⊤ := by
    rw [lintegral_sq_Iio_neg_eq]
    exact lintegral_sq_polyDistorted_ne_top (f := fun x : ℝ => hom (-x)) hL₀ hm hnegray
  have hhomfin : (∫⁻ x : ℝ, ‖hom x‖ₑ ^ 2) ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (lintegral_sq_of_window_and_rays (Y := L₀)
      (le_refl (∫⁻ x in Ioo (-L₀) L₀, ‖hom x‖ₑ ^ 2))
      (le_refl (∫⁻ x in Iio (-L₀), ‖hom x‖ₑ ^ 2))
      (le_refl (∫⁻ x in Ioi L₀, ‖hom x‖ₑ ^ 2)))
    exact ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr ⟨hmid, hneg⟩, hray⟩
  have hfor : (∫⁻ x : ℝ, ‖forced x‖ₑ ^ 2) ≠ ⊤ := by
    have h := hforced.2
    rw [eLpNorm_two_eq_sq] at h
    intro hcon
    rw [hcon] at h
    simp at h
  refine ⟨hu, ?_⟩
  rw [eLpNorm_two_eq_sq]
  refine ENNReal.rpow_lt_top_of_nonneg (by norm_num) ?_
  have hbound : (∫⁻ x : ℝ, ‖u x‖ₑ ^ 2)
      ≤ 4 * ((∫⁻ x : ℝ, ‖hom x‖ₑ ^ 2) + ∫⁻ x : ℝ, ‖forced x‖ₑ ^ 2) := by
    have hpt : ∀ x : ℝ, ‖u x‖ₑ ^ 2 ≤ 4 * (‖hom x‖ₑ ^ 2 + ‖forced x‖ₑ ^ 2) := by
      intro x
      rw [hsplit x]
      exact le_trans (pow_le_pow_left' (enorm_add_le _ _) 2) (sq_add_two_le _ _)
    calc (∫⁻ x : ℝ, ‖u x‖ₑ ^ 2)
        ≤ ∫⁻ x : ℝ, 4 * (‖hom x‖ₑ ^ 2 + ‖forced x‖ₑ ^ 2) := lintegral_mono hpt
      _ = 4 * ∫⁻ x : ℝ, (‖hom x‖ₑ ^ 2 + ‖forced x‖ₑ ^ 2) :=
          lintegral_const_mul' _ _ (by simp)
      _ ≤ 4 * ((∫⁻ x : ℝ, ‖hom x‖ₑ ^ 2) + ∫⁻ x : ℝ, ‖forced x‖ₑ ^ 2) :=
          mul_le_mul' le_rfl (le_of_eq (lintegral_add_left'
            (hhom.enorm.pow_const 2) (fun x : ℝ => ‖forced x‖ₑ ^ 2)))
  refine (lt_of_le_of_lt hbound ?_).ne
  refine ENNReal.mul_lt_top (by simp) ?_
  exact ENNReal.add_lt_top.mpr ⟨hhomfin.lt_top, hfor.lt_top⟩

end GaloisForLFunctions.RHTower
