import GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality.MixedPositiveMoments
import GaloisForLFunctions.RHTower.VonKochChebyshevBound
import GaloisForLFunctions.SquareRootThreshold.EffectiveHorizons.TheEGCContourIsExplicit
import GaloisForLFunctions.RHTower.XiOrdinateCosineMass
import GaloisForLFunctions.RHTower.XiOrderedZeroCopyEnumeration

/-!
# Zeta deletion has logarithmic-square moment growth

Below a height cutoff, reciprocal ordinates bound the total support cost.
Above it, reciprocal squares bound the variance cost. Both estimates are
uniform over finite subsets and hence over every prefix of a deletion tail.
-/

open Complex Filter Topology
open _root_.RHTower GaloisForLFunctions.SquareRootThreshold
noncomputable section
namespace GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality

/-- Half-period shift assigned to a zeta zero copy. -/
def zetaCopyShift (q : XiZeroCopy) : ℝ := Real.pi / zeroOrdinate q

def zetaDeletionShift (n : ℕ) : ℝ := zetaCopyShift (xiZeroCopyThermalEquiv n)

def zetaDeletionDepth (α : ℝ) (n : ℕ) : ℝ :=
  ((xiZeroCopyThermalEquiv n).1 : ℂ).re - 1 / 2 - α

def zetaHeadShiftBound (H : ℝ) : ℝ :=
  20 * Real.pi * (xiLineTwoLogDerivConstant + Real.log (H + 6)) * (1 + Real.log (H + 1))

def zetaTailSquareBound (H : ℝ) : ℝ := 16 * Real.pi ^ 2 * (Real.log H / H)

def zetaMixedMomentBound (H s : ℝ) : ℝ :=
  |s| * zetaHeadShiftBound H + (s ^ 2 / 2) * zetaTailSquareBound H

theorem summable_zetaDeletionShift_sq : Summable fun n => zetaDeletionShift n ^ 2 := by
  have hs := (summable_inv_sq_xiCopyOrdinate.mul_left (Real.pi ^ 2)).comp_injective
    xiZeroCopyThermalEquiv.injective
  apply hs.congr
  intro n
  dsimp only [zetaDeletionShift, zetaCopyShift, zeroOrdinate, xiCopyOrdinate, Function.comp_def]
  ring

/-- The low-ordinate support cost grows at most logarithmically squared. -/
theorem sum_zetaCopyShift_abs_le {H : ℝ} (hH : 0 ≤ H) (F : Finset XiZeroCopy)
    (hF : ∀ q ∈ F, |zeroOrdinate q| ≤ H) :
    ∑ q ∈ F, |zetaCopyShift q| ≤ zetaHeadShiftBound H := by
  classical
  have hsub : F ⊆ xiCopiesBelow H := fun q hq => mem_xiCopiesBelow.mpr (hF q hq)
  have hsum : ∑ q ∈ F, 1 / |zeroOrdinate q| ≤
      ∑ q ∈ xiCopiesBelow H, 1 / |zeroOrdinate q| :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
  calc (∑ q ∈ F, |zetaCopyShift q|) = Real.pi * ∑ q ∈ F, 1 / |zeroOrdinate q| := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q _
      rw [zetaCopyShift, abs_div, abs_of_pos Real.pi_pos]
      ring
    _ ≤ Real.pi * ∑ q ∈ xiCopiesBelow H, 1 / |zeroOrdinate q| :=
      mul_le_mul_of_nonneg_left hsum Real.pi_pos.le
    _ ≤ Real.pi * (20 * (xiLineTwoLogDerivConstant + Real.log (H + 6)) *
        (1 + Real.log (H + 1))) :=
      mul_le_mul_of_nonneg_left (sum_xiCopiesBelow_inv_abs_le hH) Real.pi_pos.le
    _ = zetaHeadShiftBound H := by unfold zetaHeadShiftBound; ring

private theorem zetaCopyShift_sq_le_norm_inv (q : XiZeroCopy) :
    zetaCopyShift q ^ 2 ≤ 4 * Real.pi ^ 2 * (‖xiSpectralPoint q‖ ^ 2)⁻¹ := by
  have hγ := four_lt_abs_xiCopyOrdinate q
  have hstrip := xi_zero_re_mem_open_unit (xi_eq_zero_of_mem_divisor_support q.1)
  have hnorm : ‖xiSpectralPoint q‖ ≤ 2 * |zeroOrdinate q| := by
    rw [norm_xiSpectralPoint]
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    have hre : |((q.1 : ℂ) - 1 / 2).re| ≤ 1 / 2 := by
      rw [Complex.sub_re, show ((1 / 2 : ℂ)).re = 1 / 2 by norm_num, abs_le]
      constructor <;> linarith only [hstrip.1, hstrip.2]
    have him : ((q.1 : ℂ) - 1 / 2).im = zeroOrdinate q := by simp [zeroOrdinate]
    rw [him]
    change 4 < |zeroOrdinate q| at hγ
    linarith only [hre, hγ]
  have hsq : ‖xiSpectralPoint q‖ ^ 2 ≤ 4 * zeroOrdinate q ^ 2 := by
    have hh := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    rw [mul_pow, sq_abs] at hh
    norm_num at hh ⊢
    exact hh
  have hγ0 : zeroOrdinate q ≠ 0 := xiCopyOrdinate_ne_zero q
  have hn0 : 0 < ‖xiSpectralPoint q‖ := norm_pos_iff.mpr (xiSpectralPoint_ne_zero q)
  calc zetaCopyShift q ^ 2 = Real.pi ^ 2 / zeroOrdinate q ^ 2 := by
      rw [zetaCopyShift, div_pow]
    _ ≤ (4 * Real.pi ^ 2) / ‖xiSpectralPoint q‖ ^ 2 := by
      apply (div_le_div_iff₀ (sq_pos_of_ne_zero hγ0) (sq_pos_of_pos hn0)).mpr
      have hh := mul_le_mul_of_nonneg_left hsq (sq_nonneg Real.pi)
      nlinarith only [hh]
    _ = _ := div_eq_mul_inv _ _

/-- The high-ordinate square cost is `O(log H/H)`, uniformly over finite subsets. -/
theorem sum_zetaCopyShift_sq_le {H : ℝ} (hH : Real.exp 12 ≤ H) (F : Finset XiZeroCopy)
    (hF : ∀ q ∈ F, H < |zeroOrdinate q|) :
    ∑ q ∈ F, zetaCopyShift q ^ 2 ≤ zetaTailSquareBound H := by
  have hre (q : XiZeroCopy) : (xiSpectralPoint q).re = zeroOrdinate q := by
    simp [xiSpectralPoint, zeroOrdinate]
  have htail := sum_inv_norm_sq_le hH F (fun q hq => by rw [hre]; exact hF q hq)
  calc (∑ q ∈ F, zetaCopyShift q ^ 2) ≤
        4 * Real.pi ^ 2 * ∑ q ∈ F, (‖xiSpectralPoint q‖ ^ 2)⁻¹ := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun q _ => zetaCopyShift_sq_le_norm_inv q
    _ ≤ 4 * Real.pi ^ 2 * (4 * (Real.log H / H)) :=
      mul_le_mul_of_nonneg_left htail (by positivity)
    _ = zetaTailSquareBound H := by unfold zetaTailSquareBound; ring

/-- Low and high ordinates pay different parts of the mixed moment. -/
theorem zeta_mixed_finite_cost_le {H : ℝ} (hH : Real.exp 12 ≤ H)
    (F : Finset XiZeroCopy) (s : ℝ) :
    (∑ q ∈ F, min |zetaCopyShift q * s| (s ^ 2 * zetaCopyShift q ^ 2 / 2)) ≤
      zetaMixedMomentBound H s := by
  classical
  let P : XiZeroCopy → Prop := fun q => |zeroOrdinate q| ≤ H
  let L := F.filter P
  let R := F.filter fun q => ¬ P q
  have hH0 : 0 ≤ H := (Real.exp_pos 12).le.trans hH
  have hhead := sum_zetaCopyShift_abs_le hH0 L
    (fun q hq => (Finset.mem_filter.mp hq).2)
  have htail := sum_zetaCopyShift_sq_le hH R
    (fun q hq => lt_of_not_ge (Finset.mem_filter.mp hq).2)
  have hlo : (∑ q ∈ L, min |zetaCopyShift q * s| (s ^ 2 * zetaCopyShift q ^ 2 / 2)) ≤
      |s| * zetaHeadShiftBound H := by
    calc _ ≤ ∑ q ∈ L, |s| * |zetaCopyShift q| := by
        apply Finset.sum_le_sum
        intro q _
        simpa only [abs_mul, mul_comm] using
          (min_le_left |zetaCopyShift q * s| (s ^ 2 * zetaCopyShift q ^ 2 / 2))
      _ = |s| * ∑ q ∈ L, |zetaCopyShift q| := (Finset.mul_sum _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hhead (abs_nonneg s)
  have hhi : (∑ q ∈ R, min |zetaCopyShift q * s| (s ^ 2 * zetaCopyShift q ^ 2 / 2)) ≤
      (s ^ 2 / 2) * zetaTailSquareBound H := by
    calc _ ≤ ∑ q ∈ R, (s ^ 2 / 2) * zetaCopyShift q ^ 2 := by
        apply Finset.sum_le_sum
        intro q _
        calc _ ≤ s ^ 2 * zetaCopyShift q ^ 2 / 2 := min_le_right _ _
          _ = _ := by ring
      _ = (s ^ 2 / 2) * ∑ q ∈ R, zetaCopyShift q ^ 2 := (Finset.mul_sum _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left htail (by positivity)
  have he := Finset.sum_filter_add_sum_filter_not F P
    (fun q => min |zetaCopyShift q * s| (s ^ 2 * zetaCopyShift q ^ 2 / 2))
  change (∑ q ∈ L, min |zetaCopyShift q * s| (s ^ 2 * zetaCopyShift q ^ 2 / 2)) +
    (∑ q ∈ R, min |zetaCopyShift q * s| (s ^ 2 * zetaCopyShift q ^ 2 / 2)) = _ at he
  rw [← he]
  exact add_le_add hlo hhi

/-- Every prefix of every deletion tail obeys the same moment bound. -/
theorem zeta_mixedMomentCost_le (α : ℝ) (M N : ℕ) (s : ℝ) {H : ℝ}
    (hH : Real.exp 12 ≤ H) :
    mixedMomentCost (filterPrefix (fun n => zetaDeletionDepth α (n + M))
      (fun n => zetaDeletionShift (n + M)) N) s ≤ zetaMixedMomentBound H s := by
  classical
  let e := xiZeroCopyThermalEquiv
  let F := (Finset.range N).image fun n => e (n + M)
  have hF := zeta_mixed_finite_cost_le hH F s
  rw [show F = (Finset.range N).image (fun n => e (n + M)) from rfl,
    Finset.sum_image (fun i _ j _ hij => Nat.add_right_cancel (e.injective hij))] at hF
  simpa only [mixedMomentCost_filterPrefix, zetaDeletionShift] using hF

#print axioms sum_zetaCopyShift_abs_le
#print axioms sum_zetaCopyShift_sq_le
#print axioms zeta_mixedMomentCost_le

end GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality
