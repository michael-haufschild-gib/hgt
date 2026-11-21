import GaloisForLFunctions.RHTower.DirichletLUniformZeroFreeRegion
import GaloisForLFunctions.WindowedLandauTheory.LandauZeroFreeBounds.ExceptionalZeroBounds.NativeLocalZeros

/-! The logarithmic region for a nonreal character, with the height shift by two. -/

open Complex

namespace WindowedLandauTheory.ZeroFreeDirichlet

theorem noZeroComplex : NoZeroComplex := by
  let P := RHTower.pfConst
  have hP : 0 < P := RHTower.pfConst_pos
  let c := min (1 / 4 : ℝ) (1 / (336 * P))
  have hc : 0 < c := lt_min (by norm_num) (by positivity)
  refine ⟨c, hc, fun q _ χ s hχ₂ hregion hzero => ?_⟩
  have hχ : χ ≠ 1 := fun h => hχ₂ (by rw [h, one_pow])
  let D := Real.log ((q : ℝ) * (|s.im| + 2))
  let D' := Real.log ((q : ℝ) * (|s.im| + 3))
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.pos q
  have hbase : (2 : ℝ) ≤ q * (|s.im| + 2) :=
    (le_add_of_nonneg_left (abs_nonneg s.im)).trans (le_mul_of_one_le_left (by positivity) hq)
  have hDlog : Real.log 2 ≤ D := Real.log_le_log (by norm_num) hbase
  have hD : 0 < D := (Real.log_pos (by norm_num)).trans_le hDlog
  have hD' : 0 < D' := zero_lt_one.trans_le (RHTower.one_le_log_conductor (q := q) s.im)
  have hshift : D' ≤ 2 * D := log_height_shift q s.im
  have hr : 1 - c / D ≤ s.re := hregion
  have hhalf : 1 / 2 < s.re := by
    have hsmall : c / D < 1 / 2 := by
      rw [div_lt_iff₀ hD]
      have h₀ := min_le_left (1 / 4 : ℝ) (1 / (336 * P))
      linarith only [h₀, hDlog, Real.log_two_gt_d9]
    linarith only [hr, hsmall]
  have hz := RHTower.zero_free_of_sq_ne_one hχ hχ₂ hhalf
    (by simpa only [Complex.re_add_im] using hzero)
  have hsep : c / D < 1 / (84 * (P * D')) := by
    rw [div_lt_div_iff₀ hD (by positivity)]
    calc c * (84 * (P * D')) ≤ (1 / (336 * P)) * (84 * (P * D')) :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) (by positivity)
      _ = D' / 4 := by field_simp [hP.ne'] <;> ring
      _ < 1 * D := by linarith only [hshift, hD]
  change s.re ≤ 1 - 1 / (84 * (P * D')) at hz
  linarith only [hr, hz, hsep]

end WindowedLandauTheory.ZeroFreeDirichlet
