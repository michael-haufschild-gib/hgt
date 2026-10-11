import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-! Scalar logarithmic means control local distortion between positive nodes. -/

noncomputable section
namespace RHTower

def finiteWeilLogarithmicMean (x y : ℝ) : ℝ := (x - y) / (Real.log x - Real.log y)

theorem finiteWeilLogarithmicMean_symm (x y : ℝ) :
    finiteWeilLogarithmicMean x y = finiteWeilLogarithmicMean y x := by
  unfold finiteWeilLogarithmicMean
  rw [show x - y = -(y - x) by ring,
    show Real.log x - Real.log y = -(Real.log y - Real.log x) by ring, neg_div_neg_eq]

theorem finiteWeilLogarithmicMean_pos {x y : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hxy : x ≠ y) : 0 < finiteWeilLogarithmicMean x y := by
  rcases lt_or_gt_of_ne hxy with h | h
  · rw [finiteWeilLogarithmicMean_symm]
    exact div_pos (sub_pos.mpr h) (sub_pos.mpr (Real.log_lt_log hx h))
  · exact div_pos (sub_pos.mpr h) (sub_pos.mpr (Real.log_lt_log hy h))

theorem finiteWeilLogarithmicMean_eq_inv_slope (x y : ℝ) :
    finiteWeilLogarithmicMean x y = (slope Real.log x y)⁻¹ := by
  rw [slope_def_field, inv_div]
  exact finiteWeilLogarithmicMean_symm x y

/-- Log concavity gives monotonicity even when the compared points straddle the fixed node. -/
theorem finiteWeilLogarithmicMean_mono_right {x y z : ℝ}
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (hxy : x ≠ y) (hxz : x ≠ z)
    (hyz : y ≤ z) : finiteWeilLogarithmicMean x y ≤ finiteWeilLogarithmicMean x z := by
  have hanti := strictConcaveOn_log_Ioi.concaveOn.slope_anti hx
  have hs : slope Real.log x z ≤ slope Real.log x y :=
    hanti ⟨hy, by simpa using hxy.symm⟩ ⟨hz, by simpa using hxz.symm⟩ hyz
  have hLy := finiteWeilLogarithmicMean_pos hx hy hxy
  have hLz := finiteWeilLogarithmicMean_pos hx hz hxz
  rw [finiteWeilLogarithmicMean_eq_inv_slope] at hLy hLz
  rw [finiteWeilLogarithmicMean_eq_inv_slope, finiteWeilLogarithmicMean_eq_inv_slope]
  exact (inv_le_inv₀ (inv_pos.mp hLy) (inv_pos.mp hLz)).mpr hs

theorem finiteWeilLogarithmicMean_mono_left {x z y : ℝ}
    (hx : 0 < x) (hz : 0 < z) (hy : 0 < y) (hxy : x ≠ y) (hzy : z ≠ y)
    (hxz : x ≤ z) : finiteWeilLogarithmicMean x y ≤ finiteWeilLogarithmicMean z y := by
  rw [finiteWeilLogarithmicMean_symm x y, finiteWeilLogarithmicMean_symm z y]
  exact finiteWeilLogarithmicMean_mono_right hy hx hz hxy.symm hzy.symm hxz

theorem finiteWeilLogarithmicMean_homogeneous {t x y : ℝ}
    (ht : 0 < t) (hx : 0 < x) (hy : 0 < y) :
    finiteWeilLogarithmicMean (t * x) (t * y) = t * finiteWeilLogarithmicMean x y := by
  unfold finiteWeilLogarithmicMean
  rw [Real.log_mul ht.ne' hx.ne', Real.log_mul ht.ne' hy.ne']
  rw [show Real.log t + Real.log x - (Real.log t + Real.log y) = Real.log x - Real.log y by ring,
    show t * x - t * y = t * (x - y) by ring, mul_div_assoc]

/-- A relative movement of one node bounds the relative change of the logarithmic mean. -/
theorem finiteWeilLogarithmicMean_local_comparison {x z y : ℝ}
    (hx : 0 < x) (hz : 0 < z) (hy : 0 < y) (hxy : x ≠ y) (hzy : z ≠ y)
    (hxz : x ≤ z) :
    finiteWeilLogarithmicMean x y ≤ finiteWeilLogarithmicMean z y ∧
    finiteWeilLogarithmicMean z y ≤ (z / x) * finiteWeilLogarithmicMean x y := by
  refine ⟨finiteWeilLogarithmicMean_mono_left hx hz hy hxy hzy hxz, ?_⟩
  let t := z / x
  have ht : 0 < t := div_pos hz hx
  have htone : 1 ≤ t := (le_div_iff₀ hx).mpr (by simpa using hxz)
  have htx : t * x = z := by dsimp [t]; field_simp
  have hty : y ≤ t * y := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right htone hy.le
  have hne : z ≠ t * y := by
    intro h
    exact hxy (mul_left_cancel₀ ht.ne' (htx.trans h))
  calc
    _ ≤ finiteWeilLogarithmicMean z (t * y) :=
      finiteWeilLogarithmicMean_mono_right hz hy (mul_pos ht hy) hzy hne hty
    _ = t * finiteWeilLogarithmicMean x y := by
      rw [← htx, finiteWeilLogarithmicMean_homogeneous ht hx hy]

end RHTower
