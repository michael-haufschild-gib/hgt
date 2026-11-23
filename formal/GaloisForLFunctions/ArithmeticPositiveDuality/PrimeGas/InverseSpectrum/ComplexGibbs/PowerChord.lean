import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-! # Variation of a positive real base at complex temperature

Reparametrizing the base by its real power turns the complex power into a
Lipschitz function on the unit interval.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open Set

private theorem unit_power_chord {u v : ℝ} (hv : 0 < v) (hvu : v ≤ u) (hu : u ≤ 1)
    {w : ℂ} (hw : 1 ≤ w.re) :
    ‖(u : ℂ) ^ w - (v : ℂ) ^ w‖ ≤ ‖w‖ * (u-v) := by
  have hw₀ : w ≠ 0 := by
    rintro rfl
    exact (not_le_of_gt zero_lt_one) hw
  apply norm_image_sub_le_of_norm_deriv_le_segment'
    (f := fun t : ℝ => (t : ℂ) ^ w) (f' := fun t => w * (t : ℂ) ^ (w-1))
    (fun t ht => (hasDerivAt_ofReal_cpow_const (hv.trans_le ht.1).ne' hw₀).hasDerivWithinAt)
    ?_ u (right_mem_Icc.mpr hvu)
  intro t ht
  rw [norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos (hv.trans_le ht.1),Complex.sub_re,Complex.one_re]
  exact mul_le_of_le_one_right (norm_nonneg w)
    (Real.rpow_le_one (hv.le.trans ht.1) (ht.2.le.trans hu) (sub_nonneg.mpr hw))

/-- A complex increment is bounded by the corresponding real thermal increment, uniformly in the bases. -/
theorem norm_thermal_chord {x y δ : ℝ} (hy : 0 < y) (hyx : y ≤ x) (hx : x ≤ 1)
    (hδ : 0 < δ) {z : ℂ} (hz : δ ≤ z.re) :
    ‖(x : ℂ) ^ z - (y : ℂ) ^ z‖ ≤ (‖z‖ / δ) * (x ^ δ - y ^ δ) := by
  let w := z / (δ : ℂ)
  have hw : 1 ≤ w.re := by
    change 1 ≤ (z / (δ : ℂ)).re
    rw [Complex.div_ofReal_re]
    exact (one_le_div hδ).mpr hz
  have hc : (δ : ℂ) * w = z := by
    change (δ : ℂ) * (z / (δ : ℂ)) = z
    field_simp [show (δ : ℂ) ≠ 0 by exact_mod_cast hδ.ne']
  have he (t : ℝ) (ht : 0 ≤ t) : ((t^δ : ℝ) : ℂ) ^ w = (t : ℂ) ^ z := by
    rw [← Complex.cpow_mul_ofReal_nonneg ht,hc]
  have h := unit_power_chord (Real.rpow_pos_of_pos hy δ)
    (Real.rpow_le_rpow hy.le hyx hδ.le) (Real.rpow_le_one (hy.le.trans hyx) hx hδ.le) hw
  simpa only [he x (hy.le.trans hyx),he y hy.le,w,norm_div,Complex.norm_of_nonneg hδ.le] using h

#print axioms norm_thermal_chord

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
