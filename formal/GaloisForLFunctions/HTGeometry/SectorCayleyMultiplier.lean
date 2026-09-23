import GaloisForLFunctions.HTGeometry.AccretiveDiskMultiplierOuter

open Complex

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Exponential whose argument is the real part of `w`. -/
def sectorExponential (w : ℂ) : ℂ := Complex.exp (I * w)

theorem sectorExponential_ne_zero (w : ℂ) : sectorExponential w ≠ 0 :=
  Complex.exp_ne_zero _

theorem sectorExponential_re (w : ℂ) :
    (sectorExponential w).re = Real.exp (-w.im) * Real.cos w.re := by
  rw [sectorExponential, Complex.exp_re]
  congr 1 <;> simp

theorem sectorExponential_re_nonneg {w : ℂ}
    (hw : |w.re| ≤ Real.pi / 2) :
    0 ≤ (sectorExponential w).re := by
  rw [sectorExponential_re]
  exact mul_nonneg (Real.exp_pos _).le
    (Real.cos_nonneg_of_mem_Icc (abs_le.mp hw))

theorem add_one_ne_zero_of_re_nonneg_sectorCayleyMultiplier {e : ℂ} (he : 0 ≤ e.re) : e + 1 ≠ 0 := by
  intro hzero
  have hre := congrArg Complex.re hzero
  norm_num at hre
  linarith

theorem norm_sub_one_le_norm_add_one {e : ℂ} (he : 0 ≤ e.re) :
    ‖e - 1‖ ≤ ‖e + 1‖ := by
  apply le_of_sq_le_sq
  rw [Complex.sq_norm, Complex.sq_norm,
    Complex.normSq_apply, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im,
    Complex.add_re, Complex.add_im, sub_zero, add_zero]
  nlinarith
  exact norm_nonneg _

/-- Cayley transform of a sector exponential. -/
def sectorCayleyValue (w : ℂ) : ℂ :=
  (sectorExponential w - 1) / (sectorExponential w + 1)

theorem norm_sectorCayleyValue_le_one {w : ℂ}
    (hw : |w.re| ≤ Real.pi / 2) :
    ‖sectorCayleyValue w‖ ≤ 1 := by
  have hre := sectorExponential_re_nonneg hw
  have hden := add_one_ne_zero_of_re_nonneg_sectorCayleyMultiplier hre
  rw [sectorCayleyValue, norm_div]
  exact (div_le_one (norm_pos_iff.mpr hden)).2
    (norm_sub_one_le_norm_add_one hre)

theorem one_sub_sectorCayleyValue_re_pos {w : ℂ}
    (hw : |w.re| ≤ Real.pi / 2) :
    0 < (1 - sectorCayleyValue w).re := by
  let e := sectorExponential w
  have hre : 0 ≤ e.re := sectorExponential_re_nonneg hw
  have hden : e + 1 ≠ 0 := add_one_ne_zero_of_re_nonneg_sectorCayleyMultiplier hre
  have hformula : 1 - sectorCayleyValue w = 2 / (e + 1) := by
    rw [sectorCayleyValue]
    change 1 - (e - 1) / (e + 1) = _
    field_simp
    ring
  rw [hformula, Complex.div_re]
  have hnorm : 0 < Complex.normSq (e + 1) := Complex.normSq_pos.mpr hden
  norm_num
  positivity

theorem one_add_sectorCayleyValue_re_pos {w : ℂ}
    (hw : |w.re| ≤ Real.pi / 2) :
    0 < (1 + sectorCayleyValue w).re := by
  let e := sectorExponential w
  have hre : 0 ≤ e.re := sectorExponential_re_nonneg hw
  have hene : e ≠ 0 := sectorExponential_ne_zero w
  have hden : e + 1 ≠ 0 := add_one_ne_zero_of_re_nonneg_sectorCayleyMultiplier hre
  have hformula : 1 + sectorCayleyValue w = 2 * e / (e + 1) := by
    rw [sectorCayleyValue]
    change 1 + (e - 1) / (e + 1) = _
    field_simp
    ring
  rw [hformula, Complex.div_re]
  have hnorm : 0 < Complex.normSq (e + 1) := Complex.normSq_pos.mpr hden
  have heNorm : 0 < Complex.normSq e := Complex.normSq_pos.mpr hene
  norm_num [Complex.mul_re]
  rw [show 2 * e.re * (e.re + 1) / Complex.normSq (e + 1) +
      2 * e.im * e.im / Complex.normSq (e + 1) =
      2 * (Complex.normSq e + e.re) / Complex.normSq (e + 1) by
        field_simp [ne_of_gt hnorm]
        rw [Complex.normSq_apply]
        ring]
  positivity

/-- Inverting the sector Cayley transform recovers its exponential. -/
theorem one_add_sectorCayleyValue_div_one_sub {w : ℂ}
    (hw : |w.re| ≤ Real.pi / 2) :
    (1 + sectorCayleyValue w) / (1 - sectorCayleyValue w) =
      sectorExponential w := by
  have hden : sectorExponential w + 1 ≠ 0 :=
    add_one_ne_zero_of_re_nonneg_sectorCayleyMultiplier (sectorExponential_re_nonneg hw)
  rw [sectorCayleyValue]
  field_simp
  ring

/-- The phase reflection of the sector exponential only sees the real part of its exponent. -/
theorem sectorExponential_div_conj (w : ℂ) :
    sectorExponential w / (starRingEnd ℂ) (sectorExponential w) =
      Complex.exp (2 * I * (w.re : ℂ)) := by
  rw [sectorExponential, ← Complex.exp_conj, ← Complex.exp_sub]
  congr 1
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring

/-- Schur multiplier obtained by applying the sector Cayley transform to a Hardy function whose
real part stays in the closed central half-period. -/
def sectorCayleyMultiplier (H : HardyDisk)
    (hH : ∀ z : ℂ, ‖z‖ < 1 → |(hardyFun H z).re| ≤ Real.pi / 2) :
    DiskMultiplier where
  fn := fun z => sectorCayleyValue (hardyFun H z)
  diff := by
    intro z hz
    have hHz : DifferentiableAt ℂ (hardyFun H) z :=
      (differentiableOn_hardyFun H).differentiableAt
        (Metric.isOpen_ball.mem_nhds hz)
    have hExp : DifferentiableAt ℂ
        (fun z => sectorExponential (hardyFun H z)) z := by
      unfold sectorExponential
      fun_prop
    have hdiff := (hExp.sub_const 1).div (hExp.add_const 1)
      (add_one_ne_zero_of_re_nonneg_sectorCayleyMultiplier
        (sectorExponential_re_nonneg (hH z (by
          simpa [Metric.mem_ball, dist_zero_right] using hz))))
    unfold sectorCayleyValue
    change DifferentiableWithinAt ℂ
      ((fun y => sectorExponential (hardyFun H y) - 1) /
        fun y => sectorExponential (hardyFun H y) + 1)
      (Metric.ball 0 1) z
    exact hdiff.differentiableWithinAt
  bd := 1
  bd_nonneg := zero_le_one
  bd_le := by
    intro z hz
    exact norm_sectorCayleyValue_le_one
      (hH z (by simpa [Metric.mem_ball, dist_zero_right] using hz))

@[simp] theorem sectorCayleyMultiplier_fn (H : HardyDisk)
    (hH : ∀ z : ℂ, ‖z‖ < 1 → |(hardyFun H z).re| ≤ Real.pi / 2)
    (z : ℂ) :
    (sectorCayleyMultiplier H hH).fn z = sectorCayleyValue (hardyFun H z) := rfl

theorem isOuterDiskMultiplier_one_sub_sectorCayleyMultiplier
    (H : HardyDisk)
    (hH : ∀ z : ℂ, ‖z‖ < 1 → |(hardyFun H z).re| ≤ Real.pi / 2) :
    IsOuterDiskMultiplier
      (DiskMultiplier.const 1 |>.sub (sectorCayleyMultiplier H hH)) := by
  apply isOuterDiskMultiplier_of_re_pos
  intro z hz
  change 0 < (1 - sectorCayleyValue (hardyFun H z)).re
  exact one_sub_sectorCayleyValue_re_pos
    (hH z (by simpa [Metric.mem_ball, dist_zero_right] using hz))

theorem isOuterDiskMultiplier_one_add_sectorCayleyMultiplier
    (H : HardyDisk)
    (hH : ∀ z : ℂ, ‖z‖ < 1 → |(hardyFun H z).re| ≤ Real.pi / 2) :
    IsOuterDiskMultiplier
      (DiskMultiplier.const 1 |>.add (sectorCayleyMultiplier H hH)) := by
  apply isOuterDiskMultiplier_of_re_pos
  intro z hz
  change 0 < (1 + sectorCayleyValue (hardyFun H z)).re
  exact one_add_sectorCayleyValue_re_pos
    (hH z (by simpa [Metric.mem_ball, dist_zero_right] using hz))

end

end GaloisForLFunctions.HTGeometry
