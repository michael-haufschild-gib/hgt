import GaloisForLFunctions.SquareRootThreshold.TheZeroIndexedRoutesMeasureOneSide
import GaloisForLFunctions.SquareRootThreshold.TheWallsMeasureOneZeroWidth
import GaloisForLFunctions.RHTower.SourceNormalClockCurvatureLaw

/-!
# The side is the depth, and the width is its supremum

The zero-indexed routes read the side of a zero `ρ` through indicators that vanish exactly on the
critical line. This module shows that every one of them is an explicit monotone function of the
**depth** `|Re ρ − ½|` of the zero, so that the per-zero side and the zero width are one unit: the
width is the supremum of the depth, and each indicator reads the depth exactly.

* **The first-prime seam charge is a hyperbolic depth meter.**
  `‖orbitwiseFirstPrimeSeamCharge ρ‖ = √2 · log 2 · sinh(log 2 · |Re ρ − ½|)`
  (`norm_orbitwiseFirstPrimeSeamCharge_eq_sinh`): the two terms `2^{−ρ̄}` and `2^{−(1−ρ)}` share
  the phase `e^{i log 2 · Im ρ}`, so the charge is the real difference `2^{−Re ρ} − 2^{Re ρ − 1}`.
* **The Hurwitz two-seed residual is the depth times a Mellin factor.**
  `primeTailSeedTwoReflectionResidual ρ = (2 Re ρ − 1) · M(ρ)`
  (`primeTailSeedTwoReflectionResidual_eq_depth_mul`).
* **The Deninger half-density mate gain is the radial character of the depth.**
  `|log(mateGain n ρ)| = 2 |Re ρ − ½| log n` (`abs_log_deningerHalfDensityMateGain_eq`).
* **The Berry–Keating coordinate and the weight-one Clifford energy read the depth with the
  height as weight.** `Im(ρ(1 − ρ)) = −2 Im ρ (Re ρ − ½)` (`im_berryKeatingU_eq`,
  `im_weightOneCliffordEnergy_eq`).
* **The centred spectral point reads the signed depth** (`xiSpectralPoint_im_eq` of the corpus).

Consequently the width is read by every indicator: `zetaZeroWidth ≤ σ` iff every seam charge is at
most `√2 log 2 sinh(σ log 2)` (`zetaZeroWidth_le_iff_forall_norm_seamCharge_le`), iff every mate
gain satisfies `|log(mateGain n ρ)| ≤ 2σ log n` (`zetaZeroWidth_le_iff_forall_abs_log_mateGain_le`),
and the supremum of the seam charges is `√2 log 2 sinh(log 2 · zetaZeroWidth)`
(`sSup_norm_seamCharge_eq_sinh_zetaZeroWidth`). The side cluster of the route ledger is therefore
graded by the width: its indicators are depth meters, and their global forms are the endpoint
`zetaZeroWidth = 0`.
-/

open Complex Set Filter Topology
open scoped Real

noncomputable section

namespace GaloisForLFunctions.SquareRootThreshold

open _root_.Zeta23 _root_.RHTower

/-- The depth of a point: its distance to the critical line. -/
def criticalDepth (ρ : ℂ) : ℝ := |ρ.re - 1 / 2|

theorem criticalDepth_nonneg (ρ : ℂ) : 0 ≤ criticalDepth ρ := abs_nonneg _

theorem criticalDepth_eq_zero_iff (ρ : ℂ) : criticalDepth ρ = 0 ↔ ρ.re = 1 / 2 := by
  unfold criticalDepth
  rw [abs_eq_zero, sub_eq_zero]

/-- Every zero of `ζ` has depth at most the width. -/
theorem criticalDepth_le_zetaZeroWidth {ρ : ℂ} (hρ : ρ ∈ zetaZeroConfig.carrier) :
    criticalDepth ρ ≤ zetaZeroWidth :=
  abs_re_sub_half_le_zetaZeroWidth hρ

/-- The width is `≤ σ` iff every zero has depth `≤ σ`. -/
theorem zetaZeroWidth_le_iff_forall_criticalDepth_le {σ : ℝ} (hσ : 0 ≤ σ) :
    zetaZeroWidth ≤ σ ↔ ∀ ρ ∈ zetaZeroConfig.carrier, criticalDepth ρ ≤ σ := by
  constructor
  · exact fun h ρ hρ => (criticalDepth_le_zetaZeroWidth hρ).trans h
  · intro h
    rw [zetaZeroWidth_le_iff_re_le hσ]
    intro ρ hρ
    have := (abs_le.mp (h ρ hρ)).2
    linarith

/-! ### 1. The first-prime seam charge is a hyperbolic depth meter -/

/-- `e^{log 2 / 2} = √2`. -/
theorem exp_half_log_two : Real.exp (Real.log 2 / 2) = Real.sqrt 2 := by
  rw [← Real.log_sqrt (by norm_num : (0 : ℝ) ≤ 2),
    Real.exp_log (Real.sqrt_pos.mpr (by norm_num))]

/-- The real difference `2^{−r} − 2^{r−1}` is `−√2 · sinh(log 2 · (r − ½))`. -/
theorem exp_neg_log_two_mul_sub_exp_log_two_mul_sub_one (r : ℝ) :
    Real.exp (-(Real.log 2 * r)) - Real.exp (Real.log 2 * (r - 1)) =
      -(Real.sqrt 2 * Real.sinh (Real.log 2 * (r - 1 / 2))) := by
  have h1 : Real.exp (-(Real.log 2 * r)) =
      Real.exp (-(Real.log 2 / 2)) * Real.exp (-(Real.log 2 * (r - 1 / 2))) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have h2 : Real.exp (Real.log 2 * (r - 1)) =
      Real.exp (-(Real.log 2 / 2)) * Real.exp (Real.log 2 * (r - 1 / 2)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have h2pos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hs : Real.exp (-(Real.log 2 / 2)) = Real.sqrt 2 / 2 := by
    rw [Real.exp_neg, exp_half_log_two, inv_eq_one_div, div_eq_div_iff h2pos.ne' two_ne_zero,
      one_mul, Real.mul_self_sqrt (by norm_num)]
  rw [h1, h2, Real.sinh_eq, hs]
  ring

/-- **The seam charge is a hyperbolic depth meter.** -/
theorem norm_orbitwiseFirstPrimeSeamCharge_eq_sinh (ρ : ℂ) :
    ‖orbitwiseFirstPrimeSeamCharge ρ‖ =
      Real.sqrt 2 * Real.log 2 * Real.sinh (Real.log 2 * criticalDepth ρ) := by
  have h2 : (2 : ℂ) ≠ 0 := two_ne_zero
  have hlog : Complex.log 2 = ((Real.log 2 : ℝ) : ℂ) := by
    rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, ← Complex.ofReal_log (by norm_num)]
  have hL : 0 < Real.log 2 := Real.log_pos (by norm_num)
  unfold orbitwiseFirstPrimeSeamCharge
  rw [Complex.cpow_def_of_ne_zero h2, Complex.cpow_def_of_ne_zero h2, hlog]
  have e1 : ((Real.log 2 : ℝ) : ℂ) * (-(starRingEnd ℂ) ρ) =
      ((-(Real.log 2 * ρ.re) : ℝ) : ℂ) + ((Real.log 2 * ρ.im : ℝ) : ℂ) * I := by
    apply Complex.ext <;>
      simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.neg_re,
        Complex.neg_im, Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im] <;>
      ring
  have e2 : ((Real.log 2 : ℝ) : ℂ) * (-(1 - ρ)) =
      ((Real.log 2 * (ρ.re - 1) : ℝ) : ℂ) + ((Real.log 2 * ρ.im : ℝ) : ℂ) * I := by
    apply Complex.ext <;>
      simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.neg_re,
        Complex.neg_im, Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im] <;>
      ring
  rw [e1, e2, Complex.exp_add, Complex.exp_add, ← sub_mul, norm_mul, norm_mul,
    Complex.norm_exp_ofReal_mul_I, mul_one, ← Complex.ofReal_exp, ← Complex.ofReal_exp,
    ← Complex.ofReal_sub, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_pos hL, exp_neg_log_two_mul_sub_exp_log_two_mul_sub_one, abs_neg,
    abs_mul, abs_of_pos (Real.sqrt_pos.mpr (by norm_num)), Real.abs_sinh, abs_mul,
    abs_of_pos hL]
  unfold criticalDepth
  ring

/-- **The width is the supremum of the seam charges.** -/
theorem zetaZeroWidth_le_iff_forall_norm_seamCharge_le {σ : ℝ} (hσ : 0 ≤ σ) :
    zetaZeroWidth ≤ σ ↔ ∀ ρ ∈ zetaZeroConfig.carrier,
      ‖orbitwiseFirstPrimeSeamCharge ρ‖ ≤ Real.sqrt 2 * Real.log 2 * Real.sinh (Real.log 2 * σ) := by
  have hL : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hc : 0 < Real.sqrt 2 * Real.log 2 := mul_pos (Real.sqrt_pos.mpr (by norm_num)) hL
  rw [zetaZeroWidth_le_iff_forall_criticalDepth_le hσ]
  refine forall₂_congr fun ρ _ => ?_
  rw [norm_orbitwiseFirstPrimeSeamCharge_eq_sinh]
  constructor
  · intro h
    exact mul_le_mul_of_nonneg_left (Real.sinh_le_sinh.mpr (mul_le_mul_of_nonneg_left h hL.le))
      hc.le
  · intro h
    exact le_of_mul_le_mul_left (Real.sinh_le_sinh.mp (le_of_mul_le_mul_left h hc)) hL

/-- The zero configuration of `ζ` is nonempty. -/
theorem zetaZeroConfig_carrier_nonempty : zetaZeroConfig.carrier.Nonempty := by
  obtain ⟨ρ, h0, h1, hzero⟩ := exists_riemannZeta_zero_mem_openStrip
  exact ⟨ρ, show IsNontrivialZero ρ from ⟨hzero, h0, h1⟩⟩

/-- **The supremum of the seam charges is the hyperbolic reading of the width.** -/
theorem sSup_norm_seamCharge_eq_sinh_zetaZeroWidth :
    sSup ((fun ρ : ℂ => ‖orbitwiseFirstPrimeSeamCharge ρ‖) '' zetaZeroConfig.carrier) =
      Real.sqrt 2 * Real.log 2 * Real.sinh (Real.log 2 * zetaZeroWidth) := by
  have hL : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hc : 0 < Real.sqrt 2 * Real.log 2 := mul_pos (Real.sqrt_pos.mpr (by norm_num)) hL
  set g : ℝ → ℝ := fun d => Real.sqrt 2 * Real.log 2 * Real.sinh (Real.log 2 * d) with hg
  have hmono : Monotone g := fun a b hab =>
    mul_le_mul_of_nonneg_left (Real.sinh_le_sinh.mpr (mul_le_mul_of_nonneg_left hab hL.le)) hc.le
  have hcont : Continuous g := by
    rw [hg]
    fun_prop
  have hne : ((fun ρ : ℂ => |ρ.re - 1 / 2|) '' zetaZeroConfig.carrier).Nonempty :=
    zetaZeroConfig_carrier_nonempty.image _
  have hmap := hmono.map_csSup_of_continuousAt hcont.continuousAt hne bddAbove_image_abs_re_sub_half
  rw [Set.image_image] at hmap
  change sSup _ = g zetaZeroWidth
  unfold zetaZeroWidth
  rw [hmap]
  congr 1
  ext x
  simp only [Set.mem_image]
  constructor
  · rintro ⟨ρ, hρ, rfl⟩
    exact ⟨ρ, hρ, (norm_orbitwiseFirstPrimeSeamCharge_eq_sinh ρ).symm⟩
  · rintro ⟨ρ, hρ, rfl⟩
    exact ⟨ρ, hρ, norm_orbitwiseFirstPrimeSeamCharge_eq_sinh ρ⟩

/-! ### 2. The Hurwitz residual, the mate gain, the Berry–Keating coordinate -/

/-- **The Hurwitz two-seed residual is the signed depth times its Mellin factor.** -/
theorem primeTailSeedTwoReflectionResidual_eq_depth_mul (ρ : ℂ) :
    primeTailSeedTwoReflectionResidual ρ =
      ((2 * ρ.re - 1 : ℝ) : ℂ) * primeTailSeedTwoReflectionMellin ρ := by
  unfold primeTailSeedTwoReflectionResidual
  congr 1
  have h : (starRingEnd ℂ) ρ + 1 - (2 - ρ) = ρ + (starRingEnd ℂ) ρ - 1 := by ring
  rw [h, Complex.add_conj]
  push_cast
  ring

theorem norm_primeTailSeedTwoReflectionResidual_eq (ρ : ℂ) :
    ‖primeTailSeedTwoReflectionResidual ρ‖ =
      2 * criticalDepth ρ * ‖primeTailSeedTwoReflectionMellin ρ‖ := by
  rw [primeTailSeedTwoReflectionResidual_eq_depth_mul, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, show (2 * ρ.re - 1 : ℝ) = 2 * (ρ.re - 1 / 2) by ring, abs_mul, abs_two]
  rfl

/-- **The mate gain is the radial character of the depth.** -/
theorem abs_log_deningerHalfDensityMateGain_eq (n : ℕ) (ρ : ℂ) :
    |Real.log (deningerHalfDensityMateGain n ρ)| = 2 * criticalDepth ρ * Real.log n := by
  rw [logarithm_deningerHalfDensityMateGain, abs_mul, abs_of_nonneg (Real.log_natCast_nonneg n),
    show (2 * ρ.re - 1 : ℝ) = 2 * (ρ.re - 1 / 2) by ring, abs_mul, abs_two]
  rfl

/-- **The width is read by the mate gains at any modulus `n ≥ 2`.** -/
theorem zetaZeroWidth_le_iff_forall_abs_log_mateGain_le {n : ℕ} (hn : 2 ≤ n) {σ : ℝ} (hσ : 0 ≤ σ) :
    zetaZeroWidth ≤ σ ↔ ∀ ρ ∈ zetaZeroConfig.carrier,
      |Real.log (deningerHalfDensityMateGain n ρ)| ≤ 2 * σ * Real.log n := by
  have hlog : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn)
  rw [zetaZeroWidth_le_iff_forall_criticalDepth_le hσ]
  refine forall₂_congr fun ρ _ => ?_
  rw [abs_log_deningerHalfDensityMateGain_eq]
  constructor
  · intro h
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h (by norm_num)) hlog.le
  · intro h
    have := le_of_mul_le_mul_right h hlog
    linarith

/-- **The Berry–Keating coordinate reads the depth with the height as weight.** -/
theorem im_berryKeatingU_eq (ρ : ℂ) : (berryKeatingU ρ).im = -(2 * ρ.im * (ρ.re - 1 / 2)) := by
  simp only [berryKeatingU, Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.one_re,
    Complex.one_im]
  ring

theorem abs_im_berryKeatingU_eq (ρ : ℂ) :
    |(berryKeatingU ρ).im| = 2 * |ρ.im| * criticalDepth ρ := by
  rw [im_berryKeatingU_eq, abs_neg, abs_mul, abs_mul, abs_two]
  rfl

/-- **The weight-one Clifford energy reads the depth with the height as weight.** -/
theorem im_weightOneCliffordEnergy_eq (a : ℝ) (ρ : ℂ) :
    (weightOneCliffordEnergy a ρ).im = 2 * ρ.im * (ρ.re - 1 / 2) := by
  rw [weightOneCliffordEnergy_eq_berryKeatingU, Complex.sub_im, Complex.ofReal_im,
    im_berryKeatingU_eq]
  ring

/-- The centred spectral point of a divisor copy reads the depth. -/
theorem abs_im_xiSpectralPoint_eq (q : XiZeroCopy) :
    |(xiSpectralPoint q).im| = criticalDepth (q.1 : ℂ) := by
  rw [xiSpectralPoint_im_eq]
  unfold criticalDepth
  rw [← abs_neg]
  congr 1
  ring

/-! ### 3. One unit -/

/-- **The side is the depth.** At every point `ρ` the seam charge, the Hurwitz residual, the mate
gain, the Berry–Keating coordinate and the Clifford energy are explicit functions of the depth
`|Re ρ − ½|`; the Boolean "on the line" of the zero-indexed routes is the value zero of a depth
meter. -/
theorem theSideIsTheDepth (ρ : ℂ) (n : ℕ) (a : ℝ) :
    ‖orbitwiseFirstPrimeSeamCharge ρ‖ =
        Real.sqrt 2 * Real.log 2 * Real.sinh (Real.log 2 * criticalDepth ρ) ∧
    ‖primeTailSeedTwoReflectionResidual ρ‖ =
        2 * criticalDepth ρ * ‖primeTailSeedTwoReflectionMellin ρ‖ ∧
    |Real.log (deningerHalfDensityMateGain n ρ)| = 2 * criticalDepth ρ * Real.log n ∧
    |(berryKeatingU ρ).im| = 2 * |ρ.im| * criticalDepth ρ ∧
    (weightOneCliffordEnergy a ρ).im = 2 * ρ.im * (ρ.re - 1 / 2) ∧
    (criticalDepth ρ = 0 ↔ ρ.re = 1 / 2) :=
  ⟨norm_orbitwiseFirstPrimeSeamCharge_eq_sinh ρ, norm_primeTailSeedTwoReflectionResidual_eq ρ,
    abs_log_deningerHalfDensityMateGain_eq n ρ, abs_im_berryKeatingU_eq ρ,
    im_weightOneCliffordEnergy_eq a ρ, criticalDepth_eq_zero_iff ρ⟩

/-- **The width is the supremum of the depth meters.** -/
theorem theWidthIsTheSupremumOfTheDepthMeters {σ : ℝ} (hσ : 0 ≤ σ) {n : ℕ} (hn : 2 ≤ n) :
    (zetaZeroWidth ≤ σ ↔ ∀ ρ ∈ zetaZeroConfig.carrier, criticalDepth ρ ≤ σ) ∧
    (zetaZeroWidth ≤ σ ↔ ∀ ρ ∈ zetaZeroConfig.carrier,
      ‖orbitwiseFirstPrimeSeamCharge ρ‖ ≤
        Real.sqrt 2 * Real.log 2 * Real.sinh (Real.log 2 * σ)) ∧
    (zetaZeroWidth ≤ σ ↔ ∀ ρ ∈ zetaZeroConfig.carrier,
      |Real.log (deningerHalfDensityMateGain n ρ)| ≤ 2 * σ * Real.log n) ∧
    sSup ((fun ρ : ℂ => ‖orbitwiseFirstPrimeSeamCharge ρ‖) '' zetaZeroConfig.carrier) =
      Real.sqrt 2 * Real.log 2 * Real.sinh (Real.log 2 * zetaZeroWidth) :=
  ⟨zetaZeroWidth_le_iff_forall_criticalDepth_le hσ,
    zetaZeroWidth_le_iff_forall_norm_seamCharge_le hσ,
    zetaZeroWidth_le_iff_forall_abs_log_mateGain_le hn hσ,
    sSup_norm_seamCharge_eq_sinh_zetaZeroWidth⟩

end GaloisForLFunctions.SquareRootThreshold

end
