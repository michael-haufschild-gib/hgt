import GaloisForLFunctions.RHTower.BVPrimeWindowDivisorTomography

/-!
# Dilation orientation of bounded-variation prime-window residues

The compact BV source is stable under positive argument dilation.  Its Mellin transform scales by
the exact character `r ^ (s - 1)`.  At a shifted zero of the pole-filled zeta this character acts
on the actual Laurent residue of the continued prime source.  Forward and inverse dilations
therefore form a source-produced Hermitian orientation pair whose squared-norm difference has the
strict sign of the horizontal displacement from the critical line.

For positive integer dilation, the two source channels are already joined before continuation:
their finite von-Mangoldt windows and their complete prime--archimedean polar coefficients obey
literal square-index decimation.  Thus the residue character is the continued image of an exact
finite source action, not a divisor-defined decoration.

This file proves a source value relation.  It neither assumes a zero orientation nor turns the
resulting sign into an RH hypothesis.
-/

open Complex Filter MeasureTheory Set Topology

noncomputable section

namespace RHTower
namespace CompactBVPrimeWindow

/-- Positive argument dilation of a compact BV prime window: `x ↦ W (r x)`. -/
def argumentDilation (W : CompactBVPrimeWindow) (r : ℝ) (hr : 0 < r) :
    CompactBVPrimeWindow where
  lower := W.lower / r
  upper := W.upper / r
  lower_pos := div_pos W.lower_pos hr
  lower_lt_upper := div_lt_div_of_pos_right W.lower_lt_upper hr
  toFun := fun x => W (r * x)
  eq_zero_off_support := by
    intro x hx
    apply W.eq_zero_off_support
    intro hrx
    apply hx
    constructor
    · exact (div_le_iff₀ hr).2 (by simpa only [mul_comm] using hrx.1)
    · exact (le_div_iff₀ hr).2 (by simpa only [mul_comm] using hrx.2)
  integrable := W.integrable.comp_mul_left' hr.ne'
  boundedVariation := by
    apply ne_top_of_le_ne_top W.boundedVariation
    simpa only [Function.comp_def] using
      eVariationOn.comp_le_of_monotoneOn W (fun x : ℝ => r * x)
        (fun _ _ _ _ hxy => mul_le_mul_of_nonneg_left hxy hr.le)
        (fun _ _ => Set.mem_univ _)

@[simp]
theorem argumentDilation_apply (W : CompactBVPrimeWindow) (r : ℝ) (hr : 0 < r) (x : ℝ) :
    W.argumentDilation r hr x = W (r * x) := rfl

@[simp]
theorem argumentDilation_lower (W : CompactBVPrimeWindow) (r : ℝ) (hr : 0 < r) :
    (W.argumentDilation r hr).lower = W.lower / r := rfl

@[simp]
theorem argumentDilation_upper (W : CompactBVPrimeWindow) (r : ℝ) (hr : 0 < r) :
    (W.argumentDilation r hr).upper = W.upper / r := rfl

private theorem cpow_mul_scaled_cpow_neg
    {r x : ℝ} (hr : 0 < r) (hx : 0 < x) (s : ℂ) :
    (r : ℂ) ^ s * ((r * x : ℝ) : ℂ) ^ (-s) = (x : ℂ) ^ (-s) := by
  rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hr.le hx.le]
  rw [Complex.cpow_neg]
  have hpow : (r : ℂ) ^ s ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (ofReal_ne_zero.mpr hr.ne'))
  rw [← mul_assoc, mul_inv_cancel₀ hpow, one_mul]

private theorem argumentDilation_mellinIntegrand
    (W : CompactBVPrimeWindow) (r : ℝ) (hr : 0 < r) (s : ℂ) (x : ℝ) :
    (W.argumentDilation r hr).mellinIntegrand s x =
      (r : ℂ) ^ s * W.mellinIntegrand s (r * x) := by
  rw [(W.argumentDilation r hr).mellinIntegrand_eq_raw,
    W.mellinIntegrand_eq_raw]
  by_cases hW : W (r * x) = 0
  · rw [argumentDilation_apply, hW]
    simp
  · have hrxMem : r * x ∈ Set.Icc W.lower W.upper := by
      by_contra hmem
      exact hW (W.eq_zero_off_support (r * x) hmem)
    have hx : 0 < x := by
      have hrxPos : 0 < r * x := W.lower_pos.trans_le hrxMem.1
      rcases (mul_pos_iff.mp hrxPos) with h | h
      · exact h.2
      · exact (not_lt_of_ge hr.le h.1).elim
    rw [argumentDilation_apply]
    calc
      W (r * x) * (x : ℂ) ^ (-s) =
          W (r * x) * ((r : ℂ) ^ s * ((r * x : ℝ) : ℂ) ^ (-s)) := by
            rw [cpow_mul_scaled_cpow_neg hr hx s]
      _ = (r : ℂ) ^ s * (W (r * x) * ((r * x : ℝ) : ℂ) ^ (-s)) := by ring

/-- Exact Mellin character of positive argument dilation. -/
theorem mellinTransform_argumentDilation
    (W : CompactBVPrimeWindow) (r : ℝ) (hr : 0 < r) (s : ℂ) :
    (W.argumentDilation r hr).mellinTransform s =
      (r : ℂ) ^ (s - 1) * W.mellinTransform s := by
  rw [mellinTransform, mellinTransform]
  calc
    (∫ x : ℝ, (W.argumentDilation r hr).mellinIntegrand s x) =
        ∫ x : ℝ, (r : ℂ) ^ s * W.mellinIntegrand s (r * x) := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall (argumentDilation_mellinIntegrand W r hr s)
    _ = (r : ℂ) ^ s * ∫ x : ℝ, W.mellinIntegrand s (r * x) := by
          rw [integral_const_mul]
    _ = (r : ℂ) ^ s *
        (|r⁻¹| • ∫ x : ℝ, W.mellinIntegrand s x) := by
          rw [Measure.integral_comp_mul_left]
    _ = (r : ℂ) ^ (s - 1) * ∫ x : ℝ, W.mellinIntegrand s x := by
          rw [abs_of_pos (inv_pos.mpr hr), Complex.real_smul]
          rw [show s - 1 = s + (-1) by ring,
            Complex.cpow_add _ _ (ofReal_ne_zero.mpr hr.ne'),
            Complex.cpow_neg_one, Complex.ofReal_inv]
          ring

/-- Reciprocal argument dilation: `x ↦ W (x / r)`. -/
def argumentExpansion (W : CompactBVPrimeWindow) (r : ℝ) (hr : 0 < r) :
    CompactBVPrimeWindow :=
  W.argumentDilation r⁻¹ (inv_pos.mpr hr)

@[simp]
theorem argumentExpansion_apply (W : CompactBVPrimeWindow) (r : ℝ) (hr : 0 < r) (x : ℝ) :
    W.argumentExpansion r hr x = W (x / r) := by
  rw [argumentExpansion, argumentDilation_apply]
  congr 1
  field_simp

/-- Exact Mellin character of reciprocal argument dilation. -/
theorem mellinTransform_argumentExpansion
    (W : CompactBVPrimeWindow) (r : ℝ) (hr : 0 < r) (s : ℂ) :
    (W.argumentExpansion r hr).mellinTransform s =
      (r : ℂ) ^ (1 - s) * W.mellinTransform s := by
  rw [argumentExpansion, mellinTransform_argumentDilation]
  have harg : (r : ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg hr.le]
    exact ne_of_lt Real.pi_pos
  rw [Complex.ofReal_inv, Complex.inv_cpow _ _ harg, ← Complex.cpow_neg]
  congr 2
  ring

private theorem sqrt_sq_mul_nat (r n : ℕ) :
    Real.sqrt (((r ^ 2 * n : ℕ) : ℝ)) = (r : ℝ) * Real.sqrt n := by
  push_cast
  rw [Real.sqrt_mul (sq_nonneg (r : ℝ)), Real.sqrt_sq_eq_abs,
    abs_of_nonneg (Nat.cast_nonneg r)]

private theorem dilation_expansion_argument_eq
    (r n k : ℕ) (hr : 0 < r) :
    (r : ℝ) * ((n : ℝ) / k) = (((r ^ 2 * n : ℕ) : ℝ) / k) / r := by
  rcases k.eq_zero_or_pos with rfl | hk
  · simp
  · push_cast
    field_simp [Nat.ne_of_gt hr, Nat.ne_of_gt hk]

private theorem natCast_pos {r : ℕ} (hr : 0 < r) : (0 : ℝ) < r :=
  Nat.cast_pos.mpr hr

/-- Exact finite-prime source effectivity: forward and inverse integer dilations are related by
literal square-index decimation before any analytic continuation or zero data enter. -/
theorem weightedPrimeWindow_argumentDilation_eq_argumentExpansion_sq_mul
    (W : CompactBVPrimeWindow) (r : ℕ) (hr : 0 < r) (n : ℕ) :
    (W.argumentDilation r (natCast_pos hr)).weightedPrimeWindow n =
      (W.argumentExpansion r (natCast_pos hr)).weightedPrimeWindow (r ^ 2 * n) := by
  unfold weightedPrimeWindow
  apply tsum_congr
  intro k
  congr 1
  rw [argumentDilation_apply, argumentExpansion_apply]
  exact congrArg W (dilation_expansion_argument_eq r n k hr)

/-- The complete finite prime--polar coefficient, including its archimedean counterterm, obeys
the same square-index decimation law.  This is the prime--archimedean source join behind the
continued residue orientation below. -/
theorem polarCoefficient_argumentDilation_eq_argumentExpansion_sq_mul
    (W : CompactBVPrimeWindow) (r : ℕ) (hr : 0 < r) (n : ℕ) :
    (W.argumentDilation r (natCast_pos hr)).polarCoefficient n =
      (W.argumentExpansion r (natCast_pos hr)).polarCoefficient (r ^ 2 * n) := by
  have hrC : (((r : ℝ) : ℂ)) ≠ 0 := by exact_mod_cast hr.ne'
  have hcpow :
      ((r : ℝ) : ℂ) ^ ((3 / 2 : ℂ) - 1) =
        ((r : ℝ) : ℂ) * ((r : ℝ) : ℂ) ^ (1 - (3 / 2 : ℂ)) := by
    rw [show (3 / 2 : ℂ) - 1 = 1 + (1 - 3 / 2) by ring,
      Complex.cpow_add _ _ hrC, Complex.cpow_one]
  have hsqrt :
      ((Real.sqrt (((r ^ 2 * n : ℕ) : ℝ)) : ℝ) : ℂ) =
        ((r : ℝ) : ℂ) * ((Real.sqrt n : ℝ) : ℂ) := by
    rw [sqrt_sq_mul_nat]
    exact map_mul (Complex.ofRealHom) _ _
  rw [polarCoefficient, polarCoefficient,
    mellinTransform_argumentDilation,
    mellinTransform_argumentExpansion,
    weightedPrimeWindow_argumentDilation_eq_argumentExpansion_sq_mul]
  rw [hcpow, hsqrt]
  ring

/-- The exact residue target carried by a compact BV continued source at the shifted point
`rho + 1/2`.  The existing residue theorem proves that this is the actual Laurent residue when
`rho` is a zero of the pole-filled zeta. -/
def continuedSourceResidueValue (W : CompactBVPrimeWindow) (rho : ℂ) : ℂ :=
  2 * W.mellinTransform (rho + 1 / 2) *
    (analyticOrderAt regularizedRiemannZeta rho).toNat

/-- Positive argument dilation acts on the exact continued-source residue by the Mellin
character `r^(rho-1/2)`. -/
theorem continuedSourceResidueValue_argumentDilation
    (W : CompactBVPrimeWindow) (r : ℝ) (hr : 0 < r) (rho : ℂ) :
    (W.argumentDilation r hr).continuedSourceResidueValue rho =
      (r : ℂ) ^ (rho - 1 / 2) * W.continuedSourceResidueValue rho := by
  rw [continuedSourceResidueValue, continuedSourceResidueValue,
    mellinTransform_argumentDilation]
  ring

/-- Reciprocal argument dilation acts on the exact continued-source residue by the opposite
Mellin character `r^(1/2-rho)`. -/
theorem continuedSourceResidueValue_argumentExpansion
    (W : CompactBVPrimeWindow) (r : ℝ) (hr : 0 < r) (rho : ℂ) :
    (W.argumentExpansion r hr).continuedSourceResidueValue rho =
      (r : ℂ) ^ (1 / 2 - rho) * W.continuedSourceResidueValue rho := by
  rw [continuedSourceResidueValue, continuedSourceResidueValue,
    mellinTransform_argumentExpansion]
  ring

/-- Forward-minus-inverse squared Laurent-residue norm of the actual prime-window source. -/
def continuedSourceResidueOrientation
    (W : CompactBVPrimeWindow) (r : ℝ) (hr : 0 < r) (rho : ℂ) : ℝ :=
  ‖(W.argumentDilation r hr).continuedSourceResidueValue rho‖ ^ 2 -
    ‖(W.argumentExpansion r hr).continuedSourceResidueValue rho‖ ^ 2

/-- **Prime-window Laurent orientation law.**  The source-produced residue orientation is the
positive base residue mass times the exact horizontal reflection character. -/
theorem continuedSourceResidueOrientation_eq
    (W : CompactBVPrimeWindow) (r : ℝ) (hr : 0 < r) (rho : ℂ) :
    W.continuedSourceResidueOrientation r hr rho =
      ‖W.continuedSourceResidueValue rho‖ ^ 2 *
        (r ^ (2 * rho.re - 1) - r ^ (1 - 2 * rho.re)) := by
  rw [continuedSourceResidueOrientation,
    continuedSourceResidueValue_argumentDilation,
    continuedSourceResidueValue_argumentExpansion,
    norm_mul, norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos hr,
    Complex.norm_cpow_eq_rpow_re_of_pos hr]
  have hplus : ((rho - 1 / 2).re : ℝ) * 2 = 2 * rho.re - 1 := by
    norm_num [Complex.sub_re]
    ring
  have hminus : ((1 / 2 - rho).re : ℝ) * 2 = 1 - 2 * rho.re := by
    norm_num [Complex.sub_re]
    ring
  rw [mul_pow, mul_pow]
  rw [← Real.rpow_mul_natCast hr.le ((rho - 1 / 2).re) 2,
    ← Real.rpow_mul_natCast hr.le ((1 / 2 - rho).re) 2]
  norm_num only [Nat.cast_ofNat]
  rw [hplus, hminus]
  ring

/-- The actual BV residue orientation has positive sign exactly on the right of the critical
line, provided the source window does not censor that residue. -/
theorem continuedSourceResidueOrientation_pos_iff
    (W : CompactBVPrimeWindow) {r : ℝ} (hr : 1 < r) {rho : ℂ}
    (hres : W.continuedSourceResidueValue rho ≠ 0) :
    0 < W.continuedSourceResidueOrientation r (lt_trans zero_lt_one hr) rho ↔
      1 / 2 < rho.re := by
  rw [continuedSourceResidueOrientation_eq]
  have hmass : 0 < ‖W.continuedSourceResidueValue rho‖ ^ 2 := by positivity
  rw [mul_pos_iff_of_pos_left hmass, sub_pos,
    Real.rpow_lt_rpow_left_iff hr]
  constructor <;> intro h <;> linarith

/-- The orientation vanishes exactly on the critical line, again under noncensorship. -/
theorem continuedSourceResidueOrientation_eq_zero_iff
    (W : CompactBVPrimeWindow) {r : ℝ} (hr : 1 < r) {rho : ℂ}
    (hres : W.continuedSourceResidueValue rho ≠ 0) :
    W.continuedSourceResidueOrientation r (lt_trans zero_lt_one hr) rho = 0 ↔
      rho.re = 1 / 2 := by
  rw [continuedSourceResidueOrientation_eq]
  have hmass : ‖W.continuedSourceResidueValue rho‖ ^ 2 ≠ 0 := by positivity
  rw [mul_eq_zero, or_iff_right hmass]
  rw [sub_eq_zero, Real.rpow_right_inj (lt_trans zero_lt_one hr) hr.ne']
  constructor <;> intro h <;> linarith

/-- At every zero of the pole-filled zeta, the residue values used above are the actual punctured
limits of the two continued prime sources. -/
theorem tendsto_argumentDilation_expansion_continuedSource_residues
    (W : CompactBVPrimeWindow) (r : ℝ) (hr : 0 < r) {rho : ℂ}
    (hrho : 0 < rho.re) (hzero : regularizedRiemannZeta rho = 0) :
    Tendsto
        (fun s : ℂ => (s - (rho + 1 / 2)) *
          (W.argumentDilation r hr).continuedSource s)
        (nhdsWithin (rho + 1 / 2) ({rho + 1 / 2}ᶜ))
        (𝓝 ((W.argumentDilation r hr).continuedSourceResidueValue rho)) ∧
      Tendsto
        (fun s : ℂ => (s - (rho + 1 / 2)) *
          (W.argumentExpansion r hr).continuedSource s)
        (nhdsWithin (rho + 1 / 2) ({rho + 1 / 2}ᶜ))
        (𝓝 ((W.argumentExpansion r hr).continuedSourceResidueValue rho)) := by
  exact ⟨
    (W.argumentDilation r hr).tendsto_continuedSource_residue_of_regularizedZeta_zero
      hrho hzero,
    (W.argumentExpansion r hr).tendsto_continuedSource_residue_of_regularizedZeta_zero
      hrho hzero⟩

end CompactBVPrimeWindow
end RHTower
