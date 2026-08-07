import GaloisForLFunctions.RHTower.BurnolCartierZeroTransferHeadPolarization

/-!
# Oriented Stokes flux of Burnol's Cartier head energy

The fixed two-head energy defect of Cartier zero-transfer is exactly horizontal displacement times
one signed current formed from the divided shift before zero-transfer.  For the fixed co-Poisson
atom this oriented current is

`|(1-rho)⁻¹|² - (log 2)² |rho⁻¹|²`.

Thus two-head non-amplification requires no comparison of full metrics or separate head
conservation: it is pointwise equivalent to nonpositivity of this one oriented divided-shift
current.  Every identity and strict sign proved here is unconditional.  The remaining source
problem is to derive the opposite, nonpositive orientation at actual Xi divisors from
Euler--Gamma--Stokes structure.
-/

open Complex Real MeasureTheory Set Filter Topology
open scoped ENNReal InnerProductSpace ComplexConjugate

noncomputable section

namespace RHTower

/-! ## Oriented head current -/

/-- Signed two-Gamma-head current: forward head energy minus cosine-oriented head energy. -/
def burnolSoninOrientedGammaHeadFlux (a : ℝ) (f : evenSubspace) : ℝ :=
  ‖burnolSoninForwardHeadCoefficient a f‖ ^ 2 -
    ‖burnolSoninCosineHeadCoefficient a f‖ ^ 2

/-- Explicit rational value of the fixed-atom divided-shift head current. -/
def burnolCartierDividedShiftHeadFlux (rho : ℂ) : ℝ :=
  ‖((1 : ℂ) - rho)⁻¹‖ ^ 2 -
    (Real.log 2) ^ 2 * ‖rho⁻¹‖ ^ 2

/-- Forward aperture head of the divided shift, read by the intrinsic bounded coefficient. -/
theorem xiDivisor_burnolSoninForwardHeadCoefficient_mellinDividedShift
    (rho : XiDivisorSupport) (h : 1 / 2 < (rho : ℂ).re) :
    burnolSoninForwardHeadCoefficient (1 / 2)
        (burnolMellinDividedShift h burnolFixedSubWindowSourceAtom) =
      ((1 : ℂ) - (rho : ℂ))⁻¹ :=
  burnolSoninForwardHeadCoefficient_eq_of_headEquals (by norm_num) _
    (xiDivisor_burnolMellinDividedShift_fixed_head rho h)

/-- Cosine-oriented aperture head of the same divided shift. -/
theorem xiDivisor_burnolSoninCosineHeadCoefficient_mellinDividedShift
    (rho : XiDivisorSupport) (h : 1 / 2 < (rho : ℂ).re) :
    burnolSoninCosineHeadCoefficient (1 / 2)
        (burnolMellinDividedShift h burnolFixedSubWindowSourceAtom) =
      -(Real.log 2 : ℂ) / (rho : ℂ) :=
  burnolSoninCosineHeadCoefficient_eq_of_headEquals (by norm_num) _
    (xiDivisor_burnolMellinDividedShift_fixed_cosine_head rho h)

/-- The intrinsic oriented current of the divided shift is the explicit rational flux. -/
theorem xiDivisor_burnolSoninOrientedGammaHeadFlux_mellinDividedShift
    (rho : XiDivisorSupport) (h : 1 / 2 < (rho : ℂ).re) :
    burnolSoninOrientedGammaHeadFlux (1 / 2)
        (burnolMellinDividedShift h burnolFixedSubWindowSourceAtom) =
      burnolCartierDividedShiftHeadFlux (rho : ℂ) := by
  rw [burnolSoninOrientedGammaHeadFlux,
    xiDivisor_burnolSoninForwardHeadCoefficient_mellinDividedShift rho h,
    xiDivisor_burnolSoninCosineHeadCoefficient_mellinDividedShift rho h,
    burnolCartierDividedShiftHeadFlux, norm_div, norm_neg, norm_inv,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.log_pos one_lt_two)]
  rw [norm_inv]
  ring

/-! ## Exact Cartier transgression -/

/-- Algebraic transgression for the reciprocal Cartier gains.  It is stated away from `0` and `1`
and uses no divisor or vanishing hypothesis. -/
theorem burnolCartier_gammaHeadEnergyDefect_eq_horizontal_mul_dividedShiftHeadFlux
    {rho : ℂ} (hrho : rho ≠ 0) (hrhoOne : rho ≠ 1) :
    ‖burnolCartierForwardHeadGain rho‖ ^ 2 +
          (Real.log 2) ^ 2 * ‖burnolCartierCosineHeadGain rho‖ ^ 2 -
        (1 + (Real.log 2) ^ 2) =
      (2 * (rho.re - 1 / 2)) * burnolCartierDividedShiftHeadFlux rho := by
  have hnormRho : ‖rho‖ ≠ 0 := norm_ne_zero_iff.mpr hrho
  have hnormOneSub : ‖(1 : ℂ) - rho‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (sub_ne_zero.mpr hrhoOne.symm)
  have hcosNum : ‖(1 : ℂ) - conj rho‖ = ‖(1 : ℂ) - rho‖ := by
    simpa using (norm_conj ((1 : ℂ) - rho))
  have hhorizontal :
      ‖rho‖ ^ 2 - ‖(1 : ℂ) - rho‖ ^ 2 = 2 * (rho.re - 1 / 2) := by
    rw [Complex.sq_norm, Complex.sq_norm]
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.one_re,
      Complex.sub_im, Complex.one_im]
    ring
  unfold burnolCartierForwardHeadGain burnolCartierCosineHeadGain
    burnolCartierDividedShiftHeadFlux
  rw [norm_div, norm_conj, norm_div, hcosNum, norm_inv, norm_inv]
  rw [← hhorizontal]
  field_simp [hnormRho, hnormOneSub]
  ring

/-- **Exact head-energy Stokes transgression.**  At an actual right-half Xi divisor, the transferred
positive two-head energy defect is horizontal displacement times the oriented divided-shift head
current. -/
theorem xiDivisor_burnolCartier_gammaHeadEnergyDefect_eq_horizontal_mul_headFlux
    (rho : XiDivisorSupport) (h : 1 / 2 < (rho : ℂ).re) :
    burnolSoninGammaHeadEnergy (1 / 2)
          (burnolCartierZeroTransfer h burnolFixedSubWindowSourceAtom) -
        burnolSoninGammaHeadEnergy (1 / 2) burnolFixedSubWindowSourceAtom =
      (2 * ((rho : ℂ).re - 1 / 2)) *
        burnolSoninOrientedGammaHeadFlux (1 / 2)
          (burnolMellinDividedShift h burnolFixedSubWindowSourceAtom) := by
  rw [xiDivisor_burnolSoninGammaHeadEnergy_cartierZeroTransfer rho h,
    burnolSoninGammaHeadEnergy_fixedSubWindowSourceAtom,
    xiDivisor_burnolSoninOrientedGammaHeadFlux_mellinDividedShift rho h]
  apply burnolCartier_gammaHeadEnergyDefect_eq_horizontal_mul_dividedShiftHeadFlux
  · intro hrho
    rw [hrho] at h
    norm_num at h
  · intro hrho
    have hlt := xiDivisor_re_lt_one_of_half_lt rho h
    rw [hrho] at hlt
    norm_num at hlt

/-! ## Strict orientation and quantitative floor -/

/-- The explicit divided-shift current is strictly positive in the open right half of the critical
strip. -/
theorem burnolCartierDividedShiftHeadFlux_pos
    {rho : ℂ} (hright : 1 / 2 < rho.re) (hlt : rho.re < 1) :
    0 < burnolCartierDividedShiftHeadFlux rho := by
  have hrho : rho ≠ 0 := by
    intro hz
    rw [hz] at hright
    norm_num at hright
  have hrhoOne : rho ≠ 1 := by
    intro hz
    rw [hz] at hlt
    norm_num at hlt
  let x : ℝ := ‖rho‖
  let y : ℝ := ‖(1 : ℂ) - rho‖
  let L : ℝ := Real.log 2
  have hx : 0 < x := norm_pos_iff.mpr hrho
  have hy : 0 < y := norm_pos_iff.mpr (sub_ne_zero.mpr hrhoOne.symm)
  have hxy : y < x := by
    have hgain := one_lt_norm_burnolCartierForwardHeadGain hright hlt
    unfold burnolCartierForwardHeadGain at hgain
    rw [norm_div, norm_conj, one_lt_div hy] at hgain
    exact hgain
  have hLpos : 0 < L := Real.log_pos one_lt_two
  have hLlt : L < 1 := by
    dsimp [L]
    linarith [Real.log_two_lt_d9]
  have hLy : L * y < x :=
    lt_trans (mul_lt_mul_of_pos_right hLlt hy) (by simpa using hxy)
  have hratio : L / x < 1 / y := (div_lt_div_iff₀ hx hy).2 (by simpa using hLy)
  have hratio' : L * x⁻¹ < y⁻¹ := by simpa [div_eq_mul_inv] using hratio
  have hxInv : 0 ≤ x⁻¹ := (inv_pos.mpr hx).le
  have hyInv : 0 ≤ y⁻¹ := (inv_pos.mpr hy).le
  have hLInv : 0 ≤ L * x⁻¹ := mul_nonneg hLpos.le hxInv
  unfold burnolCartierDividedShiftHeadFlux
  rw [norm_inv, norm_inv]
  change 0 < y⁻¹ ^ 2 - L ^ 2 * x⁻¹ ^ 2
  nlinarith [sq_nonneg (y⁻¹), sq_nonneg (L * x⁻¹)]

/-- Quantitative right-half floor.  The current exceeds the strictly positive residual Gamma
weight divided by `|rho|²`. -/
theorem burnolCartierDividedShiftHeadFlux_gt_gammaFloor
    {rho : ℂ} (hright : 1 / 2 < rho.re) (hlt : rho.re < 1) :
    (1 - (Real.log 2) ^ 2) * ‖rho‖⁻¹ ^ 2 <
      burnolCartierDividedShiftHeadFlux rho := by
  have hrho : rho ≠ 0 := by
    intro hz
    rw [hz] at hright
    norm_num at hright
  have hrhoOne : rho ≠ 1 := by
    intro hz
    rw [hz] at hlt
    norm_num at hlt
  let x : ℝ := ‖rho‖
  let y : ℝ := ‖(1 : ℂ) - rho‖
  have hx : 0 < x := norm_pos_iff.mpr hrho
  have hy : 0 < y := norm_pos_iff.mpr (sub_ne_zero.mpr hrhoOne.symm)
  have hxy : y < x := by
    have hgain := one_lt_norm_burnolCartierForwardHeadGain hright hlt
    unfold burnolCartierForwardHeadGain at hgain
    rw [norm_div, norm_conj, one_lt_div hy] at hgain
    exact hgain
  have hinv : x⁻¹ < y⁻¹ := (inv_lt_inv₀ hx hy).2 hxy
  have hxInv : 0 ≤ x⁻¹ := (inv_pos.mpr hx).le
  have hyInv : 0 ≤ y⁻¹ := (inv_pos.mpr hy).le
  unfold burnolCartierDividedShiftHeadFlux
  rw [norm_inv, norm_inv]
  change (1 - (Real.log 2) ^ 2) * x⁻¹ ^ 2 <
    y⁻¹ ^ 2 - (Real.log 2) ^ 2 * x⁻¹ ^ 2
  nlinarith [sq_nonneg (x⁻¹), sq_nonneg (y⁻¹)]

/-- Every hypothetical right-half Xi divisor gives a strictly positive intrinsic divided-shift
head current. -/
theorem xiDivisor_burnolSoninOrientedGammaHeadFlux_mellinDividedShift_pos
    (rho : XiDivisorSupport) (h : 1 / 2 < (rho : ℂ).re) :
    0 < burnolSoninOrientedGammaHeadFlux (1 / 2)
      (burnolMellinDividedShift h burnolFixedSubWindowSourceAtom) := by
  rw [xiDivisor_burnolSoninOrientedGammaHeadFlux_mellinDividedShift rho h]
  exact burnolCartierDividedShiftHeadFlux_pos h
    (xiDivisor_re_lt_one_of_half_lt rho h)

/-! ## Reduced source producer and Route R endpoint -/

/-- Pointwise, two-head non-amplification is exactly nonpositivity of the pre-transfer oriented
head current. -/
theorem xiDivisor_burnolCartier_gammaHeadEnergy_nonamplification_iff_headFlux_nonpos
    (rho : XiDivisorSupport) (h : 1 / 2 < (rho : ℂ).re) :
    burnolSoninGammaHeadEnergy (1 / 2)
          (burnolCartierZeroTransfer h burnolFixedSubWindowSourceAtom) ≤
        burnolSoninGammaHeadEnergy (1 / 2) burnolFixedSubWindowSourceAtom ↔
      burnolSoninOrientedGammaHeadFlux (1 / 2)
          (burnolMellinDividedShift h burnolFixedSubWindowSourceAtom) ≤ 0 := by
  have hfactor : 0 < 2 * ((rho : ℂ).re - 1 / 2) := by linarith
  constructor
  · intro henergy
    have hdefect :
        burnolSoninGammaHeadEnergy (1 / 2)
              (burnolCartierZeroTransfer h burnolFixedSubWindowSourceAtom) -
            burnolSoninGammaHeadEnergy (1 / 2) burnolFixedSubWindowSourceAtom ≤ 0 :=
      sub_nonpos.mpr henergy
    rw [xiDivisor_burnolCartier_gammaHeadEnergyDefect_eq_horizontal_mul_headFlux rho h]
      at hdefect
    by_contra hflux
    exact (not_lt_of_ge hdefect) (mul_pos hfactor (lt_of_not_ge hflux))
  · intro hflux
    apply sub_nonpos.mp
    rw [xiDivisor_burnolCartier_gammaHeadEnergyDefect_eq_horizontal_mul_headFlux rho h]
    exact mul_nonpos_of_nonneg_of_nonpos hfactor.le hflux

/-- Sharpened source-facing Route R producer: one fixed, signed divided-shift current must be
nonpositive. -/
def BurnolXiCartierDividedShiftHeadFluxDissipativity : Prop :=
  ∀ (rho : XiDivisorSupport) (h : 1 / 2 < (rho : ℂ).re),
    burnolSoninOrientedGammaHeadFlux (1 / 2)
      (burnolMellinDividedShift h burnolFixedSubWindowSourceAtom) ≤ 0

/-- The previous two-head contraction and the oriented-current producer are exactly equivalent. -/
theorem burnolXiCartierZeroTransferGammaHeadEnergyNonamplification_iff_headFluxDissipativity :
    BurnolXiCartierZeroTransferGammaHeadEnergyNonamplification ↔
      BurnolXiCartierDividedShiftHeadFluxDissipativity := by
  constructor
  · intro henergy rho h
    exact (xiDivisor_burnolCartier_gammaHeadEnergy_nonamplification_iff_headFlux_nonpos rho h).mp
      (henergy rho h)
  · intro hflux rho h
    exact (xiDivisor_burnolCartier_gammaHeadEnergy_nonamplification_iff_headFlux_nonpos rho h).mpr
      (hflux rho h)

/-- Route R closes if pre-divisor Euler--Gamma--Stokes structure gives nonpositivity of the single
oriented divided-shift head current. -/
theorem riemannHypothesis_of_burnolXiCartierDividedShiftHeadFluxDissipativity
    (hflux : BurnolXiCartierDividedShiftHeadFluxDissipativity) :
    RiemannHypothesis :=
  riemannHypothesis_of_burnolXiCartierZeroTransferGammaHeadEnergyNonamplification
    (burnolXiCartierZeroTransferGammaHeadEnergyNonamplification_iff_headFluxDissipativity.mpr
      hflux)

end RHTower
