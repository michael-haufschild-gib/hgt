import GaloisForLFunctions.RHTower.CCMArchimedeanFourierTail
import GaloisForLFunctions.RHTower.SuzukiMatchedOddSourceBound

open MeasureTheory Set Filter
open scoped InnerProduct
open GaloisForLFunctions.HTGeometry
noncomputable section
namespace RHTower


private theorem shifted_quadratic_low_tail (a : SuzukiPositiveAperture) (R : ℝ)
    (hband : ∀ ξ ∈ centralInterval R, ‖ccmArchimedeanRemainderScalar +
      (polarPrimeStieltjesSymbol a.1 (-2 * Real.pi * ξ) : ℂ)‖ ≤
        boundedPerturbedFormShift (suzukiWeilIntervalBoundedRemainder a) / 4)
    (f : suzukiApertureHilbert a) :
    let c := boundedPerturbedFormShift (suzukiWeilIntervalBoundedRemainder a)
    let D := ‖ccmArchimedeanRemainderScalar‖ + 46
    c / 2 * ‖f‖ ^ 2 - 4 * D ^ 2 * c *
      ‖f.1 - fourierCutoff (centralInterval R) (measurableSet_centralInterval R) f.1‖ ^ 2 ≤
        (inner ℂ (ccmShiftedBoundedWeil a f) f).re := by
  let c := boundedPerturbedFormShift (suzukiWeilIntervalBoundedRemainder a)
  let D := ‖ccmArchimedeanRemainderScalar‖ + 46
  let T := ‖f.1 - fourierCutoff (centralInterval R) (measurableSet_centralInterval R) f.1‖
  have hc : 0 < c := boundedPerturbedFormShift_pos _
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hT : 0 ≤ T := norm_nonneg _
  have hbound := norm_ccmRestrictedWeilBoundedRemainder_le_low_add_tail a R (c / 4)
    (by positivity) hband f
  have hscale := exp_aperture_le_twice_suzukiWeilIntervalShift a
  have htail : D * Real.exp a.1 * T ≤ 2 * D * c * T := by
    have h := mul_le_mul_of_nonneg_left hscale (mul_nonneg hD hT)
    nlinarith only [h]
  have hnorm : ‖ccmRestrictedWeilBoundedRemainder a f‖ ≤ c / 4 * ‖f‖ + 2 * D * c * T :=
    hbound.trans (add_le_add (le_refl _) htail)
  have hRe : -(inner ℂ (ccmRestrictedWeilBoundedRemainder a f) f).re ≤
      ‖ccmRestrictedWeilBoundedRemainder a f‖ * ‖f‖ := by
    have h := re_inner_le_norm (𝕜 := ℂ) (-(ccmRestrictedWeilBoundedRemainder a f)) f
    change (inner ℂ (-(ccmRestrictedWeilBoundedRemainder a f)) f).re ≤ _ at h
    simpa only [inner_neg_left, Complex.neg_re, norm_neg] using h
  have hprod := mul_le_mul_of_nonneg_right hnorm (norm_nonneg f)
  have hYoung := mul_nonneg hc.le (sq_nonneg (‖f‖ / 2 - 2 * D * T))
  rw [ccmShiftedBoundedWeil_re_inner]
  change c / 2 * ‖f‖ ^ 2 - 4 * D ^ 2 * c * T ^ 2 ≤
    c * ‖f‖ ^ 2 + (inner ℂ (ccmRestrictedWeilBoundedRemainder a f) f).re
  nlinarith only [hRe, hprod, hYoung]

/-- The physical coercivity of the literal shifted Suzuki form eventually
exceeds every fixed multiple of aperture, uniformly for all Ta vectors.
Both frequency regions are controlled by the actual prime--polar--Gamma form. -/
theorem eventually_suzukiTa_physical_coercivity (L : ℝ) :
    ∀ᶠ a : ℝ in atTop, ∀ ha : 0 < a, ∀ w : SuzukiTaHilbert ⟨a, ha⟩,
      L * a * ‖suzukiTaPhysicalEmbedding ⟨a, ha⟩ w‖ ^ 2 ≤ ‖w‖ ^ 2 := by
  by_cases hL : 0 < L
  · let D := ‖ccmArchimedeanRemainderScalar‖ + 46
    let M := 4 * D ^ 2
    let C := ccmArchimedeanLogComparisonConstant
    let K := 2 * C * M * L
    have hD : 0 < D := by dsimp [D]; positivity
    have hM : 0 < M := by dsimp [M]; positivity
    have hC : 0 < C := zero_lt_one.trans_le one_le_ccmArchimedeanLogComparisonConstant
    have hK : 0 < K := by dsimp [K]; positivity
    filter_upwards [eventually_ccmFullLineRemainder_symbol_small K (1 / 4) hK (by positivity),
      (Real.tendsto_exp_div_pow_atTop 1).eventually (eventually_ge_atTop (4 * L))]
      with a hsymbol hscale
    intro ha w
    let ap : SuzukiPositiveAperture := ⟨a, ha⟩
    let c := boundedPerturbedFormShift (suzukiWeilIntervalBoundedRemainder ap)
    let g := suzukiTaToFormCLM ap w
    let f := ccmArchimedeanFormToAperture ap g
    let T := ‖f.1 - fourierCutoff (centralInterval (Real.exp (K * a)))
      (measurableSet_centralInterval (Real.exp (K * a))) f.1‖
    let A := (inner ℂ (ccmShiftedBoundedWeil ap f) f).re
    have hc : 0 < c := boundedPerturbedFormShift_pos _
    have hcL : 2 * L * a ≤ c := by
      have h : 4 * L ≤ Real.exp a / a := by simpa only [pow_one] using hscale
      have hexp : 4 * L * a ≤ Real.exp a := (le_div_iff₀ ha).mp h
      have hs := exp_aperture_le_twice_suzukiWeilIntervalShift ap
      change Real.exp a ≤ 2 * c at hs
      linarith
    have hband : ∀ ξ ∈ centralInterval (Real.exp (K * a)),
        ‖ccmArchimedeanRemainderScalar + (polarPrimeStieltjesSymbol a (-2 * Real.pi * ξ) : ℂ)‖ ≤
          c / 4 := by
      intro ξ hξ
      have h := hsymbol ξ (abs_le.mpr hξ)
      have hs := exp_aperture_le_twice_suzukiWeilIntervalShift ap
      change Real.exp a ≤ 2 * c at hs
      linarith
    have hA : c / 2 * ‖f‖ ^ 2 - M * c * T ^ 2 ≤ A :=
      shifted_quadratic_low_tail ap (Real.exp (K * a)) hband f
    have hA0 : 0 ≤ A := (sq_nonneg ‖f‖).trans (ccmShiftedBoundedWeil_coercive ap f)
    have htail : K * a * T ^ 2 ≤ C * ‖g‖ ^ 2 :=
      mul_norm_sq_sub_fourierCutoff_exp_le_ccmArchimedeanFormNorm ap g (K * a)
    have hG : 2 * M * L * a * T ^ 2 ≤ ‖g‖ ^ 2 := by
      apply le_of_mul_le_mul_left (a := C) ?_ hC
      calc
        _ = K * a * T ^ 2 := by dsimp [K]; ring
        _ ≤ _ := htail
    have henergy : ‖w‖ ^ 2 = ‖g‖ ^ 2 + A := suzukiTa_energy_decomposition ap w
    have hphys : ‖suzukiTaPhysicalEmbedding ap w‖ = ‖f‖ :=
      (suzukiApertureL2Equiv ap).symm.norm_map f
    change L * a * ‖suzukiTaPhysicalEmbedding ap w‖ ^ 2 ≤ ‖w‖ ^ 2
    rw [hphys, henergy]
    have hmul := mul_le_mul_of_nonneg_left hA (show 0 ≤ 2 * L * a by positivity)
    have hpay := mul_le_mul_of_nonneg_right hcL hA0
    have hGamma := mul_le_mul_of_nonneg_left hG hc.le
    apply le_of_mul_le_mul_left (a := c) ?_ hc
    nlinarith only [hmul, hpay, hGamma]
  · filter_upwards [] with a
    intro ha w
    exact (mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hL) ha.le) (sq_nonneg _)).trans (sq_nonneg _)

end RHTower
end
