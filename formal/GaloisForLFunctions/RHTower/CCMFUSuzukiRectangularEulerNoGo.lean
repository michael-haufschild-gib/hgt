import GaloisForLFunctions.RHTower.CCMFUSuzukiPositiveMixture

/-!
# CCM-FU rectangular Euler inversion no-go

The third-grade marked rectangular operator has the formal Euler factor
`(D - 4) (D - 3)` after multiplication by `H^4`.  It is tempting to invert that
factor using only a uniform bound on the scalar output.  The exact quadratic test below rules
this out: after affine normalization, the unbounded source `(t - b)^2` has a uniformly bounded
literal rectangular response.  Thus an inverse must use source-specific prime--polar or divisor
information; reporter boundedness and Volterra geometry alone cannot recover the source.
-/

open Complex MeasureTheory Set

noncomputable section

namespace GaloisForLFunctions.RHTower

open _root_.RHTower

/-- Exact raw quadratic moment of the literal third-grade marked rectangular measure. -/
theorem rectangularMixDensity_quadratic_raw
    {b H : ℝ} (hb : 0 < b) (hbH : b ≤ H) :
    (∫ t in b..H, ccmThirdGradeCesaroRectangularMixDensity H t * t ^ 2) +
      (32 / H ^ 4) * H ^ 2 =
      192 / b ^ 2 - 192 / (H * b) + 32 / H ^ 2 := by
  have hH : 0 < H := hb.trans_le hbH
  let P : ℝ → ℝ := fun t => -192 / t ^ 2 + (192 / H) / t
  have hP : ∀ t ∈ Set.uIcc b H,
      HasDerivAt P (ccmThirdGradeCesaroRectangularMixDensity H t * t ^ 2) t := by
    intro t ht
    rw [Set.uIcc_of_le hbH] at ht
    have ht0 : t ≠ 0 := (hb.trans_le ht.1).ne'
    have h1raw := (hasDerivAt_const (x := t) (c := (1 : ℝ))).div
      (hasDerivAt_id t) ht0
    simp only [id_eq] at h1raw
    have h1 : HasDerivAt (fun x : ℝ => 1 / x) (-1 / t ^ 2) t := by
      apply h1raw.congr_deriv
      field_simp [ht0]
      ring
    have h2raw := (hasDerivAt_const (x := t) (c := (1 : ℝ))).div
      ((hasDerivAt_id t).pow 2) (pow_ne_zero 2 ht0)
    simp only [Pi.pow_apply, id_eq] at h2raw
    have h2 : HasDerivAt (fun x : ℝ => 1 / x ^ 2) (-2 / t ^ 3) t := by
      apply h2raw.congr_deriv
      field_simp [ht0]
      ring
    have hraw := (h2.const_mul (-192)).add (h1.const_mul (192 / H))
    have hPfun : P = fun y => -192 * (1 / y ^ 2) + (192 / H) * (1 / y) := by
      funext y
      dsimp only [P]
      ring
    rw [hPfun]
    apply hraw.congr_deriv
    unfold ccmThirdGradeCesaroRectangularMixDensity
    field_simp [ht0, hH.ne']
    ring
  have hint : IntervalIntegrable
      (fun t => ccmThirdGradeCesaroRectangularMixDensity H t * t ^ 2)
      volume b H := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    have ht0 : t ≠ 0 := by
      rw [Set.uIcc_of_le hbH] at ht
      exact (hb.trans_le ht.1).ne'
    unfold ccmThirdGradeCesaroRectangularMixDensity
    exact (((continuousAt_const.mul (continuousAt_const.sub continuousAt_id)).div
      (continuousAt_const.mul (continuousAt_id.pow 5))
      (mul_ne_zero hH.ne' (pow_ne_zero 5 ht0))).mul
        (continuousAt_id.pow 2)).continuousWithinAt
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hP hint]
  dsimp only [P]
  field_simp [hb.ne', hH.ne']
  ring

/-- **Sharp scalar-Euler obstruction.**  Affine-normalized quadratic growth survives every
literal source-faithful rectangular averaging window but has bounded output. -/
theorem rectangularMixDensity_quadratic_codiagonal
    {b H : ℝ} (hb : 0 < b) (hbH : b ≤ H) :
    (∫ t in b..H,
        ccmThirdGradeCesaroRectangularMixDensity H t * (t - b) ^ 2) +
      (32 / H ^ 4) * (H - b) ^ 2 =
      32 * (1 / b - 1 / H) ^ 2 := by
  have hH : 0 < H := hb.trans_le hbH
  have hraw := rectangularMixDensity_quadratic_raw hb hbH
  have hmass := integral_rectangularMixDensity_add_endpoint_eq_errorKernel hb hbH
  have hfirst := integral_rectangularMixDensity_mul_sub_add_endpoint_eq hb hbH
  have h0 : IntervalIntegrable (ccmThirdGradeCesaroRectangularMixDensity H) volume b H := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    have ht0 : t ≠ 0 := by
      rw [Set.uIcc_of_le hbH] at ht
      exact (hb.trans_le ht.1).ne'
    unfold ccmThirdGradeCesaroRectangularMixDensity
    exact ((continuousAt_const.mul (continuousAt_const.sub continuousAt_id)).div
      (continuousAt_const.mul (continuousAt_id.pow 5))
      (mul_ne_zero hH.ne' (pow_ne_zero 5 ht0))).continuousWithinAt
  have h1 : IntervalIntegrable
      (fun t => ccmThirdGradeCesaroRectangularMixDensity H t * t) volume b H := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hbH]
    intro t ht
    have ht0 : t ≠ 0 := (hb.trans_le ht.1).ne'
    unfold ccmThirdGradeCesaroRectangularMixDensity
    exact ((continuousAt_const.mul (continuousAt_const.sub continuousAt_id)).div
      (continuousAt_const.mul (continuousAt_id.pow 5))
      (mul_ne_zero hH.ne' (pow_ne_zero 5 ht0))).mul continuousAt_id |>.continuousWithinAt
  have h2 : IntervalIntegrable
      (fun t => ccmThirdGradeCesaroRectangularMixDensity H t * t ^ 2) volume b H := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hbH]
    intro t ht
    have ht0 : t ≠ 0 := (hb.trans_le ht.1).ne'
    unfold ccmThirdGradeCesaroRectangularMixDensity
    exact ((continuousAt_const.mul (continuousAt_const.sub continuousAt_id)).div
      (continuousAt_const.mul (continuousAt_id.pow 5))
      (mul_ne_zero hH.ne' (pow_ne_zero 5 ht0))).mul (continuousAt_id.pow 2) |>.continuousWithinAt
  have hcenter :
      (∫ t in b..H,
          ccmThirdGradeCesaroRectangularMixDensity H t * (t - b)) +
        (32 / H ^ 4) * (H - b) =
      ((∫ t in b..H, ccmThirdGradeCesaroRectangularMixDensity H t * t) +
        (32 / H ^ 4) * H) -
        b * ((∫ t in b..H, ccmThirdGradeCesaroRectangularMixDensity H t) + 32 / H ^ 4) := by
    have hexpand :
        (fun t => ccmThirdGradeCesaroRectangularMixDensity H t * (t - b)) =
          fun t => ccmThirdGradeCesaroRectangularMixDensity H t * t -
            b * ccmThirdGradeCesaroRectangularMixDensity H t := by
      funext t
      ring
    rw [hexpand, intervalIntegral.integral_sub h1 (h0.const_mul b),
      intervalIntegral.integral_const_mul]
    ring
  have hrawFirst :
      (∫ t in b..H, ccmThirdGradeCesaroRectangularMixDensity H t * t) +
        (32 / H ^ 4) * H =
        (32 / b ^ 3 - 32 / (H * b ^ 2)) +
          b * ccmGuinandWeilThirdGradeCesaroErrorKernel H b := by
    rw [hcenter] at hfirst
    linear_combination hfirst + b * hmass
  have hcomb :
      (∫ t in b..H,
          ccmThirdGradeCesaroRectangularMixDensity H t * (t - b) ^ 2) +
        (32 / H ^ 4) * (H - b) ^ 2 =
      ((∫ t in b..H, ccmThirdGradeCesaroRectangularMixDensity H t * t ^ 2) +
        (32 / H ^ 4) * H ^ 2) -
      2 * b * ((∫ t in b..H, ccmThirdGradeCesaroRectangularMixDensity H t * t) +
        (32 / H ^ 4) * H) +
      b ^ 2 * ((∫ t in b..H, ccmThirdGradeCesaroRectangularMixDensity H t) +
        32 / H ^ 4) := by
    have hexpand :
        (fun t => ccmThirdGradeCesaroRectangularMixDensity H t * (t - b) ^ 2) =
          fun t => ccmThirdGradeCesaroRectangularMixDensity H t * t ^ 2 -
            2 * b * (ccmThirdGradeCesaroRectangularMixDensity H t * t) +
              b ^ 2 * ccmThirdGradeCesaroRectangularMixDensity H t := by
      funext t
      ring
    rw [hexpand, intervalIntegral.integral_add
      (h2.sub (h1.const_mul (2 * b))) (h0.const_mul (b ^ 2)),
      intervalIntegral.integral_sub h2 (h1.const_mul (2 * b)),
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul]
    ring
  unfold ccmGuinandWeilThirdGradeCesaroErrorKernel at hrawFirst hmass
  rw [hcomb, hraw, hrawFirst, hmass]
  field_simp [hb.ne', hH.ne']
  ring

end GaloisForLFunctions.RHTower
