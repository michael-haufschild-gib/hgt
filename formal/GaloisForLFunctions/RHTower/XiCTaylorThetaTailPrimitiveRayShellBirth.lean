import GaloisForLFunctions.RHTower.XiCTaylorThetaTailPrimitiveRayArithmeticPartition
import GaloisForLFunctions.RHTower.XiCTaylorThetaTailPrimitiveRaySeamReflection
import GaloisForLFunctions.RHTower.XiCTaylorThetaTailCompletedFeedback

/-!
# Shell-birth law for the primitive theta-ray seam

The moving angular window of a primitive direction first appears at its Euclidean logarithmic
height.  This file proves that its two endpoints coincide there, that the finite core current at
the newborn endpoint is exactly zero, and that the first nonzero endpoint variation is
quadratically favorable: its second source derivative is `-z.im`, independently of the Taylor
depth.

Thus there is no positive atomic current created when a new primitive lattice shell enters.  The
remaining obstruction is the accumulated continuous boundary layer away from the birth radius.
-/

open Complex Real MeasureTheory Set

namespace RHTower

noncomputable section

theorem truncatedCosineSection_zero (d : ℕ) (z : ℂ) :
    truncatedCosineSection d z 0 = 1 := by
  unfold truncatedCosineSection
  rw [Finset.sum_eq_single 0]
  · norm_num
  · intro k hk hk0
    have hkpos : 0 < 2 * k := Nat.mul_pos (by norm_num) (Nat.pos_of_ne_zero hk0)
    simp [zero_pow hkpos.ne']
  · simp

theorem truncatedCosineSectionDerivative_zero (d : ℕ) (z : ℂ) :
    truncatedCosineSectionDerivative d z 0 = 0 := by
  unfold truncatedCosineSectionDerivative
  apply Finset.sum_eq_zero
  intro k hk
  by_cases hk0 : k = 0
  · subst k
    norm_num
  · have hkpos : 0 < 2 * k := Nat.mul_pos (by norm_num) (Nat.pos_of_ne_zero hk0)
    simp [zero_pow hkpos.ne']

/-- The spectral source derivative has a double source zero at the half-line endpoint. -/
theorem hasDerivAt_thetaCuspTailSecondSectionSourceSpectralDerivative_zero
    (d : ℕ) (z : ℂ) :
    HasDerivAt
      (fun t : ℝ => thetaCuspTailSecondSectionSourceSpectralDerivative d z t) 0 0 := by
  unfold thetaCuspTailSecondSectionSourceSpectralDerivative
  have hsum := HasDerivAt.sum (u := Finset.range (d + 1))
    (A := fun (k : ℕ) (t : ℝ) =>
      (-1 : ℂ) ^ k * ((2 * k : ℕ) : ℂ) * z ^ (2 * k - 1) *
        ((2 * k + 2 : ℕ) : ℂ) *
          ((t : ℂ) ^ (2 * k + 1) / (2 * k + 2).factorial))
    (A' := fun (_k : ℕ) => (0 : ℂ))
    (fun k _hk => by
      have hbase : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 0 := by
        have h := Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))
        have hval : (Complex.ofRealCLM 1 : ℂ) = 1 := by
          simp [Complex.ofRealCLM_apply]
        rw [hval] at h
        exact h
      have hpow := hbase.pow (2 * k + 1)
      have hscaled :=
        (HasDerivAt.const_mul
          ((-1 : ℂ) ^ k * ((2 * k : ℕ) : ℂ) * z ^ (2 * k - 1) *
            ((2 * k + 2 : ℕ) : ℂ)) hpow).mul_const
              (((2 * k + 2).factorial : ℂ)⁻¹)
      convert hscaled using 1
      · rfl
      · funext y
        simp only [Pi.pow_apply, div_eq_mul_inv]
        ring
      · by_cases hk0 : k = 0
        · subst k
          norm_num
        · have hkpos : 0 < 2 * k := Nat.mul_pos (by norm_num) (Nat.pos_of_ne_zero hk0)
          rw [show 2 * k + 1 - 1 = 2 * k by omega]
          simp [zero_pow hkpos.ne'])
  convert hsum using 1
  · rfl
  · funext t
    simp only [Finset.sum_apply]
  · simp

/-- **Universal endpoint two-jet.**  The second source derivative of the finite core's spectral
derivative is exactly `-2z`; all Taylor layers beyond the initial quadratic term vanish at the
endpoint. -/
theorem hasDerivAt_thetaCuspTailSecondCoreAtomSourceSpectralDerivative_zero
    (d : ℕ) (z : ℂ) :
    HasDerivAt
      (fun t : ℝ => thetaCuspTailSecondCoreAtomSourceSpectralDerivative d z t)
      (-2 * z) 0 := by
  have hsource := hasDerivAt_thetaCuspTailSecondSectionSourceDerivative d z 0
  rw [thetaCuspTailSecondSectionSourceSecondDerivative_eq_truncatedCosine,
    truncatedCosineSection_zero] at hsource
  have hspectral :=
    hasDerivAt_thetaCuspTailSecondSectionSourceSpectralDerivative_zero d z
  unfold thetaCuspTailSecondCoreAtomSourceSpectralDerivative
  convert (hsource.const_mul (-2 * z)).sub
    (hspectral.const_mul (z ^ (2 : ℕ) + 1 / 4)) using 1
  · rfl
  · rfl
  · ring

theorem thetaCuspTailSecondCoreAtomDerivative_sourceSecondDerivative_zero
    (d : ℕ) (z : ℂ) :
    deriv
      (fun x : ℝ => thetaCuspTailSecondCoreAtomSourceSpectralDerivative d z x) 0 =
      -2 * z :=
  (hasDerivAt_thetaCuspTailSecondCoreAtomSourceSpectralDerivative_zero d z).deriv

/-- Source derivative of the rank-one endpoint pair current. -/
theorem hasDerivAt_xiCTaylorThetaTailCorePairCurrent_zero_right
    (d : ℕ) (z : ℂ) (x : ℝ) :
    HasDerivAt
      (fun t : ℝ => xiCTaylorThetaTailCorePairCurrent d z (t, 0))
      ((thetaCuspTailSecondCoreAtomSourceSpectralDerivative d z x).im / 2) x := by
  rw [show (fun t : ℝ => xiCTaylorThetaTailCorePairCurrent d z (t, 0)) =
      fun t : ℝ => (thetaCuspTailSecondCoreAtomDerivative d z t).im / 2 by
    funext t
    exact xiCTaylorThetaTailCorePairCurrent_zero_right d z t]
  have h := hasDerivAt_thetaCuspTailSecondCoreAtomDerivative_source d z x
  convert ((hasDerivAt_const x Complex.imCLM).clm_apply h).div_const 2 using 1
  · rfl
  · rfl
  · rfl
  · simp

/-- **Favorable shell-birth orientation.**  The endpoint pair current is zero to first order and
its second source derivative is exactly `-z.im`, independent of the Taylor depth. -/
theorem xiCTaylorThetaTailCorePairCurrent_zero_right_sourceSecondDerivative_zero
    (d : ℕ) (z : ℂ) :
    deriv (fun x : ℝ => deriv
      (fun t : ℝ => xiCTaylorThetaTailCorePairCurrent d z (t, 0)) x) 0 =
      -z.im := by
  have hfirst : deriv
      (fun t : ℝ => xiCTaylorThetaTailCorePairCurrent d z (t, 0)) =
        fun x : ℝ =>
          (thetaCuspTailSecondCoreAtomSourceSpectralDerivative d z x).im / 2 := by
    funext x
    exact (hasDerivAt_xiCTaylorThetaTailCorePairCurrent_zero_right d z x).deriv
  rw [hfirst]
  have h := hasDerivAt_thetaCuspTailSecondCoreAtomSourceSpectralDerivative_zero d z
  have him := (hasDerivAt_const 0 Complex.imCLM).clm_apply h
  have hhalf := him.div_const 2
  convert hhalf.deriv using 1 <;> simp [Complex.mul_im]; ring

theorem xiCTaylorThetaTailCorePairCurrent_zero_right_sourceSecondDerivative_neg
    (d : ℕ) {z : ℂ} (hz : 0 < z.im) :
    deriv (fun x : ℝ => deriv
      (fun t : ℝ => xiCTaylorThetaTailCorePairCurrent d z (t, 0)) x) 0 < 0 := by
  rw [xiCTaylorThetaTailCorePairCurrent_zero_right_sourceSecondDerivative_zero]
  linarith

/-- At the radial birth height, the lower and upper angular endpoints coincide. -/
theorem thetaCuspPrimitiveRayArithmeticPolar_birthEndpoints_eq
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    thetaCuspPrimitiveRayCorePolarLowerEndpoint
        (thetaCuspPrimitiveRayRadialLog a b 0 0) (-Real.log (a : ℝ)) =
      thetaCuspPrimitiveRayCorePolarUpperEndpoint
        (thetaCuspPrimitiveRayRadialLog a b 0 0) (-Real.log (b : ℝ)) := by
  rw [thetaCuspPrimitiveRayCorePolarLowerEndpoint_neg_log_nat ha,
    thetaCuspPrimitiveRayCorePolarUpperEndpoint_neg_log_nat hb,
    thetaCuspPrimitiveRayRadialLog_zero_zero]
  let S : ℝ := (a : ℝ) ^ (2 : ℕ) + (b : ℝ) ^ (2 : ℕ)
  have hS : 0 < S := by
    dsimp only [S]
    positivity
  have hexp : Real.exp (-2 * ((1 / 2 : ℝ) * Real.log S)) = S⁻¹ := by
    rw [show -2 * ((1 / 2 : ℝ) * Real.log S) = -Real.log S by ring,
      Real.exp_neg, Real.exp_log hS]
  change (a : ℝ) ^ (2 : ℕ) * Real.exp (-2 * ((1 / 2 : ℝ) * Real.log S)) =
    1 - (b : ℝ) ^ (2 : ℕ) * Real.exp (-2 * ((1 / 2 : ℝ) * Real.log S))
  rw [hexp]
  dsimp only [S]
  field_simp [hS.ne']
  ring

/-- **No atomic shell-birth current.**  When a primitive direction first enters the active
quadrant, both logarithmic source coordinates are zero and its finite core-pair current vanishes
exactly. -/
theorem thetaCuspPrimitiveRayCorePolarKernel_birth_zero
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (d : ℕ) (z : ℂ) :
    thetaCuspPrimitiveRayCorePolarKernel d z
        (thetaCuspPrimitiveRayRadialLog a b 0 0)
        (-Real.log (a : ℝ)) (-Real.log (b : ℝ))
        (thetaCuspPrimitiveRayCorePolarLowerEndpoint
          (thetaCuspPrimitiveRayRadialLog a b 0 0) (-Real.log (a : ℝ))) = 0 := by
  let r := thetaCuspPrimitiveRayRadialLog a b 0 0
  have heq := thetaCuspPrimitiveRayArithmeticPolar_birthEndpoints_eq ha hb
  change thetaCuspPrimitiveRayCorePolarKernel d z r
      (-Real.log (a : ℝ)) (-Real.log (b : ℝ))
      (thetaCuspPrimitiveRayCorePolarLowerEndpoint r (-Real.log (a : ℝ))) = 0
  unfold thetaCuspPrimitiveRayCorePolarKernel
  rw [thetaCuspPrimitiveRayCorePolarX_lowerEndpoint]
  rw [heq]
  rw [thetaCuspPrimitiveRayCorePolarY_upperEndpoint]
  rw [xiCTaylorThetaTailCorePairCurrent_zero_left,
    thetaCuspTailSecondCoreAtomDerivative_zero]
  simp

/-! ## The favorable germ is not a global endpoint sign -/

/-- **Exact endpoint sign-reversal witness.**  Although every upper-half-plane endpoint current
is quadratically negative at shell birth, already the depth-one finite core has a strictly
positive endpoint current farther along the boundary.  Hence the missing theorem cannot be a
pointwise sign for each primitive ray; it must retain cancellation across the full ray packet. -/
theorem xiCTaylorThetaTailCorePairCurrent_one_quarter_ten_eq :
    xiCTaylorThetaTailCorePairCurrent 1 ((((1 / 4 : ℝ) : ℂ)) * I) (10, 0) =
      25 / 48 := by
  rw [xiCTaylorThetaTailCorePairCurrent_zero_right]
  unfold thetaCuspTailSecondCoreAtomDerivative
    thetaCuspTailSecondSection thetaCuspTailSecondSectionDerivative
  norm_num [Finset.sum_range_succ, Complex.I_sq, pow_succ]

theorem xiCTaylorThetaTailCorePairCurrent_one_quarter_ten_pos :
    0 < xiCTaylorThetaTailCorePairCurrent 1 ((((1 / 4 : ℝ) : ℂ)) * I) (10, 0) := by
  rw [xiCTaylorThetaTailCorePairCurrent_one_quarter_ten_eq]
  norm_num

end

end RHTower
