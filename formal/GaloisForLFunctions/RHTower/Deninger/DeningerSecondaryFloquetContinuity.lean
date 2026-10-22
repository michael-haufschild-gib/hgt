import GaloisForLFunctions.RHTower.Deninger.DeningerSecondaryFloquetEnergy
import GaloisForLFunctions.RHTower.Deninger.DeningerFloquetEnergyContinuity

/-!
# The secondary all-prime energy is continuous on the collar pair space

The centred defect is bilinear in the collar pair and its order-zero Meyer seminorm is bounded by
the order-two seminorms of the two collars, because the half-density weight costs half a unit of
exponent and the reflection costs none.  Composing with the Lipschitz bound for the all-prime
energy makes the secondary energy continuous on `H_-²`.

* `deningerSecondaryDefectSource_sub` : the defect is additive in the pair.
* `deningerSecondaryDefectSource_seminorm_le` : **`q_{1,0}(d_sec) ≤ q_{2,0}(h₊) + q_{2,0}(h₋)`.**
* `deningerSecondaryFloquetEnergy_sub_le` : **the Lipschitz bound on the pair space.**
* `deningerSecondaryFloquetEnergy_continuous` : **`(5)`: the secondary energy is continuous.**
-/

namespace RHTower

open SchwartzMap Filter Topology

noncomputable section

/-- **The defect is additive in the collar pair.** -/
theorem deningerSecondaryDefectSource_sub (x x' y y' : DeningerExpSchwartz) :
    deningerSecondaryDefectSource x y - deningerSecondaryDefectSource x' y'
      = deningerSecondaryDefectSource (x - x') (y - y') := by
  refine Subtype.ext (SchwartzMap.ext fun t => ?_)
  show ((deningerSecondaryDefectSource x y : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) t
      - ((deningerSecondaryDefectSource x' y' : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) t
    = ((deningerSecondaryDefectSource (x - x') (y - y') : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) t
  rw [deningerSecondaryDefectSource_apply, deningerSecondaryDefectSource_apply,
    deningerSecondaryDefectSource_apply, deningerSecondaryDefect, deningerSecondaryDefect,
    deningerSecondaryDefect, deningerHalfDensityLift_apply, deningerHalfDensityLift_apply,
    deningerHalfDensityLift_apply, deningerHalfDensityLift_apply, deningerHalfDensityLift_apply,
    deningerHalfDensityLift_apply]
  show _ = ((Real.exp (t / 2) : ℝ) : ℂ)
      * (((x : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) t - ((x' : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) t)
    - ((Real.exp (-t / 2) : ℝ) : ℂ)
      * (((y : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) (-t)
        - ((y' : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) (-t))
  ring

/-- **The defect costs at most two units of exponent.** -/
theorem deningerSecondaryDefectSource_seminorm_le (x y : DeningerExpSchwartz) :
    deningerMeyerSeminormFun 1 0 (deningerSecondaryDefectSource x y)
      ≤ deningerMeyerSeminormFun 2 0 x + deningerMeyerSeminormFun 2 0 y := by
  refine deningerMeyerSeminormFun_le fun t => ?_
  rw [deningerMeyerWeight, norm_iteratedFDeriv_zero, one_mul,
    deningerSecondaryDefectSource_apply, deningerSecondaryDefect,
    deningerHalfDensityLift_apply, deningerHalfDensityLift_apply]
  have hx := deningerMeyerWeight_le 2 0 x t
  have hy := deningerMeyerWeight_le 2 0 y (-t)
  rw [deningerMeyerWeight, norm_iteratedFDeriv_zero] at hx
  rw [deningerMeyerWeight, norm_iteratedFDeriv_zero, abs_neg] at hy
  have hsplit : ‖((Real.exp (t / 2) : ℝ) : ℂ) * ((x : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) t
      - ((Real.exp (-t / 2) : ℝ) : ℂ) * ((y : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) (-t)‖
      ≤ Real.exp (t / 2) * ‖((x : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) t‖
        + Real.exp (-t / 2) * ‖((y : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) (-t)‖ := by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), abs_of_pos (Real.exp_pos _)]
  have hstep := mul_le_mul_of_nonneg_left hsplit (Real.exp_pos (|t|)).le
  refine hstep.trans ?_
  have hw1 : Real.exp (|t|) * Real.exp (t / 2) ≤ Real.exp (2 * |t|) := by
    rw [← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    have := le_abs_self t
    have habs : (0 : ℝ) ≤ |t| := abs_nonneg t
    linarith
  have hw2 : Real.exp (|t|) * Real.exp (-t / 2) ≤ Real.exp (2 * |t|) := by
    rw [← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    have := neg_abs_le t
    have habs : (0 : ℝ) ≤ |t| := abs_nonneg t
    linarith
  have hnx : (0 : ℝ) ≤ ‖((x : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) t‖ := norm_nonneg _
  have hny : (0 : ℝ) ≤ ‖((y : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) (-t)‖ := norm_nonneg _
  calc Real.exp (|t|)
        * (Real.exp (t / 2) * ‖((x : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) t‖
          + Real.exp (-t / 2) * ‖((y : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) (-t)‖)
      = (Real.exp (|t|) * Real.exp (t / 2)) * ‖((x : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) t‖
        + (Real.exp (|t|) * Real.exp (-t / 2))
          * ‖((y : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) (-t)‖ := by ring
    _ ≤ Real.exp (2 * |t|) * ‖((x : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) t‖
        + Real.exp (2 * |t|) * ‖((y : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) (-t)‖ :=
        add_le_add (mul_le_mul_of_nonneg_right hw1 hnx) (mul_le_mul_of_nonneg_right hw2 hny)
    _ ≤ deningerMeyerSeminormFun 2 0 x + deningerMeyerSeminormFun 2 0 y := add_le_add hx hy

/-- **The Lipschitz bound for the secondary energy on the collar pair space.** -/
theorem deningerSecondaryFloquetEnergy_sub_le (x y x' y' : DeningerExpSchwartz) :
    |deningerSecondaryFloquetEnergy x y - deningerSecondaryFloquetEnergy x' y'|
      ≤ 25 * ((deningerMeyerSeminormFun 2 0 (x - x') + deningerMeyerSeminormFun 2 0 (y - y'))
          * ((deningerMeyerSeminormFun 2 0 x + deningerMeyerSeminormFun 2 0 y)
            + (deningerMeyerSeminormFun 2 0 x' + deningerMeyerSeminormFun 2 0 y')))
        * deningerPrimeLogWeight := by
  have hbase := deningerFloquetEnergy_sub_le (deningerSecondaryDefectSource x y)
    (deningerSecondaryDefectSource x' y')
  refine hbase.trans ?_
  have hsub : deningerSecondaryDefectSource x y - deningerSecondaryDefectSource x' y'
      = deningerSecondaryDefectSource (x - x') (y - y') :=
    deningerSecondaryDefectSource_sub x x' y y'
  rw [hsub]
  have h1 := deningerSecondaryDefectSource_seminorm_le (x - x') (y - y')
  have h2 := deningerSecondaryDefectSource_seminorm_le x y
  have h3 := deningerSecondaryDefectSource_seminorm_le x' y'
  have hnn1 : 0 ≤ deningerMeyerSeminormFun 1 0 (deningerSecondaryDefectSource (x - x') (y - y')) :=
    deningerMeyerSeminormFun_nonneg _ _ _
  have hnn2 : 0 ≤ deningerMeyerSeminormFun 1 0 (deningerSecondaryDefectSource x y)
      + deningerMeyerSeminormFun 1 0 (deningerSecondaryDefectSource x' y') := by
    have := deningerMeyerSeminormFun_nonneg 1 0 (deningerSecondaryDefectSource x y)
    have := deningerMeyerSeminormFun_nonneg 1 0 (deningerSecondaryDefectSource x' y')
    linarith
  have hC : 0 ≤ deningerPrimeLogWeight := deningerPrimeLogWeight_nonneg
  have hprod : deningerMeyerSeminormFun 1 0 (deningerSecondaryDefectSource (x - x') (y - y'))
      * (deningerMeyerSeminormFun 1 0 (deningerSecondaryDefectSource x y)
        + deningerMeyerSeminormFun 1 0 (deningerSecondaryDefectSource x' y'))
      ≤ (deningerMeyerSeminormFun 2 0 (x - x') + deningerMeyerSeminormFun 2 0 (y - y'))
        * ((deningerMeyerSeminormFun 2 0 x + deningerMeyerSeminormFun 2 0 y)
          + (deningerMeyerSeminormFun 2 0 x' + deningerMeyerSeminormFun 2 0 y')) := by
    refine mul_le_mul h1 (by linarith) hnn2 ?_
    have := deningerMeyerSeminormFun_nonneg 2 0 (x - x')
    have := deningerMeyerSeminormFun_nonneg 2 0 (y - y')
    linarith
  have h25 : (0 : ℝ) ≤ 25 := by norm_num
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hprod h25) hC

/-- **`(5)`: the secondary all-prime energy is continuous on the collar pair space.** -/
theorem deningerSecondaryFloquetEnergy_continuous :
    Continuous fun z : DeningerMeyerSource × DeningerMeyerSource =>
      deningerSecondaryFloquetEnergy (DeningerMeyerSource.toSource z.1)
        (DeningerMeyerSource.toSource z.2) := by
  set F : DeningerMeyerSource × DeningerMeyerSource → ℝ := fun z =>
    deningerSecondaryFloquetEnergy (DeningerMeyerSource.toSource z.1)
      (DeningerMeyerSource.toSource z.2) with hF
  have hsem : Continuous fun w : DeningerMeyerSource => DeningerMeyerSource.seminorms (2, 0) w :=
    DeningerMeyerSource.withSeminorms.continuous_seminorm (2, 0)
  refine continuous_iff_continuousAt.2 fun c => ?_
  set G : DeningerMeyerSource × DeningerMeyerSource → ℝ := fun z =>
    25 * ((DeningerMeyerSource.seminorms (2, 0) (z.1 - c.1)
        + DeningerMeyerSource.seminorms (2, 0) (z.2 - c.2))
      * ((DeningerMeyerSource.seminorms (2, 0) z.1 + DeningerMeyerSource.seminorms (2, 0) z.2)
        + (DeningerMeyerSource.seminorms (2, 0) c.1
          + DeningerMeyerSource.seminorms (2, 0) c.2)))
    * deningerPrimeLogWeight with hG
  have hp1 : Continuous fun z : DeningerMeyerSource × DeningerMeyerSource =>
      DeningerMeyerSource.seminorms (2, 0) z.1 := hsem.comp continuous_fst
  have hp2 : Continuous fun z : DeningerMeyerSource × DeningerMeyerSource =>
      DeningerMeyerSource.seminorms (2, 0) z.2 := hsem.comp continuous_snd
  have hd1 : Continuous fun z : DeningerMeyerSource × DeningerMeyerSource =>
      DeningerMeyerSource.seminorms (2, 0) (z.1 - c.1) :=
    hsem.comp (continuous_fst.sub continuous_const)
  have hd2 : Continuous fun z : DeningerMeyerSource × DeningerMeyerSource =>
      DeningerMeyerSource.seminorms (2, 0) (z.2 - c.2) :=
    hsem.comp (continuous_snd.sub continuous_const)
  have hGcont : Continuous G :=
    (continuous_const.mul ((hd1.add hd2).mul ((hp1.add hp2).add continuous_const))).mul
      continuous_const
  have hbound : ∀ z : DeningerMeyerSource × DeningerMeyerSource, ‖F z - F c‖ ≤ G z := by
    intro z
    have hb := deningerSecondaryFloquetEnergy_sub_le (DeningerMeyerSource.toSource z.1)
      (DeningerMeyerSource.toSource z.2) (DeningerMeyerSource.toSource c.1)
      (DeningerMeyerSource.toSource c.2)
    have hs1 : DeningerMeyerSource.toSource z.1 - DeningerMeyerSource.toSource c.1
        = DeningerMeyerSource.toSource (z.1 - c.1) := (map_sub _ _ _).symm
    have hs2 : DeningerMeyerSource.toSource z.2 - DeningerMeyerSource.toSource c.2
        = DeningerMeyerSource.toSource (z.2 - c.2) := (map_sub _ _ _).symm
    rw [hs1, hs2] at hb
    rw [Real.norm_eq_abs, hF, hG]
    simpa using hb
  have hGzero : G c = 0 := by
    have hz1 : DeningerMeyerSource.seminorms (2, 0) (c.1 - c.1) = 0 := by
      rw [sub_self, map_zero]
    have hz2 : DeningerMeyerSource.seminorms (2, 0) (c.2 - c.2) = 0 := by
      rw [sub_self, map_zero]
    show 25 * ((DeningerMeyerSource.seminorms (2, 0) (c.1 - c.1)
        + DeningerMeyerSource.seminorms (2, 0) (c.2 - c.2))
      * ((DeningerMeyerSource.seminorms (2, 0) c.1 + DeningerMeyerSource.seminorms (2, 0) c.2)
        + (DeningerMeyerSource.seminorms (2, 0) c.1
          + DeningerMeyerSource.seminorms (2, 0) c.2)))
      * deningerPrimeLogWeight = 0
    rw [hz1, hz2]
    ring
  have hGtend : Tendsto G (𝓝 c) (𝓝 0) := by
    have := hGcont.continuousAt (x := c)
    rwa [ContinuousAt, hGzero] at this
  have hdiff : Tendsto (fun z => F z - F c) (𝓝 c) (𝓝 0) := squeeze_zero_norm hbound hGtend
  have := hdiff.add_const (F c)
  simpa [ContinuousAt] using this

end

end RHTower
