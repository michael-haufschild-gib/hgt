import GaloisForLFunctions.RHTower.DeningerAllPrimeFloquetRadical
import GaloisForLFunctions.RHTower.DeningerFloquetEnergyContinuity
import GaloisForLFunctions.RHTower.DeningerSecondaryFloquetEnergy
import GaloisForLFunctions.RHTower.DeningerPeriodizationMap

/-!
# The half-density Floquet cochain energy

The trivialization `U h(t) = e^{t/2}h(t)` turns the half-density Floquet trace into the ordinary
periodization, so the all-prime half-density Floquet energy

`E_Fl(h) = ∑_p p^{-2} ∫_0^{L_p} |e^{t/2} Per_{p,1/2} h(t)|² dt`

is exactly the all-prime Floquet energy of `U h`.  It is therefore finite and continuous, positive
definite, of arithmetic weight one for the raw dilation, and exactly invariant under the centered
flow — the unique real Floquet exponent with that property.

* `deningerFloquetEnergy_smul` : the energy is quadratic.
* `deningerHalfDensityFloquetEnergy` : **`E_Fl`.**
* `deningerHalfDensityFloquetEnergy_eq_zero_iff` : **positive definiteness.**
* `deningerHalfDensityFloquetEnergy_translate` : **arithmetic weight one.**
* `deningerHalfDensityFloquetEnergy_centeredFlow` : **exact centered-flow invariance.**
-/

namespace RHTower

open SchwartzMap MeasureTheory Filter Topology

noncomputable section

/-! ## The energy is quadratic -/

theorem deningerFloquetTerm_smul (c : ℂ) (g : DeningerExpSchwartz) (q : ℕ) :
    deningerFloquetTerm (c • g) q = ‖c‖ ^ 2 * deningerFloquetTerm g q := by
  have hfun : (fun t : ℝ => ‖deningerPeriodizationSum
      (((c • g : DeningerExpSchwartz) : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) (Real.log q) t‖ ^ 2)
      = fun t : ℝ => ‖c‖ ^ 2 * ‖deningerPeriodizationSum
        ((g : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) (Real.log q) t‖ ^ 2 := by
    funext t
    have hcoe : (((c • g : DeningerExpSchwartz) : DeningerExpSchwartz) : 𝓢(ℝ, ℂ))
        = c • ((g : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) := rfl
    rw [hcoe, deningerPeriodizationSum_smul, norm_mul, mul_pow]
  rw [deningerFloquetTerm, deningerFloquetTerm, hfun, intervalIntegral.integral_const_mul]
  ring

/-- **The energy is quadratic.** -/
theorem deningerFloquetEnergy_smul (c : ℂ) (g : DeningerExpSchwartz) :
    deningerFloquetEnergy (c • g) = ‖c‖ ^ 2 * deningerFloquetEnergy g := by
  rw [deningerFloquetEnergy, deningerFloquetEnergy, ← tsum_mul_left]
  exact tsum_congr fun q => deningerFloquetTerm_smul c g (q : ℕ)

/-! ## The half-density trivialization -/

/-- The half-density lift is injective. -/
theorem deningerHalfDensityLift_injective :
    Function.Injective deningerHalfDensityLift := by
  intro a b hab
  refine Subtype.ext (SchwartzMap.ext fun t => ?_)
  have hval := congrArg (fun u : DeningerExpSchwartz =>
    ((u : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) t) hab
  rw [deningerHalfDensityLift_apply, deningerHalfDensityLift_apply] at hval
  have hne : ((Real.exp (t / 2) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (Real.exp_ne_zero _)
  exact mul_left_cancel₀ hne hval

/-- **The half-density lift intertwines the raw dilation with the scaled dilation.** -/
theorem deningerHalfDensityLift_translate (a : ℝ) (h : DeningerExpSchwartz) :
    deningerHalfDensityLift (deningerEscapeFamily 0 a h)
      = ((Real.exp (a / 2) : ℝ) : ℂ) • deningerEscapeFamily 0 a (deningerHalfDensityLift h) := by
  refine Subtype.ext (SchwartzMap.ext fun t => ?_)
  show ((deningerHalfDensityLift (deningerEscapeFamily 0 a h) : DeningerExpSchwartz) :
      𝓢(ℝ, ℂ)) t
    = ((Real.exp (a / 2) : ℝ) : ℂ)
      * ((deningerEscapeFamily 0 a (deningerHalfDensityLift h) : DeningerExpSchwartz) :
        𝓢(ℝ, ℂ)) t
  rw [deningerHalfDensityLift_apply, deningerEscapeFamily_apply, deningerEscapeFamily_apply,
    deningerHalfDensityLift_apply]
  have hkR : Real.exp (t / 2) * Real.exp (-(0 * a))
      = Real.exp (a / 2) * (Real.exp (-(0 * a)) * Real.exp ((t - a) / 2)) := by
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have hk : ((Real.exp (t / 2) : ℝ) : ℂ) * ((Real.exp (-(0 * a)) : ℝ) : ℂ)
      = ((Real.exp (a / 2) : ℝ) : ℂ) * (((Real.exp (-(0 * a)) : ℝ) : ℂ)
        * ((Real.exp ((t - a) / 2) : ℝ) : ℂ)) := by
    exact_mod_cast congrArg (fun r : ℝ => (r : ℂ)) hkR
  linear_combination (((h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) (t - a)) * hk

/-- The half-density lift commutes with scalars. -/
theorem deningerHalfDensityLift_smul (c : ℂ) (h : DeningerExpSchwartz) :
    deningerHalfDensityLift (c • h) = c • deningerHalfDensityLift h := by
  refine Subtype.ext (SchwartzMap.ext fun t => ?_)
  show ((deningerHalfDensityLift (c • h) : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) t
    = c * ((deningerHalfDensityLift h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) t
  rw [deningerHalfDensityLift_apply, deningerHalfDensityLift_apply]
  show ((Real.exp (t / 2) : ℝ) : ℂ) * (c * ((h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) t) = _
  ring

/-! ## The half-density Floquet energy -/

/-- **The all-prime half-density Floquet energy `E_Fl`.**  After the trivialization `U` the
half-density Floquet trace is the ordinary periodization, so this is the all-prime Floquet energy of
`U h`. -/
def deningerHalfDensityFloquetEnergy (h : DeningerExpSchwartz) : ℝ :=
  deningerFloquetEnergy (deningerHalfDensityLift h)

theorem deningerHalfDensityFloquetEnergy_nonneg (h : DeningerExpSchwartz) :
    0 ≤ deningerHalfDensityFloquetEnergy h :=
  deningerFloquetEnergy_nonneg _

/-- **`E_Fl` is finite and dominated by a Meyer seminorm.** -/
theorem deningerHalfDensityFloquetEnergy_le (h : DeningerExpSchwartz) :
    deningerHalfDensityFloquetEnergy h
      ≤ 25 * deningerMeyerSeminormFun 1 0 (deningerHalfDensityLift h) ^ 2
        * ∑' q : Nat.Primes, Real.log (q : ℕ) / ((q : ℕ) : ℝ) ^ 2 :=
  deningerFloquetEnergy_le _

/-- The half-density lift kills only zero. -/
theorem deningerHalfDensityLift_zero : deningerHalfDensityLift 0 = 0 := by
  refine Subtype.ext (SchwartzMap.ext fun t => ?_)
  rw [deningerHalfDensityLift_apply]
  simp

/-- **`E_Fl` is positive definite.** -/
theorem deningerHalfDensityFloquetEnergy_eq_zero_iff (h : DeningerExpSchwartz) :
    deningerHalfDensityFloquetEnergy h = 0 ↔ h = 0 := by
  rw [deningerHalfDensityFloquetEnergy, deningerFloquetEnergy_eq_zero_iff]
  constructor
  · intro hzero
    refine deningerHalfDensityLift_injective ?_
    rw [hzero, deningerHalfDensityLift_zero]
  · rintro rfl
    exact deningerHalfDensityLift_zero

theorem deningerHalfDensityFloquetEnergy_smul (c : ℂ) (h : DeningerExpSchwartz) :
    deningerHalfDensityFloquetEnergy (c • h) = ‖c‖ ^ 2 * deningerHalfDensityFloquetEnergy h := by
  rw [deningerHalfDensityFloquetEnergy, deningerHalfDensityLift_smul, deningerFloquetEnergy_smul,
    deningerHalfDensityFloquetEnergy]

/-- **Arithmetic weight one.**  The raw logarithmic dilation multiplies `E_Fl` by `e^a`. -/
theorem deningerHalfDensityFloquetEnergy_translate (a : ℝ) (h : DeningerExpSchwartz) :
    deningerHalfDensityFloquetEnergy (deningerEscapeFamily 0 a h)
      = Real.exp a * deningerHalfDensityFloquetEnergy h := by
  rw [deningerHalfDensityFloquetEnergy, deningerHalfDensityLift_translate,
    deningerFloquetEnergy_smul, deningerFloquetEnergy_shift, deningerHalfDensityFloquetEnergy]
  congr 1
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ← Real.exp_nat_mul]
  congr 1
  ring

/-- **Exact centered-flow invariance.**  `V_a = e^{-a/2}T_a` preserves `E_Fl`. -/
theorem deningerHalfDensityFloquetEnergy_centeredFlow (a : ℝ) (h : DeningerExpSchwartz) :
    deningerHalfDensityFloquetEnergy (deningerEscapeFamily (1 / 2) a h)
      = deningerHalfDensityFloquetEnergy h := by
  have hfac : deningerEscapeFamily (1 / 2) a h
      = ((Real.exp (-(a / 2)) : ℝ) : ℂ) • deningerEscapeFamily 0 a h := by
    refine Subtype.ext (SchwartzMap.ext fun t => ?_)
    show ((deningerEscapeFamily (1 / 2) a h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) t
      = ((Real.exp (-(a / 2)) : ℝ) : ℂ)
        * ((deningerEscapeFamily 0 a h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) t
    rw [deningerEscapeFamily_apply, deningerEscapeFamily_apply, ← mul_assoc,
      ← Complex.ofReal_mul, ← Real.exp_add]
    congr 3
    ring
  rw [hfac, deningerHalfDensityFloquetEnergy_smul, deningerHalfDensityFloquetEnergy_translate]
  have hnorm : ‖((Real.exp (-(a / 2)) : ℝ) : ℂ)‖ ^ 2 = Real.exp (-a) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ← Real.exp_nat_mul]
    congr 1
    ring
  rw [hnorm, ← mul_assoc, ← Real.exp_add]
  simp

/-! ## Continuity -/

/-- The trivialization costs at most one further unit of exponent at order zero. -/
theorem deningerHalfDensityLift_seminorm_le (h : DeningerExpSchwartz) :
    deningerMeyerSeminormFun 1 0 (deningerHalfDensityLift h)
      ≤ deningerMeyerSeminormFun 2 0 h := by
  refine deningerMeyerSeminormFun_le fun t => ?_
  rw [deningerMeyerWeight, norm_iteratedFDeriv_zero, one_mul, deningerHalfDensityLift_apply]
  have hx := deningerMeyerWeight_le 2 0 h t
  rw [deningerMeyerWeight, norm_iteratedFDeriv_zero] at hx
  have hsplit : ‖((Real.exp (t / 2) : ℝ) : ℂ) * ((h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) t‖
      = Real.exp (t / 2) * ‖((h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) t‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  rw [hsplit, ← mul_assoc, ← Real.exp_add]
  refine le_trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)) hx
  refine Real.exp_le_exp.2 ?_
  have := le_abs_self t
  have habs : (0 : ℝ) ≤ |t| := abs_nonneg t
  linarith

/-- **`E_Fl` is continuous** for the Meyer topology. -/
theorem deningerHalfDensityFloquetEnergy_continuous :
    Continuous fun x : DeningerMeyerSource =>
      deningerHalfDensityFloquetEnergy (DeningerMeyerSource.toSource x) := by
  set F : DeningerMeyerSource → ℝ := fun x =>
    deningerHalfDensityFloquetEnergy (DeningerMeyerSource.toSource x) with hF
  have hsem : Continuous fun x : DeningerMeyerSource => DeningerMeyerSource.seminorms (2, 0) x :=
    DeningerMeyerSource.withSeminorms.continuous_seminorm (2, 0)
  refine continuous_iff_continuousAt.2 fun c => ?_
  set G : DeningerMeyerSource → ℝ := fun x =>
    25 * (DeningerMeyerSource.seminorms (2, 0) (x - c)
      * (DeningerMeyerSource.seminorms (2, 0) x + DeningerMeyerSource.seminorms (2, 0) c))
    * deningerPrimeLogWeight with hG
  have hGcont : Continuous G :=
    (continuous_const.mul ((hsem.comp (continuous_id.sub continuous_const)).mul
      (hsem.add continuous_const))).mul continuous_const
  have hbound : ∀ x : DeningerMeyerSource, ‖F x - F c‖ ≤ G x := by
    intro x
    have hb := deningerFloquetEnergy_sub_le
      (deningerHalfDensityLift (DeningerMeyerSource.toSource x))
      (deningerHalfDensityLift (DeningerMeyerSource.toSource c))
    have hlin : deningerHalfDensityLift (DeningerMeyerSource.toSource x)
        - deningerHalfDensityLift (DeningerMeyerSource.toSource c)
        = deningerHalfDensityLift (DeningerMeyerSource.toSource x
          - DeningerMeyerSource.toSource c) := by
      refine Subtype.ext (SchwartzMap.ext fun t => ?_)
      show ((deningerHalfDensityLift (DeningerMeyerSource.toSource x) : DeningerExpSchwartz) :
          𝓢(ℝ, ℂ)) t
        - ((deningerHalfDensityLift (DeningerMeyerSource.toSource c) : DeningerExpSchwartz) :
          𝓢(ℝ, ℂ)) t = _
      rw [deningerHalfDensityLift_apply, deningerHalfDensityLift_apply,
        deningerHalfDensityLift_apply]
      show _ = ((Real.exp (t / 2) : ℝ) : ℂ)
        * (((DeningerMeyerSource.toSource x : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) t
          - ((DeningerMeyerSource.toSource c : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) t)
      ring
    rw [hlin] at hb
    have hs1 := deningerHalfDensityLift_seminorm_le
      (DeningerMeyerSource.toSource x - DeningerMeyerSource.toSource c)
    have hs2 := deningerHalfDensityLift_seminorm_le (DeningerMeyerSource.toSource x)
    have hs3 := deningerHalfDensityLift_seminorm_le (DeningerMeyerSource.toSource c)
    have hnn : (0 : ℝ) ≤ deningerMeyerSeminormFun 1 0
        (deningerHalfDensityLift (DeningerMeyerSource.toSource x))
      + deningerMeyerSeminormFun 1 0
        (deningerHalfDensityLift (DeningerMeyerSource.toSource c)) := by
      have := deningerMeyerSeminormFun_nonneg 1 0
        (deningerHalfDensityLift (DeningerMeyerSource.toSource x))
      have := deningerMeyerSeminormFun_nonneg 1 0
        (deningerHalfDensityLift (DeningerMeyerSource.toSource c))
      linarith
    have hnn2 : (0 : ℝ) ≤ deningerMeyerSeminormFun 2 0
        (DeningerMeyerSource.toSource x - DeningerMeyerSource.toSource c) :=
      deningerMeyerSeminormFun_nonneg _ _ _
    have hprod : deningerMeyerSeminormFun 1 0
        (deningerHalfDensityLift (DeningerMeyerSource.toSource x
          - DeningerMeyerSource.toSource c))
        * (deningerMeyerSeminormFun 1 0
            (deningerHalfDensityLift (DeningerMeyerSource.toSource x))
          + deningerMeyerSeminormFun 1 0
            (deningerHalfDensityLift (DeningerMeyerSource.toSource c)))
        ≤ deningerMeyerSeminormFun 2 0
            (DeningerMeyerSource.toSource x - DeningerMeyerSource.toSource c)
          * (deningerMeyerSeminormFun 2 0 (DeningerMeyerSource.toSource x)
            + deningerMeyerSeminormFun 2 0 (DeningerMeyerSource.toSource c)) :=
      mul_le_mul hs1 (by linarith) hnn hnn2
    have hfinal := hb.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hprod (by norm_num : (0 : ℝ) ≤ 25))
      deningerPrimeLogWeight_nonneg)
    have hsub : DeningerMeyerSource.toSource x - DeningerMeyerSource.toSource c
        = DeningerMeyerSource.toSource (x - c) := (map_sub _ _ _).symm
    rw [hsub] at hfinal
    rw [Real.norm_eq_abs, hF, hG]
    simp only [deningerHalfDensityFloquetEnergy]
    simpa using hfinal
  have hGzero : G c = 0 := by
    have hz : DeningerMeyerSource.seminorms (2, 0) (c - c) = 0 := by
      rw [sub_self, map_zero]
    show 25 * (DeningerMeyerSource.seminorms (2, 0) (c - c)
      * (DeningerMeyerSource.seminorms (2, 0) c + DeningerMeyerSource.seminorms (2, 0) c))
      * deningerPrimeLogWeight = 0
    rw [hz]
    ring
  have hGtend : Tendsto G (𝓝 c) (𝓝 0) := by
    have := hGcont.continuousAt (x := c)
    rwa [ContinuousAt, hGzero] at this
  have hdiff : Tendsto (fun x => F x - F c) (𝓝 c) (𝓝 0) := squeeze_zero_norm hbound hGtend
  have := hdiff.add_const (F c)
  simpa [ContinuousAt] using this

end

end RHTower
