import GaloisForLFunctions.RHTower.DeningerAdiabaticEulerConnection
import GaloisForLFunctions.RHTower.DeningerAdiabaticDistributionEndpoint
import GaloisForLFunctions.RHTower.MertensFirst
import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum

/-!
# Strict all-prime Green--Stokes connection

This file upgrades pointwise differentiation of the adiabatic Möbius inverse to an honest
`L¹(ℝ)` derivative.  The decisive estimate is local in the positive adiabatic parameter: on
`b > a/2`, dilation contributes `n⁻¹` and the coefficient contributes `n⁻ᵃᐟ²`, leaving the
summable majorant `log n / n^(1+a/2)`.  No critical absolute Euler product is asserted.

The continuous `L¹ → 𝓢'` embedding and Fourier transform then give the two collar connection and
the unsquared covariant Green--Stokes identity.
-/

namespace RHTower

open Filter Topology MeasureTheory SchwartzMap FourierTransform ArithmeticFunction

noncomputable section

/-- Even logarithmic pullback of a Meyer source. -/
def deningerAdiabaticEvenLogPull (h : DeningerMeyerSource) (x : ℝ) : ℂ :=
  deningerLogPull
    (((DeningerMeyerSource.toSource h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ))) |x|

@[simp]
theorem deningerAdiabaticEvenLogPull_even (h : DeningerMeyerSource) (x : ℝ) :
    deningerAdiabaticEvenLogPull h (-x) = deningerAdiabaticEvenLogPull h x := by
  rw [deningerAdiabaticEvenLogPull, deningerAdiabaticEvenLogPull, abs_neg]

/-- Dilation of the even logarithmic pullback by a positive ordinary integer. -/
def deningerAdiabaticEvenLogPullDilation
    (h : DeningerMeyerSource) (n : ℕ) (x : ℝ) : ℂ :=
  deningerLogPull
    (((DeningerMeyerSource.toSource h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)))
    ((n : ℝ) * |x|)

@[simp]
theorem deningerAdiabaticEvenLogPullDilation_even
    (h : DeningerMeyerSource) (n : ℕ) (x : ℝ) :
    deningerAdiabaticEvenLogPullDilation h n (-x) =
      deningerAdiabaticEvenLogPullDilation h n x := by
  rw [deningerAdiabaticEvenLogPullDilation,
    deningerAdiabaticEvenLogPullDilation, abs_neg]

theorem deningerAdiabaticEvenLogPullDilation_integrable
    (h : DeningerMeyerSource) {n : ℕ} (hn : 0 < n) :
    Integrable (deningerAdiabaticEvenLogPullDilation h n) := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hpos : IntegrableOn
      (fun x : ℝ => deningerLogPull
        (((DeningerMeyerSource.toSource h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)))
        ((n : ℝ) * x)) (Set.Ioi (0 : ℝ)) :=
    deningerLogPull_dilation_integrable (DeningerMeyerSource.toSource h).2 hnR
  have hpos' : IntegrableOn (deningerAdiabaticEvenLogPullDilation h n)
      (Set.Ioi (0 : ℝ)) := by
    refine hpos.congr_fun (fun x hx => ?_) measurableSet_Ioi
    rw [deningerAdiabaticEvenLogPullDilation, abs_of_pos hx]
  have hneg : IntegrableOn (deningerAdiabaticEvenLogPullDilation h n)
      (Set.Iio (0 : ℝ)) := by
    have href := deningerEvenPreimage_integrableOn_Iio hpos
    refine href.congr_fun (fun x hx => ?_) measurableSet_Iio
    have hxneg : x < 0 := hx
    rw [deningerAdiabaticEvenLogPullDilation, abs_of_neg hxneg]
  exact deningerIntegrable_of_rays hpos' hneg

/-- `L¹(ℝ)` realization of one positive-integer dilation. -/
def deningerAdiabaticEvenLogPullDilationLp
    (h : DeningerMeyerSource) (n : ℕ) (hn : 0 < n) :
    Lp ℂ (1 : ENNReal) (volume : Measure ℝ) :=
  (deningerAdiabaticEvenLogPullDilation_integrable h hn).toL1
    (deningerAdiabaticEvenLogPullDilation h n)

/-- Positive-ray mass of the absolute logarithmic pullback. -/
def deningerAdiabaticLogPullNormMass (h : DeningerMeyerSource) : ℝ :=
  ∫ x in Set.Ioi (0 : ℝ),
    ‖deningerLogPull
      (((DeningerMeyerSource.toSource h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ))) x‖

theorem deningerAdiabaticLogPullNormMass_nonneg (h : DeningerMeyerSource) :
    0 ≤ deningerAdiabaticLogPullNormMass h :=
  integral_nonneg fun _ => norm_nonneg _

/-- Exact modulus law: even extension costs `2`, while dilation by `n` costs `n⁻¹`. -/
theorem norm_deningerAdiabaticEvenLogPullDilationLp
    (h : DeningerMeyerSource) {n : ℕ} (hn : 0 < n) :
    ‖deningerAdiabaticEvenLogPullDilationLp h n hn‖ =
      2 * (n : ℝ)⁻¹ * deningerAdiabaticLogPullNormMass h := by
  let G : ℝ → ℝ := fun x => ‖deningerAdiabaticEvenLogPullDilation h n x‖
  have hG : Integrable G :=
    (deningerAdiabaticEvenLogPullDilation_integrable h hn).norm
  have hGeven : ∀ x : ℝ, G (-x) = G x := by
    intro x
    simp only [G, deningerAdiabaticEvenLogPullDilation_even]
  rw [L1.norm_eq_integral_norm]
  have hcoe : (∫ x : ℝ,
      ‖(deningerAdiabaticEvenLogPullDilationLp h n hn) x‖) = ∫ x : ℝ, G x := by
    simp only [deningerAdiabaticEvenLogPullDilationLp]
    apply integral_congr_ae
    filter_upwards [Integrable.coeFn_toL1
      (deningerAdiabaticEvenLogPullDilation_integrable h hn)] with x hx
    rw [hx]
  rw [hcoe, deninger_integral_even_eq_two_Ioi hG hGeven]
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hray :
      (∫ x in Set.Ioi (0 : ℝ), G x) =
        (n : ℝ)⁻¹ * deningerAdiabaticLogPullNormMass h := by
    have hraw : (∫ x in Set.Ioi (0 : ℝ), G x) =
        ∫ x in Set.Ioi (0 : ℝ),
          ‖deningerLogPull
            (((DeningerMeyerSource.toSource h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)))
            ((n : ℝ) * x)‖ := by
      refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
      simp only [G, deningerAdiabaticEvenLogPullDilation]
      rw [abs_of_pos hx]
    rw [hraw]
    have hscale := MeasureTheory.integral_comp_mul_left_Ioi
      (fun y : ℝ => ‖deningerLogPull
        (((DeningerMeyerSource.toSource h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ))) y‖)
      0 hnR
    rw [mul_zero] at hscale
    simpa only [deningerAdiabaticLogPullNormMass, smul_eq_mul] using hscale
  rw [hray]
  ring

/-- Scalar coefficient of one adiabatic Möbius dilation. -/
def deningerAdiabaticMobiusScalar (n : ℕ) (a : ℝ) : ℂ :=
  ((((moebius n : ℤ) : ℝ) * deningerAdiabaticMobiusCoefficient a n : ℝ) : ℂ)

/-- Parameter derivative of the scalar coefficient. -/
def deningerAdiabaticMobiusDerivativeScalar (n : ℕ) (a : ℝ) : ℂ :=
  ((-(((moebius n : ℤ) : ℝ) * Real.log (n : ℝ)) *
    deningerAdiabaticMobiusCoefficient a n : ℝ) : ℂ)

theorem deningerAdiabaticMobiusScalar_hasDerivAt (n : ℕ) (a : ℝ) :
    HasDerivAt (deningerAdiabaticMobiusScalar n)
      (deningerAdiabaticMobiusDerivativeScalar n a) a := by
  have hlin : HasDerivAt (fun b : ℝ => -b * Real.log (n : ℝ))
      (-Real.log (n : ℝ)) a := by
    simpa using (hasDerivAt_id a).neg.mul_const (Real.log (n : ℝ))
  have hexp : HasDerivAt
      (fun b : ℝ => Real.exp (-b * Real.log (n : ℝ)))
      (-Real.log (n : ℝ) * Real.exp (-a * Real.log (n : ℝ))) a := by
    have hraw := (Real.hasDerivAt_exp _).comp a hlin
    exact hraw.congr_deriv (by ring)
  have hreal : HasDerivAt
      (fun b : ℝ => ((moebius n : ℤ) : ℝ) *
        Real.exp (-b * Real.log (n : ℝ)))
      (((moebius n : ℤ) : ℝ) *
        (-Real.log (n : ℝ) * Real.exp (-a * Real.log (n : ℝ)))) a := by
    have hraw := (hasDerivAt_const a ((moebius n : ℤ) : ℝ)).mul hexp
    have hfun : ((fun _ : ℝ => ((moebius n : ℤ) : ℝ)) *
        fun b : ℝ => Real.exp (-b * Real.log (n : ℝ))) =ᶠ[𝓝 a]
        (fun b : ℝ => ((moebius n : ℤ) : ℝ) *
          Real.exp (-b * Real.log (n : ℝ))) :=
      Eventually.of_forall fun _ => rfl
    exact (hraw.congr_of_eventuallyEq hfun).congr_deriv (by ring)
  have hcomplex := hreal.ofReal_comp
  change HasDerivAt
    (fun b : ℝ => ((((moebius n : ℤ) : ℝ) *
      Real.exp (-b * Real.log (n : ℝ)) : ℝ) : ℂ))
    ((-(((moebius n : ℤ) : ℝ) * Real.log (n : ℝ)) *
      Real.exp (-a * Real.log (n : ℝ)) : ℝ) : ℂ) a
  convert hcomplex using 1
  ring

/-- One `L¹` term of the full even adiabatic inverse. -/
def deningerAdiabaticMobiusTermLp
    (h : DeningerMeyerSource) (n : ℕ) (a : ℝ) :
    Lp ℂ (1 : ENNReal) (volume : Measure ℝ) :=
  if hn : 0 < n then
    deningerAdiabaticMobiusScalar n a •
      deningerAdiabaticEvenLogPullDilationLp h n hn
  else 0

/-- Its parameter derivative in `L¹`. -/
def deningerAdiabaticMobiusDerivativeTermLp
    (h : DeningerMeyerSource) (n : ℕ) (a : ℝ) :
    Lp ℂ (1 : ENNReal) (volume : Measure ℝ) :=
  if hn : 0 < n then
    deningerAdiabaticMobiusDerivativeScalar n a •
      deningerAdiabaticEvenLogPullDilationLp h n hn
  else 0

theorem deningerAdiabaticMobiusTermLp_hasDerivAt
    (h : DeningerMeyerSource) (n : ℕ) (a : ℝ) :
    HasDerivAt (deningerAdiabaticMobiusTermLp h n)
      (deningerAdiabaticMobiusDerivativeTermLp h n a) a := by
  by_cases hn : 0 < n
  · have hfun : deningerAdiabaticMobiusTermLp h n =
        fun b : ℝ => deningerAdiabaticMobiusScalar n b •
          deningerAdiabaticEvenLogPullDilationLp h n hn := by
      funext b
      simp only [deningerAdiabaticMobiusTermLp, dif_pos hn]
    have hder : deningerAdiabaticMobiusDerivativeTermLp h n a =
        deningerAdiabaticMobiusDerivativeScalar n a •
          deningerAdiabaticEvenLogPullDilationLp h n hn := by
      simp only [deningerAdiabaticMobiusDerivativeTermLp, dif_pos hn]
    rw [hfun, hder]
    exact (deningerAdiabaticMobiusScalar_hasDerivAt n a).smul_const
      (deningerAdiabaticEvenLogPullDilationLp h n hn)
  · have hfun : deningerAdiabaticMobiusTermLp h n =
        fun _ : ℝ => (0 : Lp ℂ (1 : ENNReal) (volume : Measure ℝ)) := by
      funext b
      simp only [deningerAdiabaticMobiusTermLp, dif_neg hn]
    have hder : deningerAdiabaticMobiusDerivativeTermLp h n a = 0 := by
      simp only [deningerAdiabaticMobiusDerivativeTermLp, dif_neg hn]
    rw [hfun, hder]
    exact hasDerivAt_const a 0

/-- The exponential coefficient is the literal real power `n⁻ᵃ` for `n > 0`. -/
theorem deningerAdiabaticMobiusCoefficient_eq_rpow_neg
    (a : ℝ) {n : ℕ} (hn : 0 < n) :
    deningerAdiabaticMobiusCoefficient a n = (n : ℝ) ^ (-a) := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  rw [deningerAdiabaticMobiusCoefficient, Real.rpow_def_of_pos hnR]
  congr 1
  ring

/-- Dilation modulus and adiabatic coefficient combine to `n^(-(a+1))`. -/
theorem deningerAdiabaticMobiusCoefficient_mul_inv
    (a : ℝ) {n : ℕ} (hn : 0 < n) :
    deningerAdiabaticMobiusCoefficient a n * (n : ℝ)⁻¹ =
      (n : ℝ) ^ (-(a + 1)) := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  rw [deningerAdiabaticMobiusCoefficient_eq_rpow_neg a hn]
  have hone : (n : ℝ)⁻¹ = (n : ℝ) ^ (-(1 : ℝ)) := by
    rw [Real.rpow_neg hnR.le, Real.rpow_one]
  rw [hone, ← Real.rpow_add hnR]
  congr 1
  ring

theorem norm_deningerAdiabaticMobiusScalar_le
    {a : ℝ} (ha : 0 ≤ a) (n : ℕ) :
    ‖deningerAdiabaticMobiusScalar n a‖ ≤
      deningerAdiabaticMobiusCoefficient a n := by
  have hmu : |((moebius n : ℤ) : ℝ)| ≤ 1 := by
    rcases moebius_eq_or n with hm | hm | hm <;> rw [hm] <;> norm_num
  rw [deningerAdiabaticMobiusScalar, Complex.norm_real, Real.norm_eq_abs, abs_mul]
  simp only [deningerAdiabaticMobiusCoefficient]
  rw [abs_of_pos (Real.exp_pos _)]
  exact mul_le_of_le_one_left (Real.exp_nonneg _) hmu

/-- Absolute `L¹` bound for one adiabatic Möbius term. -/
theorem norm_deningerAdiabaticMobiusTermLp_le
    (h : DeningerMeyerSource) {a : ℝ} (ha : 0 ≤ a) (n : ℕ) :
    ‖deningerAdiabaticMobiusTermLp h n a‖ ≤
      (2 * deningerAdiabaticLogPullNormMass h) * (n : ℝ) ^ (-(a + 1)) := by
  by_cases hn : 0 < n
  · rw [deningerAdiabaticMobiusTermLp, dif_pos hn, norm_smul,
      norm_deningerAdiabaticEvenLogPullDilationLp h hn]
    have hmass := deningerAdiabaticLogPullNormMass_nonneg h
    calc
      ‖deningerAdiabaticMobiusScalar n a‖ *
          (2 * (n : ℝ)⁻¹ * deningerAdiabaticLogPullNormMass h) ≤
        deningerAdiabaticMobiusCoefficient a n *
          (2 * (n : ℝ)⁻¹ * deningerAdiabaticLogPullNormMass h) := by
            gcongr
            exact norm_deningerAdiabaticMobiusScalar_le ha n
      _ = (2 * deningerAdiabaticLogPullNormMass h) * (n : ℝ) ^ (-(a + 1)) := by
        rw [← deningerAdiabaticMobiusCoefficient_mul_inv a hn]
        ring
  · have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
    subst n
    rw [deningerAdiabaticMobiusTermLp, dif_neg (by omega), norm_zero]
    exact mul_nonneg (mul_nonneg zero_le_two
      (deningerAdiabaticLogPullNormMass_nonneg h)) (Real.rpow_nonneg (by norm_num) _)

/-- For every positive parameter the all-integer series converges absolutely in `L¹(ℝ)`. -/
theorem summable_deningerAdiabaticMobiusTermLp
    (h : DeningerMeyerSource) {a : ℝ} (ha : 0 < a) :
    Summable (fun n : ℕ => deningerAdiabaticMobiusTermLp h n a) := by
  have hpow : Summable (fun n : ℕ => (n : ℝ) ^ (-(a + 1))) := by
    rw [Real.summable_nat_rpow]
    linarith
  have hmaj := hpow.mul_left (2 * deningerAdiabaticLogPullNormMass h)
  exact Summable.of_norm_bounded hmaj
    (fun n => norm_deningerAdiabaticMobiusTermLp_le h ha.le n)

theorem summable_norm_deningerAdiabaticMobiusTermLp
    (h : DeningerMeyerSource) {a : ℝ} (ha : 0 < a) :
    Summable (fun n : ℕ => ‖deningerAdiabaticMobiusTermLp h n a‖) := by
  have hpow : Summable (fun n : ℕ => (n : ℝ) ^ (-(a + 1))) := by
    rw [Real.summable_nat_rpow]
    linarith
  exact (hpow.mul_left (2 * deningerAdiabaticLogPullNormMass h)).of_nonneg_of_le
    (fun _ => norm_nonneg _) (fun n => norm_deningerAdiabaticMobiusTermLp_le h ha.le n)

/-- Coefficients decrease when the positive adiabatic parameter increases. -/
theorem deningerAdiabaticMobiusCoefficient_anti
    {d b : ℝ} (hd : 0 ≤ d) (hdb : d ≤ b) {n : ℕ} (hn : 0 < n) :
    deningerAdiabaticMobiusCoefficient b n ≤
      deningerAdiabaticMobiusCoefficient d n := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  rw [deningerAdiabaticMobiusCoefficient, deningerAdiabaticMobiusCoefficient]
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (neg_le_neg hdb)
    (Real.log_nonneg hn1))

theorem norm_deningerAdiabaticMobiusDerivativeScalar_le
    {d b : ℝ} (hd : 0 ≤ d) (hdb : d ≤ b) {n : ℕ} (hn : 0 < n) :
    ‖deningerAdiabaticMobiusDerivativeScalar n b‖ ≤
      Real.log (n : ℝ) * deningerAdiabaticMobiusCoefficient d n := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hn1
  have hmu : |((moebius n : ℤ) : ℝ)| ≤ 1 := by
    rcases moebius_eq_or n with hm | hm | hm <;> rw [hm] <;> norm_num
  rw [deningerAdiabaticMobiusDerivativeScalar, Complex.norm_real, Real.norm_eq_abs,
    abs_mul]
  simp only [deningerAdiabaticMobiusCoefficient]
  rw [abs_neg, abs_mul, abs_of_nonneg hlog, abs_of_pos (Real.exp_pos _)]
  calc
    |((moebius n : ℤ) : ℝ)| * Real.log (n : ℝ) *
        deningerAdiabaticMobiusCoefficient b n ≤
      1 * Real.log (n : ℝ) * deningerAdiabaticMobiusCoefficient b n := by
        gcongr
        exact (Real.exp_pos _).le
    _ ≤ Real.log (n : ℝ) * deningerAdiabaticMobiusCoefficient d n := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_left
        (deningerAdiabaticMobiusCoefficient_anti hd hdb hn) hlog

/-- Local derivative majorant at lower adiabatic wall `d`. -/
def deningerAdiabaticDerivativeMajorant
    (d : ℝ) (h : DeningerMeyerSource) (n : ℕ) : ℝ :=
  (2 * deningerAdiabaticLogPullNormMass h) *
    (Real.log (n : ℝ) / (n : ℝ) ^ (d + 1))

theorem summable_deningerAdiabaticDerivativeMajorant
    {d : ℝ} (hd : 0 < d) (h : DeningerMeyerSource) :
    Summable (deningerAdiabaticDerivativeMajorant d h) :=
  (Mertens.summable_log_div_rpow (by linarith : 1 < d + 1)).mul_left _

/-- Uniform `L¹` derivative bound on every collar `b ≥ d > 0`. -/
theorem norm_deningerAdiabaticMobiusDerivativeTermLp_le
    {d b : ℝ} (hd : 0 < d) (hdb : d ≤ b)
    (h : DeningerMeyerSource) (n : ℕ) :
    ‖deningerAdiabaticMobiusDerivativeTermLp h n b‖ ≤
      deningerAdiabaticDerivativeMajorant d h n := by
  by_cases hn : 0 < n
  · rw [deningerAdiabaticMobiusDerivativeTermLp, dif_pos hn, norm_smul,
      norm_deningerAdiabaticEvenLogPullDilationLp h hn]
    have hmass := deningerAdiabaticLogPullNormMass_nonneg h
    have hscalar := norm_deningerAdiabaticMobiusDerivativeScalar_le hd.le hdb hn
    calc
      ‖deningerAdiabaticMobiusDerivativeScalar n b‖ *
          (2 * (n : ℝ)⁻¹ * deningerAdiabaticLogPullNormMass h) ≤
        (Real.log (n : ℝ) * deningerAdiabaticMobiusCoefficient d n) *
          (2 * (n : ℝ)⁻¹ * deningerAdiabaticLogPullNormMass h) := by
            gcongr
      _ = deningerAdiabaticDerivativeMajorant d h n := by
        calc
          (Real.log (n : ℝ) * deningerAdiabaticMobiusCoefficient d n) *
              (2 * (n : ℝ)⁻¹ * deningerAdiabaticLogPullNormMass h) =
            (2 * deningerAdiabaticLogPullNormMass h) * Real.log (n : ℝ) *
              (deningerAdiabaticMobiusCoefficient d n * (n : ℝ)⁻¹) := by ring
          _ = (2 * deningerAdiabaticLogPullNormMass h) * Real.log (n : ℝ) *
              (n : ℝ) ^ (-(d + 1)) := by
            rw [deningerAdiabaticMobiusCoefficient_mul_inv d hn]
          _ = deningerAdiabaticDerivativeMajorant d h n := by
            rw [deningerAdiabaticDerivativeMajorant,
              Real.rpow_neg (show (0 : ℝ) ≤ (n : ℝ) by positivity)]
            ring
  · have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
    subst n
    simp [deningerAdiabaticMobiusDerivativeTermLp,
      deningerAdiabaticDerivativeMajorant]

/-- Positive extension of the full-line `L¹` path, used only to state ordinary derivatives. -/
def deningerAdiabaticEvenPreimageLpExt
    (a : ℝ) (h : DeningerMeyerSource) : Lp ℂ (1 : ENNReal) (volume : Measure ℝ) :=
  if ha : 0 ≤ a then deningerAdiabaticEvenPreimageLp ha h else 0

/-- For `a > 0`, the `L¹` sum is the already constructed full adiabatic inverse. -/
theorem tsum_deningerAdiabaticMobiusTermLp_eq
    {a : ℝ} (ha : 0 < a) (h : DeningerMeyerSource) :
    (∑' n : ℕ, deningerAdiabaticMobiusTermLp h n a) =
      deningerAdiabaticEvenPreimageLp ha.le h := by
  have hsum := summable_deningerAdiabaticMobiusTermLp h ha
  apply MeasureTheory.Lp.ext
  simp only [deningerAdiabaticEvenPreimageLp]
  have hcoeSum := MeasureTheory.Lp.coeFn_tsum
    ((tsum_enorm_ne_top_iff_summable_norm).2
      (summable_norm_deningerAdiabaticMobiusTermLp h ha))
  have hterm : ∀ n : ℕ,
      (fun x : ℝ => (deningerAdiabaticMobiusTermLp h n a) x) =ᵐ[volume]
        (fun x : ℝ => deningerAdiabaticMobiusTerm h |x| n a) := by
    intro n
    by_cases hn : 0 < n
    · filter_upwards [
        MeasureTheory.Lp.coeFn_smul (deningerAdiabaticMobiusScalar n a)
          (deningerAdiabaticEvenLogPullDilationLp h n hn),
        Integrable.coeFn_toL1
          (deningerAdiabaticEvenLogPullDilation_integrable h hn)] with x hx hy
      have hy' : (deningerAdiabaticEvenLogPullDilationLp h n hn) x =
          deningerAdiabaticEvenLogPullDilation h n x := by
        change ((deningerAdiabaticEvenLogPullDilation_integrable h hn).toL1
          (deningerAdiabaticEvenLogPullDilation h n)) x = _
        exact hy
      rw [deningerAdiabaticMobiusTermLp, dif_pos hn, hx]
      simp only [Pi.smul_apply]
      rw [hy']
      rfl
    · have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
      subst n
      filter_upwards with x
      simp [deningerAdiabaticMobiusTermLp, deningerAdiabaticMobiusTerm]
  have htermAll : ∀ᵐ x : ℝ ∂volume, ∀ n : ℕ,
      (deningerAdiabaticMobiusTermLp h n a) x =
        deningerAdiabaticMobiusTerm h |x| n a :=
    eventually_countable_forall.2 hterm
  filter_upwards [hcoeSum, htermAll,
    Integrable.coeFn_toL1 (deningerAdiabaticEvenPreimage_integrable ha.le h),
    deningerCompl_zero_ae_univ] with x hsumx hterms hxM hx0
  rw [hsumx, hxM]
  have hxmem : x ∈ ({(0 : ℝ)}ᶜ : Set ℝ) := hx0.mpr (Set.mem_univ x)
  have hxne : x ≠ 0 := by simpa using hxmem
  rw [deningerAdiabaticEvenPreimage]
  calc
    (∑' n : ℕ, (deningerAdiabaticMobiusTermLp h n a) x) =
        ∑' n : ℕ, deningerAdiabaticMobiusTerm h |x| n a :=
      tsum_congr hterms
    _ = deningerAdiabaticMobiusPreimage a h |x| :=
      (deningerAdiabaticMobiusPreimage_eq_tsum a h (abs_pos.mpr hxne)).symm

/-- The full all-prime path is differentiable in `L¹(ℝ)` at every positive parameter. -/
theorem hasDerivAt_deningerAdiabaticEvenPreimageLpExt
    {a : ℝ} (ha : 0 < a) (h : DeningerMeyerSource) :
    HasDerivAt (fun b : ℝ => deningerAdiabaticEvenPreimageLpExt b h)
      (∑' n : ℕ, deningerAdiabaticMobiusDerivativeTermLp h n a) a := by
  let d : ℝ := a / 2
  have hd : 0 < d := by dsimp [d]; linarith
  have had : d < a := by dsimp [d]; linarith
  have hmain := hasDerivAt_tsum_of_isPreconnected
    (summable_deningerAdiabaticDerivativeMajorant hd h)
    isOpen_Ioi isPreconnected_Ioi
    (fun n b _ => deningerAdiabaticMobiusTermLp_hasDerivAt h n b)
    (fun n b hb => norm_deningerAdiabaticMobiusDerivativeTermLp_le hd hb.le h n)
    had
    (summable_deningerAdiabaticMobiusTermLp h ha)
    had
  have heq : (fun b : ℝ => ∑' n : ℕ, deningerAdiabaticMobiusTermLp h n b) =ᶠ[𝓝 a]
      (fun b : ℝ => deningerAdiabaticEvenPreimageLpExt b h) := by
    filter_upwards [Ioi_mem_nhds ha] with b hb
    rw [tsum_deningerAdiabaticMobiusTermLp_eq hb h,
      deningerAdiabaticEvenPreimageLpExt, dif_pos hb.le]
  exact hmain.congr_of_eventuallyEq heq.symm

/-- The derivative series is absolutely summable in `L¹(ℝ)` at every positive parameter. -/
theorem summable_deningerAdiabaticMobiusDerivativeTermLp
    {a : ℝ} (ha : 0 < a) (h : DeningerMeyerSource) :
    Summable (fun n : ℕ => deningerAdiabaticMobiusDerivativeTermLp h n a) := by
  let d : ℝ := a / 2
  have hd : 0 < d := by dsimp [d]; linarith
  have hda : d ≤ a := by dsimp [d]; linarith
  exact Summable.of_norm_bounded
    (summable_deningerAdiabaticDerivativeMajorant hd h)
    (fun n => norm_deningerAdiabaticMobiusDerivativeTermLp_le hd hda h n)

theorem summable_norm_deningerAdiabaticMobiusDerivativeTermLp
    {a : ℝ} (ha : 0 < a) (h : DeningerMeyerSource) :
    Summable (fun n : ℕ => ‖deningerAdiabaticMobiusDerivativeTermLp h n a‖) := by
  let d : ℝ := a / 2
  have hd : 0 < d := by dsimp [d]; linarith
  have hda : d ≤ a := by dsimp [d]; linarith
  exact (summable_deningerAdiabaticDerivativeMajorant hd h).of_nonneg_of_le
    (fun _ => norm_nonneg _)
    (fun n => norm_deningerAdiabaticMobiusDerivativeTermLp_le hd hda h n)

/-- The positive Euler connection applied to the concrete all-prime inverse, in `L¹(ℝ)`. -/
def deningerAdiabaticEulerPositiveLp
    (a : ℝ) (h : DeningerMeyerSource) : Lp ℂ (1 : ENNReal) (volume : Measure ℝ) :=
  ∑' n : ℕ, deningerAdiabaticMobiusDerivativeTermLp h n a

/-- The `L¹` derivative has the literal all-integer logarithmic Möbius series almost everywhere. -/
theorem deningerAdiabaticEulerPositiveLp_ae_eq_parameterDerivative
    {a : ℝ} (ha : 0 < a) (h : DeningerMeyerSource) :
    (fun x : ℝ => (deningerAdiabaticEulerPositiveLp a h) x) =ᵐ[volume]
      (fun x : ℝ => deningerAdiabaticMobiusParameterDerivative a h |x|) := by
  have hsum := summable_deningerAdiabaticMobiusDerivativeTermLp ha h
  have hcoeSum := MeasureTheory.Lp.coeFn_tsum
    ((tsum_enorm_ne_top_iff_summable_norm).2
      (summable_norm_deningerAdiabaticMobiusDerivativeTermLp ha h))
  have hterm : ∀ n : ℕ,
      (fun x : ℝ => (deningerAdiabaticMobiusDerivativeTermLp h n a) x) =ᵐ[volume]
        (fun x : ℝ => deningerAdiabaticMobiusDerivativeTerm h |x| n a) := by
    intro n
    by_cases hn : 0 < n
    · filter_upwards [
        MeasureTheory.Lp.coeFn_smul (deningerAdiabaticMobiusDerivativeScalar n a)
          (deningerAdiabaticEvenLogPullDilationLp h n hn),
        Integrable.coeFn_toL1
          (deningerAdiabaticEvenLogPullDilation_integrable h hn)] with x hx hy
      have hy' : (deningerAdiabaticEvenLogPullDilationLp h n hn) x =
          deningerAdiabaticEvenLogPullDilation h n x := by
        change ((deningerAdiabaticEvenLogPullDilation_integrable h hn).toL1
          (deningerAdiabaticEvenLogPullDilation h n)) x = _
        exact hy
      rw [deningerAdiabaticMobiusDerivativeTermLp, dif_pos hn, hx]
      simp only [Pi.smul_apply]
      rw [hy']
      rfl
    · have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
      subst n
      filter_upwards with x
      simp [deningerAdiabaticMobiusDerivativeTermLp,
        deningerAdiabaticMobiusDerivativeTerm]
  have htermAll : ∀ᵐ x : ℝ ∂volume, ∀ n : ℕ,
      (deningerAdiabaticMobiusDerivativeTermLp h n a) x =
        deningerAdiabaticMobiusDerivativeTerm h |x| n a :=
    eventually_countable_forall.2 hterm
  filter_upwards [hcoeSum, htermAll] with x hsumx hterms
  rw [deningerAdiabaticEulerPositiveLp, hsumx,
    deningerAdiabaticMobiusParameterDerivative]
  exact tsum_congr hterms

/-- On the nonzero line, the `L¹` derivative is the literal physical von Mangoldt connection. -/
theorem deningerAdiabaticEulerPositiveLp_ae_eq_physical
    {a : ℝ} (ha : 0 < a) (h : DeningerMeyerSource) :
    (fun x : ℝ => (deningerAdiabaticEulerPositiveLp a h) x) =ᵐ[volume]
      (fun x : ℝ => deningerAdiabaticEulerPositive a
        (deningerAdiabaticMobiusPreimage a h) |x|) := by
  filter_upwards [deningerAdiabaticEulerPositiveLp_ae_eq_parameterDerivative ha h,
    deningerCompl_zero_ae_univ] with x hx hx0
  rw [hx]
  have hxmem : x ∈ ({(0 : ℝ)}ᶜ : Set ℝ) := hx0.mpr (Set.mem_univ x)
  have hxne : x ≠ 0 := by simpa using hxmem
  exact (deningerAdiabaticEulerPositive_eq_parameterDerivative ha h
    (abs_pos.mpr hxne)).symm

/-- Positive Euler output as a tempered distribution. -/
def deningerAdiabaticEulerPositiveDistribution
    (a : ℝ) (h : DeningerMeyerSource) : 𝓢'(ℝ, ℂ) :=
  MeasureTheory.Lp.toTemperedDistribution (deningerAdiabaticEulerPositiveLp a h)

/-- Distribution path induced by the positive extension of the strict `L¹` family. -/
def deningerAdiabaticPreimageDistributionExt
    (a : ℝ) (h : DeningerMeyerSource) : 𝓢'(ℝ, ℂ) :=
  MeasureTheory.Lp.toTemperedDistribution (deningerAdiabaticEvenPreimageLpExt a h)

theorem deningerAdiabaticPreimageDistributionExt_eq
    {a : ℝ} (ha : 0 < a) (h : DeningerMeyerSource) :
    deningerAdiabaticPreimageDistributionExt a h =
      deningerAdiabaticPreimageDistribution ha.le h := by
  rw [deningerAdiabaticPreimageDistributionExt,
    deningerAdiabaticEvenPreimageLpExt, dif_pos ha.le,
    deningerAdiabaticPreimageDistribution]

/-- Continuous real-linear Schwartz pairing on `L¹(ℝ)`.  Its value is the associated tempered
distribution evaluated on the test function. -/
def deningerL1SchwartzPairing (g : 𝓢(ℝ, ℂ)) :
    Lp ℂ (1 : ENNReal) (volume : Measure ℝ) →L[ℝ] ℂ :=
  ((PointwiseConvergenceCLM.evalCLM (RingHom.id ℂ) ℂ g).comp
    (MeasureTheory.Lp.toTemperedDistributionCLM ℂ volume 1)).restrictScalars ℝ

@[simp]
theorem deningerL1SchwartzPairing_apply
    (g : 𝓢(ℝ, ℂ)) (f : Lp ℂ (1 : ENNReal) (volume : Measure ℝ)) :
    deningerL1SchwartzPairing g f = MeasureTheory.Lp.toTemperedDistribution f g := by
  rfl

/-- **Weak distributional Euler connection law.**  Every Schwartz pairing is differentiable, and
its derivative is the concrete `L¹` Euler output. -/
theorem hasDerivAt_deningerAdiabaticL1SchwartzPairing
    {a : ℝ} (ha : 0 < a) (h : DeningerMeyerSource) (g : 𝓢(ℝ, ℂ)) :
    HasDerivAt
      (fun b : ℝ => deningerL1SchwartzPairing g
        (deningerAdiabaticEvenPreimageLpExt b h))
      (deningerL1SchwartzPairing g (deningerAdiabaticEulerPositiveLp a h)) a := by
  have hLp := hasDerivAt_deningerAdiabaticEvenPreimageLpExt ha h
  have hLp' : HasDerivAt (fun b : ℝ => deningerAdiabaticEvenPreimageLpExt b h)
      (deningerAdiabaticEulerPositiveLp a h) a := by
    simpa only [deningerAdiabaticEulerPositiveLp] using hLp
  exact (deningerL1SchwartzPairing g).hasFDerivAt.comp_hasDerivAt a hLp'

/-- Pairing model is literally evaluation of the distribution path. -/
theorem deningerAdiabaticPreimageDistributionExt_apply_eq_pairing
    (a : ℝ) (h : DeningerMeyerSource) (g : 𝓢(ℝ, ℂ)) :
    deningerAdiabaticPreimageDistributionExt a h g =
      deningerL1SchwartzPairing g (deningerAdiabaticEvenPreimageLpExt a h) := by
  rfl

/-- Two-collar lift along the positive extension of the strict path. -/
def deningerAdiabaticCollarLiftExt
    (a : ℝ) (h : DeningerMeyerSource) : 𝓢'(ℝ, ℂ) × 𝓢'(ℝ, ℂ) :=
  (𝓕 (deningerAdiabaticPreimageDistributionExt a h),
    deningerAdiabaticPreimageDistributionExt a (deningerMeyerCollarExchange h))

/-- Diagonal contragredient derivative of the two collars. -/
def deningerAdiabaticCollarDerivative
    (a : ℝ) (h : DeningerMeyerSource) : 𝓢'(ℝ, ℂ) × 𝓢'(ℝ, ℂ) :=
  (𝓕 (deningerAdiabaticEulerPositiveDistribution a h),
    deningerAdiabaticEulerPositiveDistribution a (deningerMeyerCollarExchange h))

/-- Boundary of the source-pointed two-collar lift. -/
def deningerAdiabaticMobiusBoundaryExt
    (a : ℝ) (h : DeningerMeyerSource) : 𝓢'(ℝ, ℂ) :=
  (deningerAdiabaticCollarLiftExt a h).1 - (deningerAdiabaticCollarLiftExt a h).2

/-- Green--Stokes flux: opposite-collar Euler transport minus physical Euler transport. -/
def deningerAdiabaticGreenStokesFlux
    (a : ℝ) (h : DeningerMeyerSource) : 𝓢'(ℝ, ℂ) :=
  (deningerAdiabaticCollarDerivative a h).1 -
    (deningerAdiabaticCollarDerivative a h).2

/-- Pairing form of the unsquared two-collar boundary. -/
def deningerAdiabaticMobiusBoundaryPairing
    (b : ℝ) (h : DeningerMeyerSource) (g : 𝓢(ℝ, ℂ)) : ℂ :=
  deningerL1SchwartzPairing (𝓕 g) (deningerAdiabaticEvenPreimageLpExt b h) -
    deningerL1SchwartzPairing g
      (deningerAdiabaticEvenPreimageLpExt b (deningerMeyerCollarExchange h))

/-- Pairing form of the exact Green--Stokes flux. -/
def deningerAdiabaticGreenStokesFluxPairing
    (a : ℝ) (h : DeningerMeyerSource) (g : 𝓢(ℝ, ℂ)) : ℂ :=
  deningerL1SchwartzPairing (𝓕 g) (deningerAdiabaticEulerPositiveLp a h) -
    deningerL1SchwartzPairing g
      (deningerAdiabaticEulerPositiveLp a (deningerMeyerCollarExchange h))

theorem deningerAdiabaticMobiusBoundaryExt_apply_eq_pairing
    (b : ℝ) (h : DeningerMeyerSource) (g : 𝓢(ℝ, ℂ)) :
    deningerAdiabaticMobiusBoundaryExt b h g =
      deningerAdiabaticMobiusBoundaryPairing b h g := by
  rfl

theorem deningerAdiabaticGreenStokesFlux_apply_eq_pairing
    (a : ℝ) (h : DeningerMeyerSource) (g : 𝓢(ℝ, ℂ)) :
    deningerAdiabaticGreenStokesFlux a h g =
      deningerAdiabaticGreenStokesFluxPairing a h g := by
  rfl

/-- Continuous boundary pairing on the `L¹` two-collar product. -/
def deningerAdiabaticBoundaryPairingCLM (g : 𝓢(ℝ, ℂ)) :
    (Lp ℂ (1 : ENNReal) (volume : Measure ℝ) ×
      Lp ℂ (1 : ENNReal) (volume : Measure ℝ)) →L[ℝ] ℂ :=
  (deningerL1SchwartzPairing (𝓕 g)).coprod (-(deningerL1SchwartzPairing g))

@[simp]
theorem deningerAdiabaticBoundaryPairingCLM_apply
    (g : 𝓢(ℝ, ℂ))
    (p : Lp ℂ (1 : ENNReal) (volume : Measure ℝ) ×
      Lp ℂ (1 : ENNReal) (volume : Measure ℝ)) :
    deningerAdiabaticBoundaryPairingCLM g p =
      deningerL1SchwartzPairing (𝓕 g) p.1 - deningerL1SchwartzPairing g p.2 := by
  simp [deningerAdiabaticBoundaryPairingCLM, sub_eq_add_neg]

/-- **Strict weak Green--Stokes law.**  The derivative of every paired unsquared boundary is the
literal difference of Fourier-contragredient and physical Euler fluxes. -/
theorem hasDerivAt_deningerAdiabaticMobiusBoundaryPairing
    {a : ℝ} (ha : 0 < a) (h : DeningerMeyerSource) (g : 𝓢(ℝ, ℂ)) :
    HasDerivAt
      (fun b : ℝ => deningerAdiabaticBoundaryPairingCLM g
        (deningerAdiabaticEvenPreimageLpExt b h,
          deningerAdiabaticEvenPreimageLpExt b (deningerMeyerCollarExchange h)))
      (deningerAdiabaticBoundaryPairingCLM g
        (deningerAdiabaticEulerPositiveLp a h,
          deningerAdiabaticEulerPositiveLp a (deningerMeyerCollarExchange h))) a := by
  have hfirst := hasDerivAt_deningerAdiabaticL1SchwartzPairing
    ha h (𝓕 g)
  have hsecond := hasDerivAt_deningerAdiabaticL1SchwartzPairing
    ha (deningerMeyerCollarExchange h) g
  have hpair :=
    (hasDerivAt_deningerAdiabaticEvenPreimageLpExt ha h).prodMk
      (hasDerivAt_deningerAdiabaticEvenPreimageLpExt ha
        (deningerMeyerCollarExchange h))
  have hpair' : HasDerivAt
      (fun b : ℝ =>
        (deningerAdiabaticEvenPreimageLpExt b h,
          deningerAdiabaticEvenPreimageLpExt b (deningerMeyerCollarExchange h)))
      (deningerAdiabaticEulerPositiveLp a h,
        deningerAdiabaticEulerPositiveLp a (deningerMeyerCollarExchange h)) a := by
    simpa only [deningerAdiabaticEulerPositiveLp] using hpair
  exact (deningerAdiabaticBoundaryPairingCLM g).hasFDerivAt.comp_hasDerivAt a hpair'

/-- Expanded exact Green--Stokes identity in tempered distributions. -/
theorem deningerAdiabaticGreenStokesFlux_eq
    (a : ℝ) (h : DeningerMeyerSource) :
    deningerAdiabaticGreenStokesFlux a h =
      𝓕 (deningerAdiabaticEulerPositiveDistribution a h) -
        deningerAdiabaticEulerPositiveDistribution a (deningerMeyerCollarExchange h) := by
  rfl

end

end RHTower
