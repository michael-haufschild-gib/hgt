import GaloisForLFunctions.RHTower.MobiusThetaNativeSecondCollar
import GaloisForLFunctions.RHTower.Sieve.MoebiusLogarithmicNormalization

/-!
# Native Euler mass on both complete collars

The actual positive-damping preimage has L1 mass `2 P(h) invZeta(1+a)`.
Applying the continuous L1 integral to its established parameter derivative
identifies the complete Euler mass with `2 P(h) invZeta'(1+a)`. The normalized
removable pole fixes the limit at `2 P(h)` as damping decreases to zero.

The original first collar therefore reads `2/m` times its Xi jet at
`i(1/2-1/m)`. The unchanged exchanged collar reads `2/m` times the original
Xi jet at `i/2`: its exponential factor cancels the ray Jacobian before
reflection. These are distinct source-derived evaluations at every native
depth and internal order.

This proves limits of the actual complete Euler masses. It does not identify
a weak distributional limit or replace the critical series of scalar
pairings by an integral of its pointwise sum. The fixed Gamma/BV reader
agreement remains a separate unproved comparison.
-/

set_option autoImplicit false
open Complex MeasureTheory ArithmeticFunction Filter Topology
open scoped SchwartzMap
noncomputable section
namespace RHTower

private abbrev mass : Lp ℂ (1 : ENNReal) (volume : Measure ℝ) →L[ℂ] ℂ :=
  L1.integralCLM' ℂ

private theorem mass_eq (f : Lp ℂ (1 : ENNReal) (volume : Measure ℝ)) :
    mass f = ∫ x : ℝ, f x := by
  rw [← L1.integral_eq' ℂ, L1.integral_eq_integral]

private theorem dilation_mass (h : DeningerMeyerSource) {n : ℕ} (hn : 0 < n) :
    mass (deningerAdiabaticEvenLogPullDilationLp h n hn) =
      (2 / (n : ℂ)) * deningerPullMass (DeningerMeyerSource.toSource h) := by
  let g := deningerAdiabaticEvenLogPullDilation h n
  have hg : Integrable g := deningerAdiabaticEvenLogPullDilation_integrable h hn
  rw [mass_eq, deningerAdiabaticEvenLogPullDilationLp, L1.integral_of_fun_eq_integral]
  have hsplit := intervalIntegral.integral_Iic_add_Ioi
    (hg.integrableOn : IntegrableOn g (Set.Iic 0))
    (hg.integrableOn : IntegrableOn g (Set.Ioi 0))
  have href := integral_comp_neg_Ioi (0 : ℝ) g
  rw [neg_zero] at href
  have heq : (∫ x in Set.Ioi (0 : ℝ), g (-x)) = ∫ x in Set.Ioi (0 : ℝ), g x :=
    setIntegral_congr_fun measurableSet_Ioi fun x _ =>
      deningerAdiabaticEvenLogPullDilation_even h n x
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hpos : (∫ x in Set.Ioi (0 : ℝ), g x) =
      (n : ℝ)⁻¹ • deningerPullMass (DeningerMeyerSource.toSource h) := by
    rw [← deningerLogPull_dilation_integral (DeningerMeyerSource.toSource h) hnR]
    refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    change deningerLogPull _ ((n : ℝ) * |x|) = deningerLogPull _ ((n : ℝ) * x)
    rw [abs_of_pos hx]
  change (∫ x : ℝ, g x) = _
  rw [← hsplit, ← href, heq, hpos, real_smul, Complex.ofReal_inv,
    Complex.ofReal_natCast]
  ring

private theorem term_mass (h : DeningerMeyerSource) (a : ℝ) (n : ℕ) :
    mass (deningerAdiabaticMobiusTermLp h n a) =
      (deningerDirichletTerm a n : ℂ) *
        (2 * deningerPullMass (DeningerMeyerSource.toSource h)) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [deningerAdiabaticMobiusTermLp, deningerDirichletTerm_zero]
  rw [deningerAdiabaticMobiusTermLp, dif_pos hn, map_smul, dilation_mass h hn]
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  rw [deningerAdiabaticMobiusScalar, deningerAdiabaticMobiusCoefficient_eq_rpow_neg a hn,
    deningerDirichletTerm_eq, Real.rpow_add hnR, Real.rpow_one, Real.rpow_neg hnR.le]
  push_cast
  simp only [smul_eq_mul]
  ring

private theorem preimage_mass (h : DeningerMeyerSource) {a : ℝ} (ha : 0 < a) :
    mass (deningerAdiabaticEvenPreimageLpExt a h) =
      Sieve.invZeta (1 + (a : ℂ)) *
        (2 * deningerPullMass (DeningerMeyerSource.toSource h)) := by
  have hsum : deningerAdiabaticEvenPreimageLpExt a h =
      ∑' n : ℕ, deningerAdiabaticMobiusTermLp h n a := by
    rw [tsum_deningerAdiabaticMobiusTermLp_eq ha h,
      deningerAdiabaticEvenPreimageLpExt, dif_pos ha.le]
  rw [hsum, mass.map_tsum (summable_deningerAdiabaticMobiusTermLp h ha)]
  simp_rw [term_mass]
  rw [tsum_mul_right]
  have hc := Complex.ofRealCLM.map_tsum (deningerMobiusDirichlet_summable ha)
  change ((∑' n : ℕ, deningerDirichletTerm a n : ℝ) : ℂ) =
    ∑' n : ℕ, (deningerDirichletTerm a n : ℂ) at hc
  rw [← hc, deningerDirichlet_cast ha]
  rw [Sieve.invZeta_eq_inv (by
    intro hz
    have : (a : ℂ) = 0 := by linear_combination hz
    exact ha.ne' (Complex.ofReal_eq_zero.mp this))]

private theorem euler_mass (h : DeningerMeyerSource) {a : ℝ} (ha : 0 < a) :
    mass (deningerAdiabaticEulerPositiveLp a h) =
      deriv Sieve.invZeta (1 + (a : ℂ)) *
        (2 * deningerPullMass (DeningerMeyerSource.toSource h)) := by
  have hleft := (mass.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt a
    (hasDerivAt_deningerAdiabaticEvenPreimageLpExt ha h)
  have hs : ((1 + a : ℝ) : ℂ) ≠ 1 := by
    intro heq
    have heqR := congrArg Complex.re heq
    simp only [Complex.ofReal_re, Complex.one_re] at heqR
    linarith
  have hz : riemannZeta (((1 + a : ℝ) : ℂ)) ≠ 0 :=
    riemannZeta_ne_zero_of_one_le_re (by simp only [Complex.ofReal_re]; linarith)
  have hd := (Sieve.differentiableAt_invZeta_of_zeta_ne_zero hs hz).hasDerivAt.comp_ofReal
  have hright := (hd.scomp a ((hasDerivAt_id a).const_add 1)).mul_const
    (2 * deningerPullMass (DeningerMeyerSource.toSource h))
  simp only [one_smul, Function.comp_apply, Complex.ofReal_add, Complex.ofReal_one] at hright
  have heq : (fun b : ℝ => mass (deningerAdiabaticEvenPreimageLpExt b h)) =ᶠ[𝓝 a]
      (fun b : ℝ => Sieve.invZeta (1 + (b : ℂ)) *
        (2 * deningerPullMass (DeningerMeyerSource.toSource h))) := by
    filter_upwards [Ioi_mem_nhds ha] with b hb
    exact preimage_mass h hb
  exact (hleft.congr_of_eventuallyEq heq.symm).unique hright

private theorem euler_mass_tendsto (h : DeningerMeyerSource) :
    Tendsto (fun a : ℝ => mass (deningerAdiabaticEulerPositiveLp a h)) (𝓝[>] 0)
      (𝓝 (2 * deningerPullMass (DeningerMeyerSource.toSource h))) := by
  have han : AnalyticAt ℂ Sieve.invZeta 1 := by
    change AnalyticAt ℂ (fun s : ℂ => (s - 1) * (zetaResidueUnit s)⁻¹) 1
    exact (analyticAt_id.sub analyticAt_const).mul
      ((analyticAt_zetaResidueUnit 1).inv (by rw [zetaResidueUnit_one]; exact one_ne_zero))
  have harg : Tendsto (fun a : ℝ => 1 + (a : ℂ)) (𝓝[>] 0) (𝓝 (1 : ℂ)) := by
    have hc : Continuous (fun a : ℝ => (1 : ℂ) + (a : ℂ)) :=
      continuous_const.add Complex.continuous_ofReal
    simpa only [Complex.ofReal_zero, add_zero] using
      (hc.tendsto 0).mono_left (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from inf_le_left)
  have hlim := (han.deriv.continuousAt.tendsto.comp harg).mul_const
    (2 * deningerPullMass (DeningerMeyerSource.toSource h))
  rw [Sieve.deriv_invZeta_one, one_mul] at hlim
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with a ha
  exact (euler_mass h ha).symm

/-- The complete damped Euler mass has the original native Xi-jet limit. -/
theorem mobiusThetaNativeEulerMass_tendsto (k : ℕ) (m : ℕ+) :
    Tendsto (fun a : ℝ => ∫ x : ℝ,
      (deningerAdiabaticEulerPositiveLp a (mobiusThetaNativeMeyerSource k m)) x)
      (𝓝[>] 0)
      (𝓝 ((2 / (m : ℂ)) * iteratedDeriv k XiC (mobiusThetaNativeMassParameter m))) := by
  have hlim := euler_mass_tendsto (mobiusThetaNativeMeyerSource k m)
  simp only [mobiusThetaNativeMeyerSource_toSource,
    mobiusThetaNativeCollarSource_pullMass, mass_eq] at hlim
  convert hlim using 1
  congr 1
  ring

/-- The unchanged exchanged source's ray mass reads the original jet at `i/2`. -/
theorem mobiusThetaNativeSecondCollarSource_pullMass (k : ℕ) (m : ℕ+) :
    deningerPullMass (DeningerMeyerSource.toSource (mobiusThetaNativeSecondCollarSource k m)) =
      (m : ℂ)⁻¹ * iteratedDeriv k XiC (I / 2) := by
  have hv : |(I / 2 : ℂ).im| < 1 := by norm_num
  have hp : mobiusThetaCenteredParameter (I / 2) = 0 := by
    rw [mobiusThetaCenteredParameter, ← mul_div_assoc, I_mul_I]
    ring
  have hd := (mobiusThetaNativeCollarSource_mellin_data k m hv).2
  rw [hp] at hd
  simp only [mul_zero, zero_mul, Complex.exp_zero, one_mul] at hd
  rw [deningerPullMass, ← Real.range_exp, ← Set.image_univ,
    integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ
      (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt) Real.exp_injective.injOn,
    setIntegral_univ]
  have heq : (fun t : ℝ => |Real.exp t| •
      deningerLogPull (DeningerMeyerSource.toSource (mobiusThetaNativeSecondCollarSource k m))
        (Real.exp t)) = fun t : ℝ => mobiusThetaNativeCollarSource k m (-t) := by
    funext t
    rw [abs_of_pos (Real.exp_pos _), deningerLogPull_apply, Real.log_exp, real_smul]
    change (Real.exp t : ℂ) *
      ((Real.exp (-t) : ℂ) * mobiusThetaNativeCollarSource k m (-t)) = _
    rw [← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add, add_neg_cancel,
      Real.exp_zero, Complex.ofReal_one, one_mul]
  rw [heq, integral_neg_eq_self]
  exact hd

/-- The second complete Euler mass has its own native normalization in the damping limit. -/
theorem mobiusThetaNativeSecondEulerMass_tendsto (k : ℕ) (m : ℕ+) :
    Tendsto (fun a : ℝ => ∫ x : ℝ,
      (deningerAdiabaticEulerPositiveLp a (mobiusThetaNativeSecondCollarSource k m)) x)
      (𝓝[>] 0) (𝓝 ((2 / (m : ℂ)) * iteratedDeriv k XiC (I / 2))) := by
  have hlim := euler_mass_tendsto (mobiusThetaNativeSecondCollarSource k m)
  simp only [mobiusThetaNativeSecondCollarSource_pullMass, mass_eq] at hlim
  convert hlim using 1
  congr 1
  ring

end RHTower
