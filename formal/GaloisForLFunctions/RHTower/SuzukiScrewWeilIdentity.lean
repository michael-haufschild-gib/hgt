import GaloisForLFunctions.RHTower.SuzukiScrewSmoothTestCriterion
import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Suzuki's compact-smooth screw--Weil identity

This file formalizes Suzuki (2022), Proposition 3.1.  The first section supplies the missing
unconditional analytic bridge: the literal screw kernel is the absolutely convergent exponential
series on the full multiplicity-exact Xi divisor.  Later sections pair that series with compactly
supported smooth derivatives and identify the result with the literal Weil distribution of the
Hermitian convolution.
-/

open Complex MeasureTheory Set Function

noncomputable section

namespace RHTower

/-! ## Oriented exponential form of the unconditional screw divisor -/

/-- One oriented exponential summand of Suzuki's Xi screw divisor. -/
def xiScrewExponentialTerm (t : ℝ) (q : XiZeroCopy) : ℂ :=
  (1 - Complex.exp (I * xiSpectralPoint q * (t : ℂ))) /
    xiSpectralPoint q ^ (2 : ℕ)

theorem norm_xiScrewExponentialTerm_le (t : ℝ) (q : XiZeroCopy) :
    ‖xiScrewExponentialTerm t q‖ ≤
      (1 + Real.exp (|t| / 2)) / ‖xiSpectralPoint q‖ ^ (2 : ℕ) := by
  have hstrip : |(I * xiSpectralPoint q).re| ≤ (1 / 2 : ℝ) :=
    le_of_lt (abs_re_I_mul_xiSpectralPoint_le_half q)
  have hre : (I * xiSpectralPoint q * (t : ℂ)).re ≤ |t| / 2 := by
    rw [Complex.mul_re]
    simp only [ofReal_re, ofReal_im, mul_zero, sub_zero]
    calc
      (I * xiSpectralPoint q).re * t ≤
          |(I * xiSpectralPoint q).re * t| := le_abs_self _
      _ = |(I * xiSpectralPoint q).re| * |t| := abs_mul _ _
      _ ≤ (1 / 2) * |t| := by gcongr
      _ = |t| / 2 := by ring
  rw [xiScrewExponentialTerm, norm_div, norm_pow]
  calc
    ‖1 - Complex.exp (I * xiSpectralPoint q * (t : ℂ))‖ /
          ‖xiSpectralPoint q‖ ^ (2 : ℕ) ≤
        (‖(1 : ℂ)‖ +
          ‖Complex.exp (I * xiSpectralPoint q * (t : ℂ))‖) /
          ‖xiSpectralPoint q‖ ^ (2 : ℕ) := by
      gcongr
      exact norm_sub_le (1 : ℂ)
        (Complex.exp (I * xiSpectralPoint q * (t : ℂ)))
    _ = (1 + Real.exp (I * xiSpectralPoint q * (t : ℂ)).re) /
          ‖xiSpectralPoint q‖ ^ (2 : ℕ) := by
      rw [norm_one, Complex.norm_exp]
    _ ≤ (1 + Real.exp (|t| / 2)) / ‖xiSpectralPoint q‖ ^ (2 : ℕ) := by
      gcongr

theorem xiScrewExponentialTerm_summable (t : ℝ) :
    Summable (xiScrewExponentialTerm t) := by
  apply Summable.of_norm_bounded
    (xiSpectralPoint_inv_sq_summable.mul_left (1 + Real.exp (|t| / 2)))
  intro q
  calc
    ‖xiScrewExponentialTerm t q‖ ≤
        (1 + Real.exp (|t| / 2)) / ‖xiSpectralPoint q‖ ^ (2 : ℕ) :=
      norm_xiScrewExponentialTerm_le t q
    _ = (1 + Real.exp (|t| / 2)) *
        (1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ)) := by ring

theorem xiScrewExponentialTerm_add_reflect (t : ℝ) (q : XiZeroCopy) :
    xiScrewExponentialTerm t q +
        xiScrewExponentialTerm t (xiZeroCopyReflectEquiv q) =
      2 * xiScrewDivisorTerm t q := by
  have hq : xiSpectralPoint q ≠ 0 := xiSpectralPoint_ne_zero q
  rw [xiScrewExponentialTerm, xiScrewExponentialTerm,
    xiSpectralPoint_reflect, xiScrewDivisorTerm, Complex.cosh]
  have hexp :
      Complex.exp (I * (-xiSpectralPoint q) * (t : ℂ)) =
        Complex.exp (-(I * xiSpectralPoint q * (t : ℂ))) := by
    congr 1
    ring
  rw [hexp]
  field_simp [hq]
  rw [Complex.I_sq]
  ring

/-- The `cosh` divisor series is exactly its oriented exponential series.  Reflection symmetry of
the full divisor is used before summation; no RH hypothesis occurs. -/
theorem xiScrewDivisor_eq_tsum_exponential (t : ℝ) :
    xiScrewDivisor t = ∑' q : XiZeroCopy, xiScrewExponentialTerm t q := by
  let E : XiZeroCopy → ℂ := xiScrewExponentialTerm t
  let S : XiZeroCopy → ℂ := xiScrewDivisorTerm t
  have hE : Summable E := xiScrewExponentialTerm_summable t
  have hER : Summable (fun q => E (xiZeroCopyReflectEquiv q)) :=
    (xiZeroCopyReflectEquiv.summable_iff).2 hE
  have hS : Summable S := xiScrewDivisorTerm_summable t
  have hreflect : (∑' q, E (xiZeroCopyReflectEquiv q)) = ∑' q, E q :=
    xiZeroCopyReflectEquiv.tsum_eq E
  have htwo : 2 * (∑' q, E q) = 2 * (∑' q, S q) := by
    calc
      2 * (∑' q, E q) = (∑' q, E q) + ∑' q, E q := by ring
      _ = (∑' q, E q) + ∑' q, E (xiZeroCopyReflectEquiv q) := by
        rw [hreflect]
      _ = ∑' q, (E q + E (xiZeroCopyReflectEquiv q)) := by
        rw [hE.tsum_add hER]
      _ = ∑' q, 2 * S q := by
        apply tsum_congr
        intro q
        exact xiScrewExponentialTerm_add_reflect t q
      _ = 2 * (∑' q, S q) := by rw [tsum_mul_left]
  rw [xiScrewDivisor]
  exact (mul_left_cancel₀ (by norm_num : (2 : ℂ) ≠ 0) htwo).symm

/-! ## Literal kernel as an absolutely convergent divisor feature series -/

/-- One divisor feature in Suzuki's kernel identity (1.9). -/
def xiScrewKernelExponentialTerm (t u : ℝ) (q : XiZeroCopy) : ℂ :=
  ((Complex.exp (I * xiSpectralPoint q * (t : ℂ)) - 1) *
      (Complex.exp (-(I * xiSpectralPoint q * (u : ℂ))) - 1)) /
    xiSpectralPoint q ^ (2 : ℕ)

theorem xiScrewKernelExponentialTerm_eq (t u : ℝ) (q : XiZeroCopy) :
    xiScrewKernelExponentialTerm t u q =
      -xiScrewExponentialTerm (t - u) q +
        xiScrewExponentialTerm t q + xiScrewExponentialTerm (-u) q := by
  have hq : xiSpectralPoint q ≠ 0 := xiSpectralPoint_ne_zero q
  rw [xiScrewKernelExponentialTerm, xiScrewExponentialTerm,
    xiScrewExponentialTerm, xiScrewExponentialTerm]
  have hexp :
      Complex.exp (I * xiSpectralPoint q * ((t - u : ℝ) : ℂ)) =
        Complex.exp (I * xiSpectralPoint q * (t : ℂ)) *
          Complex.exp (-(I * xiSpectralPoint q * (u : ℂ))) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hneg :
      Complex.exp (I * xiSpectralPoint q * ((-u : ℝ) : ℂ)) =
        Complex.exp (-(I * xiSpectralPoint q * (u : ℂ))) := by
    congr 1
    push_cast
    ring
  rw [hexp, hneg]
  field_simp [hq]
  ring

theorem xiScrewKernelExponentialTerm_summable (t u : ℝ) :
    Summable (xiScrewKernelExponentialTerm t u) := by
  have h := ((xiScrewExponentialTerm_summable (t - u)).neg.add
    (xiScrewExponentialTerm_summable t)).add
      (xiScrewExponentialTerm_summable (-u))
  exact h.congr (fun q => (xiScrewKernelExponentialTerm_eq t u q).symm)

/-- Suzuki's literal kernel is its full multiplicity-exact exponential divisor series,
unconditionally. -/
theorem suzukiScrewKernel_eq_tsum_exponential (t u : ℝ) :
    suzukiScrewKernel t u =
      ∑' q : XiZeroCopy, xiScrewKernelExponentialTerm t u q := by
  have hsub := xiScrewExponentialTerm_summable (t - u)
  have ht := xiScrewExponentialTerm_summable t
  have hnu := xiScrewExponentialTerm_summable (-u)
  have hpsi (x : ℝ) : (suzukiPsi x : ℂ) =
      ∑' q : XiZeroCopy, xiScrewExponentialTerm x q := by
    rw [ofReal_suzukiPsi_eq_xiScrewDivisor_all,
      xiScrewDivisor_eq_tsum_exponential]
  rw [suzukiScrewKernel, suzukiScrewG, suzukiScrewG,
    suzukiScrewG, suzukiScrewG, hpsi (t - u), hpsi t, hpsi (-u),
    suzukiPsi_zero]
  simp only [Complex.ofReal_zero, neg_zero, add_zero]
  calc
    -(∑' q, xiScrewExponentialTerm (t - u) q) -
          -(∑' q, xiScrewExponentialTerm t q) -
          -(∑' q, xiScrewExponentialTerm (-u) q) =
        (-(∑' q, xiScrewExponentialTerm (t - u) q) +
          (∑' q, xiScrewExponentialTerm t q)) +
          (∑' q, xiScrewExponentialTerm (-u) q) := by ring
    _ = (∑' q, -xiScrewExponentialTerm (t - u) q) +
          (∑' q, xiScrewExponentialTerm t q) +
          (∑' q, xiScrewExponentialTerm (-u) q) := by rw [tsum_neg]
    _ = ∑' q, ((-xiScrewExponentialTerm (t - u) q +
          xiScrewExponentialTerm t q) + xiScrewExponentialTerm (-u) q) := by
      rw [(hsub.neg.tsum_add ht).symm,
        ((hsub.neg.add ht).tsum_add hnu).symm]
    _ = ∑' q, xiScrewKernelExponentialTerm t u q := by
      apply tsum_congr
      intro q
      exact (xiScrewKernelExponentialTerm_eq t u q).symm

/-! ## Suzuki's source class `C(a)` and complex-frequency differentiation -/

/-- Literal source class `C(a)` from Suzuki (2022), equation (3.6): smooth compactly supported
complex tests whose support lies in `[-a,a]`. -/
structure SuzukiSmoothCompactTest (a : ℝ) where
  toFun : ℝ → ℂ
  smooth : ContDiff ℝ (⊤ : ℕ∞) toFun
  support_subset : Function.support toFun ⊆ Icc (-a) a

instance (a : ℝ) : CoeFun (SuzukiSmoothCompactTest a) fun _ => ℝ → ℂ :=
  ⟨SuzukiSmoothCompactTest.toFun⟩

theorem SuzukiSmoothCompactTest.continuous {a : ℝ}
    (ψ : SuzukiSmoothCompactTest a) : Continuous ψ :=
  ψ.smooth.continuous

theorem SuzukiSmoothCompactTest.tsupport_subset {a : ℝ}
    (ψ : SuzukiSmoothCompactTest a) : tsupport ψ ⊆ Icc (-a) a :=
  closure_minimal ψ.support_subset isClosed_Icc

theorem SuzukiSmoothCompactTest.hasCompactSupport {a : ℝ}
    (ψ : SuzukiSmoothCompactTest a) : HasCompactSupport ψ := by
  exact HasCompactSupport.of_support_subset_isCompact isCompact_Icc ψ.support_subset

theorem SuzukiSmoothCompactTest.integrable {a : ℝ}
    (ψ : SuzukiSmoothCompactTest a) : Integrable ψ :=
  ψ.continuous.integrable_of_hasCompactSupport ψ.hasCompactSupport

theorem SuzukiSmoothCompactTest.deriv_smooth {a : ℝ}
    (ψ : SuzukiSmoothCompactTest a) :
    ContDiff ℝ (⊤ : ℕ∞) (deriv ψ) :=
  (contDiff_infty_iff_deriv.mp ψ.smooth).2

theorem SuzukiSmoothCompactTest.deriv_support_subset {a : ℝ}
    (ψ : SuzukiSmoothCompactTest a) :
    Function.support (deriv ψ) ⊆ Icc (-a) a :=
  support_deriv_subset.trans ψ.tsupport_subset

theorem SuzukiSmoothCompactTest.deriv_hasCompactSupport {a : ℝ}
    (ψ : SuzukiSmoothCompactTest a) : HasCompactSupport (deriv ψ) :=
  ψ.hasCompactSupport.deriv

theorem SuzukiSmoothCompactTest.deriv_integrable {a : ℝ}
    (ψ : SuzukiSmoothCompactTest a) : Integrable (deriv ψ) :=
  ψ.deriv_smooth.continuous.integrable_of_hasCompactSupport ψ.deriv_hasCompactSupport

theorem SuzukiSmoothCompactTest.integral_deriv_eq_zero {a : ℝ}
    (ψ : SuzukiSmoothCompactTest a) : ∫ x : ℝ, deriv ψ x = 0 := by
  have hC1 : ContDiff ℝ 1 ψ := ψ.smooth.of_le (by simp)
  have hint : Integrable (deriv ψ) := ψ.deriv_integrable
  have hsplit := integral_add_compl (μ := (volume : Measure ℝ))
    (measurableSet_Iic (a := (0 : ℝ))) hint
  have hIic : (∫ x : ℝ in Iic (0 : ℝ), deriv ψ x) = ψ 0 :=
    ψ.hasCompactSupport.integral_Iic_deriv_eq hC1 0
  have hIoi : (∫ x : ℝ in Ioi (0 : ℝ), deriv ψ x) = -ψ 0 :=
    ψ.hasCompactSupport.integral_Ioi_deriv_eq hC1 0
  rw [compl_Iic, hIic, hIoi] at hsplit
  simpa using hsplit.symm

/-- Differentiation maps Suzuki's `C(a)` into the exact zero-mean source class
`mathfrak C_0(a)`. -/
def SuzukiSmoothCompactTest.toDerivativeZeroMean {a : ℝ}
    (ψ : SuzukiSmoothCompactTest a) : SuzukiSmoothZeroMeanTest a where
  toFun := deriv ψ
  smooth := ψ.deriv_smooth
  support_subset := ψ.deriv_support_subset
  integral_zero := ψ.integral_deriv_eq_zero

@[simp] theorem SuzukiSmoothCompactTest.coe_toDerivativeZeroMean {a : ℝ}
    (ψ : SuzukiSmoothCompactTest a) :
    (ψ.toDerivativeZeroMean : ℝ → ℂ) = deriv ψ := rfl

/-- Suzuki's entire Fourier transform convention `hat ψ(z)=∫ψ(t)e^{izt}dt`. -/
def suzukiSmoothFourier {a : ℝ} (ψ : SuzukiSmoothCompactTest a) (z : ℂ) : ℂ :=
  ∫ x : ℝ, ψ x * Complex.exp (I * z * (x : ℂ))

theorem SuzukiSmoothCompactTest.integrable_fourierIntegrand {a : ℝ}
    (ψ : SuzukiSmoothCompactTest a) (z : ℂ) :
    Integrable fun x : ℝ => ψ x * Complex.exp (I * z * (x : ℂ)) := by
  exact (ψ.continuous.mul (Complex.continuous_exp.comp
    (continuous_const.mul continuous_ofReal))).integrable_of_hasCompactSupport
      ψ.hasCompactSupport.mul_right

theorem SuzukiSmoothCompactTest.integrable_deriv_fourierIntegrand {a : ℝ}
    (ψ : SuzukiSmoothCompactTest a) (z : ℂ) :
    Integrable fun x : ℝ => deriv ψ x * Complex.exp (I * z * (x : ℂ)) := by
  exact (ψ.deriv_smooth.continuous.mul (Complex.continuous_exp.comp
    (continuous_const.mul continuous_ofReal))).integrable_of_hasCompactSupport
      ψ.deriv_hasCompactSupport.mul_right

/-- Whole-line integration by parts at arbitrary complex frequency.  Compact support, not RH,
removes both boundary terms. -/
theorem integral_deriv_mul_cexp {a : ℝ}
    (ψ : SuzukiSmoothCompactTest a) (z : ℂ) :
    (∫ x : ℝ, deriv ψ x * Complex.exp (I * z * (x : ℂ))) =
      -(I * z) * suzukiSmoothFourier ψ z := by
  let u : ℝ → ℂ := ψ
  let u' : ℝ → ℂ := deriv ψ
  let v : ℝ → ℂ := fun x => Complex.exp (I * z * (x : ℂ))
  let v' : ℝ → ℂ := fun x => (I * z) * Complex.exp (I * z * (x : ℂ))
  have hu : ∀ x, HasDerivAt u (u' x) x := by
    intro x
    exact (ψ.smooth.differentiable (by simp)).differentiableAt.hasDerivAt
  have hv : ∀ x, HasDerivAt v (v' x) x := by
    intro x
    have hlin : HasDerivAt (fun y : ℝ => I * z * (y : ℂ)) (I * z) x := by
      simpa using ((hasDerivAt_id x).ofReal_comp.const_mul (I * z))
    convert hlin.cexp using 1 <;> ring
  have huv : Integrable (u * v) := by
    change Integrable fun x : ℝ => ψ x * Complex.exp (I * z * (x : ℂ))
    exact ψ.integrable_fourierIntegrand z
  have huv' : Integrable (u * v') := by
    have hbase := ψ.integrable_fourierIntegrand z
    have hconst : (u * v') = fun x => (I * z) *
        (ψ x * Complex.exp (I * z * (x : ℂ))) := by
      funext x
      simp only [u, v', Pi.mul_apply]
      ring
    rw [hconst]
    exact hbase.const_mul _
  have hu'v : Integrable (u' * v) := by
    change Integrable fun x : ℝ => deriv ψ x * Complex.exp (I * z * (x : ℂ))
    exact ψ.integrable_deriv_fourierIntegrand z
  have hparts := integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := u) (v := v) (u' := u') (v' := v')
    (fun x _ => hu x) (fun x _ => hv x) huv' hu'v huv
  have hleft : (∫ x : ℝ, u x * v' x) =
      (I * z) * suzukiSmoothFourier ψ z := by
    rw [suzukiSmoothFourier, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with x
    simp only [u, v', Pi.mul_apply]
    ring
  rw [hleft] at hparts
  have hright := congrArg Neg.neg hparts
  simp only [neg_neg] at hright
  change (∫ x : ℝ, deriv ψ x * Complex.exp (I * z * (x : ℂ))) = _
  calc
    _ = -(I * z * suzukiSmoothFourier ψ z) := by
      simpa only [u', v, Pi.mul_apply] using hright.symm
    _ = -(I * z) * suzukiSmoothFourier ψ z := by ring

/-- Fourier differentiation law used in Suzuki's proof of Proposition 3.1. -/
theorem suzukiSmoothFourier_deriv {a : ℝ}
    (ψ : SuzukiSmoothCompactTest a) (z : ℂ) :
    (∫ x : ℝ, deriv ψ x * Complex.exp (I * z * (x : ℂ))) =
      -I * z * suzukiSmoothFourier ψ z := by
  rw [integral_deriv_mul_cexp]
  ring

/-! ## Absolute convergence of the compact-smooth divisor pairing -/

/-- Pointwise complex conjugate of a source test, still in the same literal `C(a)`. -/
def SuzukiSmoothCompactTest.conjugate {a : ℝ}
    (ψ : SuzukiSmoothCompactTest a) : SuzukiSmoothCompactTest a where
  toFun := fun x => (starRingEnd ℂ) (ψ x)
  smooth := Complex.conjCLE.contDiff.comp ψ.smooth
  support_subset := by
    intro x hx
    apply ψ.support_subset
    exact fun hzero => hx (by simp [hzero])

@[simp] theorem SuzukiSmoothCompactTest.coe_conjugate {a : ℝ}
    (ψ : SuzukiSmoothCompactTest a) (x : ℝ) :
    ψ.conjugate x = (starRingEnd ℂ) (ψ x) := rfl

theorem SuzukiSmoothCompactTest.deriv_conjugate {a : ℝ}
    (ψ : SuzukiSmoothCompactTest a) (x : ℝ) :
    deriv ψ.conjugate x = (starRingEnd ℂ) (deriv ψ x) := by
  have hψ : HasDerivAt ψ (deriv ψ x) x :=
    (ψ.smooth.differentiable (by simp)).differentiableAt.hasDerivAt
  have h := Complex.conjCLE.hasFDerivAt.comp_hasDerivAt x hψ
  exact h.deriv

/-- The product-space summand obtained by pairing one divisor feature with two derivatives. -/
def suzukiScrewWeilPairingIntegrand {a : ℝ}
    (ψ₁ ψ₂ : SuzukiSmoothCompactTest a) (q : XiZeroCopy)
    (p : ℝ × ℝ) : ℂ :=
  xiScrewKernelExponentialTerm p.1 p.2 q * deriv ψ₁ p.2 *
    (starRingEnd ℂ) (deriv ψ₂ p.1)

theorem continuous_suzukiScrewWeilPairingIntegrand {a : ℝ}
    (ψ₁ ψ₂ : SuzukiSmoothCompactTest a) (q : XiZeroCopy) :
    Continuous (suzukiScrewWeilPairingIntegrand ψ₁ ψ₂ q) := by
  have hK : Continuous fun p : ℝ × ℝ =>
      xiScrewKernelExponentialTerm p.1 p.2 q := by
    unfold xiScrewKernelExponentialTerm
    fun_prop
  exact (hK.mul (ψ₁.deriv_smooth.continuous.comp continuous_snd)).mul
    (Complex.continuous_conj.comp
      (ψ₂.deriv_smooth.continuous.comp continuous_fst))

theorem support_suzukiScrewWeilPairingIntegrand_subset {a : ℝ}
    (ψ₁ ψ₂ : SuzukiSmoothCompactTest a) (q : XiZeroCopy) :
    Function.support (suzukiScrewWeilPairingIntegrand ψ₁ ψ₂ q) ⊆
      Icc (-a) a ×ˢ Icc (-a) a := by
  intro p hp
  have h₂ : deriv ψ₂ p.1 ≠ 0 := by
    intro hz
    apply hp
    simp [suzukiScrewWeilPairingIntegrand, hz]
  have h₁ : deriv ψ₁ p.2 ≠ 0 := by
    intro hz
    apply hp
    simp [suzukiScrewWeilPairingIntegrand, hz]
  exact ⟨ψ₂.deriv_support_subset h₂, ψ₁.deriv_support_subset h₁⟩

theorem integrable_suzukiScrewWeilPairingIntegrand {a : ℝ}
    (ψ₁ ψ₂ : SuzukiSmoothCompactTest a) (q : XiZeroCopy) :
    Integrable (suzukiScrewWeilPairingIntegrand ψ₁ ψ₂ q)
      (volume.prod volume) := by
  exact (continuous_suzukiScrewWeilPairingIntegrand ψ₁ ψ₂ q).integrable_of_hasCompactSupport
      (HasCompactSupport.of_support_subset_isCompact
        (isCompact_Icc.prod isCompact_Icc)
        (support_suzukiScrewWeilPairingIntegrand_subset ψ₁ ψ₂ q))

/-- Product-space integrand for Suzuki's literal differentiated screw form. -/
def suzukiDifferentiatedScrewIntegrand {a : ℝ}
    (ψ₁ ψ₂ : SuzukiSmoothCompactTest a) (p : ℝ × ℝ) : ℂ :=
  suzukiScrewKernel p.1 p.2 * deriv ψ₁ p.2 *
    (starRingEnd ℂ) (deriv ψ₂ p.1)

theorem continuous_suzukiDifferentiatedScrewIntegrand {a : ℝ}
    (ψ₁ ψ₂ : SuzukiSmoothCompactTest a) :
    Continuous (suzukiDifferentiatedScrewIntegrand ψ₁ ψ₂) := by
  have hK : Continuous fun p : ℝ × ℝ => suzukiScrewKernel p.1 p.2 := by
    have hreal := continuous_suzukiScrewKernelReal
    have hcast := Complex.continuous_ofReal.comp hreal
    exact hcast.congr fun p => ofReal_suzukiScrewKernelReal p.1 p.2
  exact (hK.mul (ψ₁.deriv_smooth.continuous.comp continuous_snd)).mul
    (Complex.continuous_conj.comp
      (ψ₂.deriv_smooth.continuous.comp continuous_fst))

theorem support_suzukiDifferentiatedScrewIntegrand_subset {a : ℝ}
    (ψ₁ ψ₂ : SuzukiSmoothCompactTest a) :
    Function.support (suzukiDifferentiatedScrewIntegrand ψ₁ ψ₂) ⊆
      Icc (-a) a ×ˢ Icc (-a) a := by
  intro p hp
  have h₂ : deriv ψ₂ p.1 ≠ 0 := by
    intro hz
    apply hp
    simp [suzukiDifferentiatedScrewIntegrand, hz]
  have h₁ : deriv ψ₁ p.2 ≠ 0 := by
    intro hz
    apply hp
    simp [suzukiDifferentiatedScrewIntegrand, hz]
  exact ⟨ψ₂.deriv_support_subset h₂, ψ₁.deriv_support_subset h₁⟩

theorem integrable_suzukiDifferentiatedScrewIntegrand {a : ℝ}
    (ψ₁ ψ₂ : SuzukiSmoothCompactTest a) :
    Integrable (suzukiDifferentiatedScrewIntegrand ψ₁ ψ₂)
      (volume.prod volume) := by
  exact (continuous_suzukiDifferentiatedScrewIntegrand ψ₁ ψ₂).integrable_of_hasCompactSupport
      (HasCompactSupport.of_support_subset_isCompact
        (isCompact_Icc.prod isCompact_Icc)
        (support_suzukiDifferentiatedScrewIntegrand_subset ψ₁ ψ₂))

theorem norm_cexp_i_xi_sub_one_le_of_mem_Icc {a x : ℝ}
    (ha : 0 ≤ a) (hx : x ∈ Icc (-a) a) (q : XiZeroCopy) :
    ‖Complex.exp (I * xiSpectralPoint q * (x : ℂ)) - 1‖ ≤
      Real.exp (a / 2) + 1 := by
  have hstrip : |(I * xiSpectralPoint q).re| ≤ (1 / 2 : ℝ) :=
    le_of_lt (abs_re_I_mul_xiSpectralPoint_le_half q)
  have hxabs : |x| ≤ a := (abs_le.mpr hx)
  have hre : (I * xiSpectralPoint q * (x : ℂ)).re ≤ a / 2 := by
    rw [Complex.mul_re]
    simp only [ofReal_re, ofReal_im, mul_zero, sub_zero]
    calc
      (I * xiSpectralPoint q).re * x ≤
          |(I * xiSpectralPoint q).re * x| := le_abs_self _
      _ = |(I * xiSpectralPoint q).re| * |x| := abs_mul _ _
      _ ≤ (1 / 2) * a := by gcongr
      _ = a / 2 := by ring
  calc
    ‖Complex.exp (I * xiSpectralPoint q * (x : ℂ)) - 1‖ ≤
        ‖Complex.exp (I * xiSpectralPoint q * (x : ℂ))‖ + ‖(1 : ℂ)‖ :=
      norm_sub_le _ _
    _ = Real.exp (I * xiSpectralPoint q * (x : ℂ)).re + 1 := by
      rw [Complex.norm_exp, norm_one]
    _ ≤ Real.exp (a / 2) + 1 := by gcongr

theorem norm_xiScrewKernelExponentialTerm_le_of_mem_Icc
    {a t u : ℝ} (ha : 0 ≤ a) (ht : t ∈ Icc (-a) a)
    (hu : u ∈ Icc (-a) a) (q : XiZeroCopy) :
    ‖xiScrewKernelExponentialTerm t u q‖ ≤
      (Real.exp (a / 2) + 1) ^ (2 : ℕ) *
        (1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ)) := by
  have hneg : -u ∈ Icc (-a) a := by
    constructor <;> linarith [hu.1, hu.2]
  have htbound := norm_cexp_i_xi_sub_one_le_of_mem_Icc ha ht q
  have hubound := norm_cexp_i_xi_sub_one_le_of_mem_Icc ha hneg q
  have hrewrite :
      Complex.exp (I * xiSpectralPoint q * ((-u : ℝ) : ℂ)) =
        Complex.exp (-(I * xiSpectralPoint q * (u : ℂ))) := by
    congr 1
    push_cast
    ring
  rw [hrewrite] at hubound
  rw [xiScrewKernelExponentialTerm, norm_div, norm_mul, norm_pow]
  calc
    (‖Complex.exp (I * xiSpectralPoint q * (t : ℂ)) - 1‖ *
          ‖Complex.exp (-(I * xiSpectralPoint q * (u : ℂ))) - 1‖) /
        ‖xiSpectralPoint q‖ ^ (2 : ℕ) ≤
      ((Real.exp (a / 2) + 1) * (Real.exp (a / 2) + 1)) /
        ‖xiSpectralPoint q‖ ^ (2 : ℕ) := by gcongr
    _ = (Real.exp (a / 2) + 1) ^ (2 : ℕ) *
        (1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ)) := by ring

/-- Pointwise reciprocal-square majorant for one differentiated divisor pairing. -/
theorem norm_suzukiScrewWeilPairingIntegrand_le {a : ℝ}
    (ha : 0 ≤ a) (ψ₁ ψ₂ : SuzukiSmoothCompactTest a)
    (q : XiZeroCopy) (p : ℝ × ℝ) :
    ‖suzukiScrewWeilPairingIntegrand ψ₁ ψ₂ q p‖ ≤
      ((Real.exp (a / 2) + 1) ^ (2 : ℕ) *
          (1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ))) *
        (‖deriv ψ₂ p.1‖ * ‖deriv ψ₁ p.2‖) := by
  by_cases h₁ : deriv ψ₁ p.2 = 0
  · simp [suzukiScrewWeilPairingIntegrand, h₁]
  by_cases h₂ : deriv ψ₂ p.1 = 0
  · simp [suzukiScrewWeilPairingIntegrand, h₂]
  have hp₁ : p.1 ∈ Icc (-a) a := ψ₂.deriv_support_subset h₂
  have hp₂ : p.2 ∈ Icc (-a) a := ψ₁.deriv_support_subset h₁
  have hK := norm_xiScrewKernelExponentialTerm_le_of_mem_Icc ha hp₁ hp₂ q
  rw [suzukiScrewWeilPairingIntegrand, norm_mul, norm_mul, norm_conj]
  calc
    ‖xiScrewKernelExponentialTerm p.1 p.2 q‖ * ‖deriv ψ₁ p.2‖ *
        ‖deriv ψ₂ p.1‖ ≤
      ((Real.exp (a / 2) + 1) ^ (2 : ℕ) *
          (1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ))) * ‖deriv ψ₁ p.2‖ *
        ‖deriv ψ₂ p.1‖ := by gcongr
    _ = ((Real.exp (a / 2) + 1) ^ (2 : ℕ) *
          (1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ))) *
        (‖deriv ψ₂ p.1‖ * ‖deriv ψ₁ p.2‖) := by ring

/-- `L¹` mass of the derivative of a compact smooth source test. -/
def suzukiDerivativeL1Mass {a : ℝ} (ψ : SuzukiSmoothCompactTest a) : ℝ :=
  ∫ x : ℝ, ‖deriv ψ x‖

theorem suzukiDerivativeL1Mass_nonneg {a : ℝ}
    (ψ : SuzukiSmoothCompactTest a) : 0 ≤ suzukiDerivativeL1Mass ψ :=
  integral_nonneg fun _ => norm_nonneg _

/-- Separable reciprocal-square majorant on product space. -/
def suzukiScrewWeilPairingMajorant {a : ℝ}
    (ψ₁ ψ₂ : SuzukiSmoothCompactTest a) (q : XiZeroCopy)
    (p : ℝ × ℝ) : ℝ :=
  ((Real.exp (a / 2) + 1) ^ (2 : ℕ) *
      (1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ))) *
    (‖deriv ψ₂ p.1‖ * ‖deriv ψ₁ p.2‖)

theorem continuous_suzukiScrewWeilPairingMajorant {a : ℝ}
    (ψ₁ ψ₂ : SuzukiSmoothCompactTest a) (q : XiZeroCopy) :
    Continuous (suzukiScrewWeilPairingMajorant ψ₁ ψ₂ q) := by
  unfold suzukiScrewWeilPairingMajorant
  exact continuous_const.mul
    (((ψ₂.deriv_smooth.continuous.comp continuous_fst).norm).mul
      ((ψ₁.deriv_smooth.continuous.comp continuous_snd).norm))

theorem support_suzukiScrewWeilPairingMajorant_subset {a : ℝ}
    (ψ₁ ψ₂ : SuzukiSmoothCompactTest a) (q : XiZeroCopy) :
    Function.support (suzukiScrewWeilPairingMajorant ψ₁ ψ₂ q) ⊆
      Icc (-a) a ×ˢ Icc (-a) a := by
  intro p hp
  have h₂ : deriv ψ₂ p.1 ≠ 0 := by
    intro hz
    apply hp
    simp [suzukiScrewWeilPairingMajorant, hz]
  have h₁ : deriv ψ₁ p.2 ≠ 0 := by
    intro hz
    apply hp
    simp [suzukiScrewWeilPairingMajorant, hz]
  exact ⟨ψ₂.deriv_support_subset h₂, ψ₁.deriv_support_subset h₁⟩

theorem integrable_suzukiScrewWeilPairingMajorant {a : ℝ}
    (ψ₁ ψ₂ : SuzukiSmoothCompactTest a) (q : XiZeroCopy) :
    Integrable (suzukiScrewWeilPairingMajorant ψ₁ ψ₂ q)
      (volume.prod volume) := by
  exact (continuous_suzukiScrewWeilPairingMajorant ψ₁ ψ₂ q).integrable_of_hasCompactSupport
      (HasCompactSupport.of_support_subset_isCompact
        (isCompact_Icc.prod isCompact_Icc)
        (support_suzukiScrewWeilPairingMajorant_subset ψ₁ ψ₂ q))

theorem integral_suzukiScrewWeilPairingMajorant {a : ℝ}
    (ψ₁ ψ₂ : SuzukiSmoothCompactTest a) (q : XiZeroCopy) :
    (∫ p : ℝ × ℝ, suzukiScrewWeilPairingMajorant ψ₁ ψ₂ q p
        ∂(volume.prod volume)) =
      ((Real.exp (a / 2) + 1) ^ (2 : ℕ) *
          (1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ))) *
        (suzukiDerivativeL1Mass ψ₂ * suzukiDerivativeL1Mass ψ₁) := by
  change (∫ p : ℝ × ℝ,
      ((Real.exp (a / 2) + 1) ^ (2 : ℕ) * (1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ))) *
        (‖deriv ψ₂ p.1‖ * ‖deriv ψ₁ p.2‖) ∂(volume.prod volume)) = _
  have hprod := integral_prod_mul (μ := (volume : Measure ℝ))
    (ν := (volume : Measure ℝ))
    (fun x : ℝ => ‖deriv ψ₂ x‖) (fun y : ℝ => ‖deriv ψ₁ y‖)
  rw [integral_const_mul, hprod]
  rfl

theorem integral_norm_suzukiScrewWeilPairingIntegrand_le {a : ℝ}
    (ha : 0 ≤ a) (ψ₁ ψ₂ : SuzukiSmoothCompactTest a) (q : XiZeroCopy) :
    (∫ p : ℝ × ℝ, ‖suzukiScrewWeilPairingIntegrand ψ₁ ψ₂ q p‖
        ∂(volume.prod volume)) ≤
      ((Real.exp (a / 2) + 1) ^ (2 : ℕ) *
          (suzukiDerivativeL1Mass ψ₂ * suzukiDerivativeL1Mass ψ₁)) *
        (1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ)) := by
  have hF := (integrable_suzukiScrewWeilPairingIntegrand ψ₁ ψ₂ q).norm
  have hM := integrable_suzukiScrewWeilPairingMajorant ψ₁ ψ₂ q
  calc
    (∫ p : ℝ × ℝ, ‖suzukiScrewWeilPairingIntegrand ψ₁ ψ₂ q p‖
        ∂(volume.prod volume)) ≤
      ∫ p : ℝ × ℝ, suzukiScrewWeilPairingMajorant ψ₁ ψ₂ q p
        ∂(volume.prod volume) :=
      integral_mono hF hM (norm_suzukiScrewWeilPairingIntegrand_le ha ψ₁ ψ₂ q)
    _ = ((Real.exp (a / 2) + 1) ^ (2 : ℕ) *
          (1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ))) *
        (suzukiDerivativeL1Mass ψ₂ * suzukiDerivativeL1Mass ψ₁) :=
      integral_suzukiScrewWeilPairingMajorant ψ₁ ψ₂ q
    _ = ((Real.exp (a / 2) + 1) ^ (2 : ℕ) *
          (suzukiDerivativeL1Mass ψ₂ * suzukiDerivativeL1Mass ψ₁)) *
        (1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ)) := by ring

theorem summable_integral_norm_suzukiScrewWeilPairingIntegrand {a : ℝ}
    (ha : 0 ≤ a) (ψ₁ ψ₂ : SuzukiSmoothCompactTest a) :
    Summable fun q : XiZeroCopy =>
      ∫ p : ℝ × ℝ, ‖suzukiScrewWeilPairingIntegrand ψ₁ ψ₂ q p‖
        ∂(volume.prod volume) := by
  let C : ℝ := (Real.exp (a / 2) + 1) ^ (2 : ℕ) *
    (suzukiDerivativeL1Mass ψ₂ * suzukiDerivativeL1Mass ψ₁)
  apply Summable.of_nonneg_of_le
    (fun q => integral_nonneg fun _ => norm_nonneg _)
    (fun q => integral_norm_suzukiScrewWeilPairingIntegrand_le ha ψ₁ ψ₂ q)
  exact xiSpectralPoint_inv_sq_summable.mul_left C

theorem tsum_suzukiScrewWeilPairingIntegrand {a : ℝ}
    (ψ₁ ψ₂ : SuzukiSmoothCompactTest a) (p : ℝ × ℝ) :
    (∑' q : XiZeroCopy, suzukiScrewWeilPairingIntegrand ψ₁ ψ₂ q p) =
      suzukiDifferentiatedScrewIntegrand ψ₁ ψ₂ p := by
  rw [suzukiDifferentiatedScrewIntegrand,
    suzukiScrewKernel_eq_tsum_exponential]
  unfold suzukiScrewWeilPairingIntegrand
  rw [tsum_mul_right, tsum_mul_right]

/-- Exact equation (3.1) before evaluating the individual divisor atoms. -/
theorem suzukiScrewSmoothForm_derivatives_eq_tsum_integral
    {a : ℝ} (ha : 0 ≤ a) (ψ₁ ψ₂ : SuzukiSmoothCompactTest a) :
    suzukiScrewSmoothForm ψ₁.toDerivativeZeroMean ψ₂.toDerivativeZeroMean =
      ∑' q : XiZeroCopy,
        ∫ p : ℝ × ℝ, suzukiScrewWeilPairingIntegrand ψ₁ ψ₂ q p
          ∂(volume.prod volume) := by
  have htotal := integrable_suzukiDifferentiatedScrewIntegrand ψ₁ ψ₂
  have hterm := integrable_suzukiScrewWeilPairingIntegrand ψ₁ ψ₂
  have hsum := summable_integral_norm_suzukiScrewWeilPairingIntegrand ha ψ₁ ψ₂
  rw [suzukiScrewSmoothForm]
  change (∫ t : ℝ, ∫ u : ℝ, suzukiDifferentiatedScrewIntegrand ψ₁ ψ₂ (t, u)) = _
  have htotal' : Integrable
      (Function.uncurry fun t u : ℝ => suzukiDifferentiatedScrewIntegrand ψ₁ ψ₂ (t, u))
      (volume.prod volume) := by
    have hfun :
        (Function.uncurry fun t u : ℝ =>
          suzukiDifferentiatedScrewIntegrand ψ₁ ψ₂ (t, u)) =
        suzukiDifferentiatedScrewIntegrand ψ₁ ψ₂ := by
      funext p
      rfl
    rw [hfun]
    exact htotal
  calc
    _ = ∫ p : ℝ × ℝ, suzukiDifferentiatedScrewIntegrand ψ₁ ψ₂ p
        ∂(volume.prod volume) := integral_integral htotal'
    _ = ∫ p : ℝ × ℝ,
        (∑' q : XiZeroCopy, suzukiScrewWeilPairingIntegrand ψ₁ ψ₂ q p)
          ∂(volume.prod volume) := by
      apply integral_congr_ae
      filter_upwards with p
      exact (tsum_suzukiScrewWeilPairingIntegrand ψ₁ ψ₂ p).symm
    _ = ∑' q : XiZeroCopy,
        ∫ p : ℝ × ℝ, suzukiScrewWeilPairingIntegrand ψ₁ ψ₂ q p
          ∂(volume.prod volume) :=
      (integral_tsum_of_summable_integral_norm hterm hsum).symm

/-! ## Evaluation of one divisor atom -/

theorem integral_cexp_sub_one_mul_deriv {a : ℝ}
    (ψ : SuzukiSmoothCompactTest a) (z : ℂ) :
    (∫ x : ℝ, (Complex.exp (I * z * (x : ℂ)) - 1) * deriv ψ x) =
      -I * z * suzukiSmoothFourier ψ z := by
  have hosc := ψ.integrable_deriv_fourierIntegrand z
  have hder := ψ.deriv_integrable
  calc
    (∫ x : ℝ, (Complex.exp (I * z * (x : ℂ)) - 1) * deriv ψ x) =
        ∫ x : ℝ, (deriv ψ x * Complex.exp (I * z * (x : ℂ)) - deriv ψ x) := by
      apply integral_congr_ae
      filter_upwards with x
      ring
    _ = (∫ x : ℝ, deriv ψ x * Complex.exp (I * z * (x : ℂ))) -
        ∫ x : ℝ, deriv ψ x := integral_sub hosc hder
    _ = -I * z * suzukiSmoothFourier ψ z := by
      rw [suzukiSmoothFourier_deriv, ψ.integral_deriv_eq_zero, sub_zero]

theorem integral_cexp_sub_one_mul_conj_deriv {a : ℝ}
    (ψ : SuzukiSmoothCompactTest a) (z : ℂ) :
    (∫ x : ℝ, (Complex.exp (I * z * (x : ℂ)) - 1) *
      (starRingEnd ℂ) (deriv ψ x)) =
      -I * z * suzukiSmoothFourier ψ.conjugate z := by
  have h := integral_cexp_sub_one_mul_deriv ψ.conjugate z
  calc
    _ = ∫ x : ℝ, (Complex.exp (I * z * (x : ℂ)) - 1) *
        deriv ψ.conjugate x := by
      apply integral_congr_ae
      filter_upwards with x
      rw [ψ.deriv_conjugate]
    _ = _ := h

/-- Each absolutely integrable divisor atom is exactly the product of the two source Fourier
coordinates appearing in Suzuki's proof. -/
theorem integral_suzukiScrewWeilPairingIntegrand_eq_fourier {a : ℝ}
    (ψ₁ ψ₂ : SuzukiSmoothCompactTest a) (q : XiZeroCopy) :
    (∫ p : ℝ × ℝ, suzukiScrewWeilPairingIntegrand ψ₁ ψ₂ q p
        ∂(volume.prod volume)) =
      suzukiSmoothFourier ψ₁ (-xiSpectralPoint q) *
        suzukiSmoothFourier ψ₂.conjugate (xiSpectralPoint q) := by
  let gamma : ℂ := xiSpectralPoint q
  let A : ℝ → ℂ := fun t =>
    (Complex.exp (I * gamma * (t : ℂ)) - 1) *
      (starRingEnd ℂ) (deriv ψ₂ t)
  let B : ℝ → ℂ := fun u =>
    (Complex.exp (-(I * gamma * (u : ℂ))) - 1) * deriv ψ₁ u
  have hq : gamma ≠ 0 := xiSpectralPoint_ne_zero q
  have hBexp : ∀ u : ℝ,
      Complex.exp (-(I * gamma * (u : ℂ))) =
        Complex.exp (I * (-gamma) * (u : ℂ)) := by
    intro u
    congr 1
    ring
  have hAint : (∫ t : ℝ, A t) =
      -I * gamma * suzukiSmoothFourier ψ₂.conjugate gamma := by
    exact integral_cexp_sub_one_mul_conj_deriv ψ₂ gamma
  have hBint : (∫ u : ℝ, B u) =
      -I * (-gamma) * suzukiSmoothFourier ψ₁ (-gamma) := by
    rw [show B = fun u : ℝ =>
        (Complex.exp (I * (-gamma) * (u : ℂ)) - 1) * deriv ψ₁ u by
      funext u
      dsimp only [B]
      rw [hBexp]]
    exact integral_cexp_sub_one_mul_deriv ψ₁ (-gamma)
  have hpoint : suzukiScrewWeilPairingIntegrand ψ₁ ψ₂ q =
      fun p : ℝ × ℝ => gamma⁻¹ ^ (2 : ℕ) * (A p.1 * B p.2) := by
    funext p
    rw [suzukiScrewWeilPairingIntegrand, xiScrewKernelExponentialTerm]
    dsimp only [gamma, A, B]
    field_simp [hq]
  rw [hpoint, integral_const_mul, integral_prod_mul, hAint, hBint]
  dsimp only [gamma]
  field_simp [xiSpectralPoint_ne_zero q]
  rw [Complex.I_sq]
  ring

/-! ## Literal Weil distribution and Hermitian convolution -/

/-- Entire Fourier integral in Suzuki's convention, for an arbitrary function whenever the
displayed integral exists. -/
def suzukiEntireFourier (f : ℝ → ℂ) (z : ℂ) : ℂ :=
  ∫ x : ℝ, f x * Complex.exp (I * z * (x : ℂ))

theorem suzukiEntireFourier_eq_smooth {a : ℝ}
    (ψ : SuzukiSmoothCompactTest a) (z : ℂ) :
    suzukiEntireFourier ψ z = suzukiSmoothFourier ψ z := rfl

/-- Suzuki's Hermitian reflection `tilde ψ(x)=conj(ψ(-x))`, equation (3.5). -/
def suzukiHermitianReflection {a : ℝ}
    (ψ : SuzukiSmoothCompactTest a) (x : ℝ) : ℂ :=
  (starRingEnd ℂ) (ψ (-x))

theorem continuous_suzukiHermitianReflection {a : ℝ}
    (ψ : SuzukiSmoothCompactTest a) : Continuous (suzukiHermitianReflection ψ) := by
  exact Complex.continuous_conj.comp (ψ.continuous.comp continuous_neg)

theorem support_suzukiHermitianReflection_subset {a : ℝ}
    (ψ : SuzukiSmoothCompactTest a) :
    Function.support (suzukiHermitianReflection ψ) ⊆ Icc (-a) a := by
  intro x hx
  have hneg : ψ (-x) ≠ 0 := by
    intro hz
    exact hx (by simp [suzukiHermitianReflection, hz])
  have hmem := ψ.support_subset hneg
  constructor <;> linarith [hmem.1, hmem.2]

theorem hasCompactSupport_suzukiHermitianReflection {a : ℝ}
    (ψ : SuzukiSmoothCompactTest a) :
    HasCompactSupport (suzukiHermitianReflection ψ) := by
  exact HasCompactSupport.of_support_subset_isCompact isCompact_Icc
    (support_suzukiHermitianReflection_subset ψ)

theorem integrable_suzukiHermitianReflection {a : ℝ}
    (ψ : SuzukiSmoothCompactTest a) : Integrable (suzukiHermitianReflection ψ) :=
  (continuous_suzukiHermitianReflection ψ).integrable_of_hasCompactSupport
    (hasCompactSupport_suzukiHermitianReflection ψ)

/-- Literal Hermitian convolution `(ψ₁ * tilde ψ₂)(x)` from Suzuki (2022), equation (3.5). -/
def suzukiHermitianConvolution {a : ℝ}
    (ψ₁ ψ₂ : SuzukiSmoothCompactTest a) (x : ℝ) : ℂ :=
  ∫ y : ℝ, ψ₁ y * suzukiHermitianReflection ψ₂ (x - y)

theorem suzukiHermitianConvolution_eq_convolution {a : ℝ}
    (ψ₁ ψ₂ : SuzukiSmoothCompactTest a) :
    suzukiHermitianConvolution ψ₁ ψ₂ =
      MeasureTheory.convolution ψ₁ (suzukiHermitianReflection ψ₂)
        (ContinuousLinearMap.mul ℂ ℂ) volume := by
  funext x
  rw [suzukiHermitianConvolution, MeasureTheory.convolution_def]
  rfl

theorem continuous_suzukiHermitianConvolution {a : ℝ}
    (ψ₁ ψ₂ : SuzukiSmoothCompactTest a) :
    Continuous (suzukiHermitianConvolution ψ₁ ψ₂) := by
  rw [suzukiHermitianConvolution_eq_convolution]
  exact (hasCompactSupport_suzukiHermitianReflection ψ₂).continuous_convolution_right
    (ContinuousLinearMap.mul ℂ ℂ) ψ₁.integrable.locallyIntegrable
      (continuous_suzukiHermitianReflection ψ₂)

theorem hasCompactSupport_suzukiHermitianConvolution {a : ℝ}
    (ψ₁ ψ₂ : SuzukiSmoothCompactTest a) :
    HasCompactSupport (suzukiHermitianConvolution ψ₁ ψ₂) := by
  rw [suzukiHermitianConvolution_eq_convolution]
  exact HasCompactSupport.convolution (ContinuousLinearMap.mul ℂ ℂ)
    ψ₁.hasCompactSupport (hasCompactSupport_suzukiHermitianReflection ψ₂)

theorem integrable_suzukiHermitianConvolution_fourier {a : ℝ}
    (ψ₁ ψ₂ : SuzukiSmoothCompactTest a) (z : ℂ) :
    Integrable fun x : ℝ => suzukiHermitianConvolution ψ₁ ψ₂ x *
      Complex.exp (I * z * (x : ℂ)) := by
  exact ((continuous_suzukiHermitianConvolution ψ₁ ψ₂).mul
    (Complex.continuous_exp.comp
      (continuous_const.mul continuous_ofReal))).integrable_of_hasCompactSupport
        (hasCompactSupport_suzukiHermitianConvolution ψ₁ ψ₂).mul_right

/-- Product-space integrand used to prove the complex-frequency convolution theorem. -/
def suzukiConvolutionFourierIntegrand {a : ℝ}
    (ψ₁ ψ₂ : SuzukiSmoothCompactTest a) (z : ℂ) (p : ℝ × ℝ) : ℂ :=
  ψ₁ p.2 * suzukiHermitianReflection ψ₂ (p.1 - p.2) *
    Complex.exp (I * z * (p.1 : ℂ))

theorem continuous_suzukiConvolutionFourierIntegrand {a : ℝ}
    (ψ₁ ψ₂ : SuzukiSmoothCompactTest a) (z : ℂ) :
    Continuous (suzukiConvolutionFourierIntegrand ψ₁ ψ₂ z) := by
  unfold suzukiConvolutionFourierIntegrand
  exact ((ψ₁.continuous.comp continuous_snd).mul
    ((continuous_suzukiHermitianReflection ψ₂).comp
      (continuous_fst.sub continuous_snd))).mul
        (Complex.continuous_exp.comp
          (continuous_const.mul (continuous_ofReal.comp continuous_fst)))

theorem support_suzukiConvolutionFourierIntegrand_subset {a : ℝ}
    (ha : 0 ≤ a) (ψ₁ ψ₂ : SuzukiSmoothCompactTest a) (z : ℂ) :
    Function.support (suzukiConvolutionFourierIntegrand ψ₁ ψ₂ z) ⊆
      Icc (-(2 * a)) (2 * a) ×ˢ Icc (-a) a := by
  intro p hp
  have hy : ψ₁ p.2 ≠ 0 := by
    intro hz
    exact hp (by simp [suzukiConvolutionFourierIntegrand, hz])
  have hd : suzukiHermitianReflection ψ₂ (p.1 - p.2) ≠ 0 := by
    intro hz
    exact hp (by simp [suzukiConvolutionFourierIntegrand, hz])
  have hyp := ψ₁.support_subset hy
  have hdp := support_suzukiHermitianReflection_subset ψ₂ hd
  constructor
  · constructor <;> linarith [hyp.1, hyp.2, hdp.1, hdp.2]
  · exact hyp

theorem integrable_suzukiConvolutionFourierIntegrand {a : ℝ}
    (ha : 0 ≤ a) (ψ₁ ψ₂ : SuzukiSmoothCompactTest a) (z : ℂ) :
    Integrable (suzukiConvolutionFourierIntegrand ψ₁ ψ₂ z)
      (volume.prod volume) := by
  exact (continuous_suzukiConvolutionFourierIntegrand ψ₁ ψ₂ z).integrable_of_hasCompactSupport
      (HasCompactSupport.of_support_subset_isCompact
        (isCompact_Icc.prod isCompact_Icc)
        (support_suzukiConvolutionFourierIntegrand_subset ha ψ₁ ψ₂ z))

theorem suzukiEntireFourier_hermitianReflection {a : ℝ}
    (ψ : SuzukiSmoothCompactTest a) (z : ℂ) :
    suzukiEntireFourier (suzukiHermitianReflection ψ) z =
      suzukiSmoothFourier ψ.conjugate (-z) := by
  let F : ℝ → ℂ := fun x => ψ.conjugate x *
    Complex.exp (I * (-z) * (x : ℂ))
  have hneg := integral_neg_eq_self F (μ := (volume : Measure ℝ))
  rw [suzukiEntireFourier, suzukiSmoothFourier]
  calc
    (∫ x : ℝ, suzukiHermitianReflection ψ x *
        Complex.exp (I * z * (x : ℂ))) = ∫ x : ℝ, F (-x) := by
      apply integral_congr_ae
      filter_upwards with x
      dsimp only [F, suzukiHermitianReflection]
      congr 1
      push_cast
      ring
    _ = ∫ x : ℝ, F x := hneg
    _ = _ := rfl

/-- Complex-frequency convolution theorem for Suzuki's compact smooth tests. -/
theorem suzukiEntireFourier_hermitianConvolution {a : ℝ}
    (ha : 0 ≤ a) (ψ₁ ψ₂ : SuzukiSmoothCompactTest a) (z : ℂ) :
    suzukiEntireFourier (suzukiHermitianConvolution ψ₁ ψ₂) z =
      suzukiSmoothFourier ψ₁ z * suzukiSmoothFourier ψ₂.conjugate (-z) := by
  have hH := integrable_suzukiConvolutionFourierIntegrand ha ψ₁ ψ₂ z
  rw [suzukiEntireFourier]
  calc
    (∫ x : ℝ, suzukiHermitianConvolution ψ₁ ψ₂ x *
        Complex.exp (I * z * (x : ℂ))) =
      ∫ x : ℝ, ∫ y : ℝ, suzukiConvolutionFourierIntegrand ψ₁ ψ₂ z (x, y) := by
        apply integral_congr_ae
        filter_upwards with x
        rw [suzukiHermitianConvolution]
        rw [← integral_mul_const]
        apply integral_congr_ae
        filter_upwards with y
        rfl
    _ = ∫ y : ℝ, ∫ x : ℝ,
        suzukiConvolutionFourierIntegrand ψ₁ ψ₂ z (x, y) :=
      integral_integral_swap hH
    _ = ∫ y : ℝ, (ψ₁ y * Complex.exp (I * z * (y : ℂ))) *
        suzukiEntireFourier (suzukiHermitianReflection ψ₂) z := by
      apply integral_congr_ae
      filter_upwards with y
      have htrans := integral_sub_right_eq_self (μ := (volume : Measure ℝ))
        (fun r : ℝ => ψ₁ y * suzukiHermitianReflection ψ₂ r *
          Complex.exp (I * z * ((r + y : ℝ) : ℂ))) y
      calc
        (∫ x : ℝ, suzukiConvolutionFourierIntegrand ψ₁ ψ₂ z (x, y)) =
            ∫ x : ℝ, (ψ₁ y * suzukiHermitianReflection ψ₂ (x - y) *
              Complex.exp (I * z * (((x - y) + y : ℝ) : ℂ))) := by
          apply integral_congr_ae
          filter_upwards with x
          rw [suzukiConvolutionFourierIntegrand, sub_add_cancel]
        _ = ∫ r : ℝ, ψ₁ y * suzukiHermitianReflection ψ₂ r *
              Complex.exp (I * z * ((r + y : ℝ) : ℂ)) := htrans
        _ = ∫ r : ℝ, (ψ₁ y * Complex.exp (I * z * (y : ℂ))) *
              (suzukiHermitianReflection ψ₂ r *
                Complex.exp (I * z * (r : ℂ))) := by
          apply integral_congr_ae
          filter_upwards with r
          rw [show Complex.exp (I * z * ((r + y : ℝ) : ℂ)) =
              Complex.exp (I * z * (r : ℂ)) *
                Complex.exp (I * z * (y : ℂ)) by
            rw [← Complex.exp_add]
            congr 1
            push_cast
            ring]
          ring
        _ = (ψ₁ y * Complex.exp (I * z * (y : ℂ))) *
            suzukiEntireFourier (suzukiHermitianReflection ψ₂) z := by
          rw [suzukiEntireFourier, integral_const_mul]
    _ = suzukiSmoothFourier ψ₁ z *
        suzukiEntireFourier (suzukiHermitianReflection ψ₂) z := by
      rw [suzukiSmoothFourier, integral_mul_const]
    _ = suzukiSmoothFourier ψ₁ z *
        suzukiSmoothFourier ψ₂.conjugate (-z) := by
      rw [suzukiEntireFourier_hermitianReflection]

/-- Literal Weil distribution `W(f)=Σ_γ hat f(γ)` in the source orientation.  Since the corpus
indexes zeros of `XiC(z)=xi(1/2+iz)`, source zeros of `xi(1/2-iz)` are `-xiSpectralPoint q`. -/
def suzukiWeilDistribution (f : ℝ → ℂ) : ℂ :=
  ∑' q : XiZeroCopy, suzukiEntireFourier f (-xiSpectralPoint q)

theorem summable_suzukiWeilDistribution_hermitianConvolution {a : ℝ}
    (ha : 0 ≤ a) (ψ₁ ψ₂ : SuzukiSmoothCompactTest a) :
    Summable fun q : XiZeroCopy =>
      suzukiEntireFourier (suzukiHermitianConvolution ψ₁ ψ₂)
        (-xiSpectralPoint q) := by
  have hsumInt := summable_integral_norm_suzukiScrewWeilPairingIntegrand ha ψ₁ ψ₂
  have hsumTerm : Summable fun q : XiZeroCopy =>
      ∫ p : ℝ × ℝ, suzukiScrewWeilPairingIntegrand ψ₁ ψ₂ q p
        ∂(volume.prod volume) := by
    apply Summable.of_norm_bounded hsumInt
    intro q
    exact norm_integral_le_integral_norm _
  apply hsumTerm.congr
  intro q
  rw [integral_suzukiScrewWeilPairingIntegrand_eq_fourier,
    suzukiEntireFourier_hermitianConvolution ha]
  ring

theorem suzukiWeilDistribution_hermitianConvolution {a : ℝ}
    (ha : 0 ≤ a) (ψ₁ ψ₂ : SuzukiSmoothCompactTest a) :
    suzukiWeilDistribution (suzukiHermitianConvolution ψ₁ ψ₂) =
      ∑' q : XiZeroCopy,
        suzukiSmoothFourier ψ₁ (-xiSpectralPoint q) *
          suzukiSmoothFourier ψ₂.conjugate (xiSpectralPoint q) := by
  rw [suzukiWeilDistribution]
  apply tsum_congr
  intro q
  rw [suzukiEntireFourier_hermitianConvolution ha]
  ring

/-- **Suzuki (2022), Proposition 3.1.**  For every positive aperture and every two literal tests
in `C(a)`, the paper's differentiated screw form equals the Weil distribution of their Hermitian
convolution.  The theorem is unconditional: no RH premise, zero-location premise, or added axiom. -/
theorem suzuki_proposition_three_one {a : ℝ} (ha : 0 < a)
    (ψ₁ ψ₂ : SuzukiSmoothCompactTest a) :
    suzukiScrewSmoothForm ψ₁.toDerivativeZeroMean ψ₂.toDerivativeZeroMean =
      suzukiWeilDistribution (suzukiHermitianConvolution ψ₁ ψ₂) := by
  rw [suzukiScrewSmoothForm_derivatives_eq_tsum_integral ha.le,
    suzukiWeilDistribution_hermitianConvolution ha.le]
  apply tsum_congr
  intro q
  exact integral_suzukiScrewWeilPairingIntegrand_eq_fourier ψ₁ ψ₂ q

end RHTower
