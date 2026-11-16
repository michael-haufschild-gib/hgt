import GaloisForLFunctions.ExclusionOfTheCriticalState.TheContinuationIsPolynomiallyBoundedOffTheZeros
import GaloisForLFunctions.RHTower.CCM.CCMUnitRieszVolterraLaplace
import GaloisForLFunctions.HTGeometry.BlockWindowFubini
import GaloisForLFunctions.HTGeometry.DecayingStripVerticalShift
import GaloisForLFunctions.HTGeometry.HalfLineLaplaceFourier
import GaloisForLFunctions.RHTower.EigenPairFrequencyInversion
import GaloisForLFunctions.RHTower.LevinsonDetectorRightCount
import GaloisForLFunctions.MetaplecticMobiusDescent.Detector.SubSevenEighthsZeroFreeHalfPlane

/-!
# The averaged state decays at the rate of the zeros

Let `F` be the critical state and `Ā(t) = ∫_0^t k(t - h) F(-h) dh` its causal average with the
positive kernel `k(τ) = e^{-9τ}(1 - e^{-τ})³/6`. If every centred zero has `Re z ≤ κ`, then for every
`κ' > κ`

  `|Ā(t)| ≤ C e^{-(8 - κ') t}`,   `t > 0`.

With the zero-free half-plane `Re s > 20999/24000` this gives every rate below `183001/24000`, beyond
the rate `15/2` of the barrier comparison: the convergent half of the decay law, in averaged form.

Mechanism. On `Re z > 0` the Laplace transform of `Ā` is `L F(z)/((z+9)(z+10)(z+11)(z+12))` (Fubini
on the causal wedge). By the zero side the continuation of `L F` is holomorphic and `O(|z|²)` on
`Re z ≥ κ' - 8`, so the product is `O(1/(1 + (Im z)²))` on the strip. Fourier inversion on a line
`Re z = c > 0` and the shift of that line to `Re z = κ' - 8` give the bound.
-/

noncomputable section
open MeasureTheory Set Filter Zeta23 Complex Metric Topology
open scoped FourierTransform

namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri
  CriticalArithmeticCorrelationTheory HTGeometry _root_.RHTower

/-! ### The Laplace transform of a causal exponential average -/

/-- The causal integrand is dominated by `e^{-Re z · t} |φ(h)|`. -/
theorem norm_expVolterraIntegrand_le_abs {b : ℝ} (hb : 0 ≤ b) (z : ℂ) (φ : ℝ → ℝ) (t h : ℝ) :
    ‖GaloisForLFunctions.RHTower.expVolterraIntegrand b z φ t h‖ ≤
      Real.exp (-(z.re * t)) * |φ h| := by
  by_cases hle : h ≤ t
  · have h1 : (-(z * (t : ℂ))).re = -(z.re * t) := by simp [Complex.mul_re]
    have h2 : (-((b : ℂ) * ((t : ℂ) - (h : ℂ)))).re = -(b * (t - h)) := by
      simp [Complex.mul_re]
    rw [GaloisForLFunctions.RHTower.expVolterraIntegrand, if_pos hle, norm_mul, norm_mul,
      Complex.norm_exp, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs, h1, h2]
    have hb1 : Real.exp (-(b * (t - h))) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have := mul_nonneg hb (sub_nonneg.mpr hle)
      linarith
    calc Real.exp (-(z.re * t)) * Real.exp (-(b * (t - h))) * |φ h|
        ≤ Real.exp (-(z.re * t)) * 1 * |φ h| :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hb1 (Real.exp_pos _).le) (abs_nonneg _)
      _ = Real.exp (-(z.re * t)) * |φ h| := by rw [mul_one]
  · rw [GaloisForLFunctions.RHTower.expVolterraIntegrand, if_neg hle, norm_zero]
    exact mul_nonneg (Real.exp_pos _).le (abs_nonneg _)

/-- The causal average of an integrable source with the kernel `e^{-bτ}` has Laplace transform
`(z + b)⁻¹` times that of the source: Fubini on the wedge `h ≤ t`. -/
theorem integral_Ioi_expVolterra_laplace_of_integrable {b : ℝ} (hb : 0 ≤ b) {z : ℂ}
    (hz : 0 < z.re) {φ : ℝ → ℝ} (hφ : Measurable φ) (hint : IntegrableOn φ (Ioi (0 : ℝ))) :
    (∫ t in Ioi (0 : ℝ), Complex.exp (-(z * (t : ℂ))) *
        ((∫ h in Ioc (0 : ℝ) t, Real.exp (-(b * (t - h))) * φ h : ℝ) : ℂ)) =
      (z + (b : ℂ))⁻¹ * ∫ h in Ioi (0 : ℝ), Complex.exp (-(z * (h : ℂ))) * (φ h : ℂ) := by
  have hw₁ : IntegrableOn (fun t : ℝ => Real.exp (-(z.re * t))) (Ioi (0 : ℝ)) volume :=
    GaloisForLFunctions.RHTower.integrableOn_Ioi_rexp_neg_mul hz 0
  have hw₂ : IntegrableOn (fun h : ℝ => |φ h|) (Ioi (0 : ℝ)) volume := hint.abs
  have hmeas : AEStronglyMeasurable
      (Function.uncurry (GaloisForLFunctions.RHTower.expVolterraIntegrand b z φ))
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) :=
    (GaloisForLFunctions.RHTower.measurable_uncurry_expVolterraIntegrand b z
      hφ).aestronglyMeasurable
  have hbound : ∀ᵐ p ∂((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))),
      ‖Function.uncurry (GaloisForLFunctions.RHTower.expVolterraIntegrand b z φ) p‖ ≤
        Real.exp (-(z.re * p.1)) * |φ p.2| :=
    Eventually.of_forall fun p => norm_expVolterraIntegrand_le_abs hb z φ p.1 p.2
  have hswap := GaloisForLFunctions.HTGeometry.integral_swap_of_dominated_prod
    hw₁ hw₂ hmeas hbound
  have hL : (∫ t in Ioi (0 : ℝ), ∫ h in Ioi (0 : ℝ),
        GaloisForLFunctions.RHTower.expVolterraIntegrand b z φ t h) =
      ∫ t in Ioi (0 : ℝ), Complex.exp (-(z * (t : ℂ))) *
        ((∫ h in Ioc (0 : ℝ) t, Real.exp (-(b * (t - h))) * φ h : ℝ) : ℂ) :=
    setIntegral_congr_fun measurableSet_Ioi
      (fun t ht => GaloisForLFunctions.RHTower.integral_expVolterraIntegrand_snd hφ ht)
  have hR : (∫ h in Ioi (0 : ℝ), ∫ t in Ioi (0 : ℝ),
        GaloisForLFunctions.RHTower.expVolterraIntegrand b z φ t h) =
      ∫ h in Ioi (0 : ℝ), (z + (b : ℂ))⁻¹ *
        (Complex.exp (-(z * (h : ℂ))) * (φ h : ℂ)) :=
    setIntegral_congr_fun measurableSet_Ioi
      (fun h hh => GaloisForLFunctions.RHTower.integral_expVolterraIntegrand_fst hb hz hh)
  rw [← hL, hswap, hR, MeasureTheory.integral_const_mul]

/-! ### Averages of the reflected profile -/

/-- The causal average of the reflected profile with the kernel `e^{-bτ}`:
`∫_0^t e^{-b(t-h)} F(-h) dh`. -/
def expAverage (b : ℝ) (F : ℝ → ℝ) (t : ℝ) : ℝ :=
  Real.exp (-(b * t)) * ∫ h in (0 : ℝ)..t, Real.exp (b * h) * F (-h)

theorem intervalIntegrable_exp_mul_reflect {F : ℝ → ℝ} (hF : Integrable F) (b a c : ℝ) :
    IntervalIntegrable (fun h : ℝ => Real.exp (b * h) * F (-h)) volume a c :=
  (hF.comp_neg.intervalIntegrable).continuousOn_mul
    (by fun_prop : Continuous fun h : ℝ => Real.exp (b * h)).continuousOn

theorem continuous_expAverage {F : ℝ → ℝ} (hF : Integrable F) (b : ℝ) :
    Continuous (expAverage b F) := by
  have h1 : Continuous fun t : ℝ => Real.exp (-(b * t)) := by fun_prop
  have h2 : Continuous fun t : ℝ => ∫ h in (0 : ℝ)..t, Real.exp (b * h) * F (-h) :=
    intervalIntegral.continuous_primitive (intervalIntegrable_exp_mul_reflect hF b) 0
  exact h1.mul h2

theorem expAverage_zero (b : ℝ) (F : ℝ → ℝ) : expAverage b F 0 = 0 := by
  unfold expAverage
  rw [intervalIntegral.integral_same, mul_zero]

theorem expAverage_eq_setIntegral (b : ℝ) (F : ℝ → ℝ) {t : ℝ} (ht : 0 < t) :
    expAverage b F t = ∫ h in Ioc (0 : ℝ) t, Real.exp (-(b * (t - h))) * F (-h) := by
  unfold expAverage
  rw [intervalIntegral.integral_of_le ht.le, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioc fun h _ => ?_
  show Real.exp (-(b * t)) * (Real.exp (b * h) * F (-h)) = Real.exp (-(b * (t - h))) * F (-h)
  have e : -(b * t) + b * h = -(b * (t - h)) := by ring
  rw [← mul_assoc, ← Real.exp_add, e]

theorem abs_expAverage_le {b : ℝ} (hb : 0 ≤ b) {F : ℝ → ℝ} (hF : Integrable F) {t : ℝ}
    (ht : 0 < t) : |expAverage b F t| ≤ ∫ h, |F (-h)| := by
  rw [expAverage_eq_setIntegral b F ht]
  have hg : Integrable (fun h : ℝ => |F (-h)|) (volume.restrict (Ioc (0 : ℝ) t)) :=
    hF.comp_neg.abs.restrict
  refine (Real.norm_eq_abs _).ge.trans ((norm_integral_le_of_norm_le hg ?_).trans
    (setIntegral_le_integral hF.comp_neg.abs (Eventually.of_forall fun h => abs_nonneg _)))
  refine (ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun h hh => ?_)
  show ‖Real.exp (-(b * (t - h))) * F (-h)‖ ≤ |F (-h)|
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  have he : Real.exp (-(b * (t - h))) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have := mul_nonneg hb (sub_nonneg.mpr hh.2)
    linarith
  exact mul_le_of_le_one_left (abs_nonneg _) he

/-- The reflected profile averaged with the positive kernel `e^{-9τ}(1 - e^{-τ})³/6`, written as
the partial fraction of its symbol. -/
def averagedState (F : ℝ → ℝ) (t : ℝ) : ℝ :=
  1 / 6 * expAverage 9 F t - 1 / 2 * expAverage 10 F t + 1 / 2 * expAverage 11 F t -
    1 / 6 * expAverage 12 F t

theorem continuous_averagedState {F : ℝ → ℝ} (hF : Integrable F) :
    Continuous (averagedState F) :=
  (((continuous_const.mul (continuous_expAverage hF 9)).sub
    (continuous_const.mul (continuous_expAverage hF 10))).add
    (continuous_const.mul (continuous_expAverage hF 11))).sub
    (continuous_const.mul (continuous_expAverage hF 12))

theorem averagedState_zero (F : ℝ → ℝ) : averagedState F 0 = 0 := by
  unfold averagedState
  rw [expAverage_zero, expAverage_zero, expAverage_zero, expAverage_zero]
  ring

theorem abs_averagedState_le {F : ℝ → ℝ} (hF : Integrable F) {t : ℝ} (ht : 0 < t) :
    |averagedState F t| ≤ 2 * ∫ h, |F (-h)| := by
  obtain ⟨l9, u9⟩ := abs_le.mp (abs_expAverage_le (by norm_num : (0 : ℝ) ≤ 9) hF ht)
  obtain ⟨l10, u10⟩ := abs_le.mp (abs_expAverage_le (by norm_num : (0 : ℝ) ≤ 10) hF ht)
  obtain ⟨l11, u11⟩ := abs_le.mp (abs_expAverage_le (by norm_num : (0 : ℝ) ≤ 11) hF ht)
  obtain ⟨l12, u12⟩ := abs_le.mp (abs_expAverage_le (by norm_num : (0 : ℝ) ≤ 12) hF ht)
  unfold averagedState
  rw [abs_le]
  constructor <;> linarith

/-- The reflected profile is the Laplace datum of the transform:
`∫_0^∞ e^{-zh} F(-h) dh = L F(z)`. -/
theorem integral_Ioi_reflect_eq_laplace {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F)
    (z : ℂ) :
    ∫ h in Ioi (0 : ℝ), Complex.exp (-(z * (h : ℂ))) * ((F (-h) : ℝ) : ℂ) =
      negativeHalfLineLaplace (cx F) z := by
  have h1 := integral_comp_neg_Ioi (0 : ℝ) (fun u : ℝ => Complex.exp (z * (u : ℂ)) * cx F u)
  rw [neg_zero] at h1
  have h2 : ∫ u in Iic (0 : ℝ), Complex.exp (z * (u : ℂ)) * cx F u =
      ∫ u, Complex.exp (z * (u : ℂ)) * cx F u :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun u hu => by
      have hu' : 0 ≤ u := (not_le.mp hu).le
      show Complex.exp (z * (u : ℂ)) * ((F u : ℝ) : ℂ) = 0
      rw [hF.support u hu', Complex.ofReal_zero, mul_zero]
  unfold negativeHalfLineLaplace
  rw [← h2, ← h1]
  refine setIntegral_congr_fun measurableSet_Ioi fun h _ => ?_
  show Complex.exp (-(z * (h : ℂ))) * ((F (-h) : ℝ) : ℂ) =
    Complex.exp (z * ((-h : ℝ) : ℂ)) * ((F (-h) : ℝ) : ℂ)
  rw [Complex.ofReal_neg, mul_neg]

theorem integrableOn_cexp_mul_expAverage {b : ℝ} (hb : 0 ≤ b) {F : ℝ → ℝ} (hF : Integrable F)
    {z : ℂ} (hz : 0 < z.re) :
    IntegrableOn (fun t : ℝ => Complex.exp (-(z * (t : ℂ))) * ((expAverage b F t : ℝ) : ℂ))
      (Ioi (0 : ℝ)) := by
  have hmaj : IntegrableOn (fun t : ℝ => Real.exp (-(z.re * t)) * ∫ h, |F (-h)|)
      (Ioi (0 : ℝ)) :=
    (GaloisForLFunctions.RHTower.integrableOn_Ioi_rexp_neg_mul hz 0).mul_const _
  refine Integrable.mono' hmaj ?_ ?_
  · exact ((by fun_prop : Continuous fun t : ℝ => Complex.exp (-(z * (t : ℂ)))).mul
      (Complex.continuous_ofReal.comp (continuous_expAverage hF b))).aestronglyMeasurable
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
    show ‖Complex.exp (-(z * (t : ℂ))) * ((expAverage b F t : ℝ) : ℂ)‖ ≤
      Real.exp (-(z.re * t)) * ∫ h, |F (-h)|
    have hre : (-(z * (t : ℂ))).re = -(z.re * t) := by simp [Complex.mul_re]
    rw [norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs, hre]
    exact mul_le_mul_of_nonneg_left (abs_expAverage_le hb hF ht) (Real.exp_pos _).le

theorem integral_expAverage_laplace {b : ℝ} (hb : 0 ≤ b) {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) {z : ℂ} (hz : 0 < z.re) :
    ∫ t in Ioi (0 : ℝ), Complex.exp (-(z * (t : ℂ))) * ((expAverage b F t : ℝ) : ℂ) =
      (z + (b : ℂ))⁻¹ * negativeHalfLineLaplace (cx F) z := by
  have hφ : Measurable fun h : ℝ => F (-h) := hF.meas.comp measurable_neg
  have hint : IntegrableOn (fun h : ℝ => F (-h)) (Ioi (0 : ℝ)) :=
    hF.integrable.comp_neg.integrableOn
  have h : (∫ t in Ioi (0 : ℝ), Complex.exp (-(z * (t : ℂ))) *
        ((∫ h in Ioc (0 : ℝ) t, Real.exp (-(b * (t - h))) * F (-h) : ℝ) : ℂ)) =
      (z + (b : ℂ))⁻¹ * ∫ h in Ioi (0 : ℝ), Complex.exp (-(z * (h : ℂ))) * ((F (-h) : ℝ) : ℂ) :=
    integral_Ioi_expVolterra_laplace_of_integrable hb hz hφ hint
  rw [integral_Ioi_reflect_eq_laplace hF z] at h
  rw [← h]
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  show Complex.exp (-(z * (t : ℂ))) * ((expAverage b F t : ℝ) : ℂ) =
    Complex.exp (-(z * (t : ℂ))) *
      ((∫ h in Ioc (0 : ℝ) t, Real.exp (-(b * (t - h))) * F (-h) : ℝ) : ℂ)
  rw [expAverage_eq_setIntegral b F ht]

/-! ### The symbol of the average -/

/-- The symbol of the average: `1/((z+9)(z+10)(z+11)(z+12))`. -/
def averageSymbol (z : ℂ) : ℂ := ((z + 9) * (z + 10) * (z + 11) * (z + 12))⁻¹

private theorem one_add_sq_im_le_sq_norm_add {z : ℂ} {n : ℝ} (h : 1 ≤ z.re + n) :
    1 + z.im ^ 2 ≤ ‖z + (n : ℂ)‖ ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.ofReal_re,
    Complex.ofReal_im, add_zero, pow_two]
  have h1 : (1 : ℝ) * 1 ≤ (z.re + n) * (z.re + n) := mul_self_le_mul_self zero_le_one h
  linarith

private theorem add_ofReal_ne_zero {z : ℂ} {n : ℝ} (h : 0 < z.re + n) : z + (n : ℂ) ≠ 0 :=
  fun h0 => by
    have h1 := congrArg Complex.re h0
    rw [Complex.add_re, Complex.ofReal_re, Complex.zero_re] at h1
    linarith

private theorem le_mul_of_le_sq {q a b : ℝ} (hq : 0 ≤ q) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h1 : q ≤ a ^ 2) (h2 : q ≤ b ^ 2) : q ≤ a * b := by
  have h : q ^ 2 ≤ (a * b) ^ 2 := by
    rw [mul_pow, pow_two q]
    exact mul_le_mul h1 h2 hq (sq_nonneg a)
  exact (sq_le_sq₀ hq (mul_nonneg ha hb)).mp h

/-- On `Re z ≥ -8` the symbol is at most `1/(1 + (Im z)²)²`. -/
theorem norm_averageSymbol_le {z : ℂ} (hz : -8 ≤ z.re) :
    ‖averageSymbol z‖ ≤ ((1 + z.im ^ 2) ^ 2)⁻¹ := by
  have hq0 : (0 : ℝ) ≤ 1 + z.im ^ 2 := by positivity
  have h9 : 1 + z.im ^ 2 ≤ ‖z + 9‖ ^ 2 := by
    have h := one_add_sq_im_le_sq_norm_add (z := z) (n := 9) (by linarith)
    rwa [Complex.ofReal_ofNat] at h
  have h10 : 1 + z.im ^ 2 ≤ ‖z + 10‖ ^ 2 := by
    have h := one_add_sq_im_le_sq_norm_add (z := z) (n := 10) (by linarith)
    rwa [Complex.ofReal_ofNat] at h
  have h11 : 1 + z.im ^ 2 ≤ ‖z + 11‖ ^ 2 := by
    have h := one_add_sq_im_le_sq_norm_add (z := z) (n := 11) (by linarith)
    rwa [Complex.ofReal_ofNat] at h
  have h12 : 1 + z.im ^ 2 ≤ ‖z + 12‖ ^ 2 := by
    have h := one_add_sq_im_le_sq_norm_add (z := z) (n := 12) (by linarith)
    rwa [Complex.ofReal_ofNat] at h
  have ha := le_mul_of_le_sq hq0 (norm_nonneg _) (norm_nonneg _) h9 h10
  have hb := le_mul_of_le_sq hq0 (norm_nonneg _) (norm_nonneg _) h11 h12
  have hprod : (1 + z.im ^ 2) ^ 2 ≤ ‖z + 9‖ * ‖z + 10‖ * ‖z + 11‖ * ‖z + 12‖ := by
    have := mul_le_mul ha hb hq0 (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    calc (1 + z.im ^ 2) ^ 2 = (1 + z.im ^ 2) * (1 + z.im ^ 2) := pow_two _
      _ ≤ ‖z + 9‖ * ‖z + 10‖ * (‖z + 11‖ * ‖z + 12‖) := this
      _ = ‖z + 9‖ * ‖z + 10‖ * ‖z + 11‖ * ‖z + 12‖ := by ring
  unfold averageSymbol
  rw [norm_inv, norm_mul, norm_mul, norm_mul]
  exact inv_anti₀ (by positivity) hprod

theorem averageSymbol_factors_ne_zero {s : ℂ} (hs : -8 ≤ s.re) :
    s + 9 ≠ 0 ∧ s + 10 ≠ 0 ∧ s + 11 ≠ 0 ∧ s + 12 ≠ 0 := by
  have h9 := add_ofReal_ne_zero (z := s) (n := 9) (by linarith)
  have h10 := add_ofReal_ne_zero (z := s) (n := 10) (by linarith)
  have h11 := add_ofReal_ne_zero (z := s) (n := 11) (by linarith)
  have h12 := add_ofReal_ne_zero (z := s) (n := 12) (by linarith)
  rw [Complex.ofReal_ofNat] at h9 h10 h11 h12
  exact ⟨h9, h10, h11, h12⟩

theorem differentiableAt_averageSymbol {s : ℂ} (hs : -8 ≤ s.re) :
    DifferentiableAt ℂ averageSymbol s := by
  obtain ⟨h9, h10, h11, h12⟩ := averageSymbol_factors_ne_zero hs
  have hd : ∀ n : ℂ, DifferentiableAt ℂ (fun z : ℂ => z + n) s := fun n =>
    differentiableAt_id.add_const n
  show DifferentiableAt ℂ (fun z : ℂ => ((z + 9) * (z + 10) * (z + 11) * (z + 12))⁻¹) s
  exact ((((hd 9).mul (hd 10)).mul (hd 11)).mul (hd 12)).inv
    (mul_ne_zero (mul_ne_zero (mul_ne_zero h9 h10) h11) h12)

/-- The partial fraction of the symbol: the kernel `e^{-9τ}(1 - e^{-τ})³/6` expanded. -/
theorem averageSymbol_partialFraction {z : ℂ} (hz : -8 ≤ z.re) :
    averageSymbol z =
      1 / 6 * (z + 9)⁻¹ - 1 / 2 * (z + 10)⁻¹ + 1 / 2 * (z + 11)⁻¹ - 1 / 6 * (z + 12)⁻¹ := by
  obtain ⟨h9, h10, h11, h12⟩ := averageSymbol_factors_ne_zero hz
  unfold averageSymbol
  first
    | (field_simp; ring)
    | field_simp

private theorem integral_four_term {μ : Measure ℝ} {f₁ f₂ f₃ f₄ : ℝ → ℂ} (a₁ a₂ a₃ a₄ : ℂ)
    (h₁ : Integrable f₁ μ) (h₂ : Integrable f₂ μ) (h₃ : Integrable f₃ μ)
    (h₄ : Integrable f₄ μ) :
    ∫ t, (a₁ * f₁ t - a₂ * f₂ t + a₃ * f₃ t - a₄ * f₄ t) ∂μ =
      a₁ * ∫ t, f₁ t ∂μ - a₂ * ∫ t, f₂ t ∂μ + a₃ * ∫ t, f₃ t ∂μ - a₄ * ∫ t, f₄ t ∂μ := by
  have j₁ : Integrable (fun t => a₁ * f₁ t) μ := h₁.const_mul a₁
  have j₂ : Integrable (fun t => a₂ * f₂ t) μ := h₂.const_mul a₂
  have j₃ : Integrable (fun t => a₃ * f₃ t) μ := h₃.const_mul a₃
  have j₄ : Integrable (fun t => a₄ * f₄ t) μ := h₄.const_mul a₄
  have j₁₂ : Integrable (fun t => a₁ * f₁ t - a₂ * f₂ t) μ := j₁.sub j₂
  have j₁₂₃ : Integrable (fun t => a₁ * f₁ t - a₂ * f₂ t + a₃ * f₃ t) μ := j₁₂.add j₃
  rw [integral_sub j₁₂₃ j₄, integral_add j₁₂ j₃, integral_sub j₁ j₂, integral_const_mul,
    integral_const_mul, integral_const_mul, integral_const_mul]

/-- **The transform of the averaged profile** is the symbol times the transform of the profile. -/
theorem integral_averagedState_laplace {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F) {z : ℂ}
    (hz : 0 < z.re) :
    ∫ t in Ioi (0 : ℝ), Complex.exp (-(z * (t : ℂ))) * ((averagedState F t : ℝ) : ℂ) =
      averageSymbol z * negativeHalfLineLaplace (cx F) z := by
  have hi := hF.integrable
  have e : ∀ t : ℝ, Complex.exp (-(z * (t : ℂ))) * ((averagedState F t : ℝ) : ℂ) =
      (1 / 6 : ℂ) * (Complex.exp (-(z * (t : ℂ))) * ((expAverage 9 F t : ℝ) : ℂ)) -
      (1 / 2 : ℂ) * (Complex.exp (-(z * (t : ℂ))) * ((expAverage 10 F t : ℝ) : ℂ)) +
      (1 / 2 : ℂ) * (Complex.exp (-(z * (t : ℂ))) * ((expAverage 11 F t : ℝ) : ℂ)) -
      (1 / 6 : ℂ) * (Complex.exp (-(z * (t : ℂ))) * ((expAverage 12 F t : ℝ) : ℂ)) := by
    intro t
    unfold averagedState
    push_cast
    ring
  have h4 := integral_four_term (μ := volume.restrict (Ioi (0 : ℝ))) (1 / 6) (1 / 2) (1 / 2)
    (1 / 6)
    (integrableOn_cexp_mul_expAverage (b := 9) (by norm_num) hi hz)
    (integrableOn_cexp_mul_expAverage (b := 10) (by norm_num) hi hz)
    (integrableOn_cexp_mul_expAverage (b := 11) (by norm_num) hi hz)
    (integrableOn_cexp_mul_expAverage (b := 12) (by norm_num) hi hz)
  refine (setIntegral_congr_fun measurableSet_Ioi fun t _ => e t).trans ?_
  rw [h4, integral_expAverage_laplace (b := 9) (by norm_num) hF hz,
    integral_expAverage_laplace (b := 10) (by norm_num) hF hz,
    integral_expAverage_laplace (b := 11) (by norm_num) hF hz,
    integral_expAverage_laplace (b := 12) (by norm_num) hF hz,
    averageSymbol_partialFraction (z := z) (by linarith)]
  push_cast
  ring

/-! ### Fourier inversion on a line right of the origin -/

/-- The averaged profile damped by `e^{-ct}` and extended by zero to `t ≤ 0`. -/
def dampedAverage (F : ℝ → ℝ) (c : ℝ) : ℝ → ℂ :=
  rayDamp (fun t => ((averagedState F t : ℝ) : ℂ)) c

theorem continuous_dampedAverage {F : ℝ → ℝ} (hF : Integrable F) (c : ℝ) :
    Continuous (dampedAverage F c) := by
  unfold dampedAverage rayDamp
  refine Continuous.indicator (fun a ha => ?_) ?_
  · rw [frontier_Ioi, mem_singleton_iff] at ha
    show ((averagedState F a : ℝ) : ℂ) * expRay ((c : ℝ) : ℂ) a = 0
    rw [ha, averagedState_zero, Complex.ofReal_zero, zero_mul]
  · exact (Complex.continuous_ofReal.comp (continuous_averagedState hF)).mul (continuous_expRay _)

theorem integrable_dampedAverage {F : ℝ → ℝ} (hF : Integrable F) {c : ℝ} (hc : 0 < c) :
    Integrable (dampedAverage F c) := by
  unfold dampedAverage rayDamp
  rw [integrable_indicator_iff measurableSet_Ioi]
  have hmaj : IntegrableOn (fun t : ℝ => (2 * ∫ h, |F (-h)|) * Real.exp (-(c * t)))
      (Ioi (0 : ℝ)) :=
    (GaloisForLFunctions.RHTower.integrableOn_Ioi_rexp_neg_mul hc 0).const_mul _
  refine Integrable.mono' hmaj ?_ ?_
  · exact ((Complex.continuous_ofReal.comp (continuous_averagedState hF)).mul
      (continuous_expRay _)).aestronglyMeasurable
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
    show ‖((averagedState F t : ℝ) : ℂ) * expRay ((c : ℝ) : ℂ) t‖ ≤
      (2 * ∫ h, |F (-h)|) * Real.exp (-(c * t))
    rw [norm_mul, norm_expRay, Complex.norm_real, Real.norm_eq_abs, Complex.ofReal_re]
    exact mul_le_mul_of_nonneg_right (abs_averagedState_le hF ht) (Real.exp_pos _).le

theorem fourier_dampedAverage {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F) {c : ℝ}
    (hc : 0 < c) (ξ : ℝ) :
    𝓕 (dampedAverage F c) ξ =
      averageSymbol (rayLine c ξ) * negativeHalfLineLaplace (cx F) (rayLine c ξ) := by
  have hre : 0 < (rayLine c ξ).re := by rw [rayLine_re]; exact hc
  unfold dampedAverage
  rw [fourierIntegral_rayDamp, laplaceRay, ← integral_averagedState_laplace hF hre]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  show ((averagedState F t : ℝ) : ℂ) * expRay (rayLine c ξ) t =
    Complex.exp (-(rayLine c ξ * (t : ℂ))) * ((averagedState F t : ℝ) : ℂ)
  rw [expRay, mul_comm]

theorem integrable_fourier_dampedAverage {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F)
    {c : ℝ} (hc : 0 < c) : Integrable (𝓕 (dampedAverage F c)) := by
  have hfun : 𝓕 (dampedAverage F c) = fun ξ : ℝ =>
      averageSymbol (rayLine c ξ) * negativeHalfLineLaplace (cx F) (rayLine c ξ) :=
    funext fun ξ => fourier_dampedAverage hF hc ξ
  rw [hfun]
  have hmaj : Integrable fun ξ : ℝ => transformMass F 0 * (1 + ξ ^ 2)⁻¹ :=
    integrable_inv_one_add_sq.const_mul _
  have hray : Continuous (rayLine c) := by
    show Continuous fun ξ : ℝ => (c : ℂ) + ((2 * Real.pi * ξ : ℝ) : ℂ) * Complex.I
    fun_prop
  refine Integrable.mono' hmaj ?_ (Eventually.of_forall fun ξ => ?_)
  · refine (continuous_iff_continuousAt.mpr fun ξ => ?_).aestronglyMeasurable
    have hre : (rayLine c ξ).re = c := rayLine_re c ξ
    have h1 : ContinuousAt (averageSymbol ∘ rayLine c) ξ :=
      ContinuousAt.comp
        (differentiableAt_averageSymbol (s := rayLine c ξ) (by rw [hre]; linarith)).continuousAt
        hray.continuousAt
    have h2 : ContinuousAt (negativeHalfLineLaplace (cx F) ∘ rayLine c) ξ :=
      ContinuousAt.comp
        (differentiableAt_laplace hF (p := rayLine c ξ) (by rw [hre]; linarith)).continuousAt
        hray.continuousAt
    exact h1.mul h2
  · show ‖averageSymbol (rayLine c ξ) * negativeHalfLineLaplace (cx F) (rayLine c ξ)‖ ≤
      transformMass F 0 * (1 + ξ ^ 2)⁻¹
    rw [norm_mul]
    have hre : (rayLine c ξ).re = c := rayLine_re c ξ
    have him : (rayLine c ξ).im = 2 * Real.pi * ξ := by simp [rayLine]
    have h1 := norm_averageSymbol_le (z := rayLine c ξ) (by rw [hre]; linarith)
    have h2 := norm_laplace_le_transformMass hF (σ := 0) (by norm_num) (p := rayLine c ξ)
      (by rw [hre]; exact hc.le)
    rw [him] at h1
    have h3 : ((1 + (2 * Real.pi * ξ) ^ 2) ^ 2)⁻¹ ≤ (1 + ξ ^ 2)⁻¹ := by
      have hpi : (1 : ℝ) ≤ 2 * Real.pi := by
        have := Real.pi_gt_three
        linarith
      have hpi2 : (1 : ℝ) ≤ (2 * Real.pi) ^ 2 := one_le_pow₀ hpi
      have hx : ξ ^ 2 ≤ (2 * Real.pi * ξ) ^ 2 := by
        rw [mul_pow]
        have := mul_le_mul_of_nonneg_right hpi2 (sq_nonneg ξ)
        linarith
      have hq : 1 + ξ ^ 2 ≤ (1 + (2 * Real.pi * ξ) ^ 2) ^ 2 := by
        nlinarith [hx, sq_nonneg ((2 * Real.pi * ξ) ^ 2), sq_nonneg (2 * Real.pi * ξ)]
      exact inv_anti₀ (by positivity) hq
    calc ‖averageSymbol (rayLine c ξ)‖ * ‖negativeHalfLineLaplace (cx F) (rayLine c ξ)‖
        ≤ (1 + ξ ^ 2)⁻¹ * transformMass F 0 :=
          mul_le_mul (h1.trans h3) h2 (norm_nonneg _) (by positivity)
      _ = transformMass F 0 * (1 + ξ ^ 2)⁻¹ := mul_comm _ _

/-- **Inversion on a line.** For `c > 0` and `T > 0` the averaged profile is the line integral of
its transform: `∫ k̂(z) L F(z) e^{zT} dt = 2π Ā(T)` along `z = c + it`. -/
theorem integral_line_averageSymbol_mul_laplace {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) {c : ℝ} (hc : 0 < c) {T : ℝ} (hT : 0 < T) :
    ∫ t : ℝ, averageSymbol ((c : ℂ) + t * I) * negativeHalfLineLaplace (cx F) ((c : ℂ) + t * I) *
        Complex.exp (((c : ℂ) + t * I) * T) =
      (2 * Real.pi : ℝ) * ((averagedState F T : ℝ) : ℂ) := by
  have hinv := integral_exp_mul_fourier_rescale (continuous_dampedAverage hF.integrable c)
    (integrable_dampedAverage hF.integrable hc) (integrable_fourier_dampedAverage hF hc) (-T)
  have hpt : ∀ t : ℝ, averageSymbol ((c : ℂ) + t * I) *
        negativeHalfLineLaplace (cx F) ((c : ℂ) + t * I) * Complex.exp (((c : ℂ) + t * I) * T) =
      Complex.exp ((c : ℂ) * T) * (Complex.exp (-(t : ℂ) * ((-T : ℝ) : ℂ) * Complex.I) *
        𝓕 (dampedAverage F c) (t / (2 * Real.pi))) := by
    intro t
    have hray : rayLine c (t / (2 * Real.pi)) = (c : ℂ) + t * I := by
      have h2 : 2 * Real.pi * (t / (2 * Real.pi)) = t := by field_simp
      rw [rayLine, h2]
    have hexp : ((c : ℂ) + t * I) * T = (c : ℂ) * T + -(t : ℂ) * ((-T : ℝ) : ℂ) * Complex.I := by
      push_cast
      ring
    rw [fourier_dampedAverage hF hc, hray, hexp, Complex.exp_add]
    ring
  simp_rw [hpt]
  rw [integral_const_mul, hinv, neg_neg]
  have hval : dampedAverage F c T =
      ((averagedState F T : ℝ) : ℂ) * Complex.exp (-((c : ℂ) * T)) := by
    unfold dampedAverage rayDamp
    rw [Set.indicator_of_mem (mem_Ioi.mpr hT), expRay]
  rw [hval]
  have he : Complex.exp ((c : ℂ) * T) * Complex.exp (-((c : ℂ) * T)) = 1 := by
    rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
  linear_combination ((2 * Real.pi : ℝ) : ℂ) * ((averagedState F T : ℝ) : ℂ) * he

/-! ### The strip left of the origin -/

/-- The constant of the decay bound. -/
def averagedDecayConstant (W₀ : ℝ) (F : ℝ → ℝ) (κ κ' c : ℝ) : ℝ :=
  (‖globalRemainder F 1‖ + 6 * halfPoleMass F * (∑' q : XiZeroCopy, ‖centredZero q‖⁻¹ ^ 2) *
    (1 + 1 / (κ' - κ)) * (c + 9) ^ 2) / criticalAliasCoefficient W₀

theorem averagedDecayConstant_nonneg {W₀ : ℝ} (hW : 0 < W₀) (F : ℝ → ℝ) {κ κ' : ℝ}
    (hκ' : κ < κ') (c : ℝ) : 0 ≤ averagedDecayConstant W₀ F κ κ' c := by
  have ha := criticalAliasCoefficient_positive hW
  have hm := halfPoleMass_nonneg F
  have hS : 0 ≤ ∑' q : XiZeroCopy, ‖centredZero q‖⁻¹ ^ 2 := tsum_nonneg fun q => sq_nonneg _
  have hδ : 0 < κ' - κ := sub_pos.mpr hκ'
  exact div_nonneg (add_nonneg (norm_nonneg _) (mul_nonneg (mul_nonneg (mul_nonneg
    (mul_nonneg (by norm_num) hm) hS) (add_nonneg zero_le_one (one_div_nonneg.mpr hδ.le)))
    (sq_nonneg _))) ha.le

/-- **The symbol times the continuation is `O(1/(1 + (Im s)²))` on the strip `κ' - 8 ≤ Re s ≤ c`**
when every zero has `Re z ≤ κ < κ'`. -/
theorem norm_averageSymbol_mul_stateMeromorphic_le {W₀ : ℝ} (hW : 0 < W₀) {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) {κ κ' c : ℝ} (hκ0 : 0 ≤ κ)
    (hκ : ∀ q : XiZeroCopy, (centredZero q).re ≤ κ) (hκ' : κ < κ') {s : ℂ}
    (hs1 : κ' - 8 ≤ s.re) (hs2 : s.re ≤ c) :
    ‖averageSymbol s * stateMeromorphic W₀ F s‖ ≤
      averagedDecayConstant W₀ F κ κ' c / (1 + s.im ^ 2) := by
  have ha := criticalAliasCoefficient_positive hW
  have hm := halfPoleMass_nonneg F
  have hS : 0 ≤ ∑' q : XiZeroCopy, ‖centredZero q‖⁻¹ ^ 2 := tsum_nonneg fun q => sq_nonneg _
  have hδ : 0 < κ' - κ := sub_pos.mpr hκ'
  have hq1 : 1 ≤ 1 + s.im ^ 2 := by nlinarith [sq_nonneg s.im]
  have hq0 : 0 < 1 + s.im ^ 2 := by linarith
  have hN0 := norm_nonneg (s + 8)
  have hR0 := norm_nonneg (globalRemainder F 1)
  -- the continuation and the symbol
  have hM := norm_stateMeromorphic_le_of_re hW hF hδ hκ (w := s) (by linarith)
  have hsym := norm_averageSymbol_le (z := s) (by linarith)
  -- `|s + 8|` against the height
  have hN : 1 + ‖s + 8‖ ≤ (c + 9) * (1 + |s.im|) := by
    have h := Complex.norm_le_abs_re_add_abs_im (s + 8)
    have hre : (s + 8).re = s.re + 8 := by simp
    have him : (s + 8).im = s.im := by simp
    rw [hre, him, abs_of_nonneg (show (0 : ℝ) ≤ s.re + 8 by linarith)] at h
    have hc8 : 0 ≤ c + 8 := by linarith
    nlinarith [mul_nonneg hc8 (abs_nonneg s.im), abs_nonneg s.im]
  have hsq : (1 + |s.im|) ^ 2 ≤ 2 * (1 + s.im ^ 2) := by
    nlinarith [sq_nonneg (1 - |s.im|), sq_abs s.im]
  have hN2 : (1 + ‖s + 8‖) ^ 2 ≤ 2 * (c + 9) ^ 2 * (1 + s.im ^ 2) := by
    have h1 : (1 + ‖s + 8‖) ^ 2 ≤ ((c + 9) * (1 + |s.im|)) ^ 2 :=
      pow_le_pow_left₀ (by linarith) hN 2
    have h2 : ((c + 9) * (1 + |s.im|)) ^ 2 = (c + 9) ^ 2 * (1 + |s.im|) ^ 2 := mul_pow _ _ _
    have h3 := mul_le_mul_of_nonneg_left hsq (sq_nonneg (c + 9))
    linarith
  have hfrac : 1 + ‖s + 8‖ / (κ' - κ) ≤ (1 + 1 / (κ' - κ)) * (1 + ‖s + 8‖) := by
    have hinv : 0 ≤ 1 / (κ' - κ) := one_div_nonneg.mpr hδ.le
    have e : ‖s + 8‖ / (κ' - κ) = ‖s + 8‖ * (1 / (κ' - κ)) := by ring
    rw [e]
    nlinarith [mul_nonneg hN0 hinv]
  have hC : (1 + ‖s + 8‖) * (1 + ‖s + 8‖ / (κ' - κ)) ≤
      2 * (1 + 1 / (κ' - κ)) * (c + 9) ^ 2 * (1 + s.im ^ 2) := by
    have h1 : (1 + ‖s + 8‖) * (1 + ‖s + 8‖ / (κ' - κ)) ≤
        (1 + ‖s + 8‖) * ((1 + 1 / (κ' - κ)) * (1 + ‖s + 8‖)) :=
      mul_le_mul_of_nonneg_left hfrac (by linarith)
    have h2 : 0 ≤ 1 + 1 / (κ' - κ) := add_nonneg zero_le_one (one_div_nonneg.mpr hδ.le)
    have h3 := mul_le_mul_of_nonneg_left hN2 h2
    linarith
  -- the continuation is at most the constant times `1 + (Im s)²`
  have h1 : ‖stateMeromorphic W₀ F s‖ ≤ averagedDecayConstant W₀ F κ κ' c * (1 + s.im ^ 2) := by
    unfold averagedDecayConstant
    rw [div_mul_eq_mul_div]
    refine hM.trans (div_le_div_of_nonneg_right ?_ ha.le)
    have h := mul_le_mul_of_nonneg_left hC
      (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3) hm) hS)
    have h5 := mul_nonneg hR0 (sub_nonneg.mpr hq1)
    linarith
  have e : ((1 + s.im ^ 2) ^ 2)⁻¹ * (averagedDecayConstant W₀ F κ κ' c * (1 + s.im ^ 2)) =
      averagedDecayConstant W₀ F κ κ' c / (1 + s.im ^ 2) := by
    refine eq_div_of_mul_eq hq0.ne' ?_
    have hQ2 : ((1 + s.im ^ 2) ^ 2)⁻¹ * (1 + s.im ^ 2) ^ 2 = 1 :=
      inv_mul_cancel₀ (pow_ne_zero 2 hq0.ne')
    linear_combination averagedDecayConstant W₀ F κ κ' c * hQ2
  calc ‖averageSymbol s * stateMeromorphic W₀ F s‖
      = ‖averageSymbol s‖ * ‖stateMeromorphic W₀ F s‖ := norm_mul _ _
    _ ≤ ((1 + s.im ^ 2) ^ 2)⁻¹ * (averagedDecayConstant W₀ F κ κ' c * (1 + s.im ^ 2)) :=
        mul_le_mul hsym h1 (norm_nonneg _) (inv_nonneg.mpr (sq_nonneg _))
    _ = averagedDecayConstant W₀ F κ κ' c / (1 + s.im ^ 2) := e

theorem differentiableAt_stateMeromorphic_of_re {W₀ : ℝ} {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) {κ : ℝ}
    (hκ : ∀ q : XiZeroCopy, (centredZero q).re ≤ κ) {s : ℂ} (hs : κ - 8 < s.re) :
    DifferentiableAt ℂ (stateMeromorphic W₀ F) s := by
  have h8 : (s + 8).re = s.re + 8 := by simp
  have hg : DifferentiableAt ℂ (globalRemainder F) (s + 8) :=
    differentiableAt_globalRemainder_of_re hF hκ (by rw [h8]; linarith)
  have hadd : DifferentiableAt ℂ (fun w : ℂ => w + 8) s := differentiableAt_id.add_const 8
  have hc : DifferentiableAt ℂ (fun w : ℂ => globalRemainder F (w + 8)) s := hg.comp s hadd
  show DifferentiableAt ℂ
    (fun w => -globalRemainder F (w + 8) / (criticalAliasCoefficient W₀ : ℂ)) s
  exact hc.neg.div_const _

/-- The integrand of the line integrals: symbol, continuation, exponential. -/
def averagedLineIntegrand (W₀ : ℝ) (F : ℝ → ℝ) (T : ℝ) (s : ℂ) : ℂ :=
  averageSymbol s * stateMeromorphic W₀ F s * Complex.exp (s * T)

theorem norm_averagedLineIntegrand_le {W₀ : ℝ} (hW : 0 < W₀) {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) {κ κ' c : ℝ} (hκ0 : 0 ≤ κ)
    (hκ : ∀ q : XiZeroCopy, (centredZero q).re ≤ κ) (hκ' : κ < κ') {s : ℂ}
    (hs1 : κ' - 8 ≤ s.re) (hs2 : s.re ≤ c) (T : ℝ) :
    ‖averagedLineIntegrand W₀ F T s‖ ≤
      averagedDecayConstant W₀ F κ κ' c / (1 + s.im ^ 2) * Real.exp (s.re * T) := by
  have h := norm_averageSymbol_mul_stateMeromorphic_le hW hF hκ0 hκ hκ' hs1 hs2
  have hre : (s * (T : ℂ)).re = s.re * T := by simp [Complex.mul_re]
  unfold averagedLineIntegrand
  rw [norm_mul, Complex.norm_exp, hre]
  exact mul_le_mul_of_nonneg_right h (Real.exp_pos _).le

/-- **The shift of the line.** The line integral over `Re s = c` equals the one over
`Re s = κ' - 8`. -/
theorem integral_averagedLineIntegrand_shift {W₀ : ℝ} (hW : 0 < W₀) {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) {κ κ' c : ℝ} (hκ0 : 0 ≤ κ)
    (hκ : ∀ q : XiZeroCopy, (centredZero q).re ≤ κ) (hκ' : κ < κ') (hc : κ' - 8 ≤ c) {T : ℝ}
    (hT : 0 ≤ T) :
    ∫ t : ℝ, averagedLineIntegrand W₀ F T ((c : ℂ) + t * I) =
      ∫ t : ℝ, averagedLineIntegrand W₀ F T (((κ' - 8 : ℝ) : ℂ) + t * I) := by
  have hK := averagedDecayConstant_nonneg hW F hκ' c
  have hmem : ∀ s : ℂ, s.re ∈ uIcc c (κ' - 8) → κ' - 8 ≤ s.re ∧ s.re ≤ c := fun s hs => by
    rcases Set.mem_uIcc.mp hs with h | h <;> constructor <;> linarith [h.1, h.2]
  refine integral_vertical_line_shift_of_decay (Φ := averagedLineIntegrand W₀ F T) (c₁ := c)
    (c₂ := κ' - 8) (C := averagedDecayConstant W₀ F κ κ' c * Real.exp (c * T))
    (fun s hs => ?_) (fun s hs => ?_)
  · obtain ⟨h1, h2⟩ := hmem s hs
    have hexp : DifferentiableAt ℂ (fun z : ℂ => Complex.exp (z * (T : ℂ))) s :=
      (differentiableAt_id.mul_const (T : ℂ)).cexp
    show DifferentiableAt ℂ
      (fun z => averageSymbol z * stateMeromorphic W₀ F z * Complex.exp (z * (T : ℂ))) s
    exact ((differentiableAt_averageSymbol (by linarith)).mul
      (differentiableAt_stateMeromorphic_of_re hF hκ (by linarith))).mul hexp
  · obtain ⟨h1, h2⟩ := hmem s hs
    have hb := norm_averagedLineIntegrand_le hW hF hκ0 hκ hκ' h1 h2 T
    have hq0 : 0 < 1 + s.im ^ 2 := by nlinarith [sq_nonneg s.im]
    have he : Real.exp (s.re * T) ≤ Real.exp (c * T) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right h2 hT)
    calc ‖averagedLineIntegrand W₀ F T s‖
        ≤ averagedDecayConstant W₀ F κ κ' c / (1 + s.im ^ 2) * Real.exp (s.re * T) := hb
      _ ≤ averagedDecayConstant W₀ F κ κ' c / (1 + s.im ^ 2) * Real.exp (c * T) :=
          mul_le_mul_of_nonneg_left he (div_nonneg hK hq0.le)
      _ = averagedDecayConstant W₀ F κ κ' c * Real.exp (c * T) / (1 + s.im ^ 2) := by ring

/-! ### The decay law in averaged form -/

/-- **The averaged state decays at the rate of the zeros.** If every centred zero has
`Re z ≤ κ`, then for every `κ' > κ` the averaged state is `O(e^{-(8 - κ')t})`. -/
theorem exists_bound_averagedState {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) {κ κ' : ℝ} (hκ0 : 0 ≤ κ)
    (hκ : ∀ q : XiZeroCopy, (centredZero q).re ≤ κ) (hκ' : κ < κ') :
    ∃ C : ℝ, ∀ t : ℝ, 0 < t → |averagedState F t| ≤ C * Real.exp (-((8 - κ') * t)) := by
  have hd := criticalHalfLineEnergyDomain_of_groundState hF
  obtain ⟨c, hc0, hcκ⟩ : ∃ c : ℝ, 0 < c ∧ κ' - 8 ≤ c :=
    ⟨|κ'| + 1, by positivity, by have := le_abs_self κ'; linarith⟩
  refine ⟨averagedDecayConstant W₀ F κ κ' c / 2, fun T hT => ?_⟩
  -- inversion on the line `Re s = c`, where the continuation is the transform
  have h2 : ∫ t : ℝ, averagedLineIntegrand W₀ F T ((c : ℂ) + t * I) =
      (2 * Real.pi : ℝ) * ((averagedState F T : ℝ) : ℂ) := by
    rw [← integral_line_averageSymbol_mul_laplace hd hc0 hT]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    have hre : ((c : ℂ) + t * I).re = c := by simp
    show averageSymbol ((c : ℂ) + t * I) * stateMeromorphic W₀ F ((c : ℂ) + t * I) *
        Complex.exp (((c : ℂ) + t * I) * T) =
      averageSymbol ((c : ℂ) + t * I) * negativeHalfLineLaplace (cx F) ((c : ℂ) + t * I) *
        Complex.exp (((c : ℂ) + t * I) * T)
    rw [stateMeromorphic_eq_levyContinuation (w := (c : ℂ) + t * I) (by rw [hre]; linarith),
      levyContinuation_eq_laplace hW hthreshold hF (w := (c : ℂ) + t * I)
        (by rw [hre]; linarith)]
  have h3 := integral_averagedLineIntegrand_shift hW hd hκ0 hκ hκ' hcκ hT.le
  -- the line `Re s = κ' - 8`
  have h4 : ‖∫ t : ℝ, averagedLineIntegrand W₀ F T (((κ' - 8 : ℝ) : ℂ) + t * I)‖ ≤
      ∫ t : ℝ, averagedDecayConstant W₀ F κ κ' c * Real.exp ((κ' - 8) * T) * (1 + t ^ 2)⁻¹ := by
    refine norm_integral_le_of_norm_le (integrable_inv_one_add_sq.const_mul _)
      (Eventually.of_forall fun t => ?_)
    show ‖averagedLineIntegrand W₀ F T (((κ' - 8 : ℝ) : ℂ) + t * I)‖ ≤
      averagedDecayConstant W₀ F κ κ' c * Real.exp ((κ' - 8) * T) * (1 + t ^ 2)⁻¹
    have hre : (((κ' - 8 : ℝ) : ℂ) + t * I).re = κ' - 8 := by simp
    have him : (((κ' - 8 : ℝ) : ℂ) + t * I).im = t := by simp
    have hb := norm_averagedLineIntegrand_le hW hd hκ0 hκ hκ'
      (s := ((κ' - 8 : ℝ) : ℂ) + t * I) (c := c) hre.ge (hre.le.trans hcκ) T
    rw [hre, him] at hb
    refine hb.trans (le_of_eq ?_)
    rw [div_eq_mul_inv]
    ring
  rw [integral_const_mul, integral_univ_inv_one_add_sq, ← h3, h2, norm_mul, Complex.norm_real,
    Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)] at h4
  have hexp : Real.exp ((κ' - 8) * T) = Real.exp (-((8 - κ') * T)) := by
    congr 1
    ring
  rw [hexp] at h4
  have hpi := Real.pi_pos
  have h5 : Real.pi * (2 * |averagedState F T|) ≤
      Real.pi * (averagedDecayConstant W₀ F κ κ' c * Real.exp (-((8 - κ') * T))) := by
    linarith
  have h6 := le_of_mul_le_mul_left h5 hpi
  linarith

/-! ### Beyond the barrier -/

/-- Every centred zero has `Re z ≤ 8999/24000`: the zero-free half-plane `Re s > 20999/24000`. -/
theorem re_centredZero_le_seed (q : XiZeroCopy) : (centredZero q).re ≤ 8999 / 24000 := by
  by_contra hlt
  have hgt : (8999 : ℝ) / 24000 < (centredZero q).re := not_le.mp hlt
  have hxi := xi_centredZero q
  have hre : ((1 : ℂ) / 2 + centredZero q).re = 1 / 2 + (centredZero q).re := by
    rw [re_one_half_add]
  have hpos : 0 < ((1 : ℂ) / 2 + centredZero q).re := by rw [hre]; linarith
  have hne : (1 : ℂ) / 2 + centredZero q ≠ 1 := fun h => by
    have h1 := congrArg Complex.re h
    rw [hre, Complex.one_re] at h1
    have h2 := (abs_lt.mp (abs_re_centredZero_lt q)).2
    linarith
  have hζ := (RHTower.xi_eq_zero_iff_riemannZeta_of_re_pos hpos hne).mp hxi
  have hseed : (20999 / 24000 : ℝ) < ((1 : ℂ) / 2 + centredZero q).re := by rw [hre]; linarith
  exact GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein.riemannZeta_ne_zero_of_sub_seven_eighths_lt_re
    hseed hζ

/-- **The averaged state decays at every rate below `183001/24000`**, beyond the rate `15/2` of the
barrier comparison. -/
theorem criticalState_averaged_decay_beyond_barrier {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) {β : ℝ} (hβ : β < 183001 / 24000) :
    ∃ C : ℝ, ∀ t : ℝ, 0 < t → |averagedState F t| ≤ C * Real.exp (-(β * t)) := by
  obtain ⟨C, hC⟩ := exists_bound_averagedState hW hthreshold hF (κ := 8999 / 24000)
    (κ' := 8 - β) (by norm_num) re_centredZero_le_seed (by linarith)
  refine ⟨C, fun t ht => ?_⟩
  have h := hC t ht
  rwa [show (8 : ℝ) - (8 - β) = β by ring] at h

/-- **Either RH holds, or the critical state exists and its average decays at every rate below
`183001/24000`.** -/
theorem riemannHypothesis_or_criticalState_averaged_decay :
    RiemannHypothesis ∨
      ∃ (W₀ : ℝ) (F : ℝ → ℝ), 0 < W₀ ∧
        (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal) ∧
        IsCriticalHalfLineGroundState W₀ F ∧
        ∀ β : ℝ, β < 183001 / 24000 →
          ∃ C : ℝ, ∀ t : ℝ, 0 < t → |averagedState F t| ≤ C * Real.exp (-(β * t)) := by
  rcases riemannHypothesis_or_exists_criticalHalfLineGroundState with hRH | ⟨W₀, F, hW, ht, hF⟩
  · exact Or.inl hRH
  · exact Or.inr ⟨W₀, F, hW, ht, hF, fun β hβ =>
      criticalState_averaged_decay_beyond_barrier hW ht hF hβ⟩

end GaloisForLFunctions.ExclusionOfTheCriticalState
