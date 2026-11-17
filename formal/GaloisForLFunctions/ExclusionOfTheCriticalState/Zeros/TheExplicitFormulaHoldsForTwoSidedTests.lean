import GaloisForLFunctions.ExclusionOfTheCriticalState.Zeros.TheZeroPairingOfTwoProfilesIsWeilsForm

/-!
# The explicit formula holds for two-sided tests

Weil's bare form `W(F, H) = Γ(F, H) − (P(F, H) + P(H, F))/2 + 2(C_F C_H − S_F S_H)` is invariant under
a joint translation `τ_R f(u) = f(u + R)` of both profiles (`bareMixedEnergy_shiftProfile`): the Gamma
pair `Re(F̂ Ĥ̄)` sees the common phase `e^{−irR}` only through its modulus, each prime term is a
correlation, and the charge combination `C_F C_H − S_F S_H` is a Lorentz invariant of the hyperbolic
rotation by `R/2`. The zero values transform by the opposite factors `e^{∓zR}`, which cancel in the
zero pairing.

Hence for a profile `F` of the energy domain and a smooth compactly supported test `H` on the whole
line, not necessarily vanishing on `u ≥ 0` (`hasSum_bareMixedEnergy_of_compactSupport`):

  `Σ_z L F(z) L H(−z) = W(F, H)`,

absolutely convergent. Translating by `R` beyond the support of `H` reduces it to the half-line case
`hasSum_bareMixedEnergy_of_domain`, and `τ_R F` stays in the energy domain for `R ≥ 0`.
-/

noncomputable section
open MeasureTheory Set Filter Complex Topology Zeta23
open scoped ContDiff

namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri
  CriticalArithmeticCorrelationTheory HTGeometry _root_.RHTower

/-- The translate `τ_R f(u) = f(u + R)`. -/
def shiftProfile (f : ℝ → ℝ) (R : ℝ) (u : ℝ) : ℝ := f (u + R)

theorem laplace_shiftProfile (f : ℝ → ℝ) (R : ℝ) (z : ℂ) :
    negativeHalfLineLaplace (cx (shiftProfile f R)) z =
      cexp (-(z * R)) * negativeHalfLineLaplace (cx f) z := by
  unfold negativeHalfLineLaplace
  calc ∫ u : ℝ, cexp (z * u) * cx (shiftProfile f R) u
      = ∫ u : ℝ, cexp (z * (((u + R : ℝ) : ℂ) - R)) * cx f (u + R) := by
        congr 1; funext u; simp [shiftProfile, cx]
    _ = ∫ u : ℝ, cexp (z * ((u : ℂ) - R)) * cx f u :=
        integral_add_right_eq_self (fun u : ℝ => cexp (z * ((u : ℂ) - R)) * cx f u) R
    _ = ∫ u : ℝ, cexp (-(z * R)) * (cexp (z * u) * cx f u) := by
        congr 1; funext u
        rw [← mul_assoc, ← Complex.exp_add]
        congr 2; ring
    _ = _ := integral_const_mul _ _

theorem paperFT_shiftProfile (f : ℝ → ℝ) (R : ℝ) (z : ℂ) :
    paperFT (cx (shiftProfile f R)) z = cexp (-(I * z * R)) * paperFT (cx f) z := by
  unfold paperFT
  calc ∫ u : ℝ, cx (shiftProfile f R) u * cexp (I * z * u)
      = ∫ u : ℝ, cx f (u + R) * cexp (I * z * (((u + R : ℝ) : ℂ) - R)) := by
        congr 1; funext u; simp [shiftProfile, cx]
    _ = ∫ u : ℝ, cx f u * cexp (I * z * ((u : ℂ) - R)) :=
        integral_add_right_eq_self (fun u : ℝ => cx f u * cexp (I * z * ((u : ℂ) - R))) R
    _ = ∫ u : ℝ, cexp (-(I * z * R)) * (cx f u * cexp (I * z * u)) := by
        congr 1; funext u
        rw [mul_left_comm, ← Complex.exp_add]
        congr 2; ring
    _ = _ := integral_const_mul _ _

theorem norm_shiftPhase (r R : ℝ) : ‖cexp (-(I * (r : ℂ) * R))‖ = 1 := by
  rw [show -(I * (r : ℂ) * R) = ((-(r * R) : ℝ) : ℂ) * I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

theorem norm_paperFT_shiftProfile (f : ℝ → ℝ) (R r : ℝ) :
    ‖paperFT (cx (shiftProfile f R)) r‖ = ‖paperFT (cx f) r‖ := by
  rw [paperFT_shiftProfile, norm_mul, norm_shiftPhase, one_mul]

/-- The Gamma pair `Re(F̂ Ĝ̄)` only sees the modulus of the common phase. -/
theorem gammaFourierPair_shiftProfile (f g : ℝ → ℝ) (R r : ℝ) :
    gammaFourierPair (shiftProfile f R) (shiftProfile g R) r = gammaFourierPair f g r := by
  set w := cexp (-(I * (r : ℂ) * R))
  have hw : w.re ^ 2 + w.im ^ 2 = 1 := by
    have h := Complex.sq_norm w
    rw [norm_shiftPhase, one_pow, Complex.normSq_apply] at h
    nlinarith [h]
  unfold gammaFourierPair
  rw [paperFT_shiftProfile, paperFT_shiftProfile]
  simp only [Complex.mul_re, Complex.mul_im]
  linear_combination ((paperFT (cx f) r).re * (paperFT (cx g) r).re +
    (paperFT (cx f) r).im * (paperFT (cx g) r).im) * hw

theorem gammaMixedForm_shiftProfile (f g : ℝ → ℝ) (R : ℝ) :
    gammaMixedForm (shiftProfile f R) (shiftProfile g R) = gammaMixedForm f g := by
  unfold gammaMixedForm
  simp_rw [gammaFourierPair_shiftProfile]

/-- A prime term is a correlation, hence invariant under a joint translation. -/
theorem primePairTerm_shiftProfile (a b : ℝ → ℝ) (R : ℝ) (n : ℕ) :
    primePairTerm (shiftProfile a R) (shiftProfile b R) n = primePairTerm a b n := by
  unfold primePairTerm shiftProfile
  have h1 : ∫ t, a (t + R) * b (t - Real.log n + R) = ∫ t, a t * b (t - Real.log n) := by
    rw [← integral_add_right_eq_self (fun t => a t * b (t - Real.log n)) R]
    congr 1; funext t; congr 2; ring
  have h2 : ∫ t, a (t + R) * b (t + Real.log n + R) = ∫ t, a t * b (t + Real.log n) := by
    rw [← integral_add_right_eq_self (fun t => a t * b (t + Real.log n)) R]
    congr 1; funext t; congr 2; ring
  rw [h1, h2]

theorem primeMixedForm_shiftProfile (a b : ℝ → ℝ) (R : ℝ) :
    primeMixedForm (shiftProfile a R) (shiftProfile b R) = primeMixedForm a b := by
  unfold primeMixedForm
  exact tsum_congr fun n => primePairTerm_shiftProfile a b R n

theorem coshHalfMoment_shiftProfile {f : ℝ → ℝ}
    (hc : Integrable fun u => f u * Real.cosh (u / 2))
    (hs : Integrable fun u => f u * Real.sinh (u / 2)) (R : ℝ) :
    coshHalfMoment (shiftProfile f R) =
      Real.cosh (R / 2) * coshHalfMoment f - Real.sinh (R / 2) * sinhHalfMoment f := by
  unfold coshHalfMoment sinhHalfMoment shiftProfile
  have h0 : ∫ x, f (x + R) * Real.cosh (x / 2) = ∫ x, f x * Real.cosh ((x - R) / 2) := by
    rw [← integral_add_right_eq_self (fun x => f x * Real.cosh ((x - R) / 2)) R]
    simp only [add_sub_cancel_right]
  rw [h0, ← integral_const_mul, ← integral_const_mul,
    ← integral_sub (hc.const_mul _) (hs.const_mul _)]
  congr 1; funext u
  rw [show (u - R) / 2 = u / 2 - R / 2 by ring, Real.cosh_sub]
  ring

theorem sinhHalfMoment_shiftProfile {f : ℝ → ℝ}
    (hc : Integrable fun u => f u * Real.cosh (u / 2))
    (hs : Integrable fun u => f u * Real.sinh (u / 2)) (R : ℝ) :
    sinhHalfMoment (shiftProfile f R) =
      Real.cosh (R / 2) * sinhHalfMoment f - Real.sinh (R / 2) * coshHalfMoment f := by
  unfold coshHalfMoment sinhHalfMoment shiftProfile
  have h0 : ∫ x, f (x + R) * Real.sinh (x / 2) = ∫ x, f x * Real.sinh ((x - R) / 2) := by
    rw [← integral_add_right_eq_self (fun x => f x * Real.sinh ((x - R) / 2)) R]
    simp only [add_sub_cancel_right]
  rw [h0, ← integral_const_mul, ← integral_const_mul,
    ← integral_sub (hs.const_mul _) (hc.const_mul _)]
  congr 1; funext u
  rw [show (u - R) / 2 = u / 2 - R / 2 by ring, Real.sinh_sub]
  ring

/-- **Weil's bare form is invariant under a joint translation.** -/
theorem bareMixedEnergy_shiftProfile {F H : ℝ → ℝ}
    (hFc : Integrable fun u => F u * Real.cosh (u / 2))
    (hFs : Integrable fun u => F u * Real.sinh (u / 2))
    (hHc : Integrable fun u => H u * Real.cosh (u / 2))
    (hHs : Integrable fun u => H u * Real.sinh (u / 2)) (R : ℝ) :
    bareMixedEnergy (shiftProfile F R) (shiftProfile H R) = bareMixedEnergy F H := by
  unfold bareMixedEnergy
  rw [gammaMixedForm_shiftProfile, primeMixedForm_shiftProfile, primeMixedForm_shiftProfile,
    coshHalfMoment_shiftProfile hFc hFs, coshHalfMoment_shiftProfile hHc hHs,
    sinhHalfMoment_shiftProfile hFc hFs, sinhHalfMoment_shiftProfile hHc hHs]
  have h := Real.cosh_sq_sub_sinh_sq (R / 2)
  linear_combination (2 * coshHalfMoment F * coshHalfMoment H -
    2 * sinhHalfMoment F * sinhHalfMoment H) * h

/-! ### The domain is stable under left translation -/

theorem criticalHalfLineEnergyDomain_shiftProfile {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F)
    {R : ℝ} (hR : 0 ≤ R) : CriticalHalfLineEnergyDomain (shiftProfile F R) where
  meas := hF.meas.comp (measurable_add_const R)
  integrable := hF.integrable.comp_add_right R
  sq := hF.sq.comp_add_right R
  exponential := by
    refine ((hF.exponential.comp_add_right R).const_mul (Real.exp (8 * R))).congr
      (Eventually.of_forall fun u => ?_)
    show Real.exp (8 * R) * (F (u + R) ^ 2 * Real.exp (-(8 * (u + R)))) =
      F (u + R) ^ 2 * Real.exp (-(8 * u))
    rw [mul_left_comm, ← Real.exp_add]
    congr 2; ring
  support := fun u hu => hF.support _ (by linarith)
  gamma := by
    refine hF.gamma.congr (Eventually.of_forall fun r => ?_)
    show ‖paperFT (cx F) r‖ ^ 2 * EF.gammaBracket r =
      ‖paperFT (cx (shiftProfile F R)) r‖ ^ 2 * EF.gammaBracket r
    rw [norm_paperFT_shiftProfile]

theorem integrable_mul_cosh_half_of_domain {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F) :
    Integrable fun u => F u * Real.cosh (u / 2) := by
  refine (((integrable_abs_mul_exp_of_domain hF (c := 1 / 2) (by norm_num)).add
    (integrable_abs_mul_exp_of_domain hF (c := -(1 / 2)) (by norm_num))).div_const 2).mono'
    (hF.meas.mul (by fun_prop)).aestronglyMeasurable (Eventually.of_forall fun u => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.cosh_pos _), Real.cosh_eq]
  show |F u| * ((Real.exp (u / 2) + Real.exp (-(u / 2))) / 2) ≤
    (|F u| * Real.exp (1 / 2 * u) + |F u| * Real.exp (-(1 / 2) * u)) / 2
  rw [show u / 2 = 1 / 2 * u by ring, show -(1 / 2 * u) = -(1 / 2) * u by ring]
  apply le_of_eq; ring

theorem integrable_mul_sinh_half_of_domain {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F) :
    Integrable fun u => F u * Real.sinh (u / 2) := by
  refine (((integrable_abs_mul_exp_of_domain hF (c := 1 / 2) (by norm_num)).add
    (integrable_abs_mul_exp_of_domain hF (c := -(1 / 2)) (by norm_num))).div_const 2).mono'
    (hF.meas.mul (by fun_prop)).aestronglyMeasurable (Eventually.of_forall fun u => ?_)
  rw [Real.norm_eq_abs, abs_mul, Real.sinh_eq]
  show |F u| * |(Real.exp (u / 2) - Real.exp (-(u / 2))) / 2| ≤
    (|F u| * Real.exp (1 / 2 * u) + |F u| * Real.exp (-(1 / 2) * u)) / 2
  rw [show u / 2 = 1 / 2 * u by ring, show -(1 / 2 * u) = -(1 / 2) * u by ring]
  have h1 : |(Real.exp (1 / 2 * u) - Real.exp (-(1 / 2) * u)) / 2| ≤
      (Real.exp (1 / 2 * u) + Real.exp (-(1 / 2) * u)) / 2 := by
    rw [abs_div, abs_two]
    gcongr
    exact (abs_sub _ _).trans (by rw [abs_of_pos (Real.exp_pos _), abs_of_pos (Real.exp_pos _)])
  calc |F u| * |(Real.exp (1 / 2 * u) - Real.exp (-(1 / 2) * u)) / 2|
      ≤ |F u| * ((Real.exp (1 / 2 * u) + Real.exp (-(1 / 2) * u)) / 2) :=
        mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
    _ = _ := by ring

/-! ### Two-sided tests -/

/-- **The explicit formula for a smooth compactly supported test on the whole line.** For `F` in the
energy domain and `H` smooth with compact support, `Σ_z L F(z) L H(−z) = W(F, H)`. -/
theorem hasSum_bareMixedEnergy_of_compactSupport {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F)
    {H : ℝ → ℝ} (hH : ContDiff ℝ ∞ H) (hc : HasCompactSupport H) :
    HasSum (fun q : XiZeroCopy => negativeHalfLineLaplace (cx F) (centredZero q) *
        negativeHalfLineLaplace (cx H) (-centredZero q)) ((bareMixedEnergy F H : ℝ) : ℂ) := by
  obtain ⟨M, hM⟩ := hc.isCompact.bddAbove
  set R := max M 0 + 1
  have hR : 0 ≤ R := by positivity
  have hzero : ∀ u, R ≤ u → H u = 0 := fun u hu =>
    image_eq_zero_of_notMem_tsupport fun hmem => by
      have := hM hmem
      have : M < R := by simp only [R]; linarith [le_max_left M 0]
      linarith
  have hHs : ContDiff ℝ ∞ (shiftProfile H R) := hH.comp (contDiff_id.add contDiff_const)
  have hHc : HasCompactSupport (shiftProfile H R) := hc.comp_homeomorph (Homeomorph.addRight R)
  have h := hasSum_bareMixedEnergy_of_domain (criticalHalfLineEnergyDomain_shiftProfile hF hR)
    hHs hHc (fun u hu => hzero _ (by linarith))
  have hcont : Continuous H := hH.continuous
  have hHcosh : Integrable fun u => H u * Real.cosh (u / 2) :=
    (hcont.mul (by fun_prop)).integrable_of_hasCompactSupport hc.mul_right
  have hHsinh : Integrable fun u => H u * Real.sinh (u / 2) :=
    (hcont.mul (by fun_prop)).integrable_of_hasCompactSupport hc.mul_right
  rw [bareMixedEnergy_shiftProfile (integrable_mul_cosh_half_of_domain hF)
    (integrable_mul_sinh_half_of_domain hF) hHcosh hHsinh] at h
  refine h.congr_fun fun q => ?_
  rw [laplace_shiftProfile, laplace_shiftProfile]
  have he : cexp (-(centredZero q * R)) * cexp (-(-centredZero q * R)) = 1 := by
    rw [← Complex.exp_add, show -(centredZero q * R) + -(-centredZero q * R) = 0 by ring,
      Complex.exp_zero]
  linear_combination (-(negativeHalfLineLaplace (cx F) (centredZero q) *
    negativeHalfLineLaplace (cx H) (-centredZero q))) * he

end GaloisForLFunctions.ExclusionOfTheCriticalState
