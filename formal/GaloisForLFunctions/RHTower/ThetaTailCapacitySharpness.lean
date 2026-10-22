import GaloisForLFunctions.RHTower.ThetaTailDivisorCapacity
import GaloisForLFunctions.RHTower.CausalMobiusThetaMovingCusp
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspFullDerivativeExponentialMoments
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspReflection
import GaloisForLFunctions.HTGeometry.GammaVerticalPolynomialDecay

/-!
# Sharpness of the theta-tail capacity exponent

The perturbations `u = t k^{(4m)}` have transform `t z^{4m} F(z)` (Fourier transform of
derivatives on the real line, then the identity theorem), so they preserve the complete Xi divisor
with multiplicities. The Gaussian atom bound for `k^{(4m)}` gives `|u(x)| ≤ C exp(-a e^{2|x|})` for
every `a < π`, while the capacity theorem shows that no bound with `b > 2` is possible for `t ≠ 0`.
-/

open MeasureTheory Set Filter Topology Complex
open scoped FourierTransform

namespace RHTower

noncomputable section

/-- The complex derivative source `k^{(n)}`. -/
def thetaDerivSourceC (n : ℕ) (x : ℝ) : ℂ := ((iteratedDeriv n thetaCuspFullSource x : ℝ) : ℂ)

theorem iteratedDeriv_thetaSourceC (n : ℕ) : iteratedDeriv n thetaSourceC = thetaDerivSourceC n :=
  GaloisForLFunctions.iteratedDeriv_ofReal_comp contDiff_thetaCuspFullSource n

theorem continuous_thetaDerivSourceC (n : ℕ) : Continuous (thetaDerivSourceC n) :=
  Complex.continuous_ofReal.comp (contDiff_thetaCuspFullSource.continuous_iteratedDeriv n
    (by exact_mod_cast le_top))

theorem expMomentSource_thetaDerivSourceC (n : ℕ) : ExpMomentSource (thetaDerivSourceC n) := by
  refine ⟨continuous_thetaDerivSourceC n, fun c => ?_⟩
  refine (integrable_exp_abs_mul_abs_iteratedDeriv_thetaCuspFullSource n c).congr
    (Eventually.of_forall fun x => ?_)
  simp [thetaDerivSourceC, Complex.norm_real, Real.norm_eq_abs]

/-- On the real line, `∫ e^{-itx} k^{(n)}(x) dx = (it)^n F(t)`. -/
theorem sourceTransform_thetaDerivSourceC_ofReal (n : ℕ) (t : ℝ) :
    sourceTransform (thetaDerivSourceC n) t = (I * t) ^ n * XiC t := by
  have h := Real.fourier_iteratedDeriv (f := thetaSourceC) (N := ⊤) (n := n)
    contDiff_thetaSourceC (fun m _ => by
      rw [iteratedDeriv_thetaSourceC]; exact (expMomentSource_thetaDerivSourceC m).integrable)
    le_top
  have h2 := congrFun h (t / (2 * Real.pi))
  have hπ : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  rw [fourier_eq_sourceTransform, fourier_eq_sourceTransform, iteratedDeriv_thetaSourceC,
    sourceTransform_thetaSourceC, smul_eq_mul] at h2
  have ht : ((2 * Real.pi * (t / (2 * Real.pi)) : ℝ) : ℂ) = (t : ℂ) := by
    rw [mul_div_cancel₀ _ hπ]
  push_cast at h2 ht
  rw [ht] at h2
  rw [h2]
  congr 2
  field_simp

/-- **The derivative packet transform.** `∫ e^{-izx} k^{(n)}(x) dx = (iz)^n F(z)` for every
complex `z`. -/
theorem sourceTransform_thetaDerivSourceC (n : ℕ) (z : ℂ) :
    sourceTransform (thetaDerivSourceC n) z = (I * z) ^ n * XiC z := by
  have hL : AnalyticOnNhd ℂ (sourceTransform (thetaDerivSourceC n)) univ := fun w _ =>
    (expMomentSource_thetaDerivSourceC n).differentiable_sourceTransform.analyticAt w
  have hR : AnalyticOnNhd ℂ (fun w => (I * w) ^ n * XiC w) univ := fun w _ =>
    ((differentiable_const _ |>.mul differentiable_id).pow n |>.mul XiC_differentiable).analyticAt w
  refine hL.eqOn_of_preconnected_of_frequently_eq hR isPreconnected_univ (mem_univ 0) ?_ (mem_univ z)
  have htend : Tendsto (fun m : ℕ => (((1 : ℝ) / (m + 1) : ℝ) : ℂ)) atTop (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall fun m => ?_⟩
    · have := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
      rw [← Complex.ofReal_zero]
      exact (Complex.continuous_ofReal.tendsto 0).comp this
    · simp only [mem_compl_iff, mem_singleton_iff, Complex.ofReal_eq_zero]
      positivity
  exact htend.frequently (Frequently.of_forall fun m => sourceTransform_thetaDerivSourceC_ofReal n _)

/-! ## The sharpness packets `t k^{(4m)}` -/

/-- The divisor-preserving perturbation `u = t k^{(4m)}`. -/
def thetaCapacityPacket (m : ℕ) (t : ℝ) (x : ℝ) : ℂ := (t : ℂ) * thetaDerivSourceC (4 * m) x

theorem sourceTransform_thetaCapacityPacket (m : ℕ) (t : ℝ) (z : ℂ) :
    sourceTransform (thetaCapacityPacket m t) z = t * z ^ (4 * m) * XiC z := by
  show sourceTransform (fun x => (t : ℂ) * thetaDerivSourceC (4 * m) x) z = _
  rw [sourceTransform_const_mul, sourceTransform_thetaDerivSourceC, mul_pow,
    pow_mul, Complex.I_pow_four, one_pow, one_mul]
  ring

/-- The packet transform `t z^{4m} F(z)` carries the complete Xi divisor with multiplicities. -/
theorem analyticOrderAt_XiC_le_thetaCapacityPacket (m : ℕ) (t : ℝ) (z : ℂ) :
    analyticOrderAt XiC z ≤ analyticOrderAt (sourceTransform (thetaCapacityPacket m t)) z := by
  have hfun : sourceTransform (thetaCapacityPacket m t) = (fun w => (t : ℂ) * w ^ (4 * m)) * XiC :=
    funext fun w => sourceTransform_thetaCapacityPacket m t w
  rw [hfun, analyticOrderAt_mul (by fun_prop) (XiC_differentiable.analyticAt z)]
  exact le_add_self

/-- **The packets obey the critical tail bound at `b = 2` for every `a < π`.** -/
theorem exists_norm_thetaCapacityPacket_le (m : ℕ) (t : ℝ) {a : ℝ} (ha : a < Real.pi) :
    ∃ C : ℝ, ∀ x, ‖thetaCapacityPacket m t x‖ ≤ C * Real.exp (-a * Real.exp (2 * |x|)) := by
  obtain ⟨C₀, D, hC₀, hD, hbound⟩ := exists_abs_iteratedDeriv_thetaCuspFullSource_le_gaussian (4 * m)
  have hπa : 0 < Real.pi - a := by linarith
  refine ⟨|t| * C₀ * Real.exp (D ^ 2 / (8 * (Real.pi - a))), fun x => ?_⟩
  have habs : |iteratedDeriv (4 * m) thetaCuspFullSource x| =
      |iteratedDeriv (4 * m) thetaCuspFullSource (|x|)| := by
    rcases le_or_gt 0 x with hx | hx
    · rw [abs_of_nonneg hx]
    · rw [abs_of_neg hx, iteratedDeriv_thetaCuspFullSource_neg, abs_mul, abs_pow, abs_neg,
        abs_one, one_pow, one_mul]
  have hk := hbound |x| (abs_nonneg x)
  rw [← habs] at hk
  set y := |x|
  have hy : 0 ≤ y := abs_nonneg x
  have hexp2 : 2 * y ^ 2 ≤ Real.exp (2 * y) := by
    have := Real.quadratic_le_exp_of_nonneg (show 0 ≤ 2 * y by positivity)
    nlinarith
  have hquad : D * y - (Real.pi - a) * Real.exp (2 * y) ≤ D ^ 2 / (8 * (Real.pi - a)) := by
    have h1 : D * y - (Real.pi - a) * Real.exp (2 * y) ≤ D * y - (Real.pi - a) * (2 * y ^ 2) := by
      nlinarith
    have h2 : D * y - (Real.pi - a) * (2 * y ^ 2) ≤ D ^ 2 / (8 * (Real.pi - a)) := by
      rw [le_div_iff₀ (by positivity)]
      nlinarith [sq_nonneg (4 * (Real.pi - a) * y - D)]
    linarith
  have hkey : Real.exp (D * y) * Real.exp (-Real.pi * Real.exp (2 * y)) ≤
      Real.exp (D ^ 2 / (8 * (Real.pi - a))) * Real.exp (-a * Real.exp (2 * y)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith)
  rw [thetaCapacityPacket, thetaDerivSourceC, norm_mul, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs]
  calc |t| * |iteratedDeriv (4 * m) thetaCuspFullSource x| ≤
        |t| * (C₀ * Real.exp (D * y) * Real.exp (-Real.pi * Real.exp (2 * y))) :=
        mul_le_mul_of_nonneg_left hk (abs_nonneg t)
    _ = |t| * C₀ * (Real.exp (D * y) * Real.exp (-Real.pi * Real.exp (2 * y))) := by ring
    _ ≤ |t| * C₀ * (Real.exp (D ^ 2 / (8 * (Real.pi - a))) * Real.exp (-a * Real.exp (2 * y))) :=
        mul_le_mul_of_nonneg_left hkey (by positivity)
    _ = _ := by ring

/-- **No faster tail.** For `t ≠ 0` the packet `t k^{(4m)}` obeys no bound
`C exp(-a e^{b|x|})` with `a > 0` and `b > 2`: the exponent `2` is sharp. -/
theorem not_doubleExp_bound_thetaCapacityPacket (m : ℕ) {t : ℝ} (ht : t ≠ 0) {a b C : ℝ}
    (ha : 0 < a) (hb : 2 < b) :
    ¬ ∀ x, ‖thetaCapacityPacket m t x‖ ≤ C * Real.exp (-a * Real.exp (b * |x|)) := by
  intro hC
  have hcont : Continuous (thetaCapacityPacket m t) :=
    continuous_const.mul (continuous_thetaDerivSourceC _)
  have hzero := eq_zero_of_doubleExp_divisor_of_continuous hcont ha hb hC
    (analyticOrderAt_XiC_le_thetaCapacityPacket m t)
  have hI := sourceTransform_thetaCapacityPacket m t I
  rw [hzero] at hI
  have h0 : sourceTransform (0 : ℝ → ℂ) I = 0 := by simp [sourceTransform]
  rw [h0, pow_mul, Complex.I_pow_four, one_pow, mul_one, show XiC I = XiC (I * ((1 : ℝ) : ℂ)) by simp,
    XiC_I_mul] at hI
  have hL := thetaSourceLaplace_pos 1
  have : (t : ℂ) * (thetaSourceLaplace 1 : ℂ) ≠ 0 :=
    mul_ne_zero (Complex.ofReal_ne_zero.mpr ht) (Complex.ofReal_ne_zero.mpr hL.ne')
  exact this hI.symm

end

end RHTower
