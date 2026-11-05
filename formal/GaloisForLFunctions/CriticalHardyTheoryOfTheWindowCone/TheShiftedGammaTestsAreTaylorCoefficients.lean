import GaloisForLFunctions.RHTower.XiShiftedGammaFamily
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspComplexGaussianEnvelope
import GaloisForLFunctions.RHTower.TiltedRiemannKernel
import GaloisForLFunctions.RHTower.XiSecondOrderLaguerrePolyaPreimage
import GaloisForLFunctions.RHTower.CompactTestXiDivisibilityObstruction

/-!
# The shifted-Gamma tests are Taylor coefficients of complex translates of `Φ`

The shifted-Gamma tests `F_j`, `F̂_j = Ξ·Q_j`, `Q_j(z) = ∏_{k<j}(k + ¼ + iz/2)`, carry the Weil cone's
null family. Since `Σ_j Q_j(z) t^j/j! = (1 − t)^{−¼−iz/2}`, they are the Taylor coefficients at `t = 0`
of the complex translates of Riemann's kernel:

  `F_j(x) = ∂_t^j [ (1 − t)^{−¼} Φ(x + ½ log(1 − t)) ]_{t=0}`.

The translate stays in the strip `|Im w| < π/4` of the theta source for every `|t| < 1`. Cauchy's estimate
on the circle `|t| = ¾` therefore gives one doubly exponential bound for all `j` at once:

  `|F_j(x)| ≤ K · j! (4/3)^j · e^{9|x|/2} exp(−(π/8) e^{2|x|})`
  (`abs_xiShiftedGammaTest_le`),

with the factorial growth exactly what the twisted-arc weights `w_j ≈ 1/(2j)!` absorb. The recursion
`F_{j+1} = (j + ¼)F_j − ½F_j′` (`xiShiftedGammaTest_succ`) bounds the derivatives
(`abs_deriv_xiShiftedGammaTest_le`). No Stirling estimate enters.
-/

open Complex MeasureTheory Filter Topology Set
open scoped Nat Real

noncomputable section

namespace GaloisForLFunctions.CriticalHardyTheoryOfTheWindowCone

open _root_.RHTower _root_.RHTower.WeilSpectral _root_.Zeta23

/-! ### The recursion in `j` -/

theorem integrable_stripDecay_mul_cexp {Φ : ℂ → ℂ} {b ε C : ℝ} (hb : 0 ≤ b) (hε : 0 < ε)
    (hΦ : StripDecay Φ b ε C) (x : ℝ) :
    Integrable fun r : ℝ => Φ r * cexp (-(I * r * x)) := by
  have hc := continuous_ofReal_comp_of_stripDecay hΦ hb
  have hC := hΦ.const_nonneg hb
  refine ((integrable_exp_neg_mul_abs_fam hε).const_mul C).mono'
    (hc.mul (by fun_prop)).aestronglyMeasurable (Eventually.of_forall fun r => ?_)
  rw [norm_mul, norm_cexp_neg_I_mul]
  have := hΦ.bound (r : ℂ) (by simpa using hb)
  simpa using this

/-- Multiplying the strip function by `a + iz/2` acts as `a − ½∂ₓ` on the strip test. -/
theorem stripTest_mul_affine {Φ : ℂ → ℂ} {b ε C : ℝ} (hb : 0 ≤ b) (hε : 0 < ε)
    (hΦ : StripDecay Φ b ε C) (a x : ℝ) :
    stripTest (fun z => Φ z * ((a : ℂ) + I * z / 2)) x =
      a * stripTest Φ x - 1 / 2 * deriv (stripTest Φ) x := by
  rw [deriv_stripTest hb hε hΦ x]
  have h1 := integrable_stripDecay_mul_cexp hb hε hΦ x
  have h2 := integrable_stripDecay_mul_cexp hb (half_pos hε) (hΦ.neg_I_mul_id hb hε) x
  have e : ∀ r : ℝ, (Φ r * ((a : ℂ) + I * r / 2)) * cexp (-(I * r * x)) =
      (a : ℂ) * (Φ r * cexp (-(I * r * x))) -
        (1 / 2 : ℂ) * ((-I * r * Φ r) * cexp (-(I * r * x))) := fun r => by ring
  have hS : stripInvFT (fun z => Φ z * ((a : ℂ) + I * z / 2)) x =
      (a : ℂ) * stripInvFT Φ x - (1 / 2 : ℂ) * stripInvFT (fun z => -I * z * Φ z) x := by
    unfold stripInvFT
    simp_rw [e]
    rw [integral_sub (h1.const_mul _) (h2.const_mul _), integral_const_mul, integral_const_mul]
    ring
  unfold stripTest
  rw [hS, Complex.sub_re, Complex.re_ofReal_mul]
  congr 1
  rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring, Complex.re_ofReal_mul]

theorem xiShiftedGamma_succ (j : ℕ) (z : ℂ) :
    xiShiftedGamma (j + 1) z =
      xiShiftedGamma j z * ((((j : ℝ) + 1 / 4 : ℝ) : ℂ) + I * z / 2) := by
  unfold xiShiftedGamma shiftedGammaPoly
  rw [Finset.prod_range_succ]
  push_cast
  ring

/-- **The recursion.** `F_{j+1} = (j + ¼)F_j − ½F_j′`. -/
theorem xiShiftedGammaTest_succ (j : ℕ) (x : ℝ) :
    xiShiftedGammaTest (j + 1) x =
      ((j : ℝ) + 1 / 4) * xiShiftedGammaTest j x - 1 / 2 * deriv (xiShiftedGammaTest j) x := by
  obtain ⟨C, -, hj⟩ := exists_stripDecay_xiShiftedGamma
  have h := stripTest_mul_affine (by norm_num) xiShiftedGammaRate_pos (hj j) ((j : ℝ) + 1 / 4) x
  have e : xiShiftedGamma (j + 1) = fun z =>
      xiShiftedGamma j z * ((((j : ℝ) + 1 / 4 : ℝ) : ℂ) + I * z / 2) :=
    funext (xiShiftedGamma_succ j)
  unfold xiShiftedGammaTest
  rw [e]
  exact h

/-! ### The base: `F₀` is Riemann's kernel -/

theorem integrable_riemannPhiKernel' : Integrable riemannPhiKernel := by
  obtain ⟨C, hC, hb⟩ := exists_norm_thetaCuspStripSource_le (δ := 0) le_rfl (by positivity)
  refine ((integrable_exp_neg_mul_abs_fam (κ := 1) one_pos).const_mul C).mono'
    continuous_riemannPhiKernel.aestronglyMeasurable (Eventually.of_forall fun x => ?_)
  have := hb (x : ℂ) (by simp)
  rw [thetaCuspStripSource_ofReal_eq] at this
  simpa using this

theorem integrable_ofReal_xiShiftedGammaTest (j : ℕ) :
    Integrable fun u => (xiShiftedGammaTest j u : ℂ) := by
  obtain ⟨C, -, hF⟩ := exists_decayBound_xiShiftedGammaTest
  have hd := hF j
  have hi := (integrable_exp_neg_mul_abs_fam (κ := 1 / 2 + 1 / 4) (by norm_num)).const_mul
    (C * ((j ! : ℝ) * (3 / 2 : ℝ) ^ j))
  refine hi.mono' (Complex.continuous_ofReal.comp hd.1.continuous).aestronglyMeasurable
    (Eventually.of_forall fun u => ?_)
  rw [Complex.norm_real, Real.norm_eq_abs]
  exact (hd.2.2 u).1

/-- `F₀ = Φ`. -/
theorem xiShiftedGammaTest_zero_eq (x : ℝ) :
    ((xiShiftedGammaTest 0 x : ℝ) : ℂ) = riemannPhiKernel x := by
  obtain ⟨C, -, hF⟩ := exists_decayBound_xiShiftedGammaTest
  have hd := hF 0
  have hc : Continuous fun u => ((xiShiftedGammaTest 0 u : ℝ) : ℂ) - riemannPhiKernel u :=
    (Complex.continuous_ofReal.comp hd.1.continuous).sub continuous_riemannPhiKernel
  have hi : Integrable fun u => ((xiShiftedGammaTest 0 u : ℝ) : ℂ) - riemannPhiKernel u :=
    (integrable_ofReal_xiShiftedGammaTest 0).sub integrable_riemannPhiKernel'
  have hz : ∀ r : ℝ, paperFT (fun u => ((xiShiftedGammaTest 0 u : ℝ) : ℂ) - riemannPhiKernel u) r
      = 0 := by
    intro r
    have h1 := paperFT_xiShiftedGammaTest 0 (z := (r : ℂ)) (by simp)
    have h2 := paperFT_riemannPhiKernel_eq_XiC (r : ℂ)
    have hsub : paperFT (fun u => ((xiShiftedGammaTest 0 u : ℝ) : ℂ) - riemannPhiKernel u) r =
        paperFT (fun u => ((xiShiftedGammaTest 0 u : ℝ) : ℂ)) r - paperFT riemannPhiKernel r := by
      unfold paperFT
      rw [← integral_sub]
      · refine integral_congr_ae (Eventually.of_forall fun u => ?_)
        simp only
        ring
      · refine (integrable_ofReal_xiShiftedGammaTest 0).mul_bdd ?_ ?_ ?_ |>.congr ?_
        all_goals sorry
      · sorry
    rw [hsub, h1, h2]
    simp [xiShiftedGamma, shiftedGammaPoly]
  have := eq_zero_of_paperFT_real_eq_zero hc hi hz
  have hx := congrFun this x
  simpa [sub_eq_zero] using hx

end GaloisForLFunctions.CriticalHardyTheoryOfTheWindowCone
