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
on the circle `|t| = 7/10` therefore gives one doubly exponential bound for all `j` at once:

  `|F_j(x)| ≤ K · j! (10/7)^j · e^{9|x|/2} exp(−(π/5) e^{2|x|})`
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
  have h := stripTest_mul_affine (b := 3 / 4) (by norm_num) xiShiftedGammaRate_pos (hj j)
    ((j : ℝ) + 1 / 4) x
  have e : xiShiftedGamma (j + 1) = fun z =>
      xiShiftedGamma j z * ((((j : ℝ) + 1 / 4 : ℝ) : ℂ) + I * z / 2) :=
    funext (xiShiftedGamma_succ j)
  unfold xiShiftedGammaTest
  rw [e]
  exact h

/-! ### The base: `F₀` is Riemann's kernel -/

theorem integrable_riemannPhiKernel' : Integrable riemannPhiKernel := by
  obtain ⟨C, hC, hb⟩ := exists_norm_thetaCuspStripSource_le (δ := 0) le_rfl
    (by simpa using Real.pi_pos)
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

theorem integrable_mul_cexp_real {f : ℝ → ℂ} (hf : Integrable f) (r : ℝ) :
    Integrable fun u : ℝ => f u * cexp (I * (r : ℂ) * u) := by
  refine hf.norm.mono' (hf.1.mul (Continuous.aestronglyMeasurable (by fun_prop)))
    (Eventually.of_forall fun u => ?_)
  rw [norm_mul, Complex.norm_exp]
  simp [Complex.mul_re]

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
    have h2 := _root_.RHTower.Littlewood.paperFT_riemannPhiKernel_eq_XiC (r : ℂ)
    have hsub : paperFT (fun u => ((xiShiftedGammaTest 0 u : ℝ) : ℂ) - riemannPhiKernel u) r =
        paperFT (fun u => ((xiShiftedGammaTest 0 u : ℝ) : ℂ)) r - paperFT riemannPhiKernel r := by
      unfold paperFT
      rw [← integral_sub (integrable_mul_cexp_real (integrable_ofReal_xiShiftedGammaTest 0) r)
        (integrable_mul_cexp_real integrable_riemannPhiKernel' r)]
      refine integral_congr_ae (Eventually.of_forall fun u => ?_)
      simp only
      ring
    rw [hsub, h1, h2]
    simp [xiShiftedGamma, shiftedGammaPoly]
  have := _root_.RHTower.CompactTestXiDivisibility.eq_zero_of_paperFT_real_eq_zero hc hi hz
  have hx := congrFun this x
  simpa [sub_eq_zero] using hx

/-! ### The complex jets of the theta source -/

/-- `S₀ = Φ` on the strip and `S_{j+1} = (j + ¼)S_j − ½S_j′`. On the real line `S_j = F_j`. -/
def thetaJet : ℕ → ℂ → ℂ
  | 0 => thetaCuspStripSource
  | j + 1 => fun w => (((j : ℝ) + 1 / 4 : ℝ) : ℂ) * thetaJet j w - 1 / 2 * deriv (thetaJet j) w

theorem analyticOnNhd_thetaJet (j : ℕ) : AnalyticOnNhd ℂ (thetaJet j) thetaCuspStrip := by
  induction j with
  | zero => exact analyticOnNhd_thetaCuspStripSource
  | succ j ih =>
    exact (analyticOnNhd_const.mul ih).sub (analyticOnNhd_const.mul ih.deriv)

theorem ofReal_mem_thetaCuspStrip (x : ℝ) : (x : ℂ) ∈ thetaCuspStrip := by
  simp only [thetaCuspStrip, mem_setOf_eq, Complex.ofReal_im, abs_zero]
  positivity

theorem thetaJet_ofReal (j : ℕ) (x : ℝ) : thetaJet j (x : ℂ) = (xiShiftedGammaTest j x : ℂ) := by
  induction j generalizing x with
  | zero =>
    rw [xiShiftedGammaTest_zero_eq]
    exact thetaCuspStripSource_ofReal_eq x
  | succ j ih =>
    have hd : HasDerivAt (thetaJet j) (deriv (thetaJet j) x) (x : ℂ) :=
      (analyticOnNhd_thetaJet j _ (ofReal_mem_thetaCuspStrip x)).differentiableAt.hasDerivAt
    have hr := hd.comp_ofReal
    have he : (fun y : ℝ => thetaJet j (y : ℂ)) = fun y => ((xiShiftedGammaTest j y : ℝ) : ℂ) :=
      funext ih
    rw [he] at hr
    obtain ⟨C, -, hF⟩ := exists_decayBound_xiShiftedGammaTest
    have hF2 : HasDerivAt (xiShiftedGammaTest j) (deriv (xiShiftedGammaTest j) x) x :=
      ((hF j).1.differentiable (by norm_num) x).hasDerivAt
    have huniq := hr.unique hF2.ofReal_comp
    change (((j : ℝ) + 1 / 4 : ℝ) : ℂ) * thetaJet j x - 1 / 2 * deriv (thetaJet j) x = _
    rw [ih, huniq, xiShiftedGammaTest_succ]
    push_cast
    ring

/-! ### The generating function -/

/-- `h_j(t) = (1 − t)^{−¼−j} S_j(x + ½ log(1 − t))`, with `h_j′ = h_{j+1}`. -/
def thetaGen (j : ℕ) (x : ℝ) (t : ℂ) : ℂ :=
  cexp (-(((j : ℝ) + 1 / 4 : ℝ) : ℂ) * Complex.log (1 - t)) *
    thetaJet j ((x : ℂ) + 1 / 2 * Complex.log (1 - t))

theorem one_sub_re_pos {t : ℂ} (ht : ‖t‖ < 1) : 0 < (1 - t).re := by
  have := (Complex.re_le_norm t).trans_lt ht
  simp only [Complex.sub_re, Complex.one_re]
  linarith

theorem one_sub_mem_slitPlane {t : ℂ} (ht : ‖t‖ < 1) : 1 - t ∈ Complex.slitPlane :=
  Or.inl (one_sub_re_pos ht)

theorem logShift_mem_strip (x : ℝ) {t : ℂ} (ht : ‖t‖ < 1) :
    (x : ℂ) + 1 / 2 * Complex.log (1 - t) ∈ thetaCuspStrip := by
  have h := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl (one_sub_re_pos ht))
  simp only [thetaCuspStrip, mem_setOf_eq]
  have him : ((x : ℂ) + 1 / 2 * Complex.log (1 - t)).im = 1 / 2 * (1 - t).arg := by
    simp [Complex.log_im]
  rw [him, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  linarith

theorem hasDerivAt_thetaGen (j : ℕ) (x : ℝ) {t : ℂ} (ht : ‖t‖ < 1) :
    HasDerivAt (thetaGen j x) (thetaGen (j + 1) x t) t := by
  have hs := one_sub_mem_slitPlane ht
  have hne : 1 - t ≠ 0 := Complex.slitPlane_ne_zero hs
  have hE : HasDerivAt (fun s : ℂ => Complex.log (1 - s)) (-1 / (1 - t)) t := by
    have h1 : HasDerivAt (fun s : ℂ => 1 - s) (-1) t := by
      simpa using (hasDerivAt_id t).const_sub (1 : ℂ)
    exact h1.clog hs
  set E := Complex.log (1 - t) with hEdef
  set c : ℂ := -(((j : ℝ) + 1 / 4 : ℝ) : ℂ) with hc
  have hexp : HasDerivAt (fun s : ℂ => cexp (c * Complex.log (1 - s)))
      (cexp (c * E) * (c * (-1 / (1 - t)))) t := (hE.const_mul c).cexp
  have hw : HasDerivAt (fun s : ℂ => (x : ℂ) + 1 / 2 * Complex.log (1 - s))
      (1 / 2 * (-1 / (1 - t))) t := (hE.const_mul (1 / 2 : ℂ)).const_add (x : ℂ)
  have hmem := logShift_mem_strip x ht
  have hS : HasDerivAt (thetaJet j) (deriv (thetaJet j) ((x : ℂ) + 1 / 2 * E))
      ((x : ℂ) + 1 / 2 * E) := (analyticOnNhd_thetaJet j _ hmem).differentiableAt.hasDerivAt
  have hcomp := hS.comp t hw
  have hmul := hexp.mul hcomp
  have hinv : cexp (-E) = (1 - t)⁻¹ := by rw [Complex.exp_neg, hEdef, Complex.exp_log hne]
  have hshift : cexp (-((((j + 1 : ℕ) : ℝ) + 1 / 4 : ℝ) : ℂ) * E) = cexp (c * E) * (1 - t)⁻¹ := by
    rw [← hinv, ← Complex.exp_add]
    congr 1
    rw [hc]
    push_cast
    ring
  have hval : thetaGen (j + 1) x t =
      cexp (c * E) * (c * (-1 / (1 - t))) * thetaJet j ((x : ℂ) + 1 / 2 * E) +
        cexp (c * E) * (deriv (thetaJet j) ((x : ℂ) + 1 / 2 * E) * (1 / 2 * (-1 / (1 - t)))) := by
    unfold thetaGen
    rw [hshift]
    change _ * ((((j : ℝ) + 1 / 4 : ℝ) : ℂ) * thetaJet j ((x : ℂ) + 1 / 2 * E) -
      1 / 2 * deriv (thetaJet j) ((x : ℂ) + 1 / 2 * E)) = _
    rw [hc]
    field_simp
    ring
  rw [hval]
  exact hmul

theorem iteratedDeriv_thetaGen (j : ℕ) (x : ℝ) {t : ℂ} (ht : ‖t‖ < 1) :
    iteratedDeriv j (thetaGen 0 x) t = thetaGen j x t := by
  induction j generalizing t with
  | zero => simp
  | succ j ih =>
    rw [iteratedDeriv_succ]
    have hev : iteratedDeriv j (thetaGen 0 x) =ᶠ[𝓝 t] thetaGen j x := by
      filter_upwards [Metric.isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr ht)] with s hs
      exact ih (mem_ball_zero_iff.mp hs)
    rw [hev.deriv_eq]
    exact (hasDerivAt_thetaGen j x ht).deriv

theorem thetaGen_at_zero (j : ℕ) (x : ℝ) : thetaGen j x 0 = (xiShiftedGammaTest j x : ℂ) := by
  simp [thetaGen, thetaJet_ofReal]

/-! ### The bound on the circle `|t| = 7/10` -/

/-- The doubly exponential profile `e^{9|x|/2} exp(−(π/5) e^{2|x|})`. -/
def shiftedGammaEnvelope (x : ℝ) : ℝ :=
  Real.exp (9 * |x| / 2) * Real.exp (-(Real.pi / 5) * Real.exp (2 * |x|))

theorem shiftedGammaEnvelope_pos (x : ℝ) : 0 < shiftedGammaEnvelope x := by
  unfold shiftedGammaEnvelope
  positivity

/-- The constant of the Cauchy estimate. -/
def shiftedGammaConstant : ℝ :=
  2 * thetaStripGaussianConstant (Real.pi / 8) * Real.exp (9 / 4 * Real.log (10 / 3))

theorem shiftedGammaConstant_nonneg : 0 ≤ shiftedGammaConstant := by
  have := thetaStripGaussianConstant_nonneg (Real.pi / 8)
  unfold shiftedGammaConstant
  positivity

/-- On `|t| = 7/10` the argument of `1 − t` is at most `π/4`. -/
theorem abs_arg_one_sub_le {t : ℂ} (ht : ‖t‖ = 7 / 10) : |(1 - t).arg| ≤ Real.pi / 4 := by
  have hlt : ‖t‖ < 1 := by rw [ht]; norm_num
  have hre := one_sub_re_pos hlt
  have hne : 1 - t ≠ 0 := Complex.slitPlane_ne_zero (one_sub_mem_slitPlane hlt)
  have hn : 0 < ‖1 - t‖ := norm_pos_iff.mpr hne
  have hsq : t.re ^ 2 + t.im ^ 2 = 49 / 100 := by
    have := Complex.sq_norm t
    rw [ht, Complex.normSq_apply] at this
    nlinarith
  have hnsq : ‖1 - t‖ ^ 2 = (1 - t.re) ^ 2 + t.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im]
    ring
  have hre' : 0 < 1 - t.re := by simpa using hre
  have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hs0 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hhalf : ‖1 - t‖ ≤ Real.sqrt 2 * (1 - t.re) := by
    refine abs_le_of_sq_le_sq' ?_ (by positivity) |>.2
    have e : (Real.sqrt 2 * (1 - t.re)) ^ 2 = 2 * (1 - t.re) ^ 2 := by
      rw [mul_pow, sq (Real.sqrt 2), hs2]
    rw [e, hnsq]
    nlinarith [sq_nonneg (2 * t.re - 1)]
  have hcos : Real.sqrt 2 / 2 ≤ Real.cos (1 - t).arg := by
    rw [Complex.cos_arg hne, le_div_iff₀ hn]
    simp only [Complex.sub_re, Complex.one_re]
    have h := mul_le_mul_of_nonneg_left hhalf (by positivity : (0 : ℝ) ≤ Real.sqrt 2 / 2)
    have e : Real.sqrt 2 / 2 * (Real.sqrt 2 * (1 - t.re)) = 1 - t.re := by
      calc _ = (Real.sqrt 2 * Real.sqrt 2) / 2 * (1 - t.re) := by ring
        _ = _ := by rw [hs2]; ring
    linarith
  by_contra hcon
  rw [not_le] at hcon
  have hpi := Complex.abs_arg_le_pi (1 - t)
  have hlt2 := Real.cos_lt_cos_of_nonneg_of_le_pi (x := Real.pi / 4) (y := |(1 - t).arg|)
    (by positivity) hpi hcon
  rw [Real.cos_abs, Real.cos_pi_div_four] at hlt2
  linarith

theorem norm_thetaGen_zero_le (x : ℝ) {t : ℂ} (ht : ‖t‖ = 7 / 10) :
    ‖thetaGen 0 x t‖ ≤ shiftedGammaConstant * shiftedGammaEnvelope x := by
  have hlt : ‖t‖ < 1 := by rw [ht]; norm_num
  have hne : 1 - t ≠ 0 := Complex.slitPlane_ne_zero (one_sub_mem_slitPlane hlt)
  have hn : 0 < ‖1 - t‖ := norm_pos_iff.mpr hne
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ, ℓ = Real.log (10 / 3) := ⟨_, rfl⟩
  have hℓ0 : 0 < ℓ := by rw [hℓ]; exact Real.log_pos (by norm_num)
  have hlow : (3 / 10 : ℝ) ≤ ‖1 - t‖ := by
    have := norm_sub_norm_le (1 : ℂ) t
    rw [norm_one, ht] at this
    linarith
  have hhigh : ‖1 - t‖ ≤ 10 / 3 := by
    have := norm_sub_le (1 : ℂ) t
    rw [norm_one, ht] at this
    linarith
  set E := Complex.log (1 - t) with hE
  have hEre : E.re = Real.log ‖1 - t‖ := Complex.log_re _
  have hEim : E.im = (1 - t).arg := Complex.log_im _
  have hElow : -ℓ ≤ E.re := by
    rw [hEre, hℓ]
    have h := Real.log_le_log (by norm_num) hlow
    have e : Real.log (3 / 10) = -Real.log (10 / 3) := by
      rw [← Real.log_inv]
      norm_num
    linarith
  have hEhigh : E.re ≤ ℓ := by
    rw [hEre, hℓ]
    exact Real.log_le_log hn hhigh
  have hℓ2 : ℓ ≤ 4 * Real.log 2 := by
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 10 / 3) (by norm_num : (10 / 3 : ℝ) ≤ 16)
    have e : Real.log 16 = 4 * Real.log 2 := by
      rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]
      push_cast
      ring
    rw [hℓ]
    linarith
  -- the prefactor
  have hpre : ‖cexp (-(((( (0 : ℕ) : ℝ)) + 1 / 4 : ℝ) : ℂ) * E)‖ ≤ 2 := by
    rw [Complex.norm_exp]
    have hre : (-(((( (0 : ℕ) : ℝ)) + 1 / 4 : ℝ) : ℂ) * E).re = -(1 / 4 * E.re) := by
      simp [Complex.mul_re]
    rw [hre]
    calc Real.exp (-(1 / 4 * E.re)) ≤ Real.exp (Real.log 2) :=
          Real.exp_le_exp.mpr (by linarith)
      _ = 2 := Real.exp_log (by norm_num)
  -- the point in the strip
  set w : ℂ := (x : ℂ) + 1 / 2 * E with hw
  have hwre : w.re = x + 1 / 2 * E.re := by simp [hw]
  have hwim : w.im = 1 / 2 * E.im := by simp [hw]
  have him : |w.im| ≤ Real.pi / 8 := by
    rw [hwim, hEim, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    linarith [abs_arg_one_sub_le ht]
  have hδ : 2 * (Real.pi / 8) < Real.pi / 2 := by linarith [Real.pi_pos]
  have hS := norm_thetaCuspStripSource_le_gaussian_envelope (Real.pi / 8) (by positivity) hδ w him
  have hEabs : |E.re| ≤ ℓ := abs_le.mpr ⟨hElow, hEhigh⟩
  have hre1 : |w.re| ≤ |x| + ℓ / 2 := by
    rw [hwre]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    linarith
  have hre2 : |x| - ℓ / 2 ≤ |w.re| := by
    have h := abs_sub_abs_le_abs_sub x (-(1 / 2 * E.re))
    rw [sub_neg_eq_add, ← hwre, abs_neg, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] at h
    linarith
  have hcosδ : Real.cos (2 * (Real.pi / 8)) = Real.sqrt 2 / 2 := by
    rw [show 2 * (Real.pi / 8) = Real.pi / 4 by ring, Real.cos_pi_div_four]
  have henv : thetaStripGaussianEnvelope (Real.pi / 8) w.re ≤
      Real.exp (9 / 4 * ℓ) * shiftedGammaEnvelope x := by
    unfold thetaStripGaussianEnvelope shiftedGammaEnvelope
    rw [hcosδ, ← mul_assoc]
    refine mul_le_mul ?_ ?_ (Real.exp_pos _).le (by positivity)
    · rw [← Real.exp_add]
      exact Real.exp_le_exp.mpr (by linarith)
    · refine Real.exp_le_exp.mpr ?_
      have h4 : Real.exp (2 * |x|) * (3 / 10) ≤ Real.exp (2 * |w.re|) := by
        have e4 : Real.exp (2 * |x|) * (3 / 10) = Real.exp (2 * (|x| - ℓ / 2)) := by
          rw [show 2 * (|x| - ℓ / 2) = 2 * |x| - ℓ by ring, Real.exp_sub, hℓ,
            Real.exp_log (by norm_num)]
          ring
        rw [e4]
        exact Real.exp_le_exp.mpr (by linarith)
      have hπ := Real.pi_pos
      have hs2 : (4 : ℝ) / 3 ≤ Real.sqrt 2 := by
        refine Real.le_sqrt_of_sq_le ?_
        norm_num
      have hE0 := Real.exp_pos (2 * |x|)
      have hstep : Real.pi / 5 * Real.exp (2 * |x|) ≤
          Real.pi * (Real.sqrt 2 / 2) * (Real.exp (2 * |x|) * (3 / 10)) := by
        have : (1 : ℝ) / 5 ≤ Real.sqrt 2 / 2 * (3 / 10) := by linarith
        have h5 := mul_le_mul_of_nonneg_right this (mul_pos hπ hE0).le
        nlinarith
      have hstep2 : Real.pi * (Real.sqrt 2 / 2) * (Real.exp (2 * |x|) * (3 / 10)) ≤
          Real.pi * (Real.sqrt 2 / 2) * Real.exp (2 * |w.re|) :=
        mul_le_mul_of_nonneg_left h4 (by positivity)
      linarith
  have hC := thetaStripGaussianConstant_nonneg (Real.pi / 8)
  unfold thetaGen
  change ‖cexp (-(((( (0 : ℕ) : ℝ)) + 1 / 4 : ℝ) : ℂ) * E) * thetaCuspStripSource w‖ ≤ _
  rw [norm_mul]
  calc _ ≤ 2 * (thetaStripGaussianConstant (Real.pi / 8) *
        (Real.exp (9 / 4 * ℓ) * shiftedGammaEnvelope x)) :=
        mul_le_mul hpre (hS.trans (mul_le_mul_of_nonneg_left henv hC)) (norm_nonneg _)
          (by norm_num)
    _ = _ := by unfold shiftedGammaConstant; rw [← hℓ]; ring

/-! ### The doubly exponential bound -/

/-- **One doubly exponential bound for every shifted-Gamma test.**
`|F_j(x)| ≤ K j! (10/7)^j e^{9|x|/2} exp(−(π/5) e^{2|x|})`. -/
theorem abs_xiShiftedGammaTest_le (j : ℕ) (x : ℝ) :
    |xiShiftedGammaTest j x| ≤
      shiftedGammaConstant * ((j ! : ℝ) * (10 / 7 : ℝ) ^ j) * shiftedGammaEnvelope x := by
  have hdiff : DifferentiableOn ℂ (thetaGen 0 x) (Metric.ball (0 : ℂ) 1) := fun t ht =>
    (hasDerivAt_thetaGen 0 x (mem_ball_zero_iff.mp ht)).differentiableAt.differentiableWithinAt
  have hcl : Metric.closedBall (0 : ℂ) (7 / 10) ⊆ Metric.ball (0 : ℂ) 1 :=
    Metric.closedBall_subset_ball (by norm_num)
  have hC := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le j (by norm_num : (0 : ℝ) < 7 / 10)
    (hdiff.diffContOnCl_ball hcl) (fun t ht => norm_thetaGen_zero_le x (by simpa using ht))
  rw [iteratedDeriv_thetaGen j x (by simp), thetaGen_at_zero, Complex.norm_real,
    Real.norm_eq_abs] at hC
  refine hC.trans (le_of_eq ?_)
  have e : ((10 / 7 : ℝ)) ^ j = ((7 / 10 : ℝ) ^ j)⁻¹ := by
    rw [← inv_pow]; norm_num
  rw [e]
  field_simp

/-- The derivative bound, from the recursion:
`|F_j′(x)| ≤ 5K (j+1)! (10/7)^j e^{9|x|/2} exp(−(π/5) e^{2|x|})`. -/
theorem abs_deriv_xiShiftedGammaTest_le (j : ℕ) (x : ℝ) :
    |deriv (xiShiftedGammaTest j) x| ≤
      5 * shiftedGammaConstant * (((j + 1)! : ℝ) * (10 / 7 : ℝ) ^ j) * shiftedGammaEnvelope x := by
  have hr := xiShiftedGammaTest_succ j x
  have he : deriv (xiShiftedGammaTest j) x =
      2 * (((j : ℝ) + 1 / 4) * xiShiftedGammaTest j x) - 2 * xiShiftedGammaTest (j + 1) x := by
    rw [hr]; ring
  have h0 := abs_xiShiftedGammaTest_le j x
  have h1 := abs_xiShiftedGammaTest_le (j + 1) x
  have hK := shiftedGammaConstant_nonneg
  have hG := (shiftedGammaEnvelope_pos x).le
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  set P : ℝ := shiftedGammaConstant * ((j ! : ℝ) * (10 / 7 : ℝ) ^ j) * shiftedGammaEnvelope x with hP
  have hP0 : 0 ≤ P := by positivity
  have hfac : (((j + 1)! : ℝ)) = ((j : ℝ) + 1) * (j ! : ℝ) := by
    rw [Nat.factorial_succ]; push_cast; ring
  have h1' : |xiShiftedGammaTest (j + 1) x| ≤ ((j : ℝ) + 1) * (10 / 7) * P := by
    refine h1.trans (le_of_eq ?_)
    rw [hfac, hP, pow_succ]
    ring
  have hgoal : 5 * shiftedGammaConstant * (((j + 1)! : ℝ) * (10 / 7 : ℝ) ^ j) *
      shiftedGammaEnvelope x = 5 * (((j : ℝ) + 1) * P) := by
    rw [hfac, hP]; ring
  rw [he, hgoal]
  refine (abs_sub _ _).trans ?_
  rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ (j : ℝ) + 1 / 4)]
  have hj1 : (j : ℝ) + 1 / 4 ≤ (j : ℝ) + 1 := by linarith
  have h2 : ((j : ℝ) + 1 / 4) * |xiShiftedGammaTest j x| ≤ ((j : ℝ) + 1) * P :=
    mul_le_mul hj1 h0 (abs_nonneg _) (by positivity)
  nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ (j : ℝ) + 1) hP0]

end GaloisForLFunctions.CriticalHardyTheoryOfTheWindowCone
