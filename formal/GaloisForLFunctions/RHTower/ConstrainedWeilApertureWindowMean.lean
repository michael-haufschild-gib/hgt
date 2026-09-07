import GaloisForLFunctions.RHTower.ConstrainedWeilApertureDecay
import GaloisForLFunctions.RHTower.XiEndpointStrongHeightGap

/-!
# Aperture-window means of the twisted plateau family, and recurrent negativity

Let `Θ > 0` be the largest excess `|Re ρ − ½|` over all Xi zero copies, attained at a copy `q₀`
with spectral point `z₀ = γ₀ − i(Re ρ₀ − ½)`.  For the odd plateau profile `ψ_a` at aperture `a` and
the twisted odd test `cos(γ₀ x) ψ_a(x)`, the normalised form

`S(a) = e^{−2Θa} · Re Q(cos(γ₀ x) ψ_a)`

is the sum over the copies of the real parts of exact exponential polynomials in `a` with exponents
of nonpositive real part.  Its window integral over `[A, A + L]` (`A ≥ ½`) is at most
`−c L + 2 D`, where `c = (1/4) κ(Θ)² (γ₀² − Θ²)/(γ₀² + Θ²)² > 0` comes from the constant terms of the
copies at the top height with ordinate `±γ₀` (at least the copy `q₀` itself), and `D` is the total
decay norm, finite because the coefficients of every copy are bounded and `Σ_q |z_q|⁻² < ∞`.
Consequently, for every window length `L > 4D/c` and every position `A ≥ ½` there is an aperture
`a ∈ [A, A + L]` with

`Re Q(cos(γ₀ x) ψ_a) ≤ −(c/2) e^{2Θa} < 0`.

No hypothesis on the other zeros beyond `|Im z_q| ≤ Θ` is used: clustering of off-line zeros near
the top is handled by averaging in the aperture.  The ordinate bound `|Im ρ| > 9/2` for all Xi zeros
supplies `γ₀² > Θ²`.
-/

open MeasureTheory Complex Set intervalIntegral
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-! ## Ordinates are large -/

theorem nine_halves_le_abs_re_xiSpectralPoint (q : XiZeroCopy) :
    9 / 2 ≤ |(xiSpectralPoint q).re| := by
  have h := xiDivisorSupport_fortyOne_div_two_lt_im_sq q.1
  rw [xiSpectralPoint_re_eq_im]
  have h2 : (9 / 2 : ℝ) ^ 2 < |(q.1 : ℂ).im| ^ 2 := by rw [sq_abs]; linarith
  exact (lt_of_pow_lt_pow_left₀ 2 (abs_nonneg _) h2).le

theorem xiSpectralPoint_re_ne_zero (q : XiZeroCopy) : (xiSpectralPoint q).re ≠ 0 := by
  intro h
  have := nine_halves_le_abs_re_xiSpectralPoint q
  rw [h, abs_zero] at this
  linarith

/-! ## Mass of the plateau profile -/

theorem profileMass_plateauProfile_le {a : ℝ} (ha0 : 0 ≤ a) :
    profileMass (plateauProfile a ha0) ≤ 2 * a := by
  unfold profileMass
  have hzero : ∀ u ∉ Icc (-a) a, ‖(((plateauProfile a ha0) u : ℝ) : ℂ)‖ = 0 := by
    intro u hu
    rw [norm_eq_zero]
    refine (plateauProfile a ha0).ofReal_eq_zero_of_abs_gt ?_
    rw [mem_Icc, not_and_or, not_le, not_le] at hu
    rcases hu with hu | hu
    · rw [abs_of_neg (by linarith)]; linarith
    · rw [abs_of_pos (by linarith)]; exact hu
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
  have hcont : Continuous fun u : ℝ => ‖(((plateauProfile a ha0) u : ℝ) : ℂ)‖ :=
    (Complex.continuous_ofReal.comp (plateauProfile a ha0).continuous).norm
  calc ∫ u in Icc (-a) a, ‖(((plateauProfile a ha0) u : ℝ) : ℂ)‖
      ≤ ∫ u in Icc (-a) a, (1 : ℝ) := by
        refine setIntegral_mono_on hcont.integrableOn_Icc continuous_const.integrableOn_Icc
          measurableSet_Icc fun u _ => ?_
        rw [Complex.norm_real, Real.norm_eq_abs, plateauProfile_apply]
        exact abs_plateauProfileFun_le_one a u
    _ = 2 * a := by
        rw [setIntegral_const, smul_eq_mul, mul_one, Measure.real, Real.volume_Icc,
          ENNReal.toReal_ofReal (by linarith)]
        ring

/-! ## The normalised twisted form -/

/-- `S(a) = Σ'_q Re eval(normalised ray-term polynomial of q)(a)`. -/
def normalizedTwistedForm (Θ γ a : ℝ) : ℝ :=
  ∑' q : XiZeroCopy, (ExpPoly.eval (normalizedRayTermPoly Θ γ q) a).re

theorem cexp_neg_two_theta (Θ a : ℝ) :
    Complex.exp (-(2 * Θ : ℝ) * (a : ℂ)) = ((Real.exp (-(2 * Θ) * a) : ℝ) : ℂ) := by
  rw [Complex.ofReal_exp]
  congr 1
  push_cast
  ring

/-- `S(a) = e^{−2Θa} Re Q(cos(γx)ψ_a)` for `a ≥ ½`. -/
theorem normalizedTwistedForm_eq {a : ℝ} (ha : 1 / 2 ≤ a) (ha0 : 0 ≤ a) (Θ γ : ℝ) :
    normalizedTwistedForm Θ γ a
      = Real.exp (-(2 * Θ) * a)
        * (suzukiScrewSmoothForm (twistedOddTest (plateauProfile a ha0) γ)
            (twistedOddTest (plateauProfile a ha0) γ)).re := by
  unfold normalizedTwistedForm
  rw [re_suzukiScrewSmoothForm_twistedOddTest_eq_tsum_rayTerm, ← tsum_mul_left]
  refine tsum_congr fun q => ?_
  rw [eval_normalizedRayTermPoly ha ha0, cexp_neg_two_theta, Complex.re_ofReal_mul]

/-- Uniform bound of the ray terms on an aperture window. -/
theorem abs_re_eval_normalizedRayTermPoly_le {Θ γ a B : ℝ} (ha : 1 / 2 ≤ a) (haB : a ≤ B)
    (q : XiZeroCopy) (hq : |(xiSpectralPoint q).im| ≤ Θ) :
    ‖(ExpPoly.eval (normalizedRayTermPoly Θ γ q) a).re‖
      ≤ 4 * B ^ 2 * (1 / ‖xiSpectralPoint q‖ ^ 2) := by
  have ha0 : 0 ≤ a := by linarith
  rw [eval_normalizedRayTermPoly ha ha0, cexp_neg_two_theta, Complex.re_ofReal_mul,
    Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  have h1 := norm_twistedRayTerm_le (plateauProfile a ha0) ha0 γ q
  have h2 : |(twistedRayTerm (plateauProfile a ha0) γ q).re|
      ≤ ‖twistedRayTerm (plateauProfile a ha0) γ q‖ := Complex.abs_re_le_norm _
  have hmass := profileMass_plateauProfile_le ha0
  have hmass0 := profileMass_nonneg (plateauProfile a ha0)
  have hexp : Real.exp (-(2 * Θ) * a) * Real.exp (2 * a * |(xiSpectralPoint q).im|) ≤ 1 := by
    rw [← Real.exp_add]
    apply Real.exp_le_one_iff.mpr
    nlinarith [mul_nonneg ha0 (sub_nonneg.mpr hq)]
  have hz : 0 ≤ 1 / ‖xiSpectralPoint q‖ ^ 2 := by positivity
  have hE0 : 0 ≤ Real.exp (-(2 * Θ) * a) := (Real.exp_pos _).le
  have hsq : profileMass (plateauProfile a ha0) ^ 2 ≤ (2 * a) ^ 2 :=
    pow_le_pow_left₀ hmass0 hmass 2
  have hB : (2 * a) ^ 2 ≤ 4 * B ^ 2 := by nlinarith
  calc Real.exp (-(2 * Θ) * a) * |(twistedRayTerm (plateauProfile a ha0) γ q).re|
      ≤ Real.exp (-(2 * Θ) * a) * ‖twistedRayTerm (plateauProfile a ha0) γ q‖ :=
        mul_le_mul_of_nonneg_left h2 hE0
    _ ≤ Real.exp (-(2 * Θ) * a) * (Real.exp (2 * a * |(xiSpectralPoint q).im|)
          * profileMass (plateauProfile a ha0) ^ 2 * (1 / ‖xiSpectralPoint q‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left h1 hE0
    _ = (Real.exp (-(2 * Θ) * a) * Real.exp (2 * a * |(xiSpectralPoint q).im|))
          * (profileMass (plateauProfile a ha0) ^ 2 * (1 / ‖xiSpectralPoint q‖ ^ 2)) := by ring
    _ ≤ 1 * ((2 * a) ^ 2 * (1 / ‖xiSpectralPoint q‖ ^ 2)) := by
        refine mul_le_mul hexp (mul_le_mul_of_nonneg_right hsq hz) (by positivity) zero_le_one
    _ ≤ 1 * (4 * B ^ 2 * (1 / ‖xiSpectralPoint q‖ ^ 2)) := by
        gcongr
    _ = 4 * B ^ 2 * (1 / ‖xiSpectralPoint q‖ ^ 2) := one_mul _

theorem continuousOn_normalizedTwistedForm {Θ γ A B : ℝ} (hA : 1 / 2 ≤ A)
    (hall : ∀ q : XiZeroCopy, |(xiSpectralPoint q).im| ≤ Θ) :
    ContinuousOn (normalizedTwistedForm Θ γ) (Icc A B) := by
  unfold normalizedTwistedForm
  refine continuousOn_tsum (f := fun q a => (ExpPoly.eval (normalizedRayTermPoly Θ γ q) a).re)
    (u := fun q => 4 * B ^ 2 * (1 / ‖xiSpectralPoint q‖ ^ 2)) (fun q => ?_) ?_ ?_
  · exact (Complex.continuous_re.comp (ExpPoly.continuous_eval _)).continuousOn
  · exact xiSpectralPoint_inv_sq_summable.mul_left _
  · intro q a ha
    rw [mem_Icc] at ha
    exact abs_re_eval_normalizedRayTermPoly_le (hA.trans ha.1) ha.2 q (hall q)

/-! ## The window integral as a sum over the copies -/

theorem integrableOn_re_eval (Θ γ : ℝ) (q : XiZeroCopy) (A B : ℝ) :
    IntegrableOn (fun a : ℝ => (ExpPoly.eval (normalizedRayTermPoly Θ γ q) a).re) (Ioc A B) :=
  ((Complex.continuous_re.comp (ExpPoly.continuous_eval _)).integrableOn_Icc).mono_set
    Ioc_subset_Icc_self

theorem summable_integral_norm_re_eval {Θ γ A L : ℝ} (hA : 1 / 2 ≤ A) (hL : 0 ≤ L)
    (hall : ∀ q : XiZeroCopy, |(xiSpectralPoint q).im| ≤ Θ) :
    Summable fun q : XiZeroCopy =>
      ∫ a in Ioc A (A + L), ‖(ExpPoly.eval (normalizedRayTermPoly Θ γ q) a).re‖ := by
  refine Summable.of_nonneg_of_le (fun q => integral_nonneg fun _ => norm_nonneg _) (fun q => ?_)
    (xiSpectralPoint_inv_sq_summable.mul_left (4 * (A + L) ^ 2 * L))
  calc ∫ a in Ioc A (A + L), ‖(ExpPoly.eval (normalizedRayTermPoly Θ γ q) a).re‖
      ≤ ∫ a in Ioc A (A + L), 4 * (A + L) ^ 2 * (1 / ‖xiSpectralPoint q‖ ^ 2) := by
        refine setIntegral_mono_on (integrableOn_re_eval Θ γ q A (A + L)).norm
          (continuous_const.integrableOn_Icc.mono_set Ioc_subset_Icc_self) measurableSet_Ioc
          fun a ha => ?_
        rw [mem_Ioc] at ha
        exact abs_re_eval_normalizedRayTermPoly_le (hA.trans ha.1.le) ha.2 q (hall q)
    _ = 4 * (A + L) ^ 2 * L * (1 / ‖xiSpectralPoint q‖ ^ 2) := by
        rw [setIntegral_const, smul_eq_mul, Measure.real, Real.volume_Ioc,
          ENNReal.toReal_ofReal (by linarith)]
        ring

/-- **Interchange.**  The window integral of `S` is the sum of the window integrals of the copies. -/
theorem integral_normalizedTwistedForm_eq_tsum {Θ γ A L : ℝ} (hA : 1 / 2 ≤ A) (hL : 0 ≤ L)
    (hall : ∀ q : XiZeroCopy, |(xiSpectralPoint q).im| ≤ Θ) :
    ∫ a in A..(A + L), normalizedTwistedForm Θ γ a
      = ∑' q : XiZeroCopy,
          ∫ a in A..(A + L), (ExpPoly.eval (normalizedRayTermPoly Θ γ q) a).re := by
  have hAB : A ≤ A + L := by linarith
  unfold normalizedTwistedForm
  simp_rw [intervalIntegral.integral_of_le hAB]
  exact (integral_tsum_of_summable_integral_norm (fun q => integrableOn_re_eval Θ γ q A (A + L))
    (summable_integral_norm_re_eval hA hL hall)).symm

theorem summable_integral_re_eval {Θ γ A L : ℝ} (hA : 1 / 2 ≤ A) (hL : 0 ≤ L)
    (hall : ∀ q : XiZeroCopy, |(xiSpectralPoint q).im| ≤ Θ) :
    Summable fun q : XiZeroCopy =>
      ∫ a in A..(A + L), (ExpPoly.eval (normalizedRayTermPoly Θ γ q) a).re := by
  have hAB : A ≤ A + L := by linarith
  simp_rw [intervalIntegral.integral_of_le hAB]
  exact Summable.of_norm_bounded (summable_integral_norm_re_eval hA hL hall)
    fun q => norm_integral_le_integral_norm _

/-- Per-copy window bound: `∫_A^{A+L} Re eval ≤ L · Re constTerm + 2 · decayNorm`. -/
theorem integral_re_eval_le {Θ γ A L : ℝ} (hΘ : 0 ≤ Θ) (hA : 0 ≤ A) (hL : 0 < L) (q : XiZeroCopy)
    (hq : |(xiSpectralPoint q).im| ≤ Θ) :
    ∫ a in A..(A + L), (ExpPoly.eval (normalizedRayTermPoly Θ γ q) a).re
      ≤ L * (ExpPoly.constTerm (normalizedRayTermPoly Θ γ q)).re
        + 2 * ExpPoly.decayNorm (normalizedRayTermPoly Θ γ q) := by
  have h := ExpPoly.abs_windowMean_re_sub_le _ (decaying_normalizedRayTermPoly hΘ γ hq) hA hL
  have h2 := (abs_le.mp h).2
  have h3 : (∫ a in A..(A + L), (ExpPoly.eval (normalizedRayTermPoly Θ γ q) a).re) / L
      ≤ (ExpPoly.constTerm (normalizedRayTermPoly Θ γ q)).re
        + 2 * ExpPoly.decayNorm (normalizedRayTermPoly Θ γ q) / L := by linarith
  rw [div_le_iff₀ hL] at h3
  calc ∫ a in A..(A + L), (ExpPoly.eval (normalizedRayTermPoly Θ γ q) a).re
      ≤ ((ExpPoly.constTerm (normalizedRayTermPoly Θ γ q)).re
          + 2 * ExpPoly.decayNorm (normalizedRayTermPoly Θ γ q) / L) * L := h3
    _ = L * (ExpPoly.constTerm (normalizedRayTermPoly Θ γ q)).re
          + 2 * ExpPoly.decayNorm (normalizedRayTermPoly Θ γ q) := by
        field_simp

/-! ## The constant-term sum -/

/-- The copies at the top height with ordinate `±γ`. -/
def topCentreSet (Θ γ : ℝ) : Set XiZeroCopy :=
  {q | |(xiSpectralPoint q).im| = Θ ∧
    ((xiSpectralPoint q).re = γ ∨ (xiSpectralPoint q).re = -γ)}

theorem finite_topCentreSet (Θ γ : ℝ) : (topCentreSet Θ γ).Finite := by
  have h1 := finite_xiZeroCopy_band γ zero_le_one
  have h2 := finite_xiZeroCopy_band (-γ) zero_le_one
  refine (h1.union h2).subset ?_
  intro q hq
  rcases hq.2 with h | h
  · left
    show |(q.1 : ℂ).im - γ| ≤ 1
    rw [← xiSpectralPoint_re_eq_im, h, sub_self, abs_zero]
    exact zero_le_one
  · right
    show |(q.1 : ℂ).im - -γ| ≤ 1
    rw [← xiSpectralPoint_re_eq_im, h, sub_neg_eq_add, neg_add_cancel, abs_zero]
    exact zero_le_one

/-- The real value `κ(Θ)`. -/
def topKappa (Θ : ℝ) : ℝ := (plateauKappa (Θ : ℂ)).re

theorem plateauKappa_eq_ofReal (Θ : ℝ) : plateauKappa (Θ : ℂ) = ((topKappa Θ : ℝ) : ℂ) := by
  apply Complex.ext
  · rfl
  · rw [Complex.ofReal_im]
    exact (plateauKappa_ofReal Θ).1

theorem topKappa_pos {Θ : ℝ} (hΘ : 0 < Θ) : 0 < topKappa Θ := by
  have h := (plateauKappa_ofReal Θ).2
  have : 0 < Real.exp (-Θ / 4) / Θ := by positivity
  unfold topKappa
  linarith

/-- The constant `c = (1/4) κ(Θ)² (γ² − Θ²)/(γ² + Θ²)²`. -/
def topConstant (Θ γ : ℝ) : ℝ :=
  (1 / 4) * topKappa Θ ^ 2 * (γ ^ 2 - Θ ^ 2) / (γ ^ 2 + Θ ^ 2) ^ 2

theorem topConstant_pos {Θ γ : ℝ} (hΘ : 0 < Θ) (hΘ' : Θ < 1 / 2) (hγ : 9 / 2 ≤ |γ|) :
    0 < topConstant Θ γ := by
  unfold topConstant
  have hk := topKappa_pos hΘ
  have hγ2 : (9 / 2 : ℝ) ^ 2 ≤ γ ^ 2 := by
    have := pow_le_pow_left₀ (by norm_num) hγ 2
    rwa [sq_abs] at this
  have hΘ2 : Θ ^ 2 < (1 / 2) ^ 2 := pow_lt_pow_left₀ hΘ' hΘ.le two_ne_zero
  have hnum : 0 < γ ^ 2 - Θ ^ 2 := by nlinarith
  positivity

theorem re_inv_sq_of_sq_eq {z : ℂ} {X Y : ℝ} (hx : z.re ^ 2 = X) (hy : z.im ^ 2 = Y) :
    ((z ^ 2)⁻¹).re = (X - Y) / (X + Y) ^ 2 := by
  have hre2 : (z ^ 2).re = X - Y := by
    rw [pow_two, Complex.mul_re, ← pow_two, ← pow_two, hx, hy]
  have him2 : (z ^ 2).im = 2 * z.re * z.im := by
    rw [pow_two, Complex.mul_im]; ring
  have hns : Complex.normSq (z ^ 2) = (X + Y) ^ 2 := by
    rw [Complex.normSq_apply, hre2, him2]
    have : (2 * z.re * z.im) * (2 * z.re * z.im) = 4 * X * Y := by
      rw [← hx, ← hy]; ring
    rw [this]; ring
  rw [Complex.inv_re, hre2, hns]

/-- The real part of the constant term of a top-centre copy is `−c`. -/
theorem re_constTerm_of_mem_topCentreSet {Θ γ : ℝ} (hΘ : 0 < Θ) (hγ : γ ≠ 0)
    (hall : ∀ q : XiZeroCopy, |(xiSpectralPoint q).im| ≤ Θ) {q : XiZeroCopy}
    (hq : q ∈ topCentreSet Θ γ) :
    (ExpPoly.constTerm (normalizedRayTermPoly Θ γ q)).re = -topConstant Θ γ := by
  have hre := xiSpectralPoint_re_ne_zero q
  rw [constTerm_normalizedRayTermPoly hΘ γ (hall q) hre, if_pos hq.1]
  have hcase : (if (xiSpectralPoint q).re - γ = 0 then plateauKappa (Θ : ℂ) ^ 2 else 0)
      + (if (xiSpectralPoint q).re + γ = 0 then plateauKappa (Θ : ℂ) ^ 2 else 0)
      = plateauKappa (Θ : ℂ) ^ 2 := by
    rcases hq.2 with h | h
    · rw [if_pos (by rw [h]; ring), if_neg (by rw [h]; intro h0; apply hγ; linarith), add_zero]
    · rw [if_neg (by rw [h]; intro h0; apply hγ; linarith), if_pos (by rw [h]; ring), zero_add]
  rw [hcase, plateauKappa_eq_ofReal]
  have hX : (xiSpectralPoint q).re ^ 2 = γ ^ 2 := by
    rcases hq.2 with h | h
    · rw [h]
    · rw [h]; ring
  have hY : (xiSpectralPoint q).im ^ 2 = Θ ^ 2 := by
    rw [← sq_abs, hq.1]
  have hform : -(1 / 4 : ℂ) / xiSpectralPoint q ^ 2 * ((topKappa Θ : ℝ) : ℂ) ^ 2
      = ((-(1 / 4) * topKappa Θ ^ 2 : ℝ) : ℂ) * (xiSpectralPoint q ^ 2)⁻¹ := by
    push_cast
    ring
  rw [hform, Complex.re_ofReal_mul, re_inv_sq_of_sq_eq hX hY]
  unfold topConstant
  ring

/-- Copies outside the top-centre set have vanishing constant term. -/
theorem constTerm_eq_zero_of_not_mem_topCentreSet {Θ γ : ℝ} (hΘ : 0 < Θ)
    (hall : ∀ q : XiZeroCopy, |(xiSpectralPoint q).im| ≤ Θ) {q : XiZeroCopy}
    (hq : q ∉ topCentreSet Θ γ) :
    ExpPoly.constTerm (normalizedRayTermPoly Θ γ q) = 0 := by
  have hre := xiSpectralPoint_re_ne_zero q
  rw [constTerm_normalizedRayTermPoly hΘ γ (hall q) hre]
  by_cases htop : |(xiSpectralPoint q).im| = Θ
  · rw [if_pos htop]
    have h1 : (xiSpectralPoint q).re - γ ≠ 0 := by
      intro h; apply hq; exact ⟨htop, Or.inl (by linarith)⟩
    have h2 : (xiSpectralPoint q).re + γ ≠ 0 := by
      intro h; apply hq; exact ⟨htop, Or.inr (by linarith)⟩
    rw [if_neg h1, if_neg h2]
    ring
  · rw [if_neg htop]

/-- **The constant-term sum is at most `−c`.** -/
theorem tsum_re_constTerm_le {Θ : ℝ} (hΘ : 0 < Θ) (q₀ : XiZeroCopy)
    (hq₀ : |(xiSpectralPoint q₀).im| = Θ)
    (hall : ∀ q : XiZeroCopy, |(xiSpectralPoint q).im| ≤ Θ) :
    ∑' q : XiZeroCopy,
        (ExpPoly.constTerm (normalizedRayTermPoly Θ (xiSpectralPoint q₀).re q)).re
      ≤ -topConstant Θ (xiSpectralPoint q₀).re := by
  classical
  set γ := (xiSpectralPoint q₀).re with hγdef
  have hγ : γ ≠ 0 := xiSpectralPoint_re_ne_zero q₀
  have hT := finite_topCentreSet Θ γ
  have hzero : ∀ q ∉ hT.toFinset,
      (ExpPoly.constTerm (normalizedRayTermPoly Θ γ q)).re = 0 := by
    intro q hq
    rw [hT.mem_toFinset] at hq
    rw [constTerm_eq_zero_of_not_mem_topCentreSet hΘ hall hq, Complex.zero_re]
  rw [tsum_eq_sum hzero]
  have hval : ∀ q ∈ hT.toFinset,
      (ExpPoly.constTerm (normalizedRayTermPoly Θ γ q)).re = -topConstant Θ γ := by
    intro q hq
    rw [hT.mem_toFinset] at hq
    exact re_constTerm_of_mem_topCentreSet hΘ hγ hall hq
  rw [Finset.sum_congr rfl hval, Finset.sum_const, nsmul_eq_mul]
  have hmem : q₀ ∈ hT.toFinset := by
    rw [hT.mem_toFinset]
    exact ⟨hq₀, Or.inl rfl⟩
  have hcard : (1 : ℝ) ≤ (hT.toFinset.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr ⟨q₀, hmem⟩
  have hΘ' : Θ < 1 / 2 := by
    rw [← hq₀]; exact abs_im_xiSpectralPoint_lt_half q₀
  have hc := topConstant_pos hΘ hΘ' (nine_halves_le_abs_re_xiSpectralPoint q₀)
  nlinarith

/-! ## The window bound -/

/-- The total decay norm `D = Σ_q decayNorm`. -/
def decayTotal (Θ γ : ℝ) : ℝ := ∑' q : XiZeroCopy, ExpPoly.decayNorm (normalizedRayTermPoly Θ γ q)

theorem summable_decayNorm_top {Θ : ℝ} (hΘ : 0 < Θ) (q₀ : XiZeroCopy)
    (hall : ∀ q : XiZeroCopy, |(xiSpectralPoint q).im| ≤ Θ) :
    Summable fun q : XiZeroCopy =>
      ExpPoly.decayNorm (normalizedRayTermPoly Θ (xiSpectralPoint q₀).re q) :=
  summable_decayNorm_normalizedRayTermPoly hΘ (by norm_num : (0 : ℝ) < 9 / 2) hall
    nine_halves_le_abs_re_xiSpectralPoint (nine_halves_le_abs_re_xiSpectralPoint q₀)

theorem decayTotal_nonneg (Θ γ : ℝ) : 0 ≤ decayTotal Θ γ :=
  tsum_nonneg fun _ => ExpPoly.decayNorm_nonneg _

/-- **Window bound.**  `∫_A^{A+L} S ≤ −c L + 2 D` for `A ≥ ½`, `L > 0`. -/
theorem integral_normalizedTwistedForm_le {Θ : ℝ} (hΘ : 0 < Θ) (q₀ : XiZeroCopy)
    (hq₀ : |(xiSpectralPoint q₀).im| = Θ)
    (hall : ∀ q : XiZeroCopy, |(xiSpectralPoint q).im| ≤ Θ) {A L : ℝ} (hA : 1 / 2 ≤ A)
    (hL : 0 < L) :
    ∫ a in A..(A + L), normalizedTwistedForm Θ (xiSpectralPoint q₀).re a
      ≤ -topConstant Θ (xiSpectralPoint q₀).re * L + 2 * decayTotal Θ (xiSpectralPoint q₀).re := by
  classical
  set γ := (xiSpectralPoint q₀).re with hγdef
  rw [integral_normalizedTwistedForm_eq_tsum hA hL.le hall]
  have hA0 : 0 ≤ A := by linarith
  have hsumL := summable_integral_re_eval (γ := γ) hA hL.le hall
  have hT := finite_topCentreSet Θ γ
  have hsumC : Summable fun q : XiZeroCopy =>
      L * (ExpPoly.constTerm (normalizedRayTermPoly Θ γ q)).re := by
    refine summable_of_ne_finset_zero (s := hT.toFinset) fun q hq => ?_
    rw [hT.mem_toFinset] at hq
    rw [constTerm_eq_zero_of_not_mem_topCentreSet hΘ hall hq, Complex.zero_re, mul_zero]
  have hsumD := (summable_decayNorm_top hΘ q₀ hall).mul_left 2
  have hterm : ∀ q : XiZeroCopy,
      ∫ a in A..(A + L), (ExpPoly.eval (normalizedRayTermPoly Θ γ q) a).re
        ≤ L * (ExpPoly.constTerm (normalizedRayTermPoly Θ γ q)).re
          + 2 * ExpPoly.decayNorm (normalizedRayTermPoly Θ γ q) :=
    fun q => integral_re_eval_le hΘ.le hA0 hL q (hall q)
  calc ∑' q : XiZeroCopy, ∫ a in A..(A + L), (ExpPoly.eval (normalizedRayTermPoly Θ γ q) a).re
      ≤ ∑' q : XiZeroCopy, (L * (ExpPoly.constTerm (normalizedRayTermPoly Θ γ q)).re
          + 2 * ExpPoly.decayNorm (normalizedRayTermPoly Θ γ q)) :=
        hsumL.tsum_le_tsum hterm (hsumC.add hsumD)
    _ = L * ∑' q : XiZeroCopy, (ExpPoly.constTerm (normalizedRayTermPoly Θ γ q)).re
          + 2 * decayTotal Θ γ := by
        rw [hsumC.tsum_add hsumD, tsum_mul_left, tsum_mul_left]
        rfl
    _ ≤ L * (-topConstant Θ γ) + 2 * decayTotal Θ γ := by
        have := tsum_re_constTerm_le hΘ q₀ hq₀ hall
        nlinarith
    _ = -topConstant Θ γ * L + 2 * decayTotal Θ γ := by ring

/-! ## Recurrent negativity -/

/-- **Recurrent negativity of the normalised form.**  For `L > 4D/c` every window `[A, A+L]`
with `A ≥ ½` contains an aperture where `S ≤ −c/2`. -/
theorem exists_normalizedTwistedForm_le_of_attainedTop {Θ : ℝ} (hΘ : 0 < Θ) (q₀ : XiZeroCopy)
    (hq₀ : |(xiSpectralPoint q₀).im| = Θ)
    (hall : ∀ q : XiZeroCopy, |(xiSpectralPoint q).im| ≤ Θ) {A L : ℝ} (hA : 1 / 2 ≤ A)
    (hL : 4 * decayTotal Θ (xiSpectralPoint q₀).re / topConstant Θ (xiSpectralPoint q₀).re < L) :
    ∃ a ∈ Icc A (A + L),
      normalizedTwistedForm Θ (xiSpectralPoint q₀).re a
        ≤ -(topConstant Θ (xiSpectralPoint q₀).re / 2) := by
  set γ := (xiSpectralPoint q₀).re with hγdef
  have hΘ' : Θ < 1 / 2 := by
    rw [← hq₀]; exact abs_im_xiSpectralPoint_lt_half q₀
  have hc := topConstant_pos hΘ hΘ' (nine_halves_le_abs_re_xiSpectralPoint q₀)
  have hD := decayTotal_nonneg Θ γ
  have hLpos : 0 < L := lt_of_le_of_lt (by positivity) hL
  by_contra hcon
  push Not at hcon
  have hbound := integral_normalizedTwistedForm_le hΘ q₀ hq₀ hall hA hLpos
  have hcont : ContinuousOn (normalizedTwistedForm Θ γ) (Icc A (A + L)) :=
    continuousOn_normalizedTwistedForm hA hall
  have hmono : ∫ a in A..(A + L), (-(topConstant Θ γ / 2))
      ≤ ∫ a in A..(A + L), normalizedTwistedForm Θ γ a := by
    refine intervalIntegral.integral_mono_on (by linarith)
      (continuous_const.intervalIntegrable _ _)
      (hcont.intervalIntegrable_of_Icc (by linarith)) fun a ha => (hcon a ha).le
  rw [intervalIntegral.integral_const, smul_eq_mul] at hmono
  have hL' : 4 * decayTotal Θ γ < L * topConstant Θ γ := by
    rwa [div_lt_iff₀ hc] at hL
  nlinarith

/-- **Exponentially recurrent negativity of the twisted plateau family.**  If the largest excess `Θ`
is attained at `q₀`, then there are `c > 0` and `L₀ > 0` such that every aperture window `[A, A + L]`
with `A ≥ ½` and `L ≥ L₀` contains an aperture `a` with
`Re Q(cos(γ₀ x) ψ_a) ≤ −c e^{2Θa} < 0`, where `γ₀ = Re z₀` is the ordinate of `q₀`. -/
theorem exists_aperture_twistedOddTest_neg_of_attainedTop {Θ : ℝ} (hΘ : 0 < Θ) (q₀ : XiZeroCopy)
    (hq₀ : |(xiSpectralPoint q₀).im| = Θ)
    (hall : ∀ q : XiZeroCopy, |(xiSpectralPoint q).im| ≤ Θ) :
    ∃ c : ℝ, 0 < c ∧ ∃ L₀ : ℝ, 0 < L₀ ∧ ∀ A : ℝ, 1 / 2 ≤ A → ∀ L : ℝ, L₀ ≤ L →
      ∃ a ∈ Icc A (A + L), ∀ ha0 : 0 ≤ a,
        (suzukiScrewSmoothForm
            (twistedOddTest (plateauProfile a ha0) (xiSpectralPoint q₀).re)
            (twistedOddTest (plateauProfile a ha0) (xiSpectralPoint q₀).re)).re
          ≤ -(c * Real.exp (2 * Θ * a)) := by
  set γ := (xiSpectralPoint q₀).re with hγdef
  have hΘ' : Θ < 1 / 2 := by
    rw [← hq₀]; exact abs_im_xiSpectralPoint_lt_half q₀
  have hc := topConstant_pos hΘ hΘ' (nine_halves_le_abs_re_xiSpectralPoint q₀)
  have hD := decayTotal_nonneg Θ γ
  refine ⟨topConstant Θ γ / 2, by positivity,
    4 * decayTotal Θ γ / topConstant Θ γ + 1, by positivity, fun A hA L hL => ?_⟩
  obtain ⟨a, ha, hle⟩ := exists_normalizedTwistedForm_le_of_attainedTop hΘ q₀ hq₀ hall hA
    (lt_of_lt_of_le (by linarith) hL)
  refine ⟨a, ha, fun ha0 => ?_⟩
  have ha12 : 1 / 2 ≤ a := hA.trans ha.1
  have heq := normalizedTwistedForm_eq ha12 ha0 Θ γ
  rw [heq] at hle
  have hE : 0 < Real.exp (-(2 * Θ) * a) := Real.exp_pos _
  have hprod : Real.exp (-(2 * Θ) * a) * Real.exp (2 * Θ * a) = 1 := by
    rw [← Real.exp_add]; ring_nf; exact Real.exp_zero
  have hE2 : 0 < Real.exp (2 * Θ * a) := Real.exp_pos _
  -- `E⁻ · Q ≤ −c/2` gives `Q ≤ −(c/2) E⁺` since `E⁻ E⁺ = 1`.
  have : (suzukiScrewSmoothForm (twistedOddTest (plateauProfile a ha0) γ)
      (twistedOddTest (plateauProfile a ha0) γ)).re
      = Real.exp (2 * Θ * a) * (Real.exp (-(2 * Θ) * a)
        * (suzukiScrewSmoothForm (twistedOddTest (plateauProfile a ha0) γ)
            (twistedOddTest (plateauProfile a ha0) γ)).re) := by
    rw [← mul_assoc, mul_comm (Real.exp (2 * Θ * a)), hprod, one_mul]
  rw [this]
  calc Real.exp (2 * Θ * a) * (Real.exp (-(2 * Θ) * a)
        * (suzukiScrewSmoothForm (twistedOddTest (plateauProfile a ha0) γ)
            (twistedOddTest (plateauProfile a ha0) γ)).re)
      ≤ Real.exp (2 * Θ * a) * (-(topConstant Θ γ / 2)) :=
        mul_le_mul_of_nonneg_left hle hE2.le
    _ = -(topConstant Θ γ / 2 * Real.exp (2 * Θ * a)) := by ring

/-! ## The criterion form -/

/-- The largest excess is attained: some copy has `|Im z_{q₀}| = Θ > 0` and no copy exceeds `Θ`. -/
def AttainedTopExcess : Prop :=
  ∃ Θ : ℝ, 0 < Θ ∧ ∃ q₀ : XiZeroCopy, |(xiSpectralPoint q₀).im| = Θ ∧
    ∀ q : XiZeroCopy, |(xiSpectralPoint q).im| ≤ Θ

/-- **Pointwise nonnegativity of the twisted plateau family excludes an attained top excess.**
If `Re Q(cos(γx)ψ_a) ≥ 0` for every centre `γ` and every aperture `a ≥ ½`, then the supremum of the
excesses is not attained (so either RH holds or the supremum is a limit of excesses). -/
theorem not_attainedTopExcess_of_twistedPlateau_nonneg
    (h : ∀ γ : ℝ, ∀ a : ℝ, ∀ ha0 : 0 ≤ a, 1 / 2 ≤ a →
      0 ≤ (suzukiScrewSmoothForm (twistedOddTest (plateauProfile a ha0) γ)
            (twistedOddTest (plateauProfile a ha0) γ)).re) :
    ¬ AttainedTopExcess := by
  rintro ⟨Θ, hΘ, q₀, hq₀, hall⟩
  obtain ⟨c, hc, L₀, hL₀, hw⟩ := exists_aperture_twistedOddTest_neg_of_attainedTop hΘ q₀ hq₀ hall
  obtain ⟨a, ha, hneg⟩ := hw (1 / 2) le_rfl L₀ le_rfl
  have ha0 : 0 ≤ a := by linarith [ha.1]
  have h1 := h (xiSpectralPoint q₀).re a ha0 ha.1
  have h2 := hneg ha0
  have h3 : 0 < c * Real.exp (2 * Θ * a) := by positivity
  linarith

/-- If the Riemann hypothesis fails, the excess supremum is positive; an attained supremum is then
excluded by the twisted plateau family. -/
theorem riemannHypothesis_or_not_attainedTopExcess_of_twistedPlateau_nonneg
    (h : ∀ γ : ℝ, ∀ a : ℝ, ∀ ha0 : 0 ≤ a, 1 / 2 ≤ a →
      0 ≤ (suzukiScrewSmoothForm (twistedOddTest (plateauProfile a ha0) γ)
            (twistedOddTest (plateauProfile a ha0) γ)).re) :
    RiemannHypothesis ∨ ¬ AttainedTopExcess :=
  Or.inr (not_attainedTopExcess_of_twistedPlateau_nonneg h)

end

end RHTower
