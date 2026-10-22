import GaloisForLFunctions.RHTower.Suzuki.SuzukiScrewTestRayEnergy

/-!
# The twisted odd test law for Suzuki's screw form

Let `ψ` be a real, smooth, odd profile supported in `[−a, a]` and `γ` a real centre.  The test
`φ(x) = cos(γ x) ψ(x)` is smooth, supported in `[−a, a]`, and has zero mean (its integrand is odd),
so it is an admissible zero-mean test.  Writing `z_q = (ρ_q − ½)/i = Im ρ_q − i (Re ρ_q − ½)` for the
spectral point of a Xi zero copy, its ray coefficients are

`Coef_q = −½ (A_q + A'_q)`,  `Bar_q = ½ (A_q + A'_q)`,

with the twisted moments `A_q = ∫ e^{(Re ρ_q − ½) u} e^{i (Im ρ_q − γ) u} ψ(u) du` and
`A'_q = ∫ e^{(Re ρ_q − ½) u} e^{i (Im ρ_q + γ) u} ψ(u) du`.  Hence the screw form of the test is the
exact ray energy

`Q(φ) = Σ'_q −(1/4) (A_q + A'_q)² / z_q²`.

For a copy on the critical line (`Im z_q = 0`) both moments are purely imaginary and the summand is
the nonnegative real number `(Im (A_q + A'_q))² / (4 z_q²)`.  For an off-line copy the summand is
`−(1/4)(A_q + A'_q)²/z_q²`; at the centre `γ = Im ρ_q` its first moment is the real number
`∫ e^{(Re ρ_q − ½) u} ψ(u) du`.  Nothing here uses the Riemann hypothesis.
-/

open MeasureTheory Complex Set

namespace RHTower

noncomputable section

/-- A real, smooth, odd profile supported in `[−a, a]`. -/
structure OddSmoothProfile (a : ℝ) where
  toFun : ℝ → ℝ
  smooth : ContDiff ℝ (⊤ : ℕ∞) toFun
  support_subset : Function.support toFun ⊆ Icc (-a) a
  odd : ∀ u, toFun (-u) = -toFun u

instance (a : ℝ) : CoeFun (OddSmoothProfile a) fun _ => ℝ → ℝ := ⟨OddSmoothProfile.toFun⟩

theorem OddSmoothProfile.continuous {a : ℝ} (ψ : OddSmoothProfile a) : Continuous ψ :=
  ψ.smooth.continuous

theorem OddSmoothProfile.hasCompactSupport {a : ℝ} (ψ : OddSmoothProfile a) :
    HasCompactSupport ψ :=
  HasCompactSupport.of_support_subset_isCompact isCompact_Icc ψ.support_subset

theorem OddSmoothProfile.hasCompactSupport_ofReal {a : ℝ} (ψ : OddSmoothProfile a) :
    HasCompactSupport (fun u : ℝ => ((ψ u : ℝ) : ℂ)) :=
  ψ.hasCompactSupport.comp_left Complex.ofReal_zero

/-- The twisted moment `∫ e^{(b + iμ) u} ψ(u) du` of a profile. -/
def twistedMoment {a : ℝ} (ψ : OddSmoothProfile a) (b μ : ℝ) : ℂ :=
  ∫ u : ℝ, Complex.exp (((b : ℂ) + I * (μ : ℂ)) * (u : ℂ)) * ((ψ u : ℝ) : ℂ)

theorem integrable_exp_mul_profile {a : ℝ} (ψ : OddSmoothProfile a) (c : ℂ) :
    Integrable (fun u : ℝ => Complex.exp (c * (u : ℂ)) * ((ψ u : ℝ) : ℂ)) := by
  refine Continuous.integrable_of_hasCompactSupport ?_ ?_
  · exact (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).mul
      (Complex.continuous_ofReal.comp ψ.continuous)
  · refine ψ.hasCompactSupport_ofReal.mono ?_
    intro u hu
    simp only [Function.mem_support] at hu ⊢
    intro h0
    apply hu
    rw [h0, mul_zero]

/-- Odd symmetry of the twisted moments. -/
theorem twistedMoment_neg_neg {a : ℝ} (ψ : OddSmoothProfile a) (b μ : ℝ) :
    twistedMoment ψ (-b) (-μ) = -twistedMoment ψ b μ := by
  unfold twistedMoment
  have key : ∀ u : ℝ,
      Complex.exp ((((-b : ℝ) : ℂ) + I * ((-μ : ℝ) : ℂ)) * ((-u : ℝ) : ℂ)) * ((ψ (-u) : ℝ) : ℂ)
        = -(Complex.exp (((b : ℂ) + I * (μ : ℂ)) * (u : ℂ)) * ((ψ u : ℝ) : ℂ)) := by
    intro u
    rw [ψ.odd u]
    simp only [Complex.ofReal_neg]
    have : (-(b : ℂ) + I * -(μ : ℂ)) * (-(u : ℂ)) = ((b : ℂ) + I * (μ : ℂ)) * (u : ℂ) := by ring
    rw [this]
    ring
  calc ∫ u : ℝ, Complex.exp ((((-b : ℝ) : ℂ) + I * ((-μ : ℝ) : ℂ)) * (u : ℂ)) * ((ψ u : ℝ) : ℂ)
      = ∫ u : ℝ, Complex.exp ((((-b : ℝ) : ℂ) + I * ((-μ : ℝ) : ℂ)) * ((-u : ℝ) : ℂ))
          * ((ψ (-u) : ℝ) : ℂ) :=
        (integral_neg_eq_self (fun u : ℝ =>
          Complex.exp ((((-b : ℝ) : ℂ) + I * ((-μ : ℝ) : ℂ)) * (u : ℂ)) * ((ψ u : ℝ) : ℂ))
          volume).symm
    _ = ∫ u : ℝ, -(Complex.exp (((b : ℂ) + I * (μ : ℂ)) * (u : ℂ)) * ((ψ u : ℝ) : ℂ)) := by
        congr 1
        funext u
        exact key u
    _ = -∫ u : ℝ, Complex.exp (((b : ℂ) + I * (μ : ℂ)) * (u : ℂ)) * ((ψ u : ℝ) : ℂ) :=
        integral_neg _

/-- Conjugation reflects the frequency of a twisted moment. -/
theorem conj_twistedMoment {a : ℝ} (ψ : OddSmoothProfile a) (b μ : ℝ) :
    (starRingEnd ℂ) (twistedMoment ψ b μ) = twistedMoment ψ b (-μ) := by
  unfold twistedMoment
  rw [← integral_conj]
  congr 1
  funext u
  rw [map_mul, ← Complex.exp_conj, Complex.conj_ofReal]
  congr 2
  simp [Complex.ofReal_neg]

/-- Twisted moments at frequency zero are real. -/
theorem twistedMoment_im_zero {a : ℝ} (ψ : OddSmoothProfile a) (b : ℝ) :
    (twistedMoment ψ b 0).im = 0 := by
  have h := conj_twistedMoment ψ b 0
  rw [neg_zero] at h
  have h' := congrArg Complex.im h
  simp only [Complex.conj_im] at h'
  linarith

/-- Twisted moments with zero exponential weight are purely imaginary. -/
theorem twistedMoment_re_zero {a : ℝ} (ψ : OddSmoothProfile a) (μ : ℝ) :
    (twistedMoment ψ 0 μ).re = 0 := by
  have h1 := conj_twistedMoment ψ 0 μ
  have h2 := twistedMoment_neg_neg ψ 0 μ
  rw [neg_zero] at h2
  rw [h2] at h1
  have h' := congrArg Complex.re h1
  simp only [Complex.conj_re, Complex.neg_re] at h'
  linarith

/-! ## The twisted odd test -/

/-- The zero-mean test `cos(γ x) ψ(x)` built from an odd profile. -/
def twistedOddTest {a : ℝ} (ψ : OddSmoothProfile a) (γ : ℝ) : SuzukiSmoothZeroMeanTest a where
  toFun := fun x => ((Real.cos (γ * x) * ψ x : ℝ) : ℂ)
  smooth := by
    have h1 : ContDiff ℝ (⊤ : ℕ∞) (fun x : ℝ => Real.cos (γ * x) * ψ x) :=
      (Real.contDiff_cos.comp (contDiff_const.mul contDiff_id)).mul ψ.smooth
    exact (ContinuousLinearMap.contDiff Complex.ofRealCLM).comp h1
  support_subset := by
    intro x hx
    apply ψ.support_subset
    intro h0
    apply hx
    simp [h0]
  integral_zero := by
    show ∫ x : ℝ, ((Real.cos (γ * x) * ψ x : ℝ) : ℂ) = 0
    have hodd : ∀ x : ℝ, ((Real.cos (γ * -x) * ψ (-x) : ℝ) : ℂ)
        = -((Real.cos (γ * x) * ψ x : ℝ) : ℂ) := by
      intro x
      rw [mul_neg, Real.cos_neg, ψ.odd x]
      push_cast
      ring
    have h := integral_neg_eq_self (fun x : ℝ => ((Real.cos (γ * x) * ψ x : ℝ) : ℂ)) volume
    simp only [hodd] at h
    rw [integral_neg] at h
    have h2 : (2 : ℂ) * ∫ x : ℝ, ((Real.cos (γ * x) * ψ x : ℝ) : ℂ) = 0 := by
      linear_combination -h
    exact (mul_eq_zero.mp h2).resolve_left two_ne_zero

theorem twistedOddTest_apply {a : ℝ} (ψ : OddSmoothProfile a) (γ x : ℝ) :
    (twistedOddTest ψ γ : ℝ → ℂ) x = ((Real.cos (γ * x) * ψ x : ℝ) : ℂ) := rfl

theorem integrable_exp_mul_twistedOddTest {a : ℝ} (ψ : OddSmoothProfile a) (γ : ℝ) (c : ℂ) :
    Integrable (fun u : ℝ => Complex.exp (c * (u : ℂ)) * (twistedOddTest ψ γ : ℝ → ℂ) u) := by
  refine Continuous.integrable_of_hasCompactSupport ?_ ?_
  · exact (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).mul
      (twistedOddTest ψ γ).continuous
  · refine (twistedOddTest ψ γ).hasCompactSupport.mono ?_
    intro u hu
    simp only [Function.mem_support] at hu ⊢
    intro h0
    apply hu
    rw [h0, mul_zero]

/-- The twisted pair moment `A_q + A'_q` of a profile at a zero copy and a centre. -/
def twistedPairMoment {a : ℝ} (ψ : OddSmoothProfile a) (γ : ℝ) (q : XiZeroCopy) : ℂ :=
  twistedMoment ψ (-(xiSpectralPoint q).im) ((xiSpectralPoint q).re - γ)
    + twistedMoment ψ (-(xiSpectralPoint q).im) ((xiSpectralPoint q).re + γ)

/-- The exponential-times-cosine integrand splits into two twisted exponentials (the `Coef`
direction). -/
theorem exp_neg_I_mul_twistedOddTest_eq {a : ℝ} (ψ : OddSmoothProfile a) (γ : ℝ)
    (q : XiZeroCopy) (u : ℝ) :
    Complex.exp (-(I * xiSpectralPoint q * (u : ℂ))) * (twistedOddTest ψ γ : ℝ → ℂ) u
      = (1 / 2 : ℂ) * (Complex.exp ((((xiSpectralPoint q).im : ℂ)
              + I * ((-((xiSpectralPoint q).re - γ) : ℝ) : ℂ)) * (u : ℂ)) * ((ψ u : ℝ) : ℂ)
          + Complex.exp ((((xiSpectralPoint q).im : ℂ)
              + I * ((-((xiSpectralPoint q).re + γ) : ℝ) : ℂ)) * (u : ℂ)) * ((ψ u : ℝ) : ℂ)) := by
  rw [twistedOddTest_apply, Complex.ofReal_mul, Complex.ofReal_cos, Complex.cos]
  have hz : xiSpectralPoint q = ((xiSpectralPoint q).re : ℂ) + ((xiSpectralPoint q).im : ℂ) * I :=
    (Complex.re_add_im _).symm
  have e1 : Complex.exp (-(I * xiSpectralPoint q * (u : ℂ))) * Complex.exp (((γ : ℂ) * u) * I)
      = Complex.exp ((((xiSpectralPoint q).im : ℂ)
          + I * ((-((xiSpectralPoint q).re - γ) : ℝ) : ℂ)) * (u : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    conv_lhs => rw [hz]
    push_cast
    linear_combination (-((xiSpectralPoint q).im : ℂ) * (u : ℂ)) * Complex.I_sq
  have e2 : Complex.exp (-(I * xiSpectralPoint q * (u : ℂ))) * Complex.exp (-((γ : ℂ) * u) * I)
      = Complex.exp ((((xiSpectralPoint q).im : ℂ)
          + I * ((-((xiSpectralPoint q).re + γ) : ℝ) : ℂ)) * (u : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    conv_lhs => rw [hz]
    push_cast
    linear_combination (-((xiSpectralPoint q).im : ℂ) * (u : ℂ)) * Complex.I_sq
  rw [← e1, ← e2]
  push_cast
  ring

/-- The `Bar` direction: the reflected exponential times the cosine splits into two twisted
exponentials. -/
theorem exp_I_mul_twistedOddTest_eq {a : ℝ} (ψ : OddSmoothProfile a) (γ : ℝ)
    (q : XiZeroCopy) (u : ℝ) :
    Complex.exp (I * xiSpectralPoint q * (u : ℂ)) * (twistedOddTest ψ γ : ℝ → ℂ) u
      = (1 / 2 : ℂ) * (Complex.exp ((((-(xiSpectralPoint q).im : ℝ) : ℂ)
              + I * (((xiSpectralPoint q).re - γ : ℝ) : ℂ)) * (u : ℂ)) * ((ψ u : ℝ) : ℂ)
          + Complex.exp ((((-(xiSpectralPoint q).im : ℝ) : ℂ)
              + I * (((xiSpectralPoint q).re + γ : ℝ) : ℂ)) * (u : ℂ)) * ((ψ u : ℝ) : ℂ)) := by
  rw [twistedOddTest_apply, Complex.ofReal_mul, Complex.ofReal_cos, Complex.cos]
  have hz : xiSpectralPoint q = ((xiSpectralPoint q).re : ℂ) + ((xiSpectralPoint q).im : ℂ) * I :=
    (Complex.re_add_im _).symm
  have e1 : Complex.exp (I * xiSpectralPoint q * (u : ℂ)) * Complex.exp (((γ : ℂ) * u) * I)
      = Complex.exp ((((-(xiSpectralPoint q).im : ℝ) : ℂ)
          + I * (((xiSpectralPoint q).re + γ : ℝ) : ℂ)) * (u : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    conv_lhs => rw [hz]
    push_cast
    linear_combination (((xiSpectralPoint q).im : ℂ) * (u : ℂ)) * Complex.I_sq
  have e2 : Complex.exp (I * xiSpectralPoint q * (u : ℂ)) * Complex.exp (-((γ : ℂ) * u) * I)
      = Complex.exp ((((-(xiSpectralPoint q).im : ℝ) : ℂ)
          + I * (((xiSpectralPoint q).re - γ : ℝ) : ℂ)) * (u : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    conv_lhs => rw [hz]
    push_cast
    linear_combination (((xiSpectralPoint q).im : ℂ) * (u : ℂ)) * Complex.I_sq
  rw [← e1, ← e2]
  push_cast
  ring

/-- **Ray coefficient of the twisted odd test.** -/
theorem suzukiTestRayCoef_twistedOddTest {a : ℝ} (ψ : OddSmoothProfile a) (γ : ℝ)
    (q : XiZeroCopy) :
    suzukiTestRayCoef (twistedOddTest ψ γ) q = -(1 / 2 : ℂ) * twistedPairMoment ψ γ q := by
  unfold suzukiTestRayCoef
  have hsplit : ∀ u : ℝ,
      (Complex.exp (-(I * xiSpectralPoint q * (u : ℂ))) - 1) * (twistedOddTest ψ γ : ℝ → ℂ) u
        = Complex.exp (-(I * xiSpectralPoint q * (u : ℂ))) * (twistedOddTest ψ γ : ℝ → ℂ) u
          - (twistedOddTest ψ γ : ℝ → ℂ) u := by
    intro u; ring
  simp_rw [hsplit]
  rw [integral_sub ?_ (integrable_suzukiSmoothZeroMeanTest _), (twistedOddTest ψ γ).integral_zero,
    sub_zero]
  · simp_rw [exp_neg_I_mul_twistedOddTest_eq ψ γ q]
    rw [integral_const_mul, integral_add (integrable_exp_mul_profile ψ _)
      (integrable_exp_mul_profile ψ _)]
    have h1 := twistedMoment_neg_neg ψ (-(xiSpectralPoint q).im) ((xiSpectralPoint q).re - γ)
    have h2 := twistedMoment_neg_neg ψ (-(xiSpectralPoint q).im) ((xiSpectralPoint q).re + γ)
    rw [neg_neg] at h1 h2
    unfold twistedMoment at h1 h2
    rw [h1, h2]
    unfold twistedPairMoment twistedMoment
    ring
  · have := integrable_exp_mul_twistedOddTest ψ γ (-(I * xiSpectralPoint q))
    refine this.congr (Filter.Eventually.of_forall fun u => ?_)
    simp only
    ring_nf

/-- **Reflected ray coefficient of the twisted odd test.** -/
theorem suzukiTestRayCoefBar_twistedOddTest {a : ℝ} (ψ : OddSmoothProfile a) (γ : ℝ)
    (q : XiZeroCopy) :
    suzukiTestRayCoefBar (twistedOddTest ψ γ) q = (1 / 2 : ℂ) * twistedPairMoment ψ γ q := by
  unfold suzukiTestRayCoefBar
  have hconj : ∀ t : ℝ, (starRingEnd ℂ) ((twistedOddTest ψ γ : ℝ → ℂ) t)
      = (twistedOddTest ψ γ : ℝ → ℂ) t := by
    intro t
    rw [twistedOddTest_apply, Complex.conj_ofReal]
  simp_rw [hconj]
  have hsplit : ∀ t : ℝ,
      (Complex.exp (I * xiSpectralPoint q * (t : ℂ)) - 1) * (twistedOddTest ψ γ : ℝ → ℂ) t
        = Complex.exp (I * xiSpectralPoint q * (t : ℂ)) * (twistedOddTest ψ γ : ℝ → ℂ) t
          - (twistedOddTest ψ γ : ℝ → ℂ) t := by
    intro t; ring
  simp_rw [hsplit]
  rw [integral_sub ?_ (integrable_suzukiSmoothZeroMeanTest _), (twistedOddTest ψ γ).integral_zero,
    sub_zero]
  · simp_rw [exp_I_mul_twistedOddTest_eq ψ γ q]
    rw [integral_const_mul, integral_add (integrable_exp_mul_profile ψ _)
      (integrable_exp_mul_profile ψ _)]
    unfold twistedPairMoment twistedMoment
    ring
  · have := integrable_exp_mul_twistedOddTest ψ γ (I * xiSpectralPoint q)
    exact this

/-- **The twisted odd test law.**  The screw form of `cos(γx)ψ(x)` is the exact ray energy
`Σ'_q −(1/4)(A_q + A'_q)²/z_q²`. -/
theorem suzukiScrewSmoothForm_twistedOddTest {a : ℝ} (ψ : OddSmoothProfile a) (γ : ℝ) :
    suzukiScrewSmoothForm (twistedOddTest ψ γ) (twistedOddTest ψ γ)
      = ∑' q : XiZeroCopy,
          -(1 / 4 : ℂ) * twistedPairMoment ψ γ q ^ (2 : ℕ) / xiSpectralPoint q ^ (2 : ℕ) := by
  rw [suzukiScrewSmoothForm_eq_tsum]
  refine tsum_congr fun q => ?_
  rw [suzukiTestRayCoef_twistedOddTest, suzukiTestRayCoefBar_twistedOddTest]
  ring

/-! ## Summability of the ray energy -/

/-- The ray energy of any smooth zero-mean test is absolutely summable over the zero copies. -/
theorem summable_suzukiTestRayEnergy {a : ℝ} (φ : SuzukiSmoothZeroMeanTest a) :
    Summable (fun q : XiZeroCopy =>
      suzukiTestRayCoefBar φ q * suzukiTestRayCoef φ q / xiSpectralPoint q ^ (2 : ℕ)) := by
  set M : ℝ := (Real.exp (|a| / 2) + 1) * ∫ t : ℝ, ‖(φ : ℝ → ℂ) t‖ with hM
  have hM0 : 0 ≤ M := by
    rw [hM]
    exact mul_nonneg (by positivity) (integral_nonneg fun t => norm_nonneg _)
  refine Summable.of_norm_bounded (g := fun q : XiZeroCopy => M * M * (1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ)))
    (xiSpectralPoint_inv_sq_summable.mul_left (M * M)) fun q => ?_
  rw [norm_div, norm_mul, norm_pow]
  have h1 := norm_suzukiTestRayCoefBar_le φ q
  have h2 := norm_suzukiTestRayCoef_le φ q
  rw [← hM] at h1 h2
  have hz : 0 < ‖xiSpectralPoint q‖ := norm_pos_iff.mpr (xiSpectralPoint_ne_zero q)
  rw [div_le_iff₀ (by positivity)]
  calc ‖suzukiTestRayCoefBar φ q‖ * ‖suzukiTestRayCoef φ q‖
      ≤ M * M := mul_le_mul h1 h2 (norm_nonneg _) hM0
    _ = M * M * (1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ)) * ‖xiSpectralPoint q‖ ^ (2 : ℕ) := by
        field_simp

theorem summable_twistedOddTest_rayEnergy {a : ℝ} (ψ : OddSmoothProfile a) (γ : ℝ) :
    Summable (fun q : XiZeroCopy =>
      -(1 / 4 : ℂ) * twistedPairMoment ψ γ q ^ (2 : ℕ) / xiSpectralPoint q ^ (2 : ℕ)) := by
  refine (summable_suzukiTestRayEnergy (twistedOddTest ψ γ)).congr fun q => ?_
  rw [suzukiTestRayCoef_twistedOddTest, suzukiTestRayCoefBar_twistedOddTest]
  ring

/-- The real part of the twisted odd test form is the sum of the real parts of the ray terms. -/
theorem re_suzukiScrewSmoothForm_twistedOddTest {a : ℝ} (ψ : OddSmoothProfile a) (γ : ℝ) :
    (suzukiScrewSmoothForm (twistedOddTest ψ γ) (twistedOddTest ψ γ)).re
      = ∑' q : XiZeroCopy,
          (-(1 / 4 : ℂ) * twistedPairMoment ψ γ q ^ (2 : ℕ) / xiSpectralPoint q ^ (2 : ℕ)).re := by
  rw [suzukiScrewSmoothForm_twistedOddTest]
  exact Complex.re_tsum (summable_twistedOddTest_rayEnergy ψ γ)

/-! ## Copies on the critical line contribute nonnegative real terms -/

/-- On the critical line the twisted pair moment is purely imaginary. -/
theorem twistedPairMoment_re_of_im_eq_zero {a : ℝ} (ψ : OddSmoothProfile a) (γ : ℝ)
    {q : XiZeroCopy} (hq : (xiSpectralPoint q).im = 0) :
    (twistedPairMoment ψ γ q).re = 0 := by
  unfold twistedPairMoment
  rw [hq, neg_zero, Complex.add_re, twistedMoment_re_zero, twistedMoment_re_zero, add_zero]

/-- **Critical-line copies contribute the nonnegative real term `(Im(A_q + A'_q))²/(4 z_q²)`.** -/
theorem twistedOddTest_rayTerm_of_im_eq_zero {a : ℝ} (ψ : OddSmoothProfile a) (γ : ℝ)
    {q : XiZeroCopy} (hq : (xiSpectralPoint q).im = 0) :
    -(1 / 4 : ℂ) * twistedPairMoment ψ γ q ^ (2 : ℕ) / xiSpectralPoint q ^ (2 : ℕ)
      = (((twistedPairMoment ψ γ q).im ^ (2 : ℕ) / (4 * (xiSpectralPoint q).re ^ (2 : ℕ)) : ℝ) : ℂ) := by
  have hP : twistedPairMoment ψ γ q = ((twistedPairMoment ψ γ q).im : ℂ) * I := by
    apply Complex.ext
    · simp [twistedPairMoment_re_of_im_eq_zero ψ γ hq]
    · simp
  have hz : xiSpectralPoint q = ((xiSpectralPoint q).re : ℂ) := by
    apply Complex.ext
    · simp
    · simp [hq]
  have hre : (xiSpectralPoint q).re ≠ 0 := by
    intro h0
    apply xiSpectralPoint_ne_zero q
    rw [hz, h0, Complex.ofReal_zero]
  have hre' : ((xiSpectralPoint q).re : ℂ) ≠ 0 := by exact_mod_cast hre
  conv_lhs => rw [hP, hz]
  push_cast
  rw [mul_pow, Complex.I_sq]
  field_simp

theorem twistedOddTest_rayTerm_re_nonneg_of_im_eq_zero {a : ℝ} (ψ : OddSmoothProfile a) (γ : ℝ)
    {q : XiZeroCopy} (hq : (xiSpectralPoint q).im = 0) :
    0 ≤ (-(1 / 4 : ℂ) * twistedPairMoment ψ γ q ^ (2 : ℕ) / xiSpectralPoint q ^ (2 : ℕ)).re := by
  rw [twistedOddTest_rayTerm_of_im_eq_zero ψ γ hq, Complex.ofReal_re]
  positivity

/-- If every copy lies on the critical line, the twisted odd test form is nonnegative. -/
theorem re_suzukiScrewSmoothForm_twistedOddTest_nonneg_of_forall_im_eq_zero {a : ℝ}
    (ψ : OddSmoothProfile a) (γ : ℝ) (h : ∀ q : XiZeroCopy, (xiSpectralPoint q).im = 0) :
    0 ≤ (suzukiScrewSmoothForm (twistedOddTest ψ γ) (twistedOddTest ψ γ)).re := by
  rw [re_suzukiScrewSmoothForm_twistedOddTest]
  exact tsum_nonneg fun q => twistedOddTest_rayTerm_re_nonneg_of_im_eq_zero ψ γ (h q)

/-! ## The centred off-line term -/

/-- At the centre `γ = Re z_q` the first twisted moment is the real number
`∫ e^{(Re ρ_q − ½) u} ψ(u) du`. -/
theorem twistedPairMoment_centre {a : ℝ} (ψ : OddSmoothProfile a) (q : XiZeroCopy) :
    twistedPairMoment ψ (xiSpectralPoint q).re q
      = twistedMoment ψ (-(xiSpectralPoint q).im) 0
        + twistedMoment ψ (-(xiSpectralPoint q).im) (2 * (xiSpectralPoint q).re) := by
  unfold twistedPairMoment
  rw [sub_self]
  congr 2
  ring

theorem twistedMoment_centre_im {a : ℝ} (ψ : OddSmoothProfile a) (q : XiZeroCopy) :
    (twistedMoment ψ (-(xiSpectralPoint q).im) 0).im = 0 :=
  twistedMoment_im_zero ψ _

end

end RHTower
