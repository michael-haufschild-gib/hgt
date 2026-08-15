import GaloisForLFunctions.RHTower.ProlateModeSource

/-!
# The mean-zero source of a prolate mode

A single cut-off mode has nonzero total mass: the mass is the value of its Fourier transform at the
origin, which is a nonzero scalar times the mode's centre value.  Subtracting the mass-matched
dilate cancels it.  Dilating the source dilates its Fourier transform, so the mode reappears at a
rescaled radial argument and no second variational selection is needed.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped FourierTransform Real Topology

namespace RHTower

variable {a lam : ℝ} {Φ : ℝ → ℝ}

/-- The twisted integrand of the Fourier integral is integrable. -/
theorem integrable_fourier_integrand {F : ℝ → ℂ} (h : Integrable F) (w : ℝ) :
    Integrable (fun y : ℝ =>
      Complex.exp ((↑(-2 * Real.pi * y * w) : ℂ) * Complex.I) • F y) := by
  refine Integrable.mono' h.norm ?_ ?_
  · exact ((by fun_prop : Continuous fun y : ℝ =>
      Complex.exp ((↑(-2 * Real.pi * y * w) : ℂ) * Complex.I)).aestronglyMeasurable).smul
      h.aestronglyMeasurable
  · filter_upwards with y
    rw [norm_smul, Complex.norm_exp_ofReal_mul_I, one_mul]

/-- The Fourier integral is additive. -/
theorem fourier_sub' {F₁ F₂ : ℝ → ℂ} (h₁ : Integrable F₁) (h₂ : Integrable F₂) (w : ℝ) :
    𝓕 (fun y => F₁ y - F₂ y) w = 𝓕 F₁ w - 𝓕 F₂ w := by
  rw [Real.fourier_real_eq_integral_exp_smul, Real.fourier_real_eq_integral_exp_smul,
    Real.fourier_real_eq_integral_exp_smul,
    ← MeasureTheory.integral_sub (integrable_fourier_integrand h₁ w)
      (integrable_fourier_integrand h₂ w)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  show Complex.exp ((↑(-2 * Real.pi * y * w) : ℂ) * Complex.I) • (F₁ y - F₂ y)
    = Complex.exp ((↑(-2 * Real.pi * y * w) : ℂ) * Complex.I) • F₁ y
      - Complex.exp ((↑(-2 * Real.pi * y * w) : ℂ) * Complex.I) • F₂ y
  rw [smul_sub]

/-- The Fourier integral is homogeneous. -/
theorem fourier_const_mul' {F : ℝ → ℂ} (r : ℂ) (w : ℝ) :
    𝓕 (fun y => r * F y) w = r * 𝓕 F w := by
  rw [Real.fourier_real_eq_integral_exp_smul, Real.fourier_real_eq_integral_exp_smul,
    ← MeasureTheory.integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  show Complex.exp ((↑(-2 * Real.pi * y * w) : ℂ) * Complex.I) • (r * F y)
    = r * (Complex.exp ((↑(-2 * Real.pi * y * w) : ℂ) * Complex.I) • F y)
  rw [smul_eq_mul, smul_eq_mul]
  ring

/-- **Fourier transform of a dilate.** -/
theorem fourier_comp_div {g : ℝ → ℂ} (hlam : 0 < lam) (w : ℝ) :
    𝓕 (fun y => g (y / lam)) w = (lam : ℂ) * 𝓕 g (lam * w) := by
  rw [Real.fourier_real_eq_integral_exp_smul, Real.fourier_real_eq_integral_exp_smul]
  set F : ℝ → ℂ := fun y : ℝ =>
    Complex.exp ((↑(-2 * Real.pi * y * w) : ℂ) * Complex.I) • g (y / lam) with hF
  have hcomp := MeasureTheory.Measure.integral_comp_mul_left F lam
  have habs : |lam⁻¹| = lam⁻¹ := abs_of_pos (inv_pos.mpr hlam)
  rw [habs] at hcomp
  have hpt : ∀ y : ℝ, F (lam * y)
      = Complex.exp ((↑(-2 * Real.pi * y * (lam * w)) : ℂ) * Complex.I) • g y := by
    intro y
    show Complex.exp ((↑(-2 * Real.pi * (lam * y) * w) : ℂ) * Complex.I) * g (lam * y / lam)
      = Complex.exp ((↑(-2 * Real.pi * y * (lam * w)) : ℂ) * Complex.I) * g y
    have hdiv : lam * y / lam = y := by field_simp
    rw [hdiv]
    congr 2
    push_cast
    ring
  have hleft : (∫ y : ℝ, F (lam * y))
      = ∫ y : ℝ, Complex.exp ((↑(-2 * Real.pi * y * (lam * w)) : ℂ) * Complex.I) • g y :=
    integral_congr_ae (Filter.Eventually.of_forall hpt)
  rw [hleft] at hcomp
  have hfinal : (∫ y : ℝ, F y)
      = (lam : ℝ) • ∫ y : ℝ,
        Complex.exp ((↑(-2 * Real.pi * y * (lam * w)) : ℂ) * Complex.I) • g y := by
    rw [hcomp, smul_smul, mul_inv_cancel₀ hlam.ne', one_smul]
  rw [show (∫ y : ℝ, Complex.exp ((↑(-2 * Real.pi * y * w) : ℂ) * Complex.I) • g (y / lam))
      = ∫ y : ℝ, F y from rfl, hfinal, Complex.real_smul]

/-- Dilating the aperture is dilating the argument. -/
theorem prolateModeSource_dilate (hlam : 0 < lam) (y : ℝ) :
    prolateModeSource (lam * a) Φ y = prolateModeSource a Φ (y / lam) := by
  unfold prolateModeSource GaloisForLFunctions.HTGeometry.realSymmetricHalfEndpointCutoff
  have hmem : (y ∈ Ioo (-(lam * a)) (lam * a)) ↔ (y / lam ∈ Ioo (-a) a) := by
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨by rw [lt_div_iff₀ hlam]; nlinarith, by rw [div_lt_iff₀ hlam]; nlinarith⟩
    · rintro ⟨h1, h2⟩
      rw [lt_div_iff₀ hlam] at h1
      rw [div_lt_iff₀ hlam] at h2
      exact ⟨by nlinarith, by nlinarith⟩
  have hend : (y = -(lam * a) ∨ y = lam * a) ↔ (y / lam = -a ∨ y / lam = a) := by
    constructor
    · rintro (h | h)
      · exact Or.inl (by rw [h]; field_simp)
      · exact Or.inr (by rw [h]; field_simp)
    · rintro (h | h)
      · refine Or.inl ?_
        rw [div_eq_iff hlam.ne'] at h
        linarith
      · refine Or.inr ?_
        rw [div_eq_iff hlam.ne'] at h
        linarith
  have hval : Φ (y / (lam * a)) = Φ (y / lam / a) := by
    rw [div_div]
  by_cases h1 : y ∈ Ioo (-(lam * a)) (lam * a)
  · rw [if_pos h1, if_pos (hmem.mp h1)]
    show Φ (y / (lam * a)) = Φ (y / lam / a)
    exact hval
  · rw [if_neg h1, if_neg (fun h => h1 (hmem.mpr h))]
    by_cases h2 : y = -(lam * a) ∨ y = lam * a
    · rw [if_pos h2, if_pos (hend.mp h2)]
      show Φ (y / (lam * a)) / 2 = Φ (y / lam / a) / 2
      rw [hval]
    · rw [if_neg h2, if_neg (fun h => h2 (hend.mpr h))]

/-- The mass-matched mean-zero source of a prolate mode. -/
def prolateMeanZeroSource (a lam : ℝ) (Φ : ℝ → ℝ) : ℝ → ℝ :=
  fun y => prolateModeSource a Φ y - lam⁻¹ * prolateModeSource (lam * a) Φ y

theorem even_prolateMeanZeroSource (heven : Function.Even Φ) :
    Function.Even (prolateMeanZeroSource a lam Φ) := by
  intro y
  unfold prolateMeanZeroSource
  rw [even_prolateModeSource heven y, even_prolateModeSource heven y]

theorem measurable_prolateMeanZeroSource (hΦ : Continuous Φ) :
    Measurable (prolateMeanZeroSource a lam Φ) :=
  (measurable_prolateModeSource hΦ).sub
    ((measurable_prolateModeSource hΦ).const_mul lam⁻¹)

theorem abs_prolateMeanZeroSource_le {C : ℝ} (hlam : 0 < lam)
    (hC : ∀ x : ℝ, |Φ x| ≤ C) (hC0 : 0 ≤ C) (y : ℝ) :
    |prolateMeanZeroSource a lam Φ y| ≤ C + lam⁻¹ * C := by
  unfold prolateMeanZeroSource
  have h1 := abs_prolateModeSource_le (a := a) (Φ := Φ) hC hC0 y
  have h2 := abs_prolateModeSource_le (a := lam * a) (Φ := Φ) hC hC0 y
  have hstep : |prolateModeSource a Φ y - lam⁻¹ * prolateModeSource (lam * a) Φ y|
      ≤ |prolateModeSource a Φ y| + |lam⁻¹ * prolateModeSource (lam * a) Φ y| :=
    abs_sub _ _
  rw [abs_mul, abs_of_pos (inv_pos.mpr hlam)] at hstep
  nlinarith [inv_pos.mpr hlam, abs_nonneg (prolateModeSource (lam * a) Φ y)]

theorem integrable_prolateMeanZeroSource (ha : 0 < a) (hlam : 0 < lam) (hΦ : Continuous Φ)
    {C : ℝ} (hC : ∀ x : ℝ, |Φ x| ≤ C) (hC0 : 0 ≤ C) :
    Integrable (prolateMeanZeroSource a lam Φ) :=
  (integrable_prolateModeSource ha hΦ hC hC0).sub
    ((integrable_prolateModeSource (by positivity : (0 : ℝ) < lam * a) hΦ hC hC0).const_mul lam⁻¹)

theorem hasCompactSupport_prolateMeanZeroSource (ha : 0 < a) (hlam : 0 < lam) :
    HasCompactSupport (prolateMeanZeroSource a lam Φ) :=
  (hasCompactSupport_prolateModeSource (Φ := Φ) ha).sub
    ((hasCompactSupport_prolateModeSource (Φ := Φ)
      (by positivity : (0 : ℝ) < lam * a)).mul_left)

/-- **The Fourier transform of the mean-zero source.**  Both terms are the mode itself, at radial
arguments differing by the dilation. -/
theorem fourier_prolateMeanZeroSource (ha : 0 < a) (hlam : 0 < lam) (hΦ : Continuous Φ)
    (heven : Function.Even Φ) {C : ℝ} (hC : ∀ x : ℝ, |Φ x| ≤ C) (hC0 : 0 ≤ C) (x : ℝ) :
    𝓕 (fun y => ((prolateMeanZeroSource a lam Φ y : ℝ) : ℂ)) (a * x)
      = (a : ℂ) * (fourierBandTransform (2 * Real.pi * a ^ 2) (fun t => ((Φ t : ℝ) : ℂ)) x
          - fourierBandTransform (2 * Real.pi * a ^ 2) (fun t => ((Φ t : ℝ) : ℂ)) (lam * x)) := by
  have hgint : Integrable (fun y : ℝ => ((prolateModeSource a Φ y : ℝ) : ℂ)) :=
    (integrable_prolateModeSource ha hΦ hC hC0).ofReal
  have hdint : Integrable (fun y : ℝ => ((prolateModeSource (lam * a) Φ y : ℝ) : ℂ)) :=
    (integrable_prolateModeSource (by positivity : (0 : ℝ) < lam * a) hΦ hC hC0).ofReal
  have hsplit : (fun y : ℝ => ((prolateMeanZeroSource a lam Φ y : ℝ) : ℂ))
      = fun y : ℝ => ((prolateModeSource a Φ y : ℝ) : ℂ)
        - ((lam⁻¹ : ℝ) : ℂ) * ((prolateModeSource (lam * a) Φ y : ℝ) : ℂ) := by
    funext y
    unfold prolateMeanZeroSource
    push_cast
    ring
  rw [hsplit, fourier_sub' hgint (hdint.const_mul _), fourier_const_mul']
  have hdil : (fun y : ℝ => ((prolateModeSource (lam * a) Φ y : ℝ) : ℂ))
      = fun y : ℝ => ((prolateModeSource a Φ (y / lam) : ℝ) : ℂ) := by
    funext y
    rw [prolateModeSource_dilate hlam]
  rw [hdil, fourier_comp_div (g := fun y : ℝ => ((prolateModeSource a Φ y : ℝ) : ℂ)) hlam (a * x),
    fourier_prolateModeSource ha hΦ heven x]
  have hlamx : lam * (a * x) = a * (lam * x) := by ring
  rw [hlamx, fourier_prolateModeSource ha hΦ heven (lam * x)]
  have hlamne : ((lam : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hlam.ne'
  have hinv : ((lam⁻¹ : ℝ) : ℂ) * ((lam : ℝ) : ℂ) = 1 := by
    push_cast
    field_simp
  calc ((a : ℝ) : ℂ) * fourierBandTransform (2 * Real.pi * a ^ 2) (fun t => ((Φ t : ℝ) : ℂ)) x
        - ((lam⁻¹ : ℝ) : ℂ) * (((lam : ℝ) : ℂ) *
          (((a : ℝ) : ℂ) * fourierBandTransform (2 * Real.pi * a ^ 2)
            (fun t => ((Φ t : ℝ) : ℂ)) (lam * x)))
      = ((a : ℝ) : ℂ) * fourierBandTransform (2 * Real.pi * a ^ 2) (fun t => ((Φ t : ℝ) : ℂ)) x
        - (((lam⁻¹ : ℝ) : ℂ) * ((lam : ℝ) : ℂ)) *
          (((a : ℝ) : ℂ) * fourierBandTransform (2 * Real.pi * a ^ 2)
            (fun t => ((Φ t : ℝ) : ℂ)) (lam * x)) := by ring
    _ = _ := by rw [hinv]; ring

/-- **The mean-zero source has zero mass.** -/
theorem integral_prolateMeanZeroSource (ha : 0 < a) (hlam : 0 < lam) (hΦ : Continuous Φ)
    (heven : Function.Even Φ) {C : ℝ} (hC : ∀ x : ℝ, |Φ x| ≤ C) (hC0 : 0 ≤ C) :
    (∫ y : ℝ, prolateMeanZeroSource a lam Φ y) = 0 := by
  have hF := fourier_prolateMeanZeroSource ha hlam hΦ heven hC hC0 0
  rw [mul_zero, mul_zero, sub_self, mul_zero] at hF
  have hFourier0 : 𝓕 (fun y => ((prolateMeanZeroSource a lam Φ y : ℝ) : ℂ)) 0
      = ∫ y : ℝ, ((prolateMeanZeroSource a lam Φ y : ℝ) : ℂ) := by
    rw [Real.fourier_real_eq_integral_exp_smul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    show Complex.exp ((↑(-2 * Real.pi * y * 0) : ℂ) * Complex.I) •
        ((prolateMeanZeroSource a lam Φ y : ℝ) : ℂ)
      = ((prolateMeanZeroSource a lam Φ y : ℝ) : ℂ)
    rw [show (-2 * Real.pi * y * 0 : ℝ) = 0 by ring]
    simp
  rw [hFourier0, integral_complex_ofReal] at hF
  exact_mod_cast hF

/-- A compactly supported profile has finitely many nonzero integer translates at each point. -/
theorem summable_shift_of_support {g : ℝ → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (hg : ∀ y : ℝ, M < |y| → g y = 0) (x : ℝ) :
    Summable (fun k : ℤ => g (x + k)) := by
  classical
  set N : ℤ := ⌈M + |x|⌉ with hN
  refine summable_of_ne_finset_zero (s := Finset.Icc (-N) N) fun k hk => ?_
  have hNge : M + |x| ≤ (N : ℝ) := by
    rw [hN]
    exact Int.le_ceil _
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := le_trans (by positivity) hNge
  have hknot : (N : ℝ) < |(k : ℝ)| := by
    rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hk
    rcases hk with h | h
    · have hk' : (k : ℝ) < -(N : ℝ) := by exact_mod_cast h
      rw [abs_of_neg (by linarith : (k : ℝ) < 0)]
      linarith
    · have hk' : (N : ℝ) < (k : ℝ) := by exact_mod_cast h
      rw [abs_of_pos (by linarith : (0 : ℝ) < (k : ℝ))]
      linarith
  refine hg _ ?_
  have htri : |(k : ℝ)| ≤ |x + (k : ℝ)| + |x| := by
    have h := abs_add_le (x + (k : ℝ)) (-x)
    rw [show x + (k : ℝ) + -x = (k : ℝ) by ring, abs_neg] at h
    exact h
  linarith [hknot, hNge, htri]

/-- The periodization is additive on compactly supported profiles. -/
theorem realL1Periodization_sub {g₁ g₂ : ℝ → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (h₁ : ∀ y : ℝ, M < |y| → g₁ y = 0) (h₂ : ∀ y : ℝ, M < |y| → g₂ y = 0) (x : ℝ) :
    GaloisForLFunctions.HTGeometry.realL1Periodization (fun y => g₁ y - g₂ y) x
      = GaloisForLFunctions.HTGeometry.realL1Periodization g₁ x
        - GaloisForLFunctions.HTGeometry.realL1Periodization g₂ x := by
  unfold GaloisForLFunctions.HTGeometry.realL1Periodization
  exact (summable_shift_of_support hM h₁ x).tsum_sub (summable_shift_of_support hM h₂ x)

/-- The cut-off source vanishes past its aperture, in absolute value. -/
theorem prolateModeSource_eq_zero_of_abs (ha : 0 < a) {b : ℝ} (hb : 0 < b) {y : ℝ}
    (hy : a * b < |y|) : prolateModeSource a Φ (y / b) = 0 := by
  refine prolateModeSource_eq_zero_of_not_mem ha.le ?_
  intro hmem
  have h1 : |y / b| ≤ a := abs_le.mpr ⟨hmem.1, hmem.2⟩
  rw [abs_div, abs_of_pos hb, div_le_iff₀ hb] at h1
  linarith

/-- **The symmetric-Lebesgue boundary condition for the mean-zero source.** -/
theorem tendsto_symmetricLebesgue_prolateMeanZeroSource (ha : 0 < a) (hlam : 1 ≤ lam)
    {b : ℝ} (hb : 0 < b) (hΦ : Continuous Φ) (heven : Function.Even Φ) {C : ℝ}
    (hC : ∀ x : ℝ, |Φ x| ≤ C) (hC0 : 0 ≤ C) :
    Tendsto (fun s : ℝ =>
      ((∫ t in (0 : ℝ)..s,
        |poissonMuntzAngularDatum (prolateMeanZeroSource a lam Φ) b t -
          poissonMuntzAngularDatum (prolateMeanZeroSource a lam Φ) b 0| +
        |poissonMuntzAngularDatum (prolateMeanZeroSource a lam Φ) b (-t) -
          poissonMuntzAngularDatum (prolateMeanZeroSource a lam Φ) b 0|) / s))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hlam0 : (0 : ℝ) < lam := by linarith
  have hla : (0 : ℝ) < lam * a := by positivity
  set M : ℝ := lam * a * b with hM
  have hM0 : (0 : ℝ) ≤ M := by rw [hM]; positivity
  have hsupp₁ : ∀ y : ℝ, M < |y| → prolateModeSource a Φ (y / b) = 0 := by
    intro y hy
    refine prolateModeSource_eq_zero_of_abs ha hb ?_
    have : a * b ≤ M := by
      rw [hM]
      nlinarith [mul_pos ha hb]
    linarith
  have hsupp₂ : ∀ y : ℝ, M < |y| →
      lam⁻¹ * prolateModeSource (lam * a) Φ (y / b) = 0 := by
    intro y hy
    rw [prolateModeSource_eq_zero_of_abs hla hb (by rw [hM] at hy; exact hy), mul_zero]
  have hsplit : ∀ x : ℝ,
      poissonMuntzScaledPeriodization (prolateMeanZeroSource a lam Φ) b x
        = poissonMuntzScaledPeriodization (prolateModeSource a Φ) b x
          - GaloisForLFunctions.HTGeometry.realL1Periodization
              (fun y => lam⁻¹ * prolateModeSource (lam * a) Φ (y / b)) x := by
    intro x
    unfold poissonMuntzScaledPeriodization
    exact realL1Periodization_sub hM0 hsupp₁ hsupp₂ x
  have hcont₁ : ContinuousAt (poissonMuntzScaledPeriodization (prolateModeSource a Φ) b) 0 := by
    unfold poissonMuntzScaledPeriodization prolateModeSource
    exact GaloisForLFunctions.HTGeometry.continuousAt_realL1Periodization_symmetricHalfEndpointCutoff_zero
      ha hb (hΦ.comp (continuous_id.div_const a)) (fun y => by
        show Φ (-y / a) = Φ (y / a)
        rw [show -y / a = -(y / a) by ring, heven])
  have hcont₂ : ContinuousAt
      (GaloisForLFunctions.HTGeometry.realL1Periodization
        (fun y => lam⁻¹ * prolateModeSource (lam * a) Φ (y / b))) 0 := by
    have hbase : ContinuousAt
        (poissonMuntzScaledPeriodization (prolateModeSource (lam * a) Φ) b) 0 := by
      unfold poissonMuntzScaledPeriodization prolateModeSource
      exact GaloisForLFunctions.HTGeometry.continuousAt_realL1Periodization_symmetricHalfEndpointCutoff_zero
        hla hb (hΦ.comp (continuous_id.div_const (lam * a))) (fun y => by
          show Φ (-y / (lam * a)) = Φ (y / (lam * a))
          rw [show -y / (lam * a) = -(y / (lam * a)) by ring, heven])
    have hmulout : (GaloisForLFunctions.HTGeometry.realL1Periodization
        (fun y => lam⁻¹ * prolateModeSource (lam * a) Φ (y / b)))
        = fun x => lam⁻¹ * poissonMuntzScaledPeriodization (prolateModeSource (lam * a) Φ) b x := by
      funext x
      unfold GaloisForLFunctions.HTGeometry.realL1Periodization poissonMuntzScaledPeriodization
      exact tsum_mul_left
    rw [hmulout]
    exact hbase.const_smul lam⁻¹
  refine tendsto_poissonMuntz_symmetricLebesgueAverage_of_continuousAt
    (integrable_prolateMeanZeroSource ha hlam0 hΦ hC hC0) hb ?_
  have hfun : poissonMuntzScaledPeriodization (prolateMeanZeroSource a lam Φ) b
      = fun x => poissonMuntzScaledPeriodization (prolateModeSource a Φ) b x
        - GaloisForLFunctions.HTGeometry.realL1Periodization
            (fun y => lam⁻¹ * prolateModeSource (lam * a) Φ (y / b)) x := funext hsplit
  rw [hfun]
  exact hcont₁.sub hcont₂

end RHTower
