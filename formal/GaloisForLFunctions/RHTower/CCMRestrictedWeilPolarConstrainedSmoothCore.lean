import GaloisForLFunctions.RHTower.CCMRestrictedWeilPolarBumpSources

/-!
# The pole-vanishing subspace has a smooth strict-interior core

Two side bumps with positive polar moment determinant (`polarSideDet_pos`) correct the two pole
coefficients of any strict-interior smooth source by Cramer's rule.  Applied to the centre bump
this gives a **nonzero** smooth strict-interior source in the pole-vanishing subspace at every
aperture.  Applied to a smooth approximant of a constrained form-domain vector it gives a
constrained smooth approximant: the correction coefficients are bounded by the two pole
coefficients of the approximant, which vanish in the limit because the pole coefficients are
continuous on the form domain.  So **strict-interior smooth pole-vanishing sources are dense in
the pole-vanishing subspace of the form domain**, in the form norm.
-/

open Complex MeasureTheory Set

namespace RHTower

/-! ## Moments of the three bumps -/

noncomputable def polarMomentR (a : SuzukiPositiveAperture) (s : ℝ) : ℝ :=
  polarBumpMoment (a.1 / 2) (a.1 / 8) (a_div_eight_pos a) s

noncomputable def polarMomentL (a : SuzukiPositiveAperture) (s : ℝ) : ℝ :=
  polarBumpMoment (-a.1 / 2) (a.1 / 8) (a_div_eight_pos a) s

theorem inner_polar_polarRightBump (a : SuzukiPositiveAperture) (s : ℝ) :
    inner ℂ (ccmPolarApertureVector a s)
        (ccmArchimedeanFormToAperture a (polarRightBump a).toCCMFormVector) =
      (polarMomentR a s : ℂ) :=
  inner_polar_bumpInteriorSource a _ _ _ _ s

theorem inner_polar_polarLeftBump (a : SuzukiPositiveAperture) (s : ℝ) :
    inner ℂ (ccmPolarApertureVector a s)
        (ccmArchimedeanFormToAperture a (polarLeftBump a).toCCMFormVector) =
      (polarMomentL a s : ℂ) :=
  inner_polar_bumpInteriorSource a _ _ _ _ s

theorem polarSideDet_eq (a : SuzukiPositiveAperture) :
    polarSideDet a = polarMomentR a (1 / 2) * polarMomentL a (-1 / 2) -
      polarMomentL a (1 / 2) * polarMomentR a (-1 / 2) := rfl

theorem polarMomentR_nonneg (a : SuzukiPositiveAperture) (s : ℝ) : 0 ≤ polarMomentR a s :=
  polarBumpMoment_nonneg _ _ _ s

theorem polarMomentL_nonneg (a : SuzukiPositiveAperture) (s : ℝ) : 0 ≤ polarMomentL a s :=
  polarBumpMoment_nonneg _ _ _ s

/-! ## Cramer correction -/

/-- Cramer coefficient of the right bump for pole coefficients `cp, cm`. -/
noncomputable def polarCramerAlpha (a : SuzukiPositiveAperture) (cp cm : ℂ) : ℂ :=
  (cp * (polarMomentL a (-1 / 2) : ℂ) - cm * (polarMomentL a (1 / 2) : ℂ)) / (polarSideDet a : ℂ)

/-- Cramer coefficient of the left bump. -/
noncomputable def polarCramerBeta (a : SuzukiPositiveAperture) (cp cm : ℂ) : ℂ :=
  ((polarMomentR a (1 / 2) : ℂ) * cm - (polarMomentR a (-1 / 2) : ℂ) * cp) / (polarSideDet a : ℂ)

theorem polarSideDet_complex_ne_zero (a : SuzukiPositiveAperture) : (polarSideDet a : ℂ) ≠ 0 :=
  Complex.ofReal_ne_zero.mpr (polarSideDet_pos a).ne'

theorem polarCramer_plus (a : SuzukiPositiveAperture) (cp cm : ℂ) :
    cp + -polarCramerAlpha a cp cm * (polarMomentR a (1 / 2) : ℂ) +
      -polarCramerBeta a cp cm * (polarMomentL a (1 / 2) : ℂ) = 0 := by
  unfold polarCramerAlpha polarCramerBeta
  have hd := polarSideDet_complex_ne_zero a
  have hdef : (polarSideDet a : ℂ) = (polarMomentR a (1 / 2) : ℂ) * (polarMomentL a (-1 / 2) : ℂ) -
      (polarMomentL a (1 / 2) : ℂ) * (polarMomentR a (-1 / 2) : ℂ) := by
    rw [polarSideDet_eq]; push_cast; ring
  have hform : cp + -((cp * (polarMomentL a (-1 / 2) : ℂ) - cm * (polarMomentL a (1 / 2) : ℂ)) /
        (polarSideDet a : ℂ)) * (polarMomentR a (1 / 2) : ℂ) +
      -(((polarMomentR a (1 / 2) : ℂ) * cm - (polarMomentR a (-1 / 2) : ℂ) * cp) /
        (polarSideDet a : ℂ)) * (polarMomentL a (1 / 2) : ℂ) =
      (cp * (polarSideDet a : ℂ) -
        (cp * (polarMomentL a (-1 / 2) : ℂ) - cm * (polarMomentL a (1 / 2) : ℂ)) *
          (polarMomentR a (1 / 2) : ℂ) -
        ((polarMomentR a (1 / 2) : ℂ) * cm - (polarMomentR a (-1 / 2) : ℂ) * cp) *
          (polarMomentL a (1 / 2) : ℂ)) / (polarSideDet a : ℂ) := by
    field_simp
    ring
  rw [hform, div_eq_zero_iff]
  left
  rw [hdef]
  ring

theorem polarCramer_minus (a : SuzukiPositiveAperture) (cp cm : ℂ) :
    cm + -polarCramerAlpha a cp cm * (polarMomentR a (-1 / 2) : ℂ) +
      -polarCramerBeta a cp cm * (polarMomentL a (-1 / 2) : ℂ) = 0 := by
  unfold polarCramerAlpha polarCramerBeta
  have hd := polarSideDet_complex_ne_zero a
  have hdef : (polarSideDet a : ℂ) = (polarMomentR a (1 / 2) : ℂ) * (polarMomentL a (-1 / 2) : ℂ) -
      (polarMomentL a (1 / 2) : ℂ) * (polarMomentR a (-1 / 2) : ℂ) := by
    rw [polarSideDet_eq]; push_cast; ring
  have hform : cm + -((cp * (polarMomentL a (-1 / 2) : ℂ) - cm * (polarMomentL a (1 / 2) : ℂ)) /
        (polarSideDet a : ℂ)) * (polarMomentR a (-1 / 2) : ℂ) +
      -(((polarMomentR a (1 / 2) : ℂ) * cm - (polarMomentR a (-1 / 2) : ℂ) * cp) /
        (polarSideDet a : ℂ)) * (polarMomentL a (-1 / 2) : ℂ) =
      (cm * (polarSideDet a : ℂ) -
        (cp * (polarMomentL a (-1 / 2) : ℂ) - cm * (polarMomentL a (1 / 2) : ℂ)) *
          (polarMomentR a (-1 / 2) : ℂ) -
        ((polarMomentR a (1 / 2) : ℂ) * cm - (polarMomentR a (-1 / 2) : ℂ) * cp) *
          (polarMomentL a (-1 / 2) : ℂ)) / (polarSideDet a : ℂ) := by
    field_simp
    ring
  rw [hform, div_eq_zero_iff]
  left
  rw [hdef]
  ring

/-- The pole coefficients of a source. -/
noncomputable def polarCoeffPlus {a : SuzukiPositiveAperture} (g : CCMComplexSmoothInteriorSource a) : ℂ :=
  inner ℂ (ccmPolarApertureVector a (1 / 2)) (ccmArchimedeanFormToAperture a g.toCCMFormVector)

noncomputable def polarCoeffMinus {a : SuzukiPositiveAperture} (g : CCMComplexSmoothInteriorSource a) : ℂ :=
  inner ℂ (ccmPolarApertureVector a (-1 / 2)) (ccmArchimedeanFormToAperture a g.toCCMFormVector)

/-- The Cramer-corrected source: pole coefficients removed by the two side bumps. -/
noncomputable def polarCorrectedSource {a : SuzukiPositiveAperture}
    (g : CCMComplexSmoothInteriorSource a) : CCMComplexSmoothInteriorSource a :=
  g.combo (polarRightBump a) (polarLeftBump a)
    (-polarCramerAlpha a (polarCoeffPlus g) (polarCoeffMinus g))
    (-polarCramerBeta a (polarCoeffPlus g) (polarCoeffMinus g))

theorem polarCorrectedSource_toCCMFormVector {a : SuzukiPositiveAperture}
    (g : CCMComplexSmoothInteriorSource a) :
    (polarCorrectedSource g).toCCMFormVector =
      g.toCCMFormVector +
        (-polarCramerAlpha a (polarCoeffPlus g) (polarCoeffMinus g)) • (polarRightBump a).toCCMFormVector +
        (-polarCramerBeta a (polarCoeffPlus g) (polarCoeffMinus g)) • (polarLeftBump a).toCCMFormVector :=
  CCMComplexSmoothInteriorSource.combo_toCCMFormVector _ _ _ _ _

/-- **The corrected source is pole-vanishing.** -/
theorem isPolarConstrained_polarCorrectedSource {a : SuzukiPositiveAperture}
    (g : CCMComplexSmoothInteriorSource a) :
    IsPolarConstrained a (polarCorrectedSource g).toCCMFormVector := by
  unfold IsPolarConstrained polarCorrectedSource
  rw [inner_polar_combo, inner_polar_combo, inner_polar_polarRightBump, inner_polar_polarLeftBump,
    inner_polar_polarRightBump, inner_polar_polarLeftBump]
  exact ⟨polarCramer_plus a _ _, polarCramer_minus a _ _⟩

/-! ## A nonzero pole-vanishing smooth source -/

theorem polarCenterBump_zero (a : SuzukiPositiveAperture) : polarCenterBump a 0 = 1 := by
  show ((polarBumpFn 0 (a.1 / 8) (a_div_eight_pos a) 0 : ℝ) : ℂ) = 1
  rw [(polarBumpFn 0 (a.1 / 8) (a_div_eight_pos a)).one_of_mem_closedBall]
  · simp
  · rw [Metric.mem_closedBall, dist_self]
    show (0 : ℝ) ≤ a.1 / 8 / 2
    have := a.2; positivity

theorem polarRightBump_zero (a : SuzukiPositiveAperture) : polarRightBump a 0 = 0 := by
  show ((polarBumpFn (a.1 / 2) (a.1 / 8) (a_div_eight_pos a) 0 : ℝ) : ℂ) = 0
  rw [(polarBumpFn (a.1 / 2) (a.1 / 8) (a_div_eight_pos a)).zero_of_le_dist]
  · simp
  · rw [polarBumpFn_rOut, Real.dist_eq]
    have := a.2
    rw [abs_of_nonpos (by linarith)]
    linarith

theorem polarLeftBump_zero (a : SuzukiPositiveAperture) : polarLeftBump a 0 = 0 := by
  show ((polarBumpFn (-a.1 / 2) (a.1 / 8) (a_div_eight_pos a) 0 : ℝ) : ℂ) = 0
  rw [(polarBumpFn (-a.1 / 2) (a.1 / 8) (a_div_eight_pos a)).zero_of_le_dist]
  · simp
  · rw [polarBumpFn_rOut, Real.dist_eq]
    have := a.2
    rw [abs_of_nonneg (by linarith)]
    linarith

/-- The corrected centre bump takes the value `1` at the origin. -/
theorem polarCorrectedSource_polarCenterBump_zero (a : SuzukiPositiveAperture) :
    polarCorrectedSource (polarCenterBump a) 0 = 1 := by
  unfold polarCorrectedSource
  rw [CCMComplexSmoothInteriorSource.combo_apply, polarCenterBump_zero, polarRightBump_zero,
    polarLeftBump_zero]
  ring

/-- A source with a nonzero value has a nonzero physical embedding. -/
theorem ccmArchimedeanFormToAperture_toCCMFormVector_ne_zero_of_apply_ne_zero
    {a : SuzukiPositiveAperture} (g : CCMComplexSmoothInteriorSource a) {x : ℝ} (hx : g x ≠ 0) :
    ccmArchimedeanFormToAperture a g.toCCMFormVector ≠ 0 := by
  intro h0
  have hcoe := g.toCCMFormVector_physical_coeFn
  rw [h0] at hcoe
  have hzero : ((0 : suzukiApertureHilbert a) : SoninL2) = 0 := rfl
  rw [hzero] at hcoe
  have hz : ((0 : SoninL2) : ℝ → ℂ) =ᵐ[volume] (0 : ℝ → ℂ) := Lp.coeFn_zero ℂ 2 volume
  have hg : (g : ℝ → ℂ) =ᵐ[volume] (0 : ℝ → ℂ) := by
    filter_upwards [hcoe, hz] with y h1 h2
    rw [← h1, h2]
  have heq : (g : ℝ → ℂ) = 0 :=
    (Continuous.ae_eq_iff_eq volume g.continuous continuous_const).mp hg
  exact hx (by rw [heq]; rfl)

/-- **A nonzero pole-vanishing smooth strict-interior source exists at every aperture.** -/
theorem exists_polarConstrained_smooth_ne_zero (a : SuzukiPositiveAperture) :
    ∃ g : CCMComplexSmoothInteriorSource a,
      IsPolarConstrained a g.toCCMFormVector ∧
        ccmArchimedeanFormToAperture a g.toCCMFormVector ≠ 0 :=
  ⟨polarCorrectedSource (polarCenterBump a), isPolarConstrained_polarCorrectedSource _,
    ccmArchimedeanFormToAperture_toCCMFormVector_ne_zero_of_apply_ne_zero _
      (by rw [polarCorrectedSource_polarCenterBump_zero]; exact one_ne_zero)⟩

/-! ## Constrained smooth-core density -/

theorem norm_polarCramerAlpha_le (a : SuzukiPositiveAperture) (cp cm : ℂ) :
    ‖polarCramerAlpha a cp cm‖ ≤
      (‖cp‖ * polarMomentL a (-1 / 2) + ‖cm‖ * polarMomentL a (1 / 2)) / polarSideDet a := by
  unfold polarCramerAlpha
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (polarSideDet_pos a)]
  refine div_le_div_of_nonneg_right ?_ (polarSideDet_pos a).le
  calc ‖cp * (polarMomentL a (-1 / 2) : ℂ) - cm * (polarMomentL a (1 / 2) : ℂ)‖
      ≤ ‖cp * (polarMomentL a (-1 / 2) : ℂ)‖ + ‖cm * (polarMomentL a (1 / 2) : ℂ)‖ :=
        norm_sub_le _ _
    _ = ‖cp‖ * polarMomentL a (-1 / 2) + ‖cm‖ * polarMomentL a (1 / 2) := by
        rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
          Real.norm_eq_abs, abs_of_nonneg (polarMomentL_nonneg a _),
          abs_of_nonneg (polarMomentL_nonneg a _)]

theorem norm_polarCramerBeta_le (a : SuzukiPositiveAperture) (cp cm : ℂ) :
    ‖polarCramerBeta a cp cm‖ ≤
      (polarMomentR a (1 / 2) * ‖cm‖ + polarMomentR a (-1 / 2) * ‖cp‖) / polarSideDet a := by
  unfold polarCramerBeta
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (polarSideDet_pos a)]
  refine div_le_div_of_nonneg_right ?_ (polarSideDet_pos a).le
  calc ‖(polarMomentR a (1 / 2) : ℂ) * cm - (polarMomentR a (-1 / 2) : ℂ) * cp‖
      ≤ ‖(polarMomentR a (1 / 2) : ℂ) * cm‖ + ‖(polarMomentR a (-1 / 2) : ℂ) * cp‖ :=
        norm_sub_le _ _
    _ = polarMomentR a (1 / 2) * ‖cm‖ + polarMomentR a (-1 / 2) * ‖cp‖ := by
        rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
          Real.norm_eq_abs, abs_of_nonneg (polarMomentR_nonneg a _),
          abs_of_nonneg (polarMomentR_nonneg a _)]

/-- The pole coefficient of a source is controlled by its distance to a constrained vector. -/
theorem norm_polarCoeff_le_of_constrained {a : SuzukiPositiveAperture}
    (g : CCMComplexSmoothInteriorSource a) (u : CCMArchimedeanFormDomain a) (s : ℝ) :
    ‖inner ℂ (ccmPolarApertureVector a s)
        (ccmArchimedeanFormToAperture a g.toCCMFormVector)‖ ≤
      ‖ccmPolarApertureVector a s‖ * ‖ccmArchimedeanFormToAperture a‖ *
        ‖g.toCCMFormVector - u‖ + ‖inner ℂ (ccmPolarApertureVector a s)
          (ccmArchimedeanFormToAperture a u)‖ := by
  have h : inner ℂ (ccmPolarApertureVector a s)
      (ccmArchimedeanFormToAperture a g.toCCMFormVector) =
      inner ℂ (ccmPolarApertureVector a s)
        (ccmArchimedeanFormToAperture a (g.toCCMFormVector - u)) +
      inner ℂ (ccmPolarApertureVector a s) (ccmArchimedeanFormToAperture a u) := by
    rw [map_sub, inner_sub_right]; ring
  rw [h]
  refine (norm_add_le _ _).trans ?_
  gcongr
  calc ‖inner ℂ (ccmPolarApertureVector a s)
        (ccmArchimedeanFormToAperture a (g.toCCMFormVector - u))‖
      ≤ ‖ccmPolarApertureVector a s‖ *
          ‖ccmArchimedeanFormToAperture a (g.toCCMFormVector - u)‖ := by
        convert norm_inner_le_norm (𝕜 := ℂ) (ccmPolarApertureVector a s)
          (ccmArchimedeanFormToAperture a (g.toCCMFormVector - u)) using 2
    _ ≤ ‖ccmPolarApertureVector a s‖ *
          (‖ccmArchimedeanFormToAperture a‖ * ‖g.toCCMFormVector - u‖) := by
        gcongr
        exact ContinuousLinearMap.le_opNorm _ _
    _ = _ := by ring

/-- The constant controlling the Cramer correction in terms of the approximation distance. -/
noncomputable def polarCorrectionConstant (a : SuzukiPositiveAperture) : ℝ :=
  ((‖ccmPolarApertureVector a (1 / 2)‖ * ‖ccmArchimedeanFormToAperture a‖ *
        polarMomentL a (-1 / 2) +
      ‖ccmPolarApertureVector a (-1 / 2)‖ * ‖ccmArchimedeanFormToAperture a‖ *
        polarMomentL a (1 / 2)) / polarSideDet a) *
      ‖(polarRightBump a).toCCMFormVector‖ +
    ((polarMomentR a (1 / 2) *
        (‖ccmPolarApertureVector a (-1 / 2)‖ * ‖ccmArchimedeanFormToAperture a‖) +
      polarMomentR a (-1 / 2) *
        (‖ccmPolarApertureVector a (1 / 2)‖ * ‖ccmArchimedeanFormToAperture a‖)) /
        polarSideDet a) *
      ‖(polarLeftBump a).toCCMFormVector‖

theorem polarCorrectionConstant_nonneg (a : SuzukiPositiveAperture) :
    0 ≤ polarCorrectionConstant a := by
  unfold polarCorrectionConstant
  have hdet := polarSideDet_pos a
  have h1 := polarMomentL_nonneg a (-1 / 2)
  have h2 := polarMomentL_nonneg a (1 / 2)
  have h3 := polarMomentR_nonneg a (1 / 2)
  have h4 := polarMomentR_nonneg a (-1 / 2)
  have hp := norm_nonneg (ccmPolarApertureVector a (1 / 2))
  have hm := norm_nonneg (ccmPolarApertureVector a (-1 / 2))
  have hJ := norm_nonneg (ccmArchimedeanFormToAperture a)
  have hR := norm_nonneg (polarRightBump a).toCCMFormVector
  have hL := norm_nonneg (polarLeftBump a).toCCMFormVector
  positivity

/-- **Distance of the corrected source to a constrained vector.** -/
theorem norm_polarCorrectedSource_sub_le {a : SuzukiPositiveAperture}
    (g : CCMComplexSmoothInteriorSource a) (u : CCMArchimedeanFormDomain a)
    (hu : IsPolarConstrained a u) :
    ‖(polarCorrectedSource g).toCCMFormVector - u‖ ≤
      (1 + polarCorrectionConstant a) * ‖g.toCCMFormVector - u‖ := by
  set d := ‖g.toCCMFormVector - u‖ with hd
  set cp := polarCoeffPlus g
  set cm := polarCoeffMinus g
  set Np := ‖ccmPolarApertureVector a (1 / 2)‖ * ‖ccmArchimedeanFormToAperture a‖ with hNp
  set Nm := ‖ccmPolarApertureVector a (-1 / 2)‖ * ‖ccmArchimedeanFormToAperture a‖ with hNm
  have hcp : ‖cp‖ ≤ Np * d := by
    have := norm_polarCoeff_le_of_constrained g u (1 / 2)
    rw [hu.1, norm_zero, add_zero] at this
    exact this
  have hcm : ‖cm‖ ≤ Nm * d := by
    have := norm_polarCoeff_le_of_constrained g u (-1 / 2)
    rw [hu.2, norm_zero, add_zero] at this
    exact this
  have hdet := polarSideDet_pos a
  have hLm := polarMomentL_nonneg a (-1 / 2)
  have hLp := polarMomentL_nonneg a (1 / 2)
  have hRp := polarMomentR_nonneg a (1 / 2)
  have hRm := polarMomentR_nonneg a (-1 / 2)
  have hd0 : 0 ≤ d := norm_nonneg _
  have hα : ‖polarCramerAlpha a cp cm‖ ≤
      ((Np * polarMomentL a (-1 / 2) + Nm * polarMomentL a (1 / 2)) / polarSideDet a) * d := by
    refine (norm_polarCramerAlpha_le a cp cm).trans ?_
    rw [div_mul_eq_mul_div]
    gcongr
    nlinarith [mul_le_mul_of_nonneg_right hcp hLm, mul_le_mul_of_nonneg_right hcm hLp]
  have hβ : ‖polarCramerBeta a cp cm‖ ≤
      ((polarMomentR a (1 / 2) * Nm + polarMomentR a (-1 / 2) * Np) / polarSideDet a) * d := by
    refine (norm_polarCramerBeta_le a cp cm).trans ?_
    rw [div_mul_eq_mul_div]
    gcongr
    nlinarith [mul_le_mul_of_nonneg_left hcm hRp, mul_le_mul_of_nonneg_left hcp hRm]
  rw [polarCorrectedSource_toCCMFormVector]
  have hsplit : g.toCCMFormVector + (-polarCramerAlpha a cp cm) • (polarRightBump a).toCCMFormVector +
      (-polarCramerBeta a cp cm) • (polarLeftBump a).toCCMFormVector - u =
      (g.toCCMFormVector - u) + (-polarCramerAlpha a cp cm) • (polarRightBump a).toCCMFormVector +
      (-polarCramerBeta a cp cm) • (polarLeftBump a).toCCMFormVector := by abel
  rw [hsplit]
  refine (norm_add_le _ _).trans ?_
  refine (add_le_add (norm_add_le (g.toCCMFormVector - u)
    ((-polarCramerAlpha a cp cm) • (polarRightBump a).toCCMFormVector)) le_rfl).trans ?_
  rw [norm_smul, norm_smul, norm_neg, norm_neg]
  have hR : 0 ≤ ‖(polarRightBump a).toCCMFormVector‖ := norm_nonneg _
  have hL : 0 ≤ ‖(polarLeftBump a).toCCMFormVector‖ := norm_nonneg _
  unfold polarCorrectionConstant
  rw [← hNp, ← hNm]
  nlinarith [mul_le_mul_of_nonneg_right hα hR, mul_le_mul_of_nonneg_right hβ hL]

/-- **Constrained smooth-core density.**  Every pole-vanishing form-domain vector is a form-norm
limit of pole-vanishing smooth strict-interior sources. -/
theorem exists_polarConstrained_smooth_close (a : SuzukiPositiveAperture)
    (u : CCMArchimedeanFormDomain a) (hu : IsPolarConstrained a u) {δ : ℝ} (hδ : 0 < δ) :
    ∃ g : CCMComplexSmoothInteriorSource a,
      IsPolarConstrained a g.toCCMFormVector ∧ ‖g.toCCMFormVector - u‖ < δ := by
  have hM : 0 < 1 + polarCorrectionConstant a := by
    linarith [polarCorrectionConstant_nonneg a]
  obtain ⟨g₀, hg₀⟩ := (Metric.denseRange_iff.mp
    (denseRange_ccmComplexSmoothInteriorSource_toCCMFormVector a)) u
    (δ / (1 + polarCorrectionConstant a)) (by positivity)
  refine ⟨polarCorrectedSource g₀, isPolarConstrained_polarCorrectedSource g₀, ?_⟩
  have h1 := norm_polarCorrectedSource_sub_le g₀ u hu
  rw [dist_eq_norm u g₀.toCCMFormVector, norm_sub_rev u g₀.toCCMFormVector] at hg₀
  calc ‖(polarCorrectedSource g₀).toCCMFormVector - u‖
      ≤ (1 + polarCorrectionConstant a) * ‖g₀.toCCMFormVector - u‖ := h1
    _ < (1 + polarCorrectionConstant a) * (δ / (1 + polarCorrectionConstant a)) := by
        gcongr
    _ = δ := by field_simp

end RHTower
