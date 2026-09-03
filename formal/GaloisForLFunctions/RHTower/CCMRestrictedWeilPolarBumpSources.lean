import GaloisForLFunctions.RHTower.CCMRestrictedWeilPolarConstrainedRightContinuity

/-!
# Smooth bump sources with prescribed pole coefficients

The pole coefficients of a strict-interior smooth source `g` are its exponential moments
`∫ e^{±x/2} g(x) dx` (`inner_ccmPolarApertureVector_ccmComplexSmoothFormVector`).  This file
builds real smooth bumps as strict-interior sources, bounds their exponential moments by the mass
times `e^{±c/2 ∓ r/2}` for a bump of mass `m` centred at `c` with radius `r`, and proves that two
bumps centred at `±a/2` with radius `a/8` have a strictly positive polar moment determinant.
Linear combinations of sources are again sources, with form vector the same linear combination.
Consequently the pole-vanishing subspace contains a nonzero smooth strict-interior source at every
aperture: a third bump at the origin corrected by the two side bumps.

These are the constructive inputs for the constrained smooth core of the pole-vanishing subspace.
-/

open Complex MeasureTheory Set

namespace RHTower

/-- The standard bump centred at `c` with inner radius `r/2` and outer radius `r`. -/
noncomputable def polarBumpFn (c r : ℝ) (hr : 0 < r) : ContDiffBump c :=
  ⟨r / 2, r, by positivity, by linarith⟩

theorem polarBumpFn_rOut (c r : ℝ) (hr : 0 < r) : (polarBumpFn c r hr).rOut = r := rfl

/-- A real bump as a strict-interior complex source. -/
noncomputable def bumpInteriorSource (a : SuzukiPositiveAperture) (c r : ℝ) (hr : 0 < r)
    (hc : Metric.closedBall c r ⊆ Ioo (-a.1) a.1) : CCMComplexSmoothInteriorSource a where
  toFun := fun x => ((polarBumpFn c r hr x : ℝ) : ℂ)
  smooth := Complex.ofRealCLM.contDiff.comp (polarBumpFn c r hr).contDiff
  hasCompactSupport := (polarBumpFn c r hr).hasCompactSupport.comp_left Complex.ofReal_zero
  tsupport_subset := by
    refine (tsupport_comp_subset Complex.ofReal_zero (polarBumpFn c r hr)).trans ?_
    rw [(polarBumpFn c r hr).tsupport_eq, polarBumpFn_rOut]
    exact hc

theorem bumpInteriorSource_apply (a : SuzukiPositiveAperture) (c r : ℝ) (hr : 0 < r)
    (hc : Metric.closedBall c r ⊆ Ioo (-a.1) a.1) (x : ℝ) :
    bumpInteriorSource a c r hr hc x = ((polarBumpFn c r hr x : ℝ) : ℂ) := rfl

/-- The exponential moment `∫ e^{s x} φ(x) dx` of the bump. -/
noncomputable def polarBumpMoment (c r : ℝ) (hr : 0 < r) (s : ℝ) : ℝ :=
  ∫ x, Real.exp (s * x) * polarBumpFn c r hr x

/-- The mass of the bump. -/
noncomputable def polarBumpMass (c r : ℝ) (hr : 0 < r) : ℝ := ∫ x, polarBumpFn c r hr x

theorem polarBumpMass_pos (c r : ℝ) (hr : 0 < r) : 0 < polarBumpMass c r hr :=
  (polarBumpFn c r hr).integral_pos

theorem continuous_exp_mul_polarBumpFn (c r : ℝ) (hr : 0 < r) (s : ℝ) :
    Continuous fun x => Real.exp (s * x) * polarBumpFn c r hr x :=
  (Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
    (polarBumpFn c r hr).continuous

theorem hasCompactSupport_exp_mul_polarBumpFn (c r : ℝ) (hr : 0 < r) (s : ℝ) :
    HasCompactSupport fun x => Real.exp (s * x) * polarBumpFn c r hr x :=
  (polarBumpFn c r hr).hasCompactSupport.mul_left

theorem integrable_exp_mul_polarBumpFn (c r : ℝ) (hr : 0 < r) (s : ℝ) :
    Integrable fun x => Real.exp (s * x) * polarBumpFn c r hr x :=
  (continuous_exp_mul_polarBumpFn c r hr s).integrable_of_hasCompactSupport
    (hasCompactSupport_exp_mul_polarBumpFn c r hr s)

/-- Pointwise: on the support of the bump, `s x ≤ s c + |s| r`. -/
theorem exp_mul_polarBumpFn_le (c r : ℝ) (hr : 0 < r) (s x : ℝ) :
    Real.exp (s * x) * polarBumpFn c r hr x ≤
      Real.exp (s * c + |s| * r) * polarBumpFn c r hr x := by
  by_cases h0 : polarBumpFn c r hr x = 0
  · rw [h0]; simp
  · have hx : x ∈ Metric.ball c (polarBumpFn c r hr).rOut := by
      rw [← (polarBumpFn c r hr).support_eq]
      exact h0
    rw [polarBumpFn_rOut, Metric.mem_ball, Real.dist_eq] at hx
    have hsx : s * x ≤ s * c + |s| * r := by
      have h1 : s * x - s * c = s * (x - c) := by ring
      have h2 : s * (x - c) ≤ |s| * |x - c| := by
        rw [← abs_mul]; exact le_abs_self _
      have h3 : |s| * |x - c| ≤ |s| * r := by
        exact mul_le_mul_of_nonneg_left hx.le (abs_nonneg s)
      linarith
    exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hsx) (polarBumpFn c r hr).nonneg

theorem le_exp_mul_polarBumpFn (c r : ℝ) (hr : 0 < r) (s x : ℝ) :
    Real.exp (s * c - |s| * r) * polarBumpFn c r hr x ≤
      Real.exp (s * x) * polarBumpFn c r hr x := by
  by_cases h0 : polarBumpFn c r hr x = 0
  · rw [h0]; simp
  · have hx : x ∈ Metric.ball c (polarBumpFn c r hr).rOut := by
      rw [← (polarBumpFn c r hr).support_eq]
      exact h0
    rw [polarBumpFn_rOut, Metric.mem_ball, Real.dist_eq] at hx
    have hsx : s * c - |s| * r ≤ s * x := by
      have h1 : s * c - s * x = s * (c - x) := by ring
      have h2 : s * (c - x) ≤ |s| * |c - x| := by
        rw [← abs_mul]; exact le_abs_self _
      have h3 : |s| * |c - x| ≤ |s| * r := by
        rw [abs_sub_comm]
        exact mul_le_mul_of_nonneg_left hx.le (abs_nonneg s)
      linarith
    exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hsx) (polarBumpFn c r hr).nonneg

/-- **Upper moment bound.** -/
theorem polarBumpMoment_le (c r : ℝ) (hr : 0 < r) (s : ℝ) :
    polarBumpMoment c r hr s ≤ Real.exp (s * c + |s| * r) * polarBumpMass c r hr := by
  unfold polarBumpMoment polarBumpMass
  rw [← integral_const_mul]
  refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => ?_) ?_
    (Filter.Eventually.of_forall fun x => exp_mul_polarBumpFn_le c r hr s x)
  · exact mul_nonneg (Real.exp_pos _).le (polarBumpFn c r hr).nonneg
  · exact ((polarBumpFn c r hr).continuous.integrable_of_hasCompactSupport
      (polarBumpFn c r hr).hasCompactSupport).const_mul _

/-- **Lower moment bound.** -/
theorem le_polarBumpMoment (c r : ℝ) (hr : 0 < r) (s : ℝ) :
    Real.exp (s * c - |s| * r) * polarBumpMass c r hr ≤ polarBumpMoment c r hr s := by
  unfold polarBumpMoment polarBumpMass
  rw [← integral_const_mul]
  refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => ?_)
    (integrable_exp_mul_polarBumpFn c r hr s)
    (Filter.Eventually.of_forall fun x => le_exp_mul_polarBumpFn c r hr s x)
  exact mul_nonneg (Real.exp_pos _).le (polarBumpFn c r hr).nonneg

theorem polarBumpMoment_nonneg (c r : ℝ) (hr : 0 < r) (s : ℝ) : 0 ≤ polarBumpMoment c r hr s :=
  le_trans (mul_nonneg (Real.exp_pos _).le (polarBumpMass_pos c r hr).le)
    (le_polarBumpMoment c r hr s)

/-- The pole coefficient of a bump source is its exponential moment. -/
theorem inner_polar_bumpInteriorSource (a : SuzukiPositiveAperture) (c r : ℝ) (hr : 0 < r)
    (hc : Metric.closedBall c r ⊆ Ioo (-a.1) a.1) (s : ℝ) :
    inner ℂ (ccmPolarApertureVector a s)
        (ccmArchimedeanFormToAperture a (bumpInteriorSource a c r hr hc).toCCMFormVector) =
      (polarBumpMoment c r hr s : ℂ) := by
  rw [inner_ccmPolarApertureVector_ccmComplexSmoothFormVector]
  unfold polarBumpMoment
  change ∫ x : ℝ, (Real.exp (s * x) : ℂ) * ((polarBumpFn c r hr x : ℝ) : ℂ) = _
  calc ∫ x : ℝ, (Real.exp (s * x) : ℂ) * ((polarBumpFn c r hr x : ℝ) : ℂ)
      = ∫ x : ℝ, ((Real.exp (s * x) * polarBumpFn c r hr x : ℝ) : ℂ) := by
        congr 1
        funext x
        push_cast
        ring
    _ = ((∫ x : ℝ, Real.exp (s * x) * polarBumpFn c r hr x : ℝ) : ℂ) := integral_ofReal

/-- **The polar moment determinant of two side bumps is strictly positive.** -/
theorem polar_det_pos {A₁ B₁ A₂ B₂ m₁ m₂ q : ℝ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hq : 0 < q)
    (hA₁ : m₁ * Real.exp q ≤ A₁) (hB₂ : m₂ * Real.exp q ≤ B₂)
    (hA₂ : A₂ ≤ m₂ * Real.exp (-q)) (hB₁ : B₁ ≤ m₁ * Real.exp (-q))
    (_hA₂0 : 0 ≤ A₂) (hB₁0 : 0 ≤ B₁) :
    0 < A₁ * B₂ - A₂ * B₁ := by
  have he : Real.exp (-q) < Real.exp q := Real.exp_lt_exp.mpr (by linarith)
  have he0 : 0 < Real.exp (-q) := Real.exp_pos _
  have h1 : m₁ * Real.exp q * (m₂ * Real.exp q) ≤ A₁ * B₂ := by
    apply mul_le_mul hA₁ hB₂ (by positivity) (by linarith [mul_pos hm₁ (Real.exp_pos q)])
  have h2 : A₂ * B₁ ≤ m₂ * Real.exp (-q) * (m₁ * Real.exp (-q)) :=
    mul_le_mul hA₂ hB₁ hB₁0 (by positivity)
  have h3 : m₂ * Real.exp (-q) * (m₁ * Real.exp (-q)) < m₁ * Real.exp q * (m₂ * Real.exp q) := by
    have : Real.exp (-q) * Real.exp (-q) < Real.exp q * Real.exp q :=
      mul_lt_mul'' he he he0.le he0.le
    nlinarith [mul_pos hm₁ hm₂]
  linarith

/-! ## Linear combinations of strict-interior sources -/

/-- `u + α v + β w` as a strict-interior source. -/
noncomputable def CCMComplexSmoothInteriorSource.combo {a : SuzukiPositiveAperture}
    (u v w : CCMComplexSmoothInteriorSource a) (α β : ℂ) :
    CCMComplexSmoothInteriorSource a where
  toFun := fun x => u x + α * v x + β * w x
  smooth := by
    have hv : ContDiff ℝ (⊤ : ℕ∞) fun x => α * v x := by
      have := v.smooth.const_smul α
      simpa [smul_eq_mul] using this
    have hw : ContDiff ℝ (⊤ : ℕ∞) fun x => β * w x := by
      have := w.smooth.const_smul β
      simpa [smul_eq_mul] using this
    exact (u.smooth.add hv).add hw
  hasCompactSupport := by
    have hv : HasCompactSupport fun x => α * v x :=
      v.hasCompactSupport.comp_left (mul_zero α)
    have hw : HasCompactSupport fun x => β * w x :=
      w.hasCompactSupport.comp_left (mul_zero β)
    exact (u.hasCompactSupport.add hv).add hw
  tsupport_subset := by
    have hv : tsupport (fun x => α * v x) ⊆ Ioo (-a.1) a.1 :=
      (tsupport_comp_subset (mul_zero α) (v : ℝ → ℂ)).trans v.tsupport_subset
    have hw : tsupport (fun x => β * w x) ⊆ Ioo (-a.1) a.1 :=
      (tsupport_comp_subset (mul_zero β) (w : ℝ → ℂ)).trans w.tsupport_subset
    refine (tsupport_add _ _).trans (union_subset ?_ hw)
    exact (tsupport_add _ _).trans (union_subset u.tsupport_subset hv)

theorem CCMComplexSmoothInteriorSource.combo_apply {a : SuzukiPositiveAperture}
    (u v w : CCMComplexSmoothInteriorSource a) (α β : ℂ) (x : ℝ) :
    u.combo v w α β x = u x + α * v x + β * w x := rfl

theorem inner_smul_right_aperture (a : SuzukiPositiveAperture) (p x : suzukiApertureHilbert a)
    (c : ℂ) : inner ℂ p (c • x) = c * inner ℂ p x := by
  rw [Submodule.coe_inner, Submodule.coe_inner, Submodule.coe_smul, inner_smul_right]

/-- **The form vector of a combination is the combination of the form vectors.** -/
theorem CCMComplexSmoothInteriorSource.combo_toCCMFormVector {a : SuzukiPositiveAperture}
    (u v w : CCMComplexSmoothInteriorSource a) (α β : ℂ) :
    (u.combo v w α β).toCCMFormVector =
      u.toCCMFormVector + α • v.toCCMFormVector + β • w.toCCMFormVector := by
  apply ccmArchimedeanFormToAperture_injective
  rw [map_add, map_add, map_smul, map_smul]
  apply Subtype.ext
  rw [Submodule.coe_add, Submodule.coe_add, Submodule.coe_smul, Submodule.coe_smul]
  rw [Lp.ext_iff]
  have h1 := (u.combo v w α β).toCCMFormVector_physical_coeFn
  have hu := u.toCCMFormVector_physical_coeFn
  have hv := v.toCCMFormVector_physical_coeFn
  have hw := w.toCCMFormVector_physical_coeFn
  have hadd1 := Lp.coeFn_add
    ((ccmArchimedeanFormToAperture a u.toCCMFormVector : SoninL2) +
      α • (ccmArchimedeanFormToAperture a v.toCCMFormVector : SoninL2))
    (β • (ccmArchimedeanFormToAperture a w.toCCMFormVector : SoninL2))
  have hadd2 := Lp.coeFn_add
    (ccmArchimedeanFormToAperture a u.toCCMFormVector : SoninL2)
    (α • (ccmArchimedeanFormToAperture a v.toCCMFormVector : SoninL2))
  have hsv := Lp.coeFn_smul α (ccmArchimedeanFormToAperture a v.toCCMFormVector : SoninL2)
  have hsw := Lp.coeFn_smul β (ccmArchimedeanFormToAperture a w.toCCMFormVector : SoninL2)
  filter_upwards [h1, hu, hv, hw, hadd1, hadd2, hsv, hsw] with x h1 hu hv hw hadd1 hadd2 hsv hsw
  rw [h1, hadd1, Pi.add_apply, hadd2, Pi.add_apply, hsv, hsw, Pi.smul_apply, Pi.smul_apply,
    hu, hv, hw, combo_apply, smul_eq_mul, smul_eq_mul]

/-- Pole coefficients of a combination. -/
theorem inner_polar_combo {a : SuzukiPositiveAperture}
    (u v w : CCMComplexSmoothInteriorSource a) (α β : ℂ) (s : ℝ) :
    inner ℂ (ccmPolarApertureVector a s)
        (ccmArchimedeanFormToAperture a (u.combo v w α β).toCCMFormVector) =
      inner ℂ (ccmPolarApertureVector a s)
          (ccmArchimedeanFormToAperture a u.toCCMFormVector) +
        α * inner ℂ (ccmPolarApertureVector a s)
          (ccmArchimedeanFormToAperture a v.toCCMFormVector) +
        β * inner ℂ (ccmPolarApertureVector a s)
          (ccmArchimedeanFormToAperture a w.toCCMFormVector) := by
  rw [CCMComplexSmoothInteriorSource.combo_toCCMFormVector, map_add, map_add, map_smul, map_smul,
    inner_add_right, inner_add_right, inner_smul_right_aperture, inner_smul_right_aperture]

/-! ## A nonzero pole-vanishing smooth source at every aperture -/

theorem side_ball_subset (a : SuzukiPositiveAperture) :
    Metric.closedBall (a.1 / 2) (a.1 / 8) ⊆ Ioo (-a.1) a.1 := by
  intro x hx
  rw [Metric.mem_closedBall, Real.dist_eq, abs_le] at hx
  have := a.2
  constructor <;> linarith [hx.1, hx.2]

theorem side_ball_subset' (a : SuzukiPositiveAperture) :
    Metric.closedBall (-a.1 / 2) (a.1 / 8) ⊆ Ioo (-a.1) a.1 := by
  intro x hx
  rw [Metric.mem_closedBall, Real.dist_eq, abs_le] at hx
  have := a.2
  constructor <;> linarith [hx.1, hx.2]

theorem center_ball_subset (a : SuzukiPositiveAperture) :
    Metric.closedBall (0 : ℝ) (a.1 / 8) ⊆ Ioo (-a.1) a.1 := by
  intro x hx
  rw [Metric.mem_closedBall, Real.dist_eq, sub_zero, abs_le] at hx
  have := a.2
  constructor <;> linarith [hx.1, hx.2]

theorem a_div_eight_pos (a : SuzukiPositiveAperture) : 0 < a.1 / 8 := by
  have := a.2; positivity

/-- The right side bump. -/
noncomputable def polarRightBump (a : SuzukiPositiveAperture) : CCMComplexSmoothInteriorSource a :=
  bumpInteriorSource a (a.1 / 2) (a.1 / 8) (a_div_eight_pos a) (side_ball_subset a)

/-- The left side bump. -/
noncomputable def polarLeftBump (a : SuzukiPositiveAperture) : CCMComplexSmoothInteriorSource a :=
  bumpInteriorSource a (-a.1 / 2) (a.1 / 8) (a_div_eight_pos a) (side_ball_subset' a)

/-- The centre bump. -/
noncomputable def polarCenterBump (a : SuzukiPositiveAperture) : CCMComplexSmoothInteriorSource a :=
  bumpInteriorSource a 0 (a.1 / 8) (a_div_eight_pos a) (center_ball_subset a)

/-- The polar moment determinant of the two side bumps. -/
noncomputable def polarSideDet (a : SuzukiPositiveAperture) : ℝ :=
  polarBumpMoment (a.1 / 2) (a.1 / 8) (a_div_eight_pos a) (1 / 2) *
      polarBumpMoment (-a.1 / 2) (a.1 / 8) (a_div_eight_pos a) (-1 / 2) -
    polarBumpMoment (-a.1 / 2) (a.1 / 8) (a_div_eight_pos a) (1 / 2) *
      polarBumpMoment (a.1 / 2) (a.1 / 8) (a_div_eight_pos a) (-1 / 2)

theorem polarSideDet_pos (a : SuzukiPositiveAperture) : 0 < polarSideDet a := by
  have ha := a.2
  have hr := a_div_eight_pos a
  set r := a.1 / 8 with hr_def
  have habs : |(1 / 2 : ℝ)| = 1 / 2 := abs_of_pos (by norm_num)
  have habs' : |(-1 / 2 : ℝ)| = 1 / 2 := by rw [abs_of_neg (by norm_num)]; norm_num
  have hq : 0 < 3 * a.1 / 16 := by positivity
  refine polar_det_pos (polarBumpMass_pos (a.1 / 2) r hr) (polarBumpMass_pos (-a.1 / 2) r hr) hq
    ?_ ?_ ?_ ?_ (polarBumpMoment_nonneg _ _ _ _) (polarBumpMoment_nonneg _ _ _ _)
  · have h := le_polarBumpMoment (a.1 / 2) r hr (1 / 2)
    rw [habs] at h
    have : 1 / 2 * (a.1 / 2) - 1 / 2 * r = 3 * a.1 / 16 := by rw [hr_def]; ring
    rw [this] at h
    linarith [h]
  · have h := le_polarBumpMoment (-a.1 / 2) r hr (-1 / 2)
    rw [habs'] at h
    have : -1 / 2 * (-a.1 / 2) - 1 / 2 * r = 3 * a.1 / 16 := by rw [hr_def]; ring
    rw [this] at h
    linarith [h]
  · have h := polarBumpMoment_le (-a.1 / 2) r hr (1 / 2)
    rw [habs] at h
    have : 1 / 2 * (-a.1 / 2) + 1 / 2 * r = -(3 * a.1 / 16) := by rw [hr_def]; ring
    rw [this] at h
    linarith [h]
  · have h := polarBumpMoment_le (a.1 / 2) r hr (-1 / 2)
    rw [habs'] at h
    have : -1 / 2 * (a.1 / 2) + 1 / 2 * r = -(3 * a.1 / 16) := by rw [hr_def]; ring
    rw [this] at h
    linarith [h]

end RHTower
