import GaloisForLFunctions.RHTower.CCM.CCMRestrictedWeilPolarConstrainedSmoothCore

/-!
# The pole-vanishing multiplier `∂² − 1/4`

The two pole coefficients of a source are its exponential moments `∫ e^{±x/2} g`.  Two
integrations by parts give `∫ e^{sx} g'' = s² ∫ e^{sx} g` for every compactly supported `C²`
function `g`, so the operator `D = ∂² − 1/4`, whose Mellin symbol is `s(s − 1)` in the centred
variable, annihilates both pole coefficients: `D g` is pole-vanishing for every smooth
strict-interior source `g`.  This is the canonical description of the pole-vanishing smooth
core as the image of `D`. The same-aperture range converse and uniqueness are proved by
exponential primitives in `CCMRestrictedWeilPolarInverse`; that argument does not require the
convolution representation `g = −e^{−|x|/2} ∗ f`.
-/

open Complex MeasureTheory Set intervalIntegral

namespace RHTower

/-- A compactly supported function and its first two derivatives vanish beyond some radius. -/
theorem exists_radius_deriv_deriv_eq_zero {g : ℝ → ℂ} (hsupp : HasCompactSupport g) :
    ∃ R : ℝ, 0 < R ∧ ∀ x, R ≤ |x| →
      g x = 0 ∧ deriv g x = 0 ∧ deriv (deriv g) x = 0 := by
  obtain ⟨R, hR, hzero⟩ := hsupp.exists_pos_le_norm
  refine ⟨R + 1, by linarith, fun x hx => ?_⟩
  simp only [Real.norm_eq_abs] at hzero
  have hnhds : g =ᶠ[nhds x] 0 := by
    have hopen : IsOpen {y : ℝ | R < |y|} := isOpen_lt continuous_const continuous_abs
    have hmem : x ∈ {y : ℝ | R < |y|} := by
      show R < |x|; linarith
    filter_upwards [hopen.mem_nhds hmem] with y hy
    exact hzero y (le_of_lt hy)
  have h1 : deriv g =ᶠ[nhds x] 0 := by
    filter_upwards [hnhds.eventually_nhds] with y hy
    have hy' : g =ᶠ[nhds y] 0 := hy
    rw [hy'.deriv_eq]
    simp
  refine ⟨hzero x (by linarith), ?_, ?_⟩
  · rw [hnhds.deriv_eq]; simp
  · rw [h1.deriv_eq]; simp

/-- Integral of a function vanishing beyond a radius as an interval integral. -/
theorem integral_eq_intervalIntegral_of_radius {f : ℝ → ℂ} {R : ℝ} (hR : 0 < R)
    (hzero : ∀ x, R ≤ |x| → f x = 0) :
    ∫ x, f x = ∫ x in (-R)..R, f x := by
  rw [integral_of_le (by linarith)]
  symm
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro x hx
  apply hzero
  rw [mem_Ioc, not_and_or] at hx
  rcases hx with h | h
  · push Not at h
    rw [abs_of_nonpos (by linarith)]
    linarith
  · push Not at h
    rw [abs_of_pos (by linarith)]
    linarith

theorem hasDerivAt_exp_mul_complex (s x : ℝ) :
    HasDerivAt (fun y : ℝ => (Real.exp (s * y) : ℂ)) ((Real.exp (s * x) : ℂ) * (s : ℂ)) x := by
  have h : HasDerivAt (fun y : ℝ => Real.exp (s * y)) (Real.exp (s * x) * s) x := by
    have := (Real.hasDerivAt_exp (s * x)).comp x ((hasDerivAt_id x).const_mul s)
    simp only [mul_one] at this
    exact this
  exact h.ofReal_comp.congr_deriv (by push_cast; ring)

theorem continuous_exp_mul_complex (s : ℝ) :
    Continuous fun y : ℝ => (Real.exp (s * y) : ℂ) :=
  continuous_ofReal.comp (Real.continuous_exp.comp (continuous_const.mul continuous_id))

/-- **Two integrations by parts.** -/
theorem integral_exp_mul_deriv_deriv {g : ℝ → ℂ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hsupp : HasCompactSupport g) (s : ℝ) :
    ∫ x, (Real.exp (s * x) : ℂ) * deriv (deriv g) x =
      (s : ℂ) ^ (2 : ℕ) * ∫ x, (Real.exp (s * x) : ℂ) * g x := by
  obtain ⟨R, hR, hz⟩ := exists_radius_deriv_deriv_eq_zero hsupp
  have hg1 : ContDiff ℝ (⊤ : ℕ∞) (deriv g) := by
    have := hg.iterate_deriv 1
    simpa using this
  have hg2 : ContDiff ℝ (⊤ : ℕ∞) (deriv (deriv g)) := by
    have := hg.iterate_deriv 2
    simpa [Function.iterate_succ, Function.comp] using this
  have htop : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
  have hgd : Differentiable ℝ g := hg.differentiable htop
  have hg1d : Differentiable ℝ (deriv g) := hg1.differentiable htop
  have hcont2 : Continuous (deriv (deriv g)) := hg2.continuous
  have hcont1 : Continuous (deriv g) := hg1.continuous
  have hcontg : Continuous g := hg.continuous
  have hRabs : R ≤ |R| := le_abs_self R
  have hRabs' : R ≤ |-R| := by rw [abs_neg]; exact le_abs_self R
  have hzA : ∀ x, R ≤ |x| → (Real.exp (s * x) : ℂ) * deriv (deriv g) x = 0 := fun x hx => by
    rw [(hz x hx).2.2, mul_zero]
  have hzB : ∀ x, R ≤ |x| → (Real.exp (s * x) : ℂ) * g x = 0 := fun x hx => by
    rw [(hz x hx).1, mul_zero]
  rw [integral_eq_intervalIntegral_of_radius hR hzA, integral_eq_intervalIntegral_of_radius hR hzB]
  have hIBP1 : ∫ x in (-R)..R, (Real.exp (s * x) : ℂ) * deriv (deriv g) x =
      (Real.exp (s * R) : ℂ) * deriv g R - (Real.exp (s * (-R)) : ℂ) * deriv g (-R) -
        ∫ x in (-R)..R, ((Real.exp (s * x) : ℂ) * (s : ℂ)) * deriv g x :=
    integral_mul_deriv_eq_deriv_mul (fun x _ => hasDerivAt_exp_mul_complex s x)
      (fun x _ => (hg1d x).hasDerivAt)
      (((continuous_exp_mul_complex s).mul continuous_const).intervalIntegrable _ _)
      (hcont2.intervalIntegrable _ _)
  have hIBP2 : ∫ x in (-R)..R, ((Real.exp (s * x) : ℂ) * (s : ℂ)) * deriv g x =
      ((Real.exp (s * R) : ℂ) * (s : ℂ)) * g R - ((Real.exp (s * (-R)) : ℂ) * (s : ℂ)) * g (-R) -
        ∫ x in (-R)..R, ((Real.exp (s * x) : ℂ) * (s : ℂ) * (s : ℂ)) * g x :=
    integral_mul_deriv_eq_deriv_mul (fun x _ => (hasDerivAt_exp_mul_complex s x).mul_const (s : ℂ))
      (fun x _ => (hgd x).hasDerivAt)
      ((((continuous_exp_mul_complex s).mul continuous_const).mul
        continuous_const).intervalIntegrable _ _)
      (hcont1.intervalIntegrable _ _)
  rw [hIBP1, (hz R hRabs).2.1, (hz (-R) hRabs').2.1, hIBP2, (hz R hRabs).1, (hz (-R) hRabs').1]
  have hcongr : ∫ x in (-R)..R, ((Real.exp (s * x) : ℂ) * (s : ℂ) * (s : ℂ)) * g x =
      (s : ℂ) ^ (2 : ℕ) * ∫ x in (-R)..R, (Real.exp (s * x) : ℂ) * g x := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1
    funext x
    ring
  rw [hcongr]
  ring

/-- **The multiplier `∂² − 1/4` kills the exponential moments at `s = ±1/2`.** -/
theorem integral_exp_mul_polarMultiplier {g : ℝ → ℂ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hsupp : HasCompactSupport g) {s : ℝ} (hs : s ^ (2 : ℕ) = 1 / 4) :
    ∫ x, (Real.exp (s * x) : ℂ) * (deriv (deriv g) x - g x / 4) = 0 := by
  have hcont2 : Continuous (deriv (deriv g)) := by
    have := hg.iterate_deriv 2
    simpa [Function.iterate_succ, Function.comp] using this.continuous
  have hint1 : Integrable fun x => (Real.exp (s * x) : ℂ) * deriv (deriv g) x := by
    refine ((continuous_exp_mul_complex s).mul hcont2).integrable_of_hasCompactSupport ?_
    show HasCompactSupport ((fun x => (Real.exp (s * x) : ℂ)) * deriv (deriv g))
    exact hsupp.deriv.deriv.mul_left
  have hintg : Integrable fun x => (Real.exp (s * x) : ℂ) * g x := by
    refine ((continuous_exp_mul_complex s).mul hg.continuous).integrable_of_hasCompactSupport ?_
    show HasCompactSupport ((fun x => (Real.exp (s * x) : ℂ)) * g)
    exact hsupp.mul_left
  have hint2 : Integrable fun x => (Real.exp (s * x) : ℂ) * (g x / 4) := by
    refine (hintg.div_const (4 : ℂ)).congr (Filter.Eventually.of_forall fun x => ?_)
    simp only
    ring
  have hsplit : (fun x => (Real.exp (s * x) : ℂ) * (deriv (deriv g) x - g x / 4)) =
      fun x => (Real.exp (s * x) : ℂ) * deriv (deriv g) x - (Real.exp (s * x) : ℂ) * (g x / 4) := by
    funext x; ring
  rw [hsplit, integral_sub hint1 hint2, integral_exp_mul_deriv_deriv hg hsupp s]
  have h4 : (fun x => (Real.exp (s * x) : ℂ) * (g x / 4)) =
      fun x => (1 / 4 : ℂ) * ((Real.exp (s * x) : ℂ) * g x) := by
    funext x; ring
  rw [h4, MeasureTheory.integral_const_mul]
  have hs' : (s : ℂ) ^ (2 : ℕ) = 1 / 4 := by
    rw [← Complex.ofReal_pow, hs]
    norm_num
  rw [hs']
  ring

/-! ## The multiplier on strict-interior sources -/

/-- `D g = g'' − g/4` as a strict-interior source. -/
noncomputable def CCMComplexSmoothInteriorSource.polarMultiplier {a : SuzukiPositiveAperture}
    (g : CCMComplexSmoothInteriorSource a) : CCMComplexSmoothInteriorSource a where
  toFun := fun x => deriv (deriv g) x + (-(1 / 4 : ℂ)) * g x
  smooth := by
    have h2 : ContDiff ℝ (⊤ : ℕ∞) (deriv (deriv (g : ℝ → ℂ))) := by
      have := g.smooth.iterate_deriv 2
      simpa [Function.iterate_succ, Function.comp] using this
    have hg : ContDiff ℝ (⊤ : ℕ∞) fun x => (-(1 / 4 : ℂ)) * g x := by
      have := g.smooth.const_smul (-(1 / 4 : ℂ))
      simpa [smul_eq_mul] using this
    exact h2.add hg
  hasCompactSupport := by
    have hg : HasCompactSupport fun x => (-(1 / 4 : ℂ)) * g x :=
      g.hasCompactSupport.comp_left (mul_zero _)
    exact g.hasCompactSupport.deriv.deriv.add hg
  tsupport_subset := by
    have hg : tsupport (fun x => (-(1 / 4 : ℂ)) * g x) ⊆ Ioo (-a.1) a.1 :=
      (tsupport_comp_subset (mul_zero _) (g : ℝ → ℂ)).trans g.tsupport_subset
    refine (tsupport_add _ _).trans (union_subset ?_ hg)
    exact (tsupport_deriv_subset.trans tsupport_deriv_subset).trans g.tsupport_subset

theorem CCMComplexSmoothInteriorSource.polarMultiplier_apply {a : SuzukiPositiveAperture}
    (g : CCMComplexSmoothInteriorSource a) (x : ℝ) :
    g.polarMultiplier x = deriv (deriv g) x + (-(1 / 4 : ℂ)) * g x := rfl

/-- **`D g` is pole-vanishing for every smooth strict-interior source `g`.** -/
theorem isPolarConstrained_polarMultiplier {a : SuzukiPositiveAperture}
    (g : CCMComplexSmoothInteriorSource a) :
    IsPolarConstrained a g.polarMultiplier.toCCMFormVector := by
  have hkey : ∀ s : ℝ, s ^ (2 : ℕ) = 1 / 4 →
      ∫ x : ℝ, (Real.exp (s * x) : ℂ) * g.polarMultiplier x = 0 := by
    intro s hs
    have := integral_exp_mul_polarMultiplier g.smooth g.hasCompactSupport hs
    rw [← this]
    congr 1
    funext x
    rw [CCMComplexSmoothInteriorSource.polarMultiplier_apply]
    ring
  unfold IsPolarConstrained
  rw [inner_ccmPolarApertureVector_ccmComplexSmoothFormVector,
    inner_ccmPolarApertureVector_ccmComplexSmoothFormVector]
  exact ⟨hkey _ (by norm_num), hkey _ (by norm_num)⟩

end RHTower
