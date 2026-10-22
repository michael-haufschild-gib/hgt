import GaloisForLFunctions.RHTower.CCM.CCMRestrictedWeilPolarMultiplier
import GaloisForLFunctions.HTGeometry.CompactPrimitive

/-!
# The exact compact inverse of the Weil pole multiplier

The two exponential moments are precisely the obstruction to solving `g'' - g/4 = f`
with smooth support inside the same aperture. The inverse is the difference of two
exponentially weighted primitives. This identifies the constrained smooth core with
the image of the differential multiplier without any loss of aperture.
-/

open Complex MeasureTheory Set
open scoped InnerProduct
open GaloisForLFunctions.HTGeometry

noncomputable section
namespace RHTower

/-- A primitive solving `u' = s*u + f`, pinned at `b`. -/
def ccmPolarExponentialPrimitive (s b : ℝ) (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  (Real.exp (s * x) : ℂ) * ∫ t in b..x, (Real.exp (-s * t) : ℂ) * f t

theorem hasDerivAt_ccmPolarExponentialPrimitive (s b : ℝ) {f : ℝ → ℂ}
    (hf : Continuous f) (x : ℝ) :
    HasDerivAt (ccmPolarExponentialPrimitive s b f)
      ((s : ℂ) * ccmPolarExponentialPrimitive s b f x + f x) x := by
  have hc : Continuous fun t => (Real.exp (-s * t) : ℂ) * f t :=
    (continuous_exp_mul_complex (-s)).mul hf
  have hp : HasDerivAt (fun y => ∫ t in b..y, (Real.exp (-s * t) : ℂ) * f t)
      ((Real.exp (-s * x) : ℂ) * f x) x := intervalIntegral.integral_hasDerivAt_right
    (hc.intervalIntegrable b x) (hc.stronglyMeasurableAtFilter _ _) hc.continuousAt
  have he : (Real.exp (s * x) : ℂ) * (Real.exp (-s * x) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, ← Real.exp_add]
    simp
  apply ((hasDerivAt_exp_mul_complex s x).mul hp).congr_deriv
  dsimp only [ccmPolarExponentialPrimitive]
  linear_combination (f x) * he

theorem contDiff_ccmPolarExponentialPrimitive (s b : ℝ) {f : ℝ → ℂ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    ContDiff ℝ (⊤ : ℕ∞) (ccmPolarExponentialPrimitive s b f) := by
  have hplus : ContDiff ℝ (⊤ : ℕ∞) fun x => (Real.exp (s * x) : ℂ) :=
    Complex.ofRealCLM.contDiff.comp (Real.contDiff_exp.comp (contDiff_const.mul contDiff_id))
  have hminus : ContDiff ℝ (⊤ : ℕ∞) fun x => (Real.exp (-s * x) : ℂ) :=
    Complex.ofRealCLM.contDiff.comp (Real.contDiff_exp.comp (contDiff_const.mul contDiff_id))
  exact hplus.mul (contDiff_primitive (hminus.mul hf) b)

theorem ccmPolarExponentialPrimitive_eq_zero_outside {r : ℝ} (hr : 0 < r)
    (s : ℝ) {f : ℝ → ℂ} (hf : Continuous f)
    (hs : ∀ x, x ∉ Ioo (-r) r → f x = 0)
    (hm : ∫ x, (Real.exp (-s * x) : ℂ) * f x = 0) :
    ∀ x, x ∉ Ioo (-r) r → ccmPolarExponentialPrimitive s (-r) f x = 0 := by
  have hzero : ∀ x, x ∉ Ioo (-r) r → (Real.exp (-s * x) : ℂ) * f x = 0 := by
    intro x hx
    rw [hs x hx, mul_zero]
  have hinterval : ∫ x in (-r)..r, (Real.exp (-s * x) : ℂ) * f x = 0 := by
    rw [← integral_eq_intervalIntegral_of_radius hr]
    · exact hm
    · intro x hx
      exact hzero x (fun hmem => (not_lt_of_ge hx) (abs_lt.mpr hmem))
  intro x hx
  have hp := primitive_eq_zero_outside ((continuous_exp_mul_complex (-s)).mul hf)
      hzero hinterval x hx
  change (∫ t in (-r)..x, (Real.exp (-s * t) : ℂ) * f t) = 0 at hp
  rw [ccmPolarExponentialPrimitive, hp, mul_zero]

/-- The Green solution of `g'' - g/4 = f`, with zero Cauchy data at `b`. -/
def ccmPolarGreen (b : ℝ) (f : ℝ → ℂ) : ℝ → ℂ :=
  ccmPolarExponentialPrimitive (1 / 2) b f -
    ccmPolarExponentialPrimitive (-1 / 2) b f

theorem contDiff_ccmPolarGreen (b : ℝ) {f : ℝ → ℂ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    ContDiff ℝ (⊤ : ℕ∞) (ccmPolarGreen b f) :=
  (contDiff_ccmPolarExponentialPrimitive _ _ hf).sub
    (contDiff_ccmPolarExponentialPrimitive _ _ hf)

theorem deriv_ccmPolarGreen (b : ℝ) {f : ℝ → ℂ} (hf : Continuous f) :
    deriv (ccmPolarGreen b f) = fun x =>
      (1 / 2 : ℂ) * (ccmPolarExponentialPrimitive (1 / 2) b f x +
        ccmPolarExponentialPrimitive (-1 / 2) b f x) := by
  funext x
  have h := ((hasDerivAt_ccmPolarExponentialPrimitive (1 / 2) b hf x).sub
    (hasDerivAt_ccmPolarExponentialPrimitive (-1 / 2) b hf x)).deriv
  change deriv (ccmPolarExponentialPrimitive (1 / 2) b f -
    ccmPolarExponentialPrimitive (-1 / 2) b f) x = _
  rw [h]
  push_cast
  ring

theorem deriv_deriv_ccmPolarGreen (b : ℝ) {f : ℝ → ℂ} (hf : Continuous f) (x : ℝ) :
    deriv (deriv (ccmPolarGreen b f)) x = (1 / 4 : ℂ) * ccmPolarGreen b f x + f x := by
  rw [deriv_ccmPolarGreen b hf]
  have h := (((hasDerivAt_ccmPolarExponentialPrimitive (1 / 2) b hf x).add
    (hasDerivAt_ccmPolarExponentialPrimitive (-1 / 2) b hf x)).const_mul
      (1 / 2 : ℂ)).deriv
  calc
    _ = (1 / 2 : ℂ) *
        (((1 / 2 : ℝ) : ℂ) * ccmPolarExponentialPrimitive (1 / 2) b f x + f x +
        (((-1 / 2 : ℝ) : ℂ) * ccmPolarExponentialPrimitive (-1 / 2) b f x + f x)) := h
    _ = _ := by
      simp only [ccmPolarGreen, Pi.sub_apply]
      push_cast
      ring

/-- The Green solution has no exterior tails when both pole moments vanish. -/
theorem ccmPolarGreen_eq_zero_outside {r : ℝ} (hr : 0 < r) {f : ℝ → ℂ}
    (hf : Continuous f) (hs : ∀ x, x ∉ Ioo (-r) r → f x = 0)
    (hm : (∫ x, (Real.exp ((1 / 2) * x) : ℂ) * f x) = 0 ∧
      (∫ x, (Real.exp ((-1 / 2) * x) : ℂ) * f x) = 0) :
    ∀ x, x ∉ Ioo (-r) r → ccmPolarGreen (-r) f x = 0 := by
  have hp := ccmPolarExponentialPrimitive_eq_zero_outside hr (1 / 2) hf hs
    (by simpa only [neg_div] using hm.2)
  have hn := ccmPolarExponentialPrimitive_eq_zero_outside hr (-1 / 2) hf hs
    (by simpa only [neg_div, neg_neg] using hm.1)
  intro x hx
  simp only [ccmPolarGreen, Pi.sub_apply, hp x hx, hn x hx, sub_self]

theorem CCMComplexSmoothInteriorSource.eq_of_coe_eq {a : SuzukiPositiveAperture}
    (f g : CCMComplexSmoothInteriorSource a) (h : (f : ℝ → ℂ) = g) : f = g := by
  cases f
  cases g
  cases h
  rfl

/-- Every smooth pole-constrained source is the exact multiplier image of a smooth source
inside the same aperture. -/
theorem exists_polarMultiplier_preimage {a : SuzukiPositiveAperture}
    (f : CCMComplexSmoothInteriorSource a) (hf : IsPolarConstrained a f.toCCMFormVector) :
    ∃ g : CCMComplexSmoothInteriorSource a, g.polarMultiplier = f := by
  obtain ⟨b, hba, hsupp⟩ := exists_strict_smaller_aperture_of_compact_tsupport a f
  have hm : (∫ x, (Real.exp ((1 / 2) * x) : ℂ) * f x) = 0 ∧
      (∫ x, (Real.exp ((-1 / 2) * x) : ℂ) * f x) = 0 := by
    simpa only [IsPolarConstrained,
      inner_ccmPolarApertureVector_ccmComplexSmoothFormVector] using hf
  have hs : ∀ x, x ∉ Ioo (-b.1) b.1 → f x = 0 := by
    intro x hx
    by_contra hn
    exact hx (hsupp (subset_tsupport f hn))
  have hzero := ccmPolarGreen_eq_zero_outside b.2 f.continuous hs hm
  have hgts : tsupport (ccmPolarGreen (-b.1) f) ⊆ Icc (-b.1) b.1 := by
    apply closure_minimal _ isClosed_Icc
    intro x hx
    exact Ioo_subset_Icc_self (by_contra fun h => hx (hzero x h))
  let g : CCMComplexSmoothInteriorSource a := {
    toFun := ccmPolarGreen (-b.1) f
    smooth := contDiff_ccmPolarGreen _ f.smooth
    hasCompactSupport := IsCompact.of_isClosed_subset isCompact_Icc
      (isClosed_tsupport _) hgts
    tsupport_subset := hgts.trans (by
      intro x hx
      exact ⟨by linarith [hx.1], by linarith [hx.2]⟩) }
  refine ⟨g, CCMComplexSmoothInteriorSource.eq_of_coe_eq _ _ ?_⟩
  funext x
  change deriv (deriv (ccmPolarGreen (-b.1) f)) x +
    (-(1 / 4 : ℂ)) * ccmPolarGreen (-b.1) f x = f x
  rw [deriv_deriv_ccmPolarGreen _ f.continuous]
  ring

/-- The two pole moments characterize the full multiplier image at each fixed aperture. -/
theorem isPolarConstrained_iff_exists_polarMultiplier_preimage
    {a : SuzukiPositiveAperture} (f : CCMComplexSmoothInteriorSource a) :
    IsPolarConstrained a f.toCCMFormVector ↔
      ∃ g : CCMComplexSmoothInteriorSource a, g.polarMultiplier = f := by
  constructor
  · exact exists_polarMultiplier_preimage f
  · rintro ⟨g, rfl⟩
    exact isPolarConstrained_polarMultiplier g

private theorem compact_firstOrder_eq_zero {f : ℝ → ℂ}
    (hf : Differentiable ℝ f) (hc : HasCompactSupport f) (s : ℝ)
    (hode : ∀ x, deriv f x = (s : ℂ) * f x) : f = 0 := by
  have hd : ∀ x, HasDerivAt (fun y => (Real.exp (-s * y) : ℂ) * f y) 0 x := by
    intro x
    apply ((hasDerivAt_exp_mul_complex (-s) x).mul (hf x).hasDerivAt).congr_deriv
    rw [hode x]
    push_cast
    ring
  obtain ⟨R, _, hz⟩ := hc.exists_pos_le_norm
  have hfR : f R = 0 := hz R (by simpa only [Real.norm_eq_abs] using le_abs_self R)
  funext x
  have hconstant := is_const_of_deriv_eq_zero
    (fun y => (hd y).differentiableAt) (fun y => (hd y).deriv) x R
  rw [hfR, mul_zero] at hconstant
  exact (mul_eq_zero.mp hconstant).resolve_left
    (by exact_mod_cast Real.exp_ne_zero (-s * x))

/-- The pole multiplier has no nonzero compactly supported smooth kernel. -/
theorem compact_polarMultiplier_kernel {f : ℝ → ℂ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f)
    (hode : ∀ x, deriv (deriv f) x = (1 / 4 : ℂ) * f x) : f = 0 := by
  have hfd : Differentiable ℝ f := hf.differentiable (by simp)
  have hf1 : ContDiff ℝ (⊤ : ℕ∞) (deriv f) := by
    simpa using hf.iterate_deriv 1
  let h : ℝ → ℂ := fun x => deriv f x - (1 / 2 : ℂ) * f x
  have hhd : Differentiable ℝ h :=
    hf1.differentiable (by simp) |>.sub (hfd.const_mul _)
  have hhc : HasCompactSupport h :=
    hc.deriv.sub (hc.comp_left (mul_zero (1 / 2 : ℂ)))
  have hzero : h = 0 := compact_firstOrder_eq_zero hhd hhc (-1 / 2) (by
    intro x
    have hd := ((hf1.differentiable (by simp) x).hasDerivAt.sub
      ((hfd x).hasDerivAt.const_mul (1 / 2 : ℂ))).deriv
    change deriv (deriv f - fun y => (1 / 2 : ℂ) * f y) x = _
    rw [hd, hode x]
    dsimp [h]
    push_cast
    ring)
  apply compact_firstOrder_eq_zero hfd hc (1 / 2)
  intro x
  have hx := congrFun hzero x
  change deriv f x - (1 / 2 : ℂ) * f x = 0 at hx
  push_cast
  exact sub_eq_zero.mp hx

/-- The differential parametrization of the constrained smooth core is injective. -/
theorem CCMComplexSmoothInteriorSource.polarMultiplier_injective (a : SuzukiPositiveAperture) :
    Function.Injective (@CCMComplexSmoothInteriorSource.polarMultiplier a) := by
  intro f g hfg
  have hfd : Differentiable ℝ (f : ℝ → ℂ) := f.smooth.differentiable (by simp)
  have hgd : Differentiable ℝ (g : ℝ → ℂ) := g.smooth.differentiable (by simp)
  have hf1 : ContDiff ℝ (⊤ : ℕ∞) (deriv (f : ℝ → ℂ)) := by
    simpa using f.smooth.iterate_deriv 1
  have hg1 : ContDiff ℝ (⊤ : ℕ∞) (deriv (g : ℝ → ℂ)) := by
    simpa using g.smooth.iterate_deriv 1
  have hsub1 : deriv ((f : ℝ → ℂ) - (g : ℝ → ℂ)) = deriv (f : ℝ → ℂ) - deriv (g : ℝ → ℂ) :=
    funext fun x => deriv_sub (hfd x) (hgd x)
  have hsub2 : deriv (deriv ((f : ℝ → ℂ) - (g : ℝ → ℂ))) =
      deriv (deriv (f : ℝ → ℂ)) - deriv (deriv (g : ℝ → ℂ)) := by
    rw [hsub1]
    exact funext fun x => deriv_sub
      (hf1.differentiable (by simp) x) (hg1.differentiable (by simp) x)
  have hzero : (f : ℝ → ℂ) - (g : ℝ → ℂ) = 0 := compact_polarMultiplier_kernel
    (f.smooth.sub g.smooth) (f.hasCompactSupport.sub g.hasCompactSupport) (by
      intro x
      rw [hsub2]
      have hx := congrArg (fun u : CCMComplexSmoothInteriorSource a => u x) hfg
      change deriv (deriv (f : ℝ → ℂ)) x + (-(1 / 4 : ℂ)) * f x =
        deriv (deriv (g : ℝ → ℂ)) x + (-(1 / 4 : ℂ)) * g x at hx
      simp only [Pi.sub_apply]
      linear_combination hx)
  exact CCMComplexSmoothInteriorSource.eq_of_coe_eq _ _ (sub_eq_zero.mp hzero)

/-- The two pole moments are exactly the obstruction to a unique smooth compact solution
of `g'' - g/4 = f` in the original aperture. -/
theorem isPolarConstrained_iff_existsUnique_polarMultiplier_preimage
    {a : SuzukiPositiveAperture} (f : CCMComplexSmoothInteriorSource a) :
    IsPolarConstrained a f.toCCMFormVector ↔
      ∃! g : CCMComplexSmoothInteriorSource a, g.polarMultiplier = f := by
  constructor
  · intro hf
    obtain ⟨g, hg⟩ := exists_polarMultiplier_preimage f hf
    exact ⟨g, hg, fun y hy =>
      CCMComplexSmoothInteriorSource.polarMultiplier_injective a (hy.trans hg.symm)⟩
  · rintro ⟨g, hg, _⟩
    exact (isPolarConstrained_iff_exists_polarMultiplier_preimage f).mpr ⟨g, hg⟩

end RHTower
