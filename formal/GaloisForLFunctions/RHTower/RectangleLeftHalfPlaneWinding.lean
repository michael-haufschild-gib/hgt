import GaloisForLFunctions.RHTower.EntireArgumentVariationRectangle

/-!
# Equal zero counts when a ratio stays in the left half-plane on a rectangle boundary

Let `F₁, F₀` be entire, nonvanishing on the boundary of the rectangle `[c, d] × [T₁, T₂]`, and let
`g` be analytic on the boundary with `logDeriv F₁ = logDeriv g + logDeriv F₀` and `Re g < 0` there
(typically `g = F₁/F₀`). Then `F₁` and `F₀` have the same number of zeros in the closed rectangle,
counted with multiplicity (`sum_analyticOrderAt_eq_of_logDeriv_ratio_re_neg`).

**Proof.**
- On each edge, `−g` takes values in the right half-plane, so `log(−g)` is a primitive along the
  edge. The edge integral of the argument derivative of `g` is therefore the increment of
  `Im log(−g)` (`integral_re_logDeriv_vertical_eq_of_re_neg`,
  `integral_im_logDeriv_horizontal_eq_of_re_neg`).
- The four increments telescope to zero around the boundary. Subtracting the argument principles
  of `F₁` and `F₀` (`exists_entire_argument_variation_rectangle`) leaves `2π(N₁ − N₀) = 0`.
-/

open Complex Set intervalIntegral

namespace RHTower

noncomputable section

/-- The logarithmic derivative is continuous at a point where the function is analytic and
nonzero. -/
theorem continuousAt_logDeriv_of_analyticAt {g : ℂ → ℂ} {z : ℂ} (hg : AnalyticAt ℂ g z)
    (hz : g z ≠ 0) : ContinuousAt (logDeriv g) z := by
  have h : ContinuousAt (fun w => deriv g w / g w) z :=
    hg.deriv.continuousAt.div hg.continuousAt hz
  exact h.congr (Filter.Eventually.of_forall fun w => (logDeriv_apply g w).symm)

/-- **Vertical edge.** If `Re g < 0` along the vertical segment, the integral of `Re(g'/g)` is the
increment of `Im log(−g)`. -/
theorem integral_re_logDeriv_vertical_eq_of_re_neg {g : ℂ → ℂ} {x T₁ T₂ : ℝ}
    (hg : ∀ t ∈ uIcc T₁ T₂, AnalyticAt ℂ g ((x : ℂ) + t * I))
    (hneg : ∀ t ∈ uIcc T₁ T₂, (g ((x : ℂ) + t * I)).re < 0) :
    ∫ t in T₁..T₂, (logDeriv g ((x : ℂ) + t * I)).re =
      (Complex.log (-g ((x : ℂ) + T₂ * I))).im - (Complex.log (-g ((x : ℂ) + T₁ * I))).im := by
  have hpath : ∀ t : ℝ, HasDerivAt (fun u : ℝ => (x : ℂ) + u * I) I t := by
    intro t
    simpa using ((hasDerivAt_id t).ofReal_comp.mul_const I).const_add (x : ℂ)
  have hne : ∀ t ∈ uIcc T₁ T₂, g ((x : ℂ) + t * I) ≠ 0 := fun t ht h => by
    have := hneg t ht
    rw [h, Complex.zero_re] at this
    exact lt_irrefl 0 this
  have hderiv : ∀ t ∈ uIcc T₁ T₂, HasDerivAt
      (fun u : ℝ => (Complex.log (-g ((x : ℂ) + u * I))).im)
      ((logDeriv g ((x : ℂ) + t * I)).re) t := by
    intro t ht
    have h1 : HasDerivAt (fun u : ℝ => -g ((x : ℂ) + u * I))
        (-(I • deriv g ((x : ℂ) + t * I))) t :=
      ((hg t ht).differentiableAt.hasDerivAt.scomp t (hpath t)).neg
    have hslit : -g ((x : ℂ) + t * I) ∈ Complex.slitPlane :=
      Complex.mem_slitPlane_iff.mpr (Or.inl (by rw [Complex.neg_re]; linarith [hneg t ht]))
    have h2 := h1.clog_real hslit
    have h3 : HasDerivAt (fun u : ℝ => (Complex.log (-g ((x : ℂ) + u * I))).im)
        ((-(I • deriv g ((x : ℂ) + t * I)) / -g ((x : ℂ) + t * I)).im) t :=
      Complex.imCLM.hasFDerivAt.comp_hasDerivAt t h2
    refine h3.congr_deriv ?_
    rw [logDeriv_apply, smul_eq_mul, neg_div_neg_eq, mul_div_assoc, Complex.mul_im, Complex.I_re,
      Complex.I_im]
    ring
  have hcont : ContinuousOn (fun t : ℝ => (logDeriv g ((x : ℂ) + t * I)).re) (uIcc T₁ T₂) := by
    intro t ht
    have hc : ContinuousAt (fun u : ℝ => (x : ℂ) + u * I) t := (hpath t).continuousAt
    exact (Complex.continuous_re.continuousAt.comp
      ((continuousAt_logDeriv_of_analyticAt (hg t ht) (hne t ht)).comp
        (f := fun u : ℝ => (x : ℂ) + u * I) hc)).continuousWithinAt
  exact integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable)

/-- **Horizontal edge.** If `Re g < 0` along the horizontal segment, the integral of `Im(g'/g)` is
the increment of `Im log(−g)`. -/
theorem integral_im_logDeriv_horizontal_eq_of_re_neg {g : ℂ → ℂ} {c d T : ℝ}
    (hg : ∀ x ∈ uIcc c d, AnalyticAt ℂ g ((x : ℂ) + T * I))
    (hneg : ∀ x ∈ uIcc c d, (g ((x : ℂ) + T * I)).re < 0) :
    ∫ x in c..d, (logDeriv g ((x : ℂ) + T * I)).im =
      (Complex.log (-g ((d : ℂ) + T * I))).im - (Complex.log (-g ((c : ℂ) + T * I))).im := by
  have hpath : ∀ x : ℝ, HasDerivAt (fun u : ℝ => (u : ℂ) + T * I) 1 x := by
    intro x
    simpa using (hasDerivAt_id x).ofReal_comp.add_const ((T : ℂ) * I)
  have hne : ∀ x ∈ uIcc c d, g ((x : ℂ) + T * I) ≠ 0 := fun x hx h => by
    have := hneg x hx
    rw [h, Complex.zero_re] at this
    exact lt_irrefl 0 this
  have hderiv : ∀ x ∈ uIcc c d, HasDerivAt
      (fun u : ℝ => (Complex.log (-g ((u : ℂ) + T * I))).im)
      ((logDeriv g ((x : ℂ) + T * I)).im) x := by
    intro x hx
    have h1 : HasDerivAt (fun u : ℝ => -g ((u : ℂ) + T * I))
        (-((1 : ℝ) • deriv g ((x : ℂ) + T * I))) x :=
      ((hg x hx).differentiableAt.hasDerivAt.scomp x (hpath x)).neg
    have hslit : -g ((x : ℂ) + T * I) ∈ Complex.slitPlane :=
      Complex.mem_slitPlane_iff.mpr (Or.inl (by rw [Complex.neg_re]; linarith [hneg x hx]))
    have h2 := h1.clog_real hslit
    have h3 : HasDerivAt (fun u : ℝ => (Complex.log (-g ((u : ℂ) + T * I))).im)
        ((-((1 : ℝ) • deriv g ((x : ℂ) + T * I)) / -g ((x : ℂ) + T * I)).im) x :=
      Complex.imCLM.hasFDerivAt.comp_hasDerivAt x h2
    refine h3.congr_deriv ?_
    rw [logDeriv_apply, one_smul, neg_div_neg_eq]
  have hcont : ContinuousOn (fun x : ℝ => (logDeriv g ((x : ℂ) + T * I)).im) (uIcc c d) := by
    intro x hx
    have hc : ContinuousAt (fun u : ℝ => (u : ℂ) + T * I) x := (hpath x).continuousAt
    exact (Complex.continuous_im.continuousAt.comp
      ((continuousAt_logDeriv_of_analyticAt (hg x hx) (hne x hx)).comp
        (f := fun u : ℝ => (u : ℂ) + T * I) hc)).continuousWithinAt
  exact integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable)

/-- The boundary hypothesis: at `z`, both entire functions are nonzero, `g` is analytic with
negative real part, and the logarithmic derivatives are related by `g`. -/
def RatioLeftBoundary (F₁ F₀ g : ℂ → ℂ) (z : ℂ) : Prop :=
  F₁ z ≠ 0 ∧ F₀ z ≠ 0 ∧ AnalyticAt ℂ g z ∧ (g z).re < 0 ∧
    logDeriv F₁ z = logDeriv g z + logDeriv F₀ z

/-- **Equal zero counts.** If `F₁, F₀` are entire and `RatioLeftBoundary F₁ F₀ g` holds on the
boundary of `[c, d] × [T₁, T₂]`, then `F₁` and `F₀` have the same number of zeros, with
multiplicity, in the closed rectangle. -/
theorem sum_analyticOrderAt_eq_of_logDeriv_ratio_re_neg {F₁ F₀ g : ℂ → ℂ}
    (hF₁ : AnalyticOnNhd ℂ F₁ Set.univ) (hF₀ : AnalyticOnNhd ℂ F₀ Set.univ)
    (hn₁ : ∃ z : ℂ, F₁ z ≠ 0) (hn₀ : ∃ z : ℂ, F₀ z ≠ 0)
    {c d T₁ T₂ : ℝ} (hcd : c < d) (hT : T₁ < T₂)
    (hbot : ∀ x ∈ uIcc c d, RatioLeftBoundary F₁ F₀ g ((x : ℂ) + T₁ * I))
    (htop : ∀ x ∈ uIcc c d, RatioLeftBoundary F₁ F₀ g ((x : ℂ) + T₂ * I))
    (hright : ∀ t ∈ uIcc T₁ T₂, RatioLeftBoundary F₁ F₀ g ((d : ℂ) + t * I))
    (hleft : ∀ t ∈ uIcc T₁ T₂, RatioLeftBoundary F₁ F₀ g ((c : ℂ) + t * I)) :
    ∃ Z₁ Z₀ : Finset ℂ,
      (∀ z : ℂ, z ∈ Z₁ ↔ z ∈ (uIcc c d ×ℂ uIcc T₁ T₂) ∧ F₁ z = 0) ∧
      (∀ z : ℂ, z ∈ Z₀ ↔ z ∈ (uIcc c d ×ℂ uIcc T₁ T₂) ∧ F₀ z = 0) ∧
      ∑ w ∈ Z₁, (analyticOrderAt F₁ w).toNat = ∑ w ∈ Z₀, (analyticOrderAt F₀ w).toNat := by
  obtain ⟨Z₁, hZ₁, h₁⟩ := exists_entire_argument_variation_rectangle hF₁ hn₁ hcd hT
    (fun x hx => (hbot x hx).1) (fun x hx => (htop x hx).1)
    (fun t ht => (hright t ht).1) (fun t ht => (hleft t ht).1)
  obtain ⟨Z₀, hZ₀, h₀⟩ := exists_entire_argument_variation_rectangle hF₀ hn₀ hcd hT
    (fun x hx => (hbot x hx).2.1) (fun x hx => (htop x hx).2.1)
    (fun t ht => (hright t ht).2.1) (fun t ht => (hleft t ht).2.1)
  refine ⟨Z₁, Z₀, hZ₁, hZ₀, ?_⟩
  -- continuity of the `F₀` edge integrands
  have hcF₀ : ∀ z : ℂ, F₀ z ≠ 0 → ContinuousAt (logDeriv F₀) z := fun z hz =>
    continuousAt_logDeriv_of_analyticAt (hF₀ z (Set.mem_univ z)) hz
  have hcg : ∀ z : ℂ, AnalyticAt ℂ g z → (g z).re < 0 → ContinuousAt (logDeriv g) z :=
    fun z hz hre => continuousAt_logDeriv_of_analyticAt hz (fun h => by
      rw [h, Complex.zero_re] at hre; exact lt_irrefl 0 hre)
  have hvpath : ∀ (x : ℝ), Continuous (fun u : ℝ => (x : ℂ) + u * I) := fun x => by
    fun_prop
  have hhpath : ∀ (T : ℝ), Continuous (fun u : ℝ => (u : ℂ) + T * I) := fun T => by
    fun_prop
  -- vertical splits
  have hvert : ∀ x : ℝ, (∀ t ∈ uIcc T₁ T₂, RatioLeftBoundary F₁ F₀ g ((x : ℂ) + t * I)) →
      ∫ t in T₁..T₂, (logDeriv F₁ ((x : ℂ) + t * I)).re =
        (∫ t in T₁..T₂, (logDeriv g ((x : ℂ) + t * I)).re) +
          ∫ t in T₁..T₂, (logDeriv F₀ ((x : ℂ) + t * I)).re := by
    intro x hx
    have ig : IntervalIntegrable (fun t : ℝ => (logDeriv g ((x : ℂ) + t * I)).re)
        MeasureTheory.volume T₁ T₂ := by
      refine ContinuousOn.intervalIntegrable fun t ht => ?_
      exact (Complex.continuous_re.continuousAt.comp ((hcg _ (hx t ht).2.2.1
        (hx t ht).2.2.2.1).comp (f := fun u : ℝ => (x : ℂ) + u * I)
          (hvpath x).continuousAt)).continuousWithinAt
    have i0 : IntervalIntegrable (fun t : ℝ => (logDeriv F₀ ((x : ℂ) + t * I)).re)
        MeasureTheory.volume T₁ T₂ := by
      refine ContinuousOn.intervalIntegrable fun t ht => ?_
      exact (Complex.continuous_re.continuousAt.comp ((hcF₀ _ (hx t ht).2.1).comp
        (f := fun u : ℝ => (x : ℂ) + u * I) (hvpath x).continuousAt)).continuousWithinAt
    rw [← intervalIntegral.integral_add ig i0]
    refine intervalIntegral.integral_congr fun t ht => ?_
    simp only [(hx t ht).2.2.2.2, Complex.add_re]
  have hhor : ∀ T : ℝ, (∀ x ∈ uIcc c d, RatioLeftBoundary F₁ F₀ g ((x : ℂ) + T * I)) →
      ∫ x in c..d, (logDeriv F₁ ((x : ℂ) + T * I)).im =
        (∫ x in c..d, (logDeriv g ((x : ℂ) + T * I)).im) +
          ∫ x in c..d, (logDeriv F₀ ((x : ℂ) + T * I)).im := by
    intro T hx
    have ig : IntervalIntegrable (fun x : ℝ => (logDeriv g ((x : ℂ) + T * I)).im)
        MeasureTheory.volume c d := by
      refine ContinuousOn.intervalIntegrable fun x hxm => ?_
      exact (Complex.continuous_im.continuousAt.comp ((hcg _ (hx x hxm).2.2.1
        (hx x hxm).2.2.2.1).comp (f := fun u : ℝ => (u : ℂ) + T * I)
          (hhpath T).continuousAt)).continuousWithinAt
    have i0 : IntervalIntegrable (fun x : ℝ => (logDeriv F₀ ((x : ℂ) + T * I)).im)
        MeasureTheory.volume c d := by
      refine ContinuousOn.intervalIntegrable fun x hxm => ?_
      exact (Complex.continuous_im.continuousAt.comp ((hcF₀ _ (hx x hxm).2.1).comp
        (f := fun u : ℝ => (u : ℂ) + T * I) (hhpath T).continuousAt)).continuousWithinAt
    rw [← intervalIntegral.integral_add ig i0]
    refine intervalIntegral.integral_congr fun x hxm => ?_
    simp only [(hx x hxm).2.2.2.2, Complex.add_im]
  -- the `g` edge integrals telescope
  have eL := integral_re_logDeriv_vertical_eq_of_re_neg (g := g) (x := c)
    (fun t ht => (hleft t ht).2.2.1) (fun t ht => (hleft t ht).2.2.2.1)
  have eR := integral_re_logDeriv_vertical_eq_of_re_neg (g := g) (x := d)
    (fun t ht => (hright t ht).2.2.1) (fun t ht => (hright t ht).2.2.2.1)
  have eB := integral_im_logDeriv_horizontal_eq_of_re_neg (g := g) (T := T₁)
    (fun x hx => (hbot x hx).2.2.1) (fun x hx => (hbot x hx).2.2.2.1)
  have eU := integral_im_logDeriv_horizontal_eq_of_re_neg (g := g) (T := T₂)
    (fun x hx => (htop x hx).2.2.1) (fun x hx => (htop x hx).2.2.2.1)
  rw [hvert c hleft, hvert d hright, hhor T₁ hbot, hhor T₂ htop, eL, eR, eB, eU] at h₁
  have hpi : 0 < 2 * Real.pi := by positivity
  have key : 2 * Real.pi * (∑ w ∈ Z₁, ((analyticOrderAt F₁ w).toNat : ℝ)) =
      2 * Real.pi * (∑ w ∈ Z₀, ((analyticOrderAt F₀ w).toNat : ℝ)) := by
    linarith
  have := mul_left_cancel₀ hpi.ne' key
  exact_mod_cast this

end

end RHTower
