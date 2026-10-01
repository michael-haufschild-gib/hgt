import GaloisForLFunctions.RHTower.RectangleLeftHalfPlaneWinding

/-!
# Zero counts when a ratio stays in closed half-planes along boundary segments

Let `F₁, F₀` be entire and `g` analytic on the boundary of `[c, d] × [T₁, T₂]` with
`logDeriv F₁ = logDeriv g + logDeriv F₀` there. Suppose the boundary splits at an abscissa
`c < m < d` into six segments on each of which `g` or `−g` lies in the slit plane with nonnegative
real part:
- `−g` on the left edge and on the left halves of the horizontal edges;
- `g` on the right edge and on the right halves.

Then the zero counts of `F₁` and `F₀` in the closed rectangle differ by at most `3`
(`abs_sum_analyticOrderAt_sub_le_three`).

**Proof.** On each segment `Im log(±g)` is a primitive of the argument derivative of `g` and takes
values in `[−π/2, π/2]`. So each of the six segments contributes at most `π`, and the argument
principle gives `2π |N₁ − N₀| ≤ 6π`.
-/

open Complex Set intervalIntegral

namespace RHTower

noncomputable section

/-- **Vertical segment in the slit plane.** -/
theorem integral_re_logDeriv_vertical_eq_of_slitPlane {g : ℂ → ℂ} {x T₁ T₂ : ℝ}
    (hg : ∀ t ∈ uIcc T₁ T₂, AnalyticAt ℂ g ((x : ℂ) + t * I))
    (hs : ∀ t ∈ uIcc T₁ T₂, g ((x : ℂ) + t * I) ∈ slitPlane) :
    ∫ t in T₁..T₂, (logDeriv g ((x : ℂ) + t * I)).re =
      (Complex.log (g ((x : ℂ) + T₂ * I))).im - (Complex.log (g ((x : ℂ) + T₁ * I))).im := by
  have hpath : ∀ t : ℝ, HasDerivAt (fun u : ℝ => (x : ℂ) + u * I) I t := by
    intro t
    simpa using ((hasDerivAt_id t).ofReal_comp.mul_const I).const_add (x : ℂ)
  have hne : ∀ t ∈ uIcc T₁ T₂, g ((x : ℂ) + t * I) ≠ 0 := fun t ht =>
    slitPlane_ne_zero (hs t ht)
  have hderiv : ∀ t ∈ uIcc T₁ T₂, HasDerivAt
      (fun u : ℝ => (Complex.log (g ((x : ℂ) + u * I))).im)
      ((logDeriv g ((x : ℂ) + t * I)).re) t := by
    intro t ht
    have h1 : HasDerivAt (fun u : ℝ => g ((x : ℂ) + u * I))
        (I • deriv g ((x : ℂ) + t * I)) t :=
      (hg t ht).differentiableAt.hasDerivAt.scomp t (hpath t)
    have h2 := h1.clog_real (hs t ht)
    have h3 : HasDerivAt (fun u : ℝ => (Complex.log (g ((x : ℂ) + u * I))).im)
        (((I • deriv g ((x : ℂ) + t * I)) / g ((x : ℂ) + t * I)).im) t :=
      Complex.imCLM.hasFDerivAt.comp_hasDerivAt t h2
    refine h3.congr_deriv ?_
    rw [logDeriv_apply, smul_eq_mul, mul_div_assoc, Complex.mul_im, Complex.I_re,
      Complex.I_im]
    ring
  have hcont : ContinuousOn (fun t : ℝ => (logDeriv g ((x : ℂ) + t * I)).re) (uIcc T₁ T₂) := by
    intro t ht
    exact (Complex.continuous_re.continuousAt.comp
      ((continuousAt_logDeriv_of_analyticAt (hg t ht) (hne t ht)).comp
        (f := fun u : ℝ => (x : ℂ) + u * I) (hpath t).continuousAt)).continuousWithinAt
  exact integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable

/-- **Horizontal segment in the slit plane.** -/
theorem integral_im_logDeriv_horizontal_eq_of_slitPlane {g : ℂ → ℂ} {c d T : ℝ}
    (hg : ∀ x ∈ uIcc c d, AnalyticAt ℂ g ((x : ℂ) + T * I))
    (hs : ∀ x ∈ uIcc c d, g ((x : ℂ) + T * I) ∈ slitPlane) :
    ∫ x in c..d, (logDeriv g ((x : ℂ) + T * I)).im =
      (Complex.log (g ((d : ℂ) + T * I))).im - (Complex.log (g ((c : ℂ) + T * I))).im := by
  have hpath : ∀ x : ℝ, HasDerivAt (fun u : ℝ => (u : ℂ) + T * I) 1 x := by
    intro x
    simpa using (hasDerivAt_id x).ofReal_comp.add_const ((T : ℂ) * I)
  have hne : ∀ x ∈ uIcc c d, g ((x : ℂ) + T * I) ≠ 0 := fun x hx =>
    slitPlane_ne_zero (hs x hx)
  have hderiv : ∀ x ∈ uIcc c d, HasDerivAt
      (fun u : ℝ => (Complex.log (g ((u : ℂ) + T * I))).im)
      ((logDeriv g ((x : ℂ) + T * I)).im) x := by
    intro x hx
    have h1 : HasDerivAt (fun u : ℝ => g ((u : ℂ) + T * I))
        ((1 : ℝ) • deriv g ((x : ℂ) + T * I)) x :=
      (hg x hx).differentiableAt.hasDerivAt.scomp x (hpath x)
    have h2 := h1.clog_real (hs x hx)
    have h3 : HasDerivAt (fun u : ℝ => (Complex.log (g ((u : ℂ) + T * I))).im)
        ((((1 : ℝ) • deriv g ((x : ℂ) + T * I)) / g ((x : ℂ) + T * I)).im) x :=
      Complex.imCLM.hasFDerivAt.comp_hasDerivAt x h2
    refine h3.congr_deriv ?_
    rw [logDeriv_apply, one_smul]
  have hcont : ContinuousOn (fun x : ℝ => (logDeriv g ((x : ℂ) + T * I)).im) (uIcc c d) := by
    intro x hx
    exact (Complex.continuous_im.continuousAt.comp
      ((continuousAt_logDeriv_of_analyticAt (hg x hx) (hne x hx)).comp
        (f := fun u : ℝ => (u : ℂ) + T * I) (hpath x).continuousAt)).continuousWithinAt
  exact integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable

/-- `logDeriv (−g) = logDeriv g`. -/
theorem logDeriv_neg_fun (g : ℂ → ℂ) (z : ℂ) : logDeriv (fun w => -g w) z = logDeriv g z := by
  rw [logDeriv_apply, logDeriv_apply, deriv.fun_neg, neg_div_neg_eq]

/-- A point of the closed right half-plane minus the origin has `|Im log| ≤ π/2`. -/
theorem abs_im_log_le_of_re_nonneg {w : ℂ} (hw : 0 ≤ w.re) : |(Complex.log w).im| ≤ Real.pi / 2 := by
  rw [Complex.log_im]
  exact Complex.abs_arg_le_pi_div_two_iff.mpr hw

/-- The segment hypothesis: `g` analytic at `z`, `g z` in the slit plane with nonnegative real
part. -/
def HalfPlaneGood (g : ℂ → ℂ) (z : ℂ) : Prop :=
  AnalyticAt ℂ g z ∧ g z ∈ slitPlane ∧ 0 ≤ (g z).re

/-- The boundary relation between `F₁`, `F₀` and `g` at `z`. -/
def RatioRelation (F₁ F₀ g : ℂ → ℂ) (z : ℂ) : Prop :=
  F₁ z ≠ 0 ∧ F₀ z ≠ 0 ∧ logDeriv F₁ z = logDeriv g z + logDeriv F₀ z

theorem continuousAt_logDeriv_of_halfPlaneGood {g : ℂ → ℂ} {z : ℂ} (h : HalfPlaneGood g z) :
    ContinuousAt (logDeriv g) z :=
  continuousAt_logDeriv_of_analyticAt h.1 (slitPlane_ne_zero h.2.1)

theorem halfPlaneGood_neg_analytic {g : ℂ → ℂ} {z : ℂ} (h : HalfPlaneGood (fun w => -g w) z) :
    AnalyticAt ℂ g z ∧ g z ≠ 0 := by
  refine ⟨?_, fun h0 => slitPlane_ne_zero h.2.1 (by simp [h0])⟩
  have h2 : AnalyticAt ℂ (fun w => -(-g w)) z := h.1.neg
  simp only [neg_neg] at h2
  exact h2

/-- **Six-segment winding bound.** Under the segment hypotheses, the zero counts of `F₁` and `F₀`
in the closed rectangle differ by at most `3`. -/
theorem abs_sum_analyticOrderAt_sub_le_three {F₁ F₀ g : ℂ → ℂ}
    (hF₁ : AnalyticOnNhd ℂ F₁ Set.univ) (hF₀ : AnalyticOnNhd ℂ F₀ Set.univ)
    (hn₁ : ∃ z : ℂ, F₁ z ≠ 0) (hn₀ : ∃ z : ℂ, F₀ z ≠ 0)
    {c m d T₁ T₂ : ℝ} (hcm : c < m) (hmd : m < d) (hT : T₁ < T₂)
    (rbot : ∀ x ∈ uIcc c d, RatioRelation F₁ F₀ g ((x : ℂ) + T₁ * I))
    (rtop : ∀ x ∈ uIcc c d, RatioRelation F₁ F₀ g ((x : ℂ) + T₂ * I))
    (rright : ∀ t ∈ uIcc T₁ T₂, RatioRelation F₁ F₀ g ((d : ℂ) + t * I))
    (rleft : ∀ t ∈ uIcc T₁ T₂, RatioRelation F₁ F₀ g ((c : ℂ) + t * I))
    (gleft : ∀ t ∈ uIcc T₁ T₂, HalfPlaneGood (fun w => -g w) ((c : ℂ) + t * I))
    (gright : ∀ t ∈ uIcc T₁ T₂, HalfPlaneGood g ((d : ℂ) + t * I))
    (gbotL : ∀ x ∈ uIcc c m, HalfPlaneGood (fun w => -g w) ((x : ℂ) + T₁ * I))
    (gbotR : ∀ x ∈ uIcc m d, HalfPlaneGood g ((x : ℂ) + T₁ * I))
    (gtopL : ∀ x ∈ uIcc c m, HalfPlaneGood (fun w => -g w) ((x : ℂ) + T₂ * I))
    (gtopR : ∀ x ∈ uIcc m d, HalfPlaneGood g ((x : ℂ) + T₂ * I)) :
    ∃ Z₁ Z₀ : Finset ℂ,
      (∀ z : ℂ, z ∈ Z₁ ↔ z ∈ (uIcc c d ×ℂ uIcc T₁ T₂) ∧ F₁ z = 0) ∧
      (∀ z : ℂ, z ∈ Z₀ ↔ z ∈ (uIcc c d ×ℂ uIcc T₁ T₂) ∧ F₀ z = 0) ∧
      |(∑ w ∈ Z₁, ((analyticOrderAt F₁ w).toNat : ℝ)) -
        ∑ w ∈ Z₀, ((analyticOrderAt F₀ w).toNat : ℝ)| ≤ 3 := by
  obtain ⟨Z₁, hZ₁, h₁⟩ := exists_entire_argument_variation_rectangle hF₁ hn₁ (hcm.trans hmd) hT
    (fun x hx => (rbot x hx).1) (fun x hx => (rtop x hx).1)
    (fun t ht => (rright t ht).1) (fun t ht => (rleft t ht).1)
  obtain ⟨Z₀, hZ₀, h₀⟩ := exists_entire_argument_variation_rectangle hF₀ hn₀ (hcm.trans hmd) hT
    (fun x hx => (rbot x hx).2.1) (fun x hx => (rtop x hx).2.1)
    (fun t ht => (rright t ht).2.1) (fun t ht => (rleft t ht).2.1)
  refine ⟨Z₁, Z₀, hZ₁, hZ₀, ?_⟩
  have hcd : c < d := hcm.trans hmd
  have hucd : uIcc c d = uIcc c m ∪ uIcc m d := by
    rw [uIcc_of_le hcd.le, uIcc_of_le hcm.le, uIcc_of_le hmd.le, Icc_union_Icc_eq_Icc hcm.le hmd.le]
  -- `g` is analytic and nonzero on the whole boundary
  have hgood : ∀ z : ℂ, (HalfPlaneGood g z ∨ HalfPlaneGood (fun w => -g w) z) →
      ContinuousAt (logDeriv g) z := by
    rintro z (h | h)
    · exact continuousAt_logDeriv_of_halfPlaneGood h
    · obtain ⟨ha, hne⟩ := halfPlaneGood_neg_analytic h
      exact continuousAt_logDeriv_of_analyticAt ha hne
  have hbotg : ∀ x ∈ uIcc c d, HalfPlaneGood g ((x : ℂ) + T₁ * I) ∨
      HalfPlaneGood (fun w => -g w) ((x : ℂ) + T₁ * I) := by
    intro x hx
    rw [hucd] at hx
    rcases hx with hx | hx
    · exact Or.inr (gbotL x hx)
    · exact Or.inl (gbotR x hx)
  have htopg : ∀ x ∈ uIcc c d, HalfPlaneGood g ((x : ℂ) + T₂ * I) ∨
      HalfPlaneGood (fun w => -g w) ((x : ℂ) + T₂ * I) := by
    intro x hx
    rw [hucd] at hx
    rcases hx with hx | hx
    · exact Or.inr (gtopL x hx)
    · exact Or.inl (gtopR x hx)
  have hcF₀ : ∀ z : ℂ, F₀ z ≠ 0 → ContinuousAt (logDeriv F₀) z := fun z hz =>
    continuousAt_logDeriv_of_analyticAt (hF₀ z (Set.mem_univ z)) hz
  have hvpath : ∀ x : ℝ, Continuous (fun u : ℝ => (x : ℂ) + u * I) := fun x => by fun_prop
  have hhpath : ∀ T : ℝ, Continuous (fun u : ℝ => (u : ℂ) + T * I) := fun T => by fun_prop
  -- interval integrability of the edge integrands
  have ivg : ∀ x : ℝ, (∀ t ∈ uIcc T₁ T₂, ContinuousAt (logDeriv g) ((x : ℂ) + t * I)) →
      IntervalIntegrable (fun t : ℝ => (logDeriv g ((x : ℂ) + t * I)).re)
        MeasureTheory.volume T₁ T₂ := fun x hx =>
    ContinuousOn.intervalIntegrable fun t ht =>
      (Complex.continuous_re.continuousAt.comp ((hx t ht).comp
        (f := fun u : ℝ => (x : ℂ) + u * I) (hvpath x).continuousAt)).continuousWithinAt
  have iv0 : ∀ x : ℝ, (∀ t ∈ uIcc T₁ T₂, F₀ ((x : ℂ) + t * I) ≠ 0) →
      IntervalIntegrable (fun t : ℝ => (logDeriv F₀ ((x : ℂ) + t * I)).re)
        MeasureTheory.volume T₁ T₂ := fun x hx =>
    ContinuousOn.intervalIntegrable fun t ht =>
      (Complex.continuous_re.continuousAt.comp ((hcF₀ _ (hx t ht)).comp
        (f := fun u : ℝ => (x : ℂ) + u * I) (hvpath x).continuousAt)).continuousWithinAt
  have ihg : ∀ (T a b : ℝ), (∀ x ∈ uIcc a b, ContinuousAt (logDeriv g) ((x : ℂ) + T * I)) →
      IntervalIntegrable (fun x : ℝ => (logDeriv g ((x : ℂ) + T * I)).im)
        MeasureTheory.volume a b := fun T a b hx =>
    ContinuousOn.intervalIntegrable fun x hxm =>
      (Complex.continuous_im.continuousAt.comp ((hx x hxm).comp
        (f := fun u : ℝ => (u : ℂ) + T * I) (hhpath T).continuousAt)).continuousWithinAt
  have ih0 : ∀ T : ℝ, (∀ x ∈ uIcc c d, F₀ ((x : ℂ) + T * I) ≠ 0) →
      IntervalIntegrable (fun x : ℝ => (logDeriv F₀ ((x : ℂ) + T * I)).im)
        MeasureTheory.volume c d := fun T hx =>
    ContinuousOn.intervalIntegrable fun x hxm =>
      (Complex.continuous_im.continuousAt.comp ((hcF₀ _ (hx x hxm)).comp
        (f := fun u : ℝ => (u : ℂ) + T * I) (hhpath T).continuousAt)).continuousWithinAt
  -- splitting the `F₁` integrals
  have hvsplit : ∀ x : ℝ, (∀ t ∈ uIcc T₁ T₂, RatioRelation F₁ F₀ g ((x : ℂ) + t * I)) →
      (∀ t ∈ uIcc T₁ T₂, ContinuousAt (logDeriv g) ((x : ℂ) + t * I)) →
      ∫ t in T₁..T₂, (logDeriv F₁ ((x : ℂ) + t * I)).re =
        (∫ t in T₁..T₂, (logDeriv g ((x : ℂ) + t * I)).re) +
          ∫ t in T₁..T₂, (logDeriv F₀ ((x : ℂ) + t * I)).re := by
    intro x hr hc
    rw [← intervalIntegral.integral_add (ivg x hc) (iv0 x fun t ht => (hr t ht).2.1)]
    refine intervalIntegral.integral_congr fun t ht => ?_
    simp only [(hr t ht).2.2, Complex.add_re]
  have hhsplit : ∀ T : ℝ, (∀ x ∈ uIcc c d, RatioRelation F₁ F₀ g ((x : ℂ) + T * I)) →
      (∀ x ∈ uIcc c d, ContinuousAt (logDeriv g) ((x : ℂ) + T * I)) →
      ∫ x in c..d, (logDeriv F₁ ((x : ℂ) + T * I)).im =
        (∫ x in c..d, (logDeriv g ((x : ℂ) + T * I)).im) +
          ∫ x in c..d, (logDeriv F₀ ((x : ℂ) + T * I)).im := by
    intro T hr hc
    rw [← intervalIntegral.integral_add (ihg T c d hc) (ih0 T fun x hx => (hr x hx).2.1)]
    refine intervalIntegral.integral_congr fun x hx => ?_
    simp only [(hr x hx).2.2, Complex.add_im]
  have hcleft : ∀ t ∈ uIcc T₁ T₂, ContinuousAt (logDeriv g) ((c : ℂ) + t * I) :=
    fun t ht => hgood _ (Or.inr (gleft t ht))
  have hcright : ∀ t ∈ uIcc T₁ T₂, ContinuousAt (logDeriv g) ((d : ℂ) + t * I) :=
    fun t ht => hgood _ (Or.inl (gright t ht))
  have hcbot : ∀ x ∈ uIcc c d, ContinuousAt (logDeriv g) ((x : ℂ) + T₁ * I) :=
    fun x hx => hgood _ (hbotg x hx)
  have hctop : ∀ x ∈ uIcc c d, ContinuousAt (logDeriv g) ((x : ℂ) + T₂ * I) :=
    fun x hx => hgood _ (htopg x hx)
  rw [hvsplit c rleft hcleft, hvsplit d rright hcright, hhsplit T₁ rbot hcbot,
    hhsplit T₂ rtop hctop] at h₁
  -- the `g` edge integrals as increments of `Im log(±g)`
  have hsubL : uIcc c m ⊆ uIcc c d := by
    rw [hucd]; exact subset_union_left
  have hsubR : uIcc m d ⊆ uIcc c d := by
    rw [hucd]; exact subset_union_right
  have hsplitH : ∀ T : ℝ, (∀ x ∈ uIcc c d, ContinuousAt (logDeriv g) ((x : ℂ) + T * I)) →
      ∫ x in c..d, (logDeriv g ((x : ℂ) + T * I)).im =
        (∫ x in c..m, (logDeriv g ((x : ℂ) + T * I)).im) +
          ∫ x in m..d, (logDeriv g ((x : ℂ) + T * I)).im := fun T hc =>
    (intervalIntegral.integral_add_adjacent_intervals
      (ihg T c m fun x hx => hc x (hsubL hx)) (ihg T m d fun x hx => hc x (hsubR hx))).symm
  rw [hsplitH T₁ hcbot, hsplitH T₂ hctop] at h₁
  -- each piece
  have eL : ∫ t in T₁..T₂, (logDeriv g ((c : ℂ) + t * I)).re =
      (Complex.log (-g ((c : ℂ) + T₂ * I))).im - (Complex.log (-g ((c : ℂ) + T₁ * I))).im := by
    have := integral_re_logDeriv_vertical_eq_of_slitPlane (g := fun w => -g w) (x := c)
      (fun t ht => (gleft t ht).1) (fun t ht => (gleft t ht).2.1)
    simpa only [logDeriv_neg_fun] using this
  have eR := integral_re_logDeriv_vertical_eq_of_slitPlane (g := g) (x := d)
    (fun t ht => (gright t ht).1) (fun t ht => (gright t ht).2.1)
  have eBL : ∫ x in c..m, (logDeriv g ((x : ℂ) + T₁ * I)).im =
      (Complex.log (-g ((m : ℂ) + T₁ * I))).im - (Complex.log (-g ((c : ℂ) + T₁ * I))).im := by
    have := integral_im_logDeriv_horizontal_eq_of_slitPlane (g := fun w => -g w) (c := c) (d := m)
      (T := T₁) (fun x hx => (gbotL x hx).1) (fun x hx => (gbotL x hx).2.1)
    simpa only [logDeriv_neg_fun] using this
  have eBR := integral_im_logDeriv_horizontal_eq_of_slitPlane (g := g) (c := m) (d := d)
    (T := T₁) (fun x hx => (gbotR x hx).1) (fun x hx => (gbotR x hx).2.1)
  have eUL : ∫ x in c..m, (logDeriv g ((x : ℂ) + T₂ * I)).im =
      (Complex.log (-g ((m : ℂ) + T₂ * I))).im - (Complex.log (-g ((c : ℂ) + T₂ * I))).im := by
    have := integral_im_logDeriv_horizontal_eq_of_slitPlane (g := fun w => -g w) (c := c) (d := m)
      (T := T₂) (fun x hx => (gtopL x hx).1) (fun x hx => (gtopL x hx).2.1)
    simpa only [logDeriv_neg_fun] using this
  have eUR := integral_im_logDeriv_horizontal_eq_of_slitPlane (g := g) (c := m) (d := d)
    (T := T₂) (fun x hx => (gtopR x hx).1) (fun x hx => (gtopR x hx).2.1)
  rw [eL, eR, eBL, eBR, eUL, eUR] at h₁
  -- bounds on the twelve logarithms
  have hb : ∀ w : ℂ, 0 ≤ w.re → |(Complex.log w).im| ≤ Real.pi / 2 :=
    fun w hw => abs_im_log_le_of_re_nonneg hw
  have mem_l : ∀ {a b : ℝ}, a ≤ b → a ∈ uIcc a b := fun h => by rw [uIcc_of_le h]; exact ⟨le_rfl, h⟩
  have mem_r : ∀ {a b : ℝ}, a ≤ b → b ∈ uIcc a b := fun h => by rw [uIcc_of_le h]; exact ⟨h, le_rfl⟩
  have b1 := hb _ (gleft T₂ (mem_r hT.le)).2.2
  have b2 := hb _ (gleft T₁ (mem_l hT.le)).2.2
  have b3 := hb _ (gright T₂ (mem_r hT.le)).2.2
  have b4 := hb _ (gright T₁ (mem_l hT.le)).2.2
  have b5 := hb _ (gbotL m (mem_r hcm.le)).2.2
  have b6 := hb _ (gbotL c (mem_l hcm.le)).2.2
  have b7 := hb _ (gbotR d (mem_r hmd.le)).2.2
  have b8 := hb _ (gbotR m (mem_l hmd.le)).2.2
  have b9 := hb _ (gtopL m (mem_r hcm.le)).2.2
  have b10 := hb _ (gtopL c (mem_l hcm.le)).2.2
  have b11 := hb _ (gtopR d (mem_r hmd.le)).2.2
  have b12 := hb _ (gtopR m (mem_l hmd.le)).2.2
  simp only at b1 b2 b5 b6 b9 b10
  rw [abs_le] at b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12
  have hpi : 0 < Real.pi := Real.pi_pos
  rw [abs_le]
  constructor <;> nlinarith

end

end RHTower
