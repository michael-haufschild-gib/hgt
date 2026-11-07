import GaloisForLFunctions.BlackHoleRingdown.TheExpansionIsUniformAtLateTimes

/-!
# The contour package

Let `R` be analytic on `-A ≤ Re u ≤ 0`, with `Q = R/ξ(1+2u)` integrable on the two vertical lines and small on
the horizontal edges at the good heights. Then for the field `𝓖(τ) = ∫ e^{iyτ} Q(iy) dy`, the partial sums of
`2π Res_p [e^{uτ} Q]` over the zeros up to the good heights converge to `𝓖 - R_A`, where
`R_A(τ) = ∫ e^{(-A+iy)τ} Q(-A+iy) dy = O(e^{-Aτ})`. The convergence is uniform on every half line
`τ ≥ -τ₀`, because `|e^{uτ}| ≤ e^{Aτ₀}` on the strip.

Nothing here depends on how `R` was produced, so the same package serves a pulse, a Gaussian packet, and any
jet of either.
-/

open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace GaloisForLFunctions.BlackHoleRingdown

open _root_.RHTower HTGeometry

/-- The hypotheses of the contour argument at depth `A`. -/
structure ContourData (A : ℝ) (R : ℂ → ℂ) : Prop where
  analytic : ∀ u : ℂ, -A ≤ u.re → u.re ≤ 0 → AnalyticAt ℂ R u
  right : Integrable fun y : ℝ => inverseXiQuotient R ((y : ℂ) * I)
  left : Integrable fun y : ℝ => inverseXiQuotient R (((-A : ℝ) : ℂ) + (y : ℂ) * I)
  edge : ∃ B : ℕ → ℝ, Tendsto B atTop (𝓝 0) ∧ ∀ᶠ k in atTop, ∀ u : ℂ, -A ≤ u.re → u.re ≤ 0 →
    |u.im| = goodHeight k / 2 → ‖inverseXiQuotient R u‖ ≤ B k

/-- The numerator at time `τ`. -/
def timeNumerator (R : ℂ → ℂ) (τ : ℝ) (u : ℂ) : ℂ := R u * Complex.exp (u * (τ : ℂ))

theorem inverseXiQuotient_timeNumerator (R : ℂ → ℂ) (τ : ℝ) (u : ℂ) :
    inverseXiQuotient (timeNumerator R τ) u = Complex.exp (u * (τ : ℂ)) * inverseXiQuotient R u := by
  simp only [inverseXiQuotient, timeNumerator]
  ring

/-- The field on the line `Re u = 0`. -/
def contourField (R : ℂ → ℂ) (τ : ℝ) : ℂ :=
  ∫ y : ℝ, inverseXiQuotient (timeNumerator R τ) ((y : ℂ) * I)

/-- The remainder on the line `Re u = -A`. -/
def contourRemainder (A : ℝ) (R : ℂ → ℂ) (τ : ℝ) : ℂ :=
  ∫ y : ℝ, inverseXiQuotient (timeNumerator R τ) (((-A : ℝ) : ℂ) + (y : ℂ) * I)

/-- `2π` times the residues at the zeros up to the `k`-th good height. -/
def contourPartial (R : ℂ → ℂ) (τ : ℝ) (k : ℕ) : ℂ :=
  2 * Real.pi * ∑ p ∈ ringdownPoles (goodHeight k),
    laurentCoeff (inverseXiQuotient (timeNumerator R τ)) p (-1)

/-- **The residue theorem on the rectangle**, for an analytic numerator. -/
theorem rectangleIntegral'_quotient {A : ℝ} (hA : 1 ≤ A) {R : ℂ → ℂ}
    (hR : ∀ u : ℂ, -A ≤ u.re → u.re ≤ 0 → AnalyticAt ℂ R u) (k : ℕ) :
    RectangleIntegral' (inverseXiQuotient R) ⟨-A, -(goodHeight k / 2)⟩ ⟨0, goodHeight k / 2⟩ =
      ∑ p ∈ ringdownPoles (goodHeight k), laurentCoeff (inverseXiQuotient R) p (-1) := by
  have hT := one_le_goodHeight k
  have hre1 : (-A : ℝ) ≤ 0 := by linarith
  have him1 : -(goodHeight k / 2) ≤ goodHeight k / 2 := by linarith
  have hmemRect : ∀ s ∈ Rectangle (⟨-A, -(goodHeight k / 2)⟩ : ℂ) ⟨0, goodHeight k / 2⟩,
      -A ≤ s.re ∧ s.re ≤ 0 ∧ |s.im| ≤ goodHeight k / 2 := by
    intro s hs
    rw [Rectangle, Complex.mem_reProdIm] at hs
    simp only at hs
    rw [uIcc_of_le hre1, uIcc_of_le him1] at hs
    exact ⟨hs.1.1, hs.1.2, abs_le.mpr hs.2⟩
  refine rectangleIntegral'_eq_sum_laurentCoeff hre1 him1 ?_ ?_ ?_
  · intro p hp
    obtain ⟨h0, hle⟩ := mem_ringdownPoles.mp hp
    have hloc := re_of_mem_ringdownPoleSet (T := goodHeight k) ⟨h0, hle⟩
    have hne : |p.im| ≠ goodHeight k / 2 := by
      intro he
      refine xi_ne_zero_of_abs_im_goodHeight k (s := 1 + 2 * p) ?_ h0
      have h3 : (1 + 2 * p).im = 2 * p.im := by simp
      rw [h3, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), he]
      ring
    have hlt : |p.im| < goodHeight k / 2 := lt_of_le_of_ne hle hne
    rw [rectangle_mem_nhds_iff, Complex.mem_reProdIm]
    simp only
    rw [uIoo_of_le hre1, uIoo_of_le him1]
    exact ⟨⟨by linarith [hloc.1], hloc.2⟩, abs_lt.mp hlt⟩
  · intro p hp
    obtain ⟨h0, hle⟩ := mem_ringdownPoles.mp hp
    have hloc := re_of_mem_ringdownPoleSet (T := goodHeight k) ⟨h0, hle⟩
    exact (hR p (by linarith [hloc.1]) hloc.2.le).meromorphicAt.div
      (differentiable_xi_shift.analyticAt p).meromorphicAt
  · intro s hs hsP
    obtain ⟨h1, h2, h3⟩ := hmemRect s hs
    refine (hR s h1 h2).div (differentiable_xi_shift.analyticAt s) fun h0 => hsP ?_
    exact mem_ringdownPoles.mpr ⟨h0, h3⟩

theorem ContourData.analytic_time {A : ℝ} {R : ℂ → ℂ} (hD : ContourData A R) (τ : ℝ) (u : ℂ)
    (h1 : -A ≤ u.re) (h2 : u.re ≤ 0) : AnalyticAt ℂ (timeNumerator R τ) u :=
  (hD.analytic u h1 h2).mul (by fun_prop)

/-- The partial sum from the edges and the truncated lines. -/
theorem contourPartial_eq {A : ℝ} (hA : 1 ≤ A) {R : ℂ → ℂ} (hD : ContourData A R) (τ : ℝ) (k : ℕ) :
    contourPartial R τ k =
      (HIntegral (inverseXiQuotient (timeNumerator R τ)) (-A) 0 (-(goodHeight k / 2)) -
          HIntegral (inverseXiQuotient (timeNumerator R τ)) (-A) 0 (goodHeight k / 2)) / I +
        (∫ y in (-(goodHeight k / 2))..(goodHeight k / 2),
          inverseXiQuotient (timeNumerator R τ) ((y : ℂ) * I)) -
        ∫ y in (-(goodHeight k / 2))..(goodHeight k / 2),
          inverseXiQuotient (timeNumerator R τ) (((-A : ℝ) : ℂ) + (y : ℂ) * I) := by
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  rw [contourPartial, ← rectangleIntegral'_quotient hA (hD.analytic_time τ) k]
  simp only [RectangleIntegral', RectangleIntegral, VIntegral, smul_eq_mul]
  simp only [Complex.ofReal_zero, zero_add]
  field_simp

/-- The modulus of the time factor on the strip, for `τ ≥ -τ₀`. -/
theorem norm_cexp_mul_le {A τ₀ τ : ℝ} (hA : 0 ≤ A) (hτ₀ : 0 ≤ τ₀) (hτ : -τ₀ ≤ τ) {u : ℂ}
    (h1 : -A ≤ u.re) (h2 : u.re ≤ 0) : ‖Complex.exp (u * (τ : ℂ))‖ ≤ Real.exp (A * τ₀) := by
  rw [Complex.norm_exp]
  have hre : (u * (τ : ℂ)).re = u.re * τ := by simp
  rw [hre]
  refine Real.exp_le_exp.mpr ?_
  rcases le_total 0 τ with h | h
  · have : u.re * τ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h2 h
    have : 0 ≤ A * τ₀ := by positivity
    linarith
  · nlinarith

theorem continuous_time_factor (τ : ℝ) (c : ℝ) :
    Continuous fun y : ℝ => Complex.exp (((c : ℂ) + (y : ℂ) * I) * (τ : ℂ)) := by
  fun_prop

theorem integrable_time_right {A : ℝ} {R : ℂ → ℂ} (hD : ContourData A R) (τ : ℝ) :
    Integrable fun y : ℝ => inverseXiQuotient (timeNumerator R τ) ((y : ℂ) * I) := by
  have hc : Continuous fun y : ℝ => Complex.exp ((y : ℂ) * I * (τ : ℂ)) := by fun_prop
  have heq : (fun y : ℝ => inverseXiQuotient (timeNumerator R τ) ((y : ℂ) * I)) =
      fun y : ℝ => Complex.exp ((y : ℂ) * I * (τ : ℂ)) * inverseXiQuotient R ((y : ℂ) * I) :=
    funext fun y => inverseXiQuotient_timeNumerator R τ _
  rw [heq]
  refine (hD.right.norm).mono' (hc.aestronglyMeasurable.mul hD.right.aestronglyMeasurable)
    (Eventually.of_forall fun y => ?_)
  rw [norm_mul, Complex.norm_exp]
  have hre : ((y : ℂ) * I * (τ : ℂ)).re = 0 := by simp
  rw [hre, Real.exp_zero, one_mul]

theorem integrable_time_left {A : ℝ} {R : ℂ → ℂ} (hD : ContourData A R) (τ : ℝ) :
    Integrable fun y : ℝ => inverseXiQuotient (timeNumerator R τ) (((-A : ℝ) : ℂ) + (y : ℂ) * I) := by
  have hc := continuous_time_factor τ (-A)
  have heq : (fun y : ℝ => inverseXiQuotient (timeNumerator R τ) (((-A : ℝ) : ℂ) + (y : ℂ) * I)) =
      fun y : ℝ => Complex.exp ((((-A : ℝ) : ℂ) + (y : ℂ) * I) * (τ : ℂ)) *
        inverseXiQuotient R (((-A : ℝ) : ℂ) + (y : ℂ) * I) :=
    funext fun y => inverseXiQuotient_timeNumerator R τ _
  rw [heq]
  refine (hD.left.norm.const_mul (Real.exp (-A * τ))).mono'
    (hc.aestronglyMeasurable.mul hD.left.aestronglyMeasurable) (Eventually.of_forall fun y => ?_)
  rw [norm_mul, Complex.norm_exp]
  have hre : ((((-A : ℝ) : ℂ) + (y : ℂ) * I) * (τ : ℂ)).re = -A * τ := by simp
  rw [hre]

/-- **The remainder is `O(e^{-Aτ})`**, uniformly in `τ`. -/
theorem norm_contourRemainder_le (A : ℝ) (R : ℂ → ℂ) (τ : ℝ) :
    ‖contourRemainder A R τ‖ ≤
      (∫ y : ℝ, ‖inverseXiQuotient R (((-A : ℝ) : ℂ) + (y : ℂ) * I)‖) * Real.exp (-A * τ) := by
  have hpoint : ∀ y : ℝ,
      ‖inverseXiQuotient (timeNumerator R τ) (((-A : ℝ) : ℂ) + (y : ℂ) * I)‖ =
        Real.exp (-A * τ) * ‖inverseXiQuotient R (((-A : ℝ) : ℂ) + (y : ℂ) * I)‖ := by
    intro y
    rw [inverseXiQuotient_timeNumerator, norm_mul, Complex.norm_exp]
    congr 2
    simp
  calc ‖contourRemainder A R τ‖
      ≤ ∫ y : ℝ, ‖inverseXiQuotient (timeNumerator R τ) (((-A : ℝ) : ℂ) + (y : ℂ) * I)‖ :=
        norm_integral_le_integral_norm _
    _ = Real.exp (-A * τ) * ∫ y : ℝ, ‖inverseXiQuotient R (((-A : ℝ) : ℂ) + (y : ℂ) * I)‖ := by
        simp_rw [hpoint]
        exact integral_const_mul _ _
    _ = _ := mul_comm _ _

/-- **The uniform bound of the contour package.** -/
theorem exists_contour_uniform_bound {A : ℝ} (hA : 1 ≤ A) {R : ℂ → ℂ} (hD : ContourData A R) :
    ∃ B : ℕ → ℝ, Tendsto B atTop (𝓝 0) ∧ ∀ᶠ k in atTop, ∀ τ₀ τ : ℝ, 0 ≤ τ₀ → -τ₀ ≤ τ →
      ‖(contourField R τ - contourRemainder A R τ) - contourPartial R τ k‖ ≤
        Real.exp (A * τ₀) * B k := by
  have hAnn : 0 ≤ A := by linarith
  obtain ⟨E, hE, hEdge⟩ := hD.edge
  set n₁ : ℝ → ℝ := fun y => ‖inverseXiQuotient R ((y : ℂ) * I)‖ with hn₁
  set n₂ : ℝ → ℝ := fun y => ‖inverseXiQuotient R (((-A : ℝ) : ℂ) + (y : ℂ) * I)‖ with hn₂
  have hint₁ : Integrable n₁ := hD.right.norm
  have hint₂ : Integrable n₂ := hD.left.norm
  have hLat : Tendsto (fun k => goodHeight k / 2) atTop atTop :=
    tendsto_goodHeight.atTop_div_const (by norm_num)
  refine ⟨fun k => ((∫ y, n₁ y) - ∫ y in (-(goodHeight k / 2))..(goodHeight k / 2), n₁ y) +
      ((∫ y, n₂ y) - ∫ y in (-(goodHeight k / 2))..(goodHeight k / 2), n₂ y) + 2 * (E k * A), ?_, ?_⟩
  · have ht₁ := (tendsto_integral_sub_interval hint₁).comp hLat
    have ht₂ := (tendsto_integral_sub_interval hint₂).comp hLat
    have hedges : Tendsto (fun k => 2 * (E k * A)) atTop (𝓝 0) := by
      simpa using (hE.mul_const A).const_mul 2
    have hsum := (ht₁.add ht₂).add hedges
    rw [add_zero, add_zero] at hsum
    exact hsum
  · filter_upwards [hEdge, hLat.eventually_ge_atTop 0] with k hk hL0 τ₀ τ hτ₀ hτ
    set L := goodHeight k / 2 with hL
    set G := Real.exp (A * τ₀) with hG
    have hG1 : 1 ≤ G := Real.one_le_exp (by positivity)
    have hG0 : 0 ≤ G := by linarith
    have hline₁ : ‖(∫ y : ℝ, inverseXiQuotient (timeNumerator R τ) ((y : ℂ) * I)) -
        ∫ y in (-L)..L, inverseXiQuotient (timeNumerator R τ) ((y : ℂ) * I)‖ ≤
        (∫ y, n₁ y) - ∫ y in (-L)..L, n₁ y := by
      refine norm_integral_sub_interval_le (integrable_time_right hD τ) hint₁ (fun y => ?_) hL0
      rw [inverseXiQuotient_timeNumerator, norm_mul, Complex.norm_exp]
      have hre : ((y : ℂ) * I * (τ : ℂ)).re = 0 := by simp
      rw [hre, Real.exp_zero, one_mul]
    have hline₂ : ‖(∫ y : ℝ, inverseXiQuotient (timeNumerator R τ) (((-A : ℝ) : ℂ) + (y : ℂ) * I)) -
        ∫ y in (-L)..L, inverseXiQuotient (timeNumerator R τ) (((-A : ℝ) : ℂ) + (y : ℂ) * I)‖ ≤
        G * ((∫ y, n₂ y) - ∫ y in (-L)..L, n₂ y) := by
      have hgn : Integrable fun y : ℝ => G * n₂ y := hint₂.const_mul G
      have hb := norm_integral_sub_interval_le (integrable_time_left hD τ) hgn (fun y => by
        rw [inverseXiQuotient_timeNumerator, norm_mul]
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
        exact norm_cexp_mul_le hAnn hτ₀ hτ (by simp) (by simp; linarith)) hL0
      rw [integral_const_mul, intervalIntegral.integral_const_mul, ← mul_sub] at hb
      exact hb
    have hEdge' : ∀ s : ℝ, |s| = L →
        ‖HIntegral (inverseXiQuotient (timeNumerator R τ)) (-A) 0 s‖ ≤ G * (E k * A) := by
      intro s hs
      rw [HIntegral]
      have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := -A) (b := 0)
        (f := fun q : ℝ => inverseXiQuotient (timeNumerator R τ) ((q : ℂ) + (s : ℂ) * I))
        (C := G * E k) (fun q hq => by
          rw [uIoc_of_le (by linarith)] at hq
          have hre : ((q : ℂ) + (s : ℂ) * I).re = q := by simp
          have him : ((q : ℂ) + (s : ℂ) * I).im = s := by simp
          rw [inverseXiQuotient_timeNumerator, norm_mul]
          exact mul_le_mul (norm_cexp_mul_le hAnn hτ₀ hτ (by rw [hre]; exact hq.1.le)
            (by rw [hre]; exact hq.2)) (hk _ (by rw [hre]; exact hq.1.le) (by rw [hre]; exact hq.2)
            (by rw [him]; exact hs)) (norm_nonneg _) hG0)
      refine hb.trans (le_of_eq ?_)
      rw [sub_neg_eq_add, zero_add, abs_of_nonneg hAnn]
      ring
    have hE₁ := hEdge' (-L) (by rw [abs_neg, abs_of_nonneg hL0])
    have hE₂ := hEdge' L (abs_of_nonneg hL0)
    rw [contourPartial_eq hA hD τ k, ← hL, contourField, contourRemainder]
    set H₁ := HIntegral (inverseXiQuotient (timeNumerator R τ)) (-A) 0 (-L)
    set H₂ := HIntegral (inverseXiQuotient (timeNumerator R τ)) (-A) 0 L
    set J₁ := ∫ y : ℝ, inverseXiQuotient (timeNumerator R τ) ((y : ℂ) * I)
    set J₂ := ∫ y : ℝ, inverseXiQuotient (timeNumerator R τ) (((-A : ℝ) : ℂ) + (y : ℂ) * I)
    set K₁ := ∫ y in (-L)..L, inverseXiQuotient (timeNumerator R τ) ((y : ℂ) * I)
    set K₂ := ∫ y in (-L)..L, inverseXiQuotient (timeNumerator R τ) (((-A : ℝ) : ℂ) + (y : ℂ) * I)
    have hsplit : J₁ - J₂ - ((H₁ - H₂) / I + K₁ - K₂) = (J₁ - K₁) - (J₂ - K₂) - (H₁ - H₂) / I := by
      ring
    have hIn : ‖(H₁ - H₂) / I‖ ≤ ‖H₁‖ + ‖H₂‖ := by
      rw [norm_div, Complex.norm_I, div_one]
      exact norm_sub_le _ _
    rw [hsplit]
    have hT1 : (∫ y, n₁ y) - ∫ y in (-L)..L, n₁ y ≥ 0 := (norm_nonneg _).trans hline₁
    calc ‖(J₁ - K₁) - (J₂ - K₂) - (H₁ - H₂) / I‖
        ≤ ‖J₁ - K₁‖ + ‖J₂ - K₂‖ + ‖(H₁ - H₂) / I‖ := by
          refine (norm_sub_le _ _).trans ?_
          gcongr
          exact norm_sub_le _ _
      _ ≤ ((∫ y, n₁ y) - ∫ y in (-L)..L, n₁ y) + G * ((∫ y, n₂ y) - ∫ y in (-L)..L, n₂ y) +
            (G * (E k * A) + G * (E k * A)) := by
          linarith
      _ ≤ G * (((∫ y, n₁ y) - ∫ y in (-L)..L, n₁ y) + ((∫ y, n₂ y) - ∫ y in (-L)..L, n₂ y) +
            2 * (E k * A)) := by
          nlinarith

/-- **The contour package.**  If the data hold at every depth, then there is `R` with
`R(τ) = O(e^{-Aτ})` for every `A ≥ 1`, and the partial sums converge to `𝓖 - R`, uniformly on `τ ≥ -τ₀`. -/
theorem contour_expansion {R : ℂ → ℂ} (hD : ∀ A : ℝ, 1 ≤ A → ContourData A R) :
    ∃ Rem : ℝ → ℂ, (∀ A : ℝ, 1 ≤ A → ∃ C : ℝ, 0 ≤ C ∧ ∀ τ : ℝ, ‖Rem τ‖ ≤ C * Real.exp (-A * τ)) ∧
      (∀ τ₀ : ℝ, 0 ≤ τ₀ → TendstoUniformlyOn (fun k τ => contourPartial R τ k)
        (fun τ => contourField R τ - Rem τ) atTop (Ici (-τ₀))) := by
  have hunif : ∀ (A : ℝ), 1 ≤ A → ∀ τ₀ : ℝ, 0 ≤ τ₀ →
      TendstoUniformlyOn (fun k τ => contourPartial R τ k)
        (fun τ => contourField R τ - contourRemainder A R τ) atTop (Ici (-τ₀)) := by
    intro A hA τ₀ hτ₀
    obtain ⟨B, hB, hbound⟩ := exists_contour_uniform_bound hA (hD A hA)
    rw [Metric.tendstoUniformlyOn_iff]
    intro δ hδ
    have hG : 0 < Real.exp (A * τ₀) := Real.exp_pos _
    have hB' : Tendsto (fun k => Real.exp (A * τ₀) * B k) atTop (𝓝 0) := by
      simpa using hB.const_mul (Real.exp (A * τ₀))
    filter_upwards [hbound, hB'.eventually (gt_mem_nhds hδ)] with k hk hBk τ hτ
    rw [dist_eq_norm]
    exact (hk τ₀ τ hτ₀ hτ).trans_lt hBk
  have hindep : ∀ (A : ℝ), 1 ≤ A → ∀ τ : ℝ, contourRemainder A R τ = contourRemainder 1 R τ := by
    intro A hA τ
    set τ₀ := |τ| with hτ₀
    have hτ : τ ∈ Ici (-τ₀) := neg_abs_le τ
    have h1 := (hunif A hA τ₀ (abs_nonneg τ)).tendsto_at hτ
    have h2 := (hunif 1 le_rfl τ₀ (abs_nonneg τ)).tendsto_at hτ
    exact sub_right_injective (tendsto_nhds_unique h1 h2)
  refine ⟨contourRemainder 1 R, fun A hA => ?_, fun τ₀ hτ₀ => hunif 1 le_rfl τ₀ hτ₀⟩
  refine ⟨∫ y : ℝ, ‖inverseXiQuotient R (((-A : ℝ) : ℂ) + (y : ℂ) * I)‖,
    integral_nonneg fun _ => norm_nonneg _, fun τ => ?_⟩
  rw [← hindep A hA τ]
  exact norm_contourRemainder_le A R τ

end GaloisForLFunctions.BlackHoleRingdown

end
