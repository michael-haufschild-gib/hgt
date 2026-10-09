import GaloisForLFunctions.RHTower.CircleArgumentPhaseRelativeIndex

/-!
# Reflection dominance from a positive horizontal logarithmic derivative

Let `F` be holomorphic and zero-free on `Re s > 0`, with real structure `F(s̄) = conj F(s)`.
Suppose `Re (F'/F)(s) > 0` on `{Re s > 0, |Im s| ≥ T₀}`.  Then, at every height `|t| ≥ T₀`:

* `σ ↦ |F(σ+it)|` is strictly increasing on `(0, ∞)`, because
  `d/dσ |F(σ+it)|² = 2 |F|² Re(F'/F)`;
* `|F(1-s)| = |F(1-σ+it)| < |F(s)|` for `½ < σ < 1`, by the real structure;
* the reflection `R(s) = F(s) + F(1-s)`, which satisfies `R(1-s) = R(s)`, has no zero with
  `0 < Re s < 1`, `Re s ≠ ½`;
* on `Re s = ½`, `R = 2 Re F` and `R' = 2i Im F' = 2i Re(F'/F) Im F`, so every zero is simple;
* every Hardy boundary-phase pair of `R` on a disc in `{½ < Re s < 1, |Im s| ≥ T₀}` has relative
  index and cubic trace zero.

This is the Hermite–Biehler mechanism read through the Gohberg–Krein index of the boundary phase.
-/

open Complex Filter Topology Set MeasureTheory Metric

namespace RHTower

noncomputable section

namespace ReflectionDominance

variable {F : ℂ → ℂ}

/-- Horizontal derivative of `σ ↦ ‖F(σ+it)‖²`. -/
theorem hasDerivAt_normSq_horizontal (hd : ∀ s : ℂ, 0 < s.re → DifferentiableAt ℂ F s)
    (hne : ∀ s : ℂ, 0 < s.re → F s ≠ 0) {σ t : ℝ} (hσ : 0 < σ) :
    HasDerivAt (fun u : ℝ => ‖F ((u : ℂ) + t * I)‖ ^ 2)
      (2 * ‖F ((σ : ℂ) + t * I)‖ ^ 2 * (logDeriv F ((σ : ℂ) + t * I)).re) σ := by
  set s : ℂ := (σ : ℂ) + t * I with hsdef
  have hsre : 0 < s.re := by simp [hsdef, hσ]
  have hdF : HasDerivAt F (deriv F s) s := (hd s hsre).hasDerivAt
  have hc : HasDerivAt (fun u : ℝ => F ((u : ℂ) + t * I)) (deriv F s) σ := by
    have h1 : HasDerivAt (fun w : ℂ => F (w + t * I)) (deriv F s) (σ : ℂ) :=
      HasDerivAt.comp_add_const (σ : ℂ) ((t : ℂ) * I) hdF
    exact h1.comp_ofReal
  have hn := hc.norm_sq
  have hF0 := hne s hsre
  convert hn using 1
  rw [Complex.inner, logDeriv_apply]
  set A := F s
  set D := deriv F s
  have hD : D = (D / A) * A := by field_simp
  conv_rhs => rw [hD]
  rw [mul_assoc (D / A) A, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.re_mul_ofReal]
  ring

/-- **Horizontal monotonicity.** -/
theorem strictMonoOn_norm_horizontal (hd : ∀ s : ℂ, 0 < s.re → DifferentiableAt ℂ F s)
    (hne : ∀ s : ℂ, 0 < s.re → F s ≠ 0) {T₀ : ℝ}
    (hpos : ∀ s : ℂ, 0 < s.re → T₀ ≤ |s.im| → 0 < (logDeriv F s).re) {t : ℝ}
    (ht : T₀ ≤ |t|) :
    StrictMonoOn (fun u : ℝ => ‖F ((u : ℂ) + t * I)‖) (Ioi 0) := by
  have hsq : StrictMonoOn (fun u : ℝ => ‖F ((u : ℂ) + t * I)‖ ^ 2) (Ioi 0) := by
    apply strictMonoOn_of_deriv_pos (convex_Ioi 0)
    · intro u hu
      exact (hasDerivAt_normSq_horizontal hd hne (t := t) hu).continuousAt.continuousWithinAt
    · intro u hu
      rw [interior_Ioi] at hu
      have hu0 : (0 : ℝ) < u := hu
      rw [(hasDerivAt_normSq_horizontal hd hne (t := t) hu0).deriv]
      have hsre : 0 < ((u : ℂ) + t * I).re := by simp [hu0]
      have him : ((u : ℂ) + t * I).im = t := by simp
      have hp := hpos _ hsre (by rw [him]; exact ht)
      have hn : 0 < ‖F ((u : ℂ) + t * I)‖ := norm_pos_iff.2 (hne _ hsre)
      positivity
  intro a ha b hb hab
  exact lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) (hsq ha hb hab)

/-- The reflected function `F(s) + F(1 - s)`. -/
def reflected (F : ℂ → ℂ) (s : ℂ) : ℂ := F s + F (1 - s)

theorem reflected_one_sub (F : ℂ → ℂ) (s : ℂ) : reflected F (1 - s) = reflected F s := by
  rw [reflected, reflected, sub_sub_cancel, add_comm]

/-- Reflection across `Re s = ½` preserves the modulus at fixed height. -/
theorem norm_one_sub (hconj : ∀ s : ℂ, F ((starRingEnd ℂ) s) = (starRingEnd ℂ) (F s)) (s : ℂ) :
    ‖F (1 - s)‖ = ‖F (((1 - s.re : ℝ) : ℂ) + s.im * I)‖ := by
  have hw : 1 - s = (starRingEnd ℂ) (((1 - s.re : ℝ) : ℂ) + s.im * I) := by
    apply Complex.ext <;> simp
  rw [hw, hconj, Complex.norm_conj]

/-- Strict dominance over the reflection right of the critical line. -/
theorem norm_one_sub_lt (hd : ∀ s : ℂ, 0 < s.re → DifferentiableAt ℂ F s)
    (hne : ∀ s : ℂ, 0 < s.re → F s ≠ 0)
    (hconj : ∀ s : ℂ, F ((starRingEnd ℂ) s) = (starRingEnd ℂ) (F s)) {T₀ : ℝ}
    (hpos : ∀ s : ℂ, 0 < s.re → T₀ ≤ |s.im| → 0 < (logDeriv F s).re) {s : ℂ}
    (h1 : 1 / 2 < s.re) (h2 : s.re < 1) (ht : T₀ ≤ |s.im|) :
    ‖F (1 - s)‖ < ‖F s‖ := by
  rw [norm_one_sub hconj]
  have hmono := strictMonoOn_norm_horizontal hd hne hpos ht
  have hs : (s.re : ℂ) + s.im * I = s := Complex.re_add_im s
  have h := hmono (show (0 : ℝ) < 1 - s.re by linarith) (show (0 : ℝ) < s.re by linarith)
    (show 1 - s.re < s.re by linarith)
  simpa only [hs] using h

/-- **Reflection RH.**  The reflection has no zero in the critical strip off `Re s = ½` at height
`|Im s| ≥ T₀`. -/
theorem reflected_ne_zero (hd : ∀ s : ℂ, 0 < s.re → DifferentiableAt ℂ F s)
    (hne : ∀ s : ℂ, 0 < s.re → F s ≠ 0)
    (hconj : ∀ s : ℂ, F ((starRingEnd ℂ) s) = (starRingEnd ℂ) (F s)) {T₀ : ℝ}
    (hpos : ∀ s : ℂ, 0 < s.re → T₀ ≤ |s.im| → 0 < (logDeriv F s).re) {s : ℂ}
    (h0 : 0 < s.re) (h1 : s.re < 1) (hhalf : s.re ≠ 1 / 2) (ht : T₀ ≤ |s.im|) :
    reflected F s ≠ 0 := by
  have key : ∀ w : ℂ, 1 / 2 < w.re → w.re < 1 → T₀ ≤ |w.im| → F w + F (1 - w) ≠ 0 := by
    intro w hw1 hw2 hwt hz
    have hlt := norm_one_sub_lt hd hne hconj hpos hw1 hw2 hwt
    rw [add_eq_zero_iff_eq_neg] at hz
    rw [hz, norm_neg] at hlt
    exact lt_irrefl _ hlt
  rcases lt_or_gt_of_ne hhalf with hlt | hgt
  · have h := key (1 - s) (by simp; linarith) (by simp; linarith) (by simpa using ht)
    rw [sub_sub_cancel, add_comm] at h
    exact h
  · exact key s hgt h1 ht

/-- The real structure transfers to the derivative. -/
theorem deriv_conj (hconj : ∀ s : ℂ, F ((starRingEnd ℂ) s) = (starRingEnd ℂ) (F s)) (s : ℂ) :
    deriv F ((starRingEnd ℂ) s) = (starRingEnd ℂ) (deriv F s) := by
  have hfun : F = (starRingEnd ℂ) ∘ F ∘ (starRingEnd ℂ) := by
    funext w
    simp [Function.comp_def, hconj]
  have h := congrFun (deriv_conj_conj (f := F)) ((starRingEnd ℂ) s)
  rw [← hfun] at h
  simpa [Function.comp_def] using h

/-- The reflection is holomorphic on the open critical strip. -/
theorem differentiableAt_reflected (hd : ∀ s : ℂ, 0 < s.re → DifferentiableAt ℂ F s) {s : ℂ}
    (h0 : 0 < s.re) (h1 : s.re < 1) : DifferentiableAt ℂ (reflected F) s := by
  have h1' : 0 < (1 - s).re := by simp; linarith
  have hb : DifferentiableAt ℂ (fun w : ℂ => F (1 - w)) s :=
    (hd _ h1').comp s (differentiableAt_const _ |>.sub differentiableAt_id)
  exact (hd s h0).add hb

/-- **Simple critical-line zeros.**  At a zero `½ + it`, `|t| ≥ T₀`, of the reflection,
`R'(½+it) = 2i Im F'(½+it) = 2i Re(F'/F) Im F(½+it) ≠ 0`. -/
theorem deriv_reflected_ne_zero_of_line (hd : ∀ s : ℂ, 0 < s.re → DifferentiableAt ℂ F s)
    (hne : ∀ s : ℂ, 0 < s.re → F s ≠ 0)
    (hconj : ∀ s : ℂ, F ((starRingEnd ℂ) s) = (starRingEnd ℂ) (F s)) {T₀ : ℝ}
    (hpos : ∀ s : ℂ, 0 < s.re → T₀ ≤ |s.im| → 0 < (logDeriv F s).re) {t : ℝ}
    (ht : T₀ ≤ |t|) (hz : reflected F (1 / 2 + t * I) = 0) :
    deriv (reflected F) (1 / 2 + t * I) ≠ 0 := by
  set s : ℂ := 1 / 2 + t * I with hsdef
  have hsim : s.im = t := by simp [hsdef]
  have hconjs : 1 - s = (starRingEnd ℂ) s := by
    apply Complex.ext <;> (simp [hsdef]; try norm_num)
  have hs0 : 0 < s.re := by simp [hsdef]
  have h1s : 0 < (1 - s).re := by rw [hconjs]; simpa using hs0
  have hdF : HasDerivAt F (deriv F s) s := (hd s hs0).hasDerivAt
  have hdF' : HasDerivAt F (deriv F (1 - s)) (1 - s) := (hd _ h1s).hasDerivAt
  have hinner : HasDerivAt (fun w : ℂ => 1 - w) (-1) s := by
    simpa using (hasDerivAt_id s).const_sub (1 : ℂ)
  have hR : HasDerivAt (reflected F) (deriv F s + deriv F (1 - s) * (-1)) s :=
    hdF.add (hdF'.comp s hinner)
  rw [hR.deriv, hconjs, deriv_conj hconj]
  have hzF : F s + (starRingEnd ℂ) (F s) = 0 := by
    have := hz
    rw [reflected, hconjs, hconj] at this
    exact this
  have hreF : (F s).re = 0 := by
    have := congrArg Complex.re hzF
    simp at this
    linarith
  have hF0 : F s ≠ 0 := hne s hs0
  have himF : (F s).im ≠ 0 := by
    intro him
    exact hF0 (Complex.ext (by simpa using hreF) (by simpa using him))
  have hL := hpos s hs0 (by rw [hsim]; exact ht)
  have hderiv : deriv F s = logDeriv F s * F s := by
    rw [logDeriv_apply]; field_simp
  intro h0
  have him0 : (deriv F s + (starRingEnd ℂ) (deriv F s) * (-1)).im = 0 := by rw [h0]; simp
  have him1 : (deriv F s).im = 0 := by
    simp at him0
    linarith
  rw [hderiv, Complex.mul_im, hreF, mul_zero, add_zero] at him1
  rcases mul_eq_zero.1 him1 with h | h
  · exact (ne_of_gt hL) h
  · exact himF h

/-! ## Height-local form: only the horizontal segment between `s` and its reflection matters -/

/-- Strict horizontal growth from positivity of `Re (F'/F)` on an open horizontal segment. -/
theorem norm_lt_of_segment (hd : ∀ s : ℂ, 0 < s.re → DifferentiableAt ℂ F s)
    (hne : ∀ s : ℂ, 0 < s.re → F s ≠ 0) {a b t : ℝ} (ha : 0 < a) (hab : a < b)
    (hseg : ∀ u : ℝ, a < u → u < b → 0 < (logDeriv F ((u : ℂ) + t * I)).re) :
    ‖F ((a : ℂ) + t * I)‖ < ‖F ((b : ℂ) + t * I)‖ := by
  have hsq : StrictMonoOn (fun u : ℝ => ‖F ((u : ℂ) + t * I)‖ ^ 2) (Icc a b) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
    · intro u hu
      have hu0 : 0 < u := by linarith [hu.1]
      exact (hasDerivAt_normSq_horizontal hd hne (t := t) hu0).continuousAt.continuousWithinAt
    · intro u hu
      rw [interior_Icc] at hu
      have hu0 : 0 < u := by linarith [hu.1]
      rw [(hasDerivAt_normSq_horizontal hd hne (t := t) hu0).deriv]
      have hsre : 0 < ((u : ℂ) + t * I).re := by simp [hu0]
      have hp := hseg u hu.1 hu.2
      have hn : 0 < ‖F ((u : ℂ) + t * I)‖ := norm_pos_iff.2 (hne _ hsre)
      positivity
  exact lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _)
    (hsq (left_mem_Icc.2 hab.le) (right_mem_Icc.2 hab.le) hab)

/-- **Resonance localization.**  An off-line zero `s` of the reflection in the critical strip
forces a point of the open horizontal segment between `s` and `1 - s̄` where `Re (F'/F) ≤ 0`. -/
theorem exists_segment_re_logDeriv_nonpos_of_reflected_eq_zero
    (hd : ∀ s : ℂ, 0 < s.re → DifferentiableAt ℂ F s) (hne : ∀ s : ℂ, 0 < s.re → F s ≠ 0)
    (hconj : ∀ s : ℂ, F ((starRingEnd ℂ) s) = (starRingEnd ℂ) (F s)) {s : ℂ}
    (h0 : 0 < s.re) (h1 : s.re < 1) (hhalf : s.re ≠ 1 / 2) (hz : reflected F s = 0) :
    ∃ u : ℝ, min s.re (1 - s.re) < u ∧ u < max s.re (1 - s.re) ∧
      (logDeriv F ((u : ℂ) + s.im * I)).re ≤ 0 := by
  by_contra hcon
  push Not at hcon
  have hs : (s.re : ℂ) + s.im * I = s := Complex.re_add_im s
  have hrefl := norm_one_sub hconj s
  rw [reflected, add_eq_zero_iff_eq_neg] at hz
  have hnorm : ‖F s‖ = ‖F (1 - s)‖ := by rw [hz, norm_neg]
  rcases lt_or_gt_of_ne hhalf with hlt | hgt
  · have h := norm_lt_of_segment hd hne (t := s.im) h0 (show s.re < 1 - s.re by linarith)
      (fun u hu1 hu2 => hcon u (by rw [min_eq_left (by linarith)]; exact hu1)
        (by rw [max_eq_right (by linarith)]; exact hu2))
    rw [hs, ← hrefl] at h
    exact lt_irrefl _ (hnorm ▸ h)
  · have h := norm_lt_of_segment hd hne (t := s.im) (show 0 < 1 - s.re by linarith)
      (show 1 - s.re < s.re by linarith)
      (fun u hu1 hu2 => hcon u (by rw [min_eq_right (by linarith)]; exact hu1)
        (by rw [max_eq_left (by linarith)]; exact hu2))
    rw [hs, ← hrefl] at h
    exact lt_irrefl _ (hnorm ▸ h)

/-- Right half of the critical strip above `T₀`. -/
def dominanceRegion (T₀ : ℝ) : Set ℂ := {w | 1 / 2 < w.re ∧ w.re < 1 ∧ T₀ ≤ |w.im|}

/-- **TG sub-unit gate for the reflection.**  Every Hardy boundary-phase pair of the reflection on a
disc in the right half-strip above `T₀` has vanishing relative index and cubic trace. -/
theorem reflected_relativeIndex_eq_zero (hd : ∀ s : ℂ, 0 < s.re → DifferentiableAt ℂ F s)
    (hne : ∀ s : ℂ, 0 < s.re → F s ≠ 0)
    (hconj : ∀ s : ℂ, F ((starRingEnd ℂ) s) = (starRingEnd ℂ) (F s)) {T₀ : ℝ}
    (hpos : ∀ s : ℂ, 0 < s.re → T₀ ≤ |s.im| → 0 < (logDeriv F s).re)
    (D : DiscArgumentDatum) (hF : D.F = reflected F) (hball : ball D.c D.t ⊆ dominanceRegion T₀) :
    restrictedProjectionRelativeIndex D.circlePhase.datum.conjugateProjection
        D.circlePhase.datum.projection = 0 ∧
      ContinuousLinearMap.opTrace (restrictedProjectionCubicDefect
        D.circlePhase.datum.conjugateProjection D.circlePhase.datum.projection) = 0 := by
  have hZempty : ∀ Z : Finset ℂ, (∀ ρ ∈ Z, ρ ∈ ball D.c D.t) →
      (∀ z ∈ ball D.c D.t, D.F z = 0 ↔ z ∈ Z) → Z = ∅ := by
    intro Z hZball hZzero
    apply Finset.eq_empty_of_forall_notMem
    intro ρ hρ
    have hρb := hZball ρ hρ
    have hzero := (hZzero ρ hρb).2 hρ
    obtain ⟨hre, hre1, him⟩ := hball hρb
    rw [hF] at hzero
    exact reflected_ne_zero hd hne hconj hpos (by linarith) hre1 (ne_of_gt hre) him hzero
  refine ⟨?_, ?_⟩
  · obtain ⟨Z, hZball, hZzero, hidx⟩ := D.relativeIndex_eq_zeroCount
    rw [hidx, hZempty Z hZball hZzero, Finset.sum_empty]
  · obtain ⟨Z, hZball, hZzero, htr⟩ := D.opTrace_cubicDefect_eq_zeroCount
    rw [htr, hZempty Z hZball hZzero, Finset.sum_empty]

/-- Every closed disc in the right half-strip above `T₀` carries a boundary-phase datum of the
reflection with vanishing Hardy relative index. -/
theorem exists_reflectedDiscDatum (hd : ∀ s : ℂ, 0 < s.re → DifferentiableAt ℂ F s)
    (hne : ∀ s : ℂ, 0 < s.re → F s ≠ 0)
    (hconj : ∀ s : ℂ, F ((starRingEnd ℂ) s) = (starRingEnd ℂ) (F s)) {T₀ : ℝ}
    (hpos : ∀ s : ℂ, 0 < s.re → T₀ ≤ |s.im| → 0 < (logDeriv F s).re) {c : ℂ} {r : ℝ}
    (hr : 0 < r) (hball : closedBall c r ⊆ dominanceRegion T₀) :
    ∃ D : DiscArgumentDatum, D.F = reflected F ∧ D.c = c ∧ D.t = r ∧
      restrictedProjectionRelativeIndex D.circlePhase.datum.conjugateProjection
        D.circlePhase.datum.projection = 0 := by
  have hcl : c.re - r > 1 / 2 ∧ c.re + r < 1 := by
    have h1 := (hball (show c - r ∈ closedBall c r by simp [abs_of_pos hr])).1
    have h2 := (hball (show c + r ∈ closedBall c r by simp [abs_of_pos hr])).2.1
    simp at h1 h2
    exact ⟨by linarith, h2⟩
  set δ : ℝ := min (c.re - r - 1 / 2) (1 - c.re - r) / 2 with hδ
  have hmin : 0 < min (c.re - r - 1 / 2) (1 - c.re - r) :=
    lt_min (by linarith [hcl.1]) (by linarith [hcl.2])
  have hδpos : 0 < δ := by rw [hδ]; positivity
  set U : Set ℂ := {w | 0 < w.re ∧ w.re < 1}
  have hUopen : IsOpen U :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)
  have hsub : closedBall c (r + δ) ⊆ U := by
    intro w hw
    have hd' : ‖w - c‖ ≤ r + δ := by simpa [dist_eq_norm] using hw
    have hre : |w.re - c.re| ≤ r + δ := by
      have := Complex.abs_re_le_norm (w - c)
      simp at this
      linarith
    have hδ1 : δ < c.re - r - 1 / 2 := by
      have := min_le_left (c.re - r - 1 / 2) (1 - c.re - r); rw [hδ]; linarith
    have hδ2 : δ < 1 - c.re - r := by
      have := min_le_right (c.re - r - 1 / 2) (1 - c.re - r); rw [hδ]; linarith
    constructor
    · linarith [neg_abs_le (w.re - c.re)]
    · linarith [le_abs_self (w.re - c.re)]
  have hdiff : DifferentiableOn ℂ (reflected F) U := fun w hw =>
    (differentiableAt_reflected hd hw.1 hw.2).differentiableWithinAt
  have hne' : ∀ ζ ∈ sphere c r, reflected F ζ ≠ 0 := by
    intro ζ hζ
    obtain ⟨hre, hre1, him⟩ := hball (sphere_subset_closedBall hζ)
    exact reflected_ne_zero hd hne hconj hpos (by linarith) hre1 (ne_of_gt hre) him
  let D : DiscArgumentDatum :=
    { c := c, t := r, R := r + δ, U := U, F := reflected F,
      t_pos := hr, t_lt_R := by linarith, isOpen := hUopen, closedBall_subset := hsub,
      differentiableOn := hdiff, ne_zero := hne' }
  exact ⟨D, rfl, rfl, rfl, (reflected_relativeIndex_eq_zero hd hne hconj hpos D rfl
    (ball_subset_closedBall.trans hball)).1⟩

end ReflectionDominance

end

end RHTower
