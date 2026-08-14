import GaloisForLFunctions.RHTower.RectIntegralEdges

/-!
# Fixed-contour weighted Littlewood identity

The moving-left-edge presentation of Littlewood's lemma is awkward in a proof assistant: a moving
edge crosses finitely many zero abscissae, and a `Finset ℝ` of abscissae cannot retain analytic
multiplicity or distinguish zeros with equal real part.

A single weighted contour avoids both defects.  Applying the argument principle with the analytic
weight `z ↦ z - c` gives the first horizontal moment of the zeros directly.  Expanding that fixed
contour edge by edge and differentiating only `log ‖f‖` gives the standard branch-free Littlewood
boundary formula.  Interior zeros are allowed; only the four boundary edges must be nonzero.
-/

open Complex MeasureTheory intervalIntegral

namespace RHTower

/-- Taking the imaginary part of an exact weighted argument-principle value extracts the real part
of the multiplicity-weighted zero sum, edge by edge. -/
theorem two_pi_mul_weighted_re_sum_eq_edges
    {F : ℂ → ℂ} {z₁ z₂ : ℂ} {Z : Finset ℂ} {m : ℂ → ℕ} {g : ℂ → ℂ}
    (hval : rectIntegral F z₁ z₂ =
      2 * Real.pi * I * ∑ w ∈ Z, ((m w : ℕ) : ℂ) * g w)
    (hbot : IntervalIntegrable (fun x : ℝ => F ((x : ℂ) + z₁.im * I)) volume z₁.re z₂.re)
    (htop : IntervalIntegrable (fun x : ℝ => F ((x : ℂ) + z₂.im * I)) volume z₁.re z₂.re)
    (hright : IntervalIntegrable (fun y : ℝ => F ((z₂.re : ℂ) + y * I)) volume z₁.im z₂.im)
    (hleft : IntervalIntegrable (fun y : ℝ => F ((z₁.re : ℂ) + y * I)) volume z₁.im z₂.im) :
    2 * Real.pi * (∑ w ∈ Z, (m w : ℝ) * (g w).re)
      = (∫ x in z₁.re..z₂.re, (F ((x : ℂ) + z₁.im * I)).im)
        - (∫ x in z₁.re..z₂.re, (F ((x : ℂ) + z₂.im * I)).im)
        + (∫ y in z₁.im..z₂.im, (F ((z₂.re : ℂ) + y * I)).re)
        - ∫ y in z₁.im..z₂.im, (F ((z₁.re : ℂ) + y * I)).re := by
  have hsum :
      (∑ w ∈ Z, ((m w : ℕ) : ℂ) * g w).re =
        ∑ w ∈ Z, (m w : ℝ) * (g w).re := by
    simp [Complex.mul_re]
  rw [← im_rectIntegral F z₁ z₂ hbot htop hright hleft, hval]
  simp [Complex.mul_im, hsum]

/-- Along a vertical line the derivative of `log ‖f‖` is the negative imaginary part of the
logarithmic derivative.  This is the vertical counterpart of
`hasDerivAt_log_norm_comp`, still without choosing a branch of complex logarithm. -/
theorem hasDerivAt_log_norm_vertical {f : ℂ → ℂ} {a t : ℝ}
    (hd : HasDerivAt f (deriv f ((a : ℂ) + t * I)) ((a : ℂ) + t * I))
    (hne : f ((a : ℂ) + t * I) ≠ 0) :
    HasDerivAt (fun u : ℝ => Real.log ‖f ((a : ℂ) + u * I)‖)
      (-(logDeriv f ((a : ℂ) + t * I)).im) t := by
  have hpath : HasDerivAt (fun u : ℝ => (a : ℂ) + u * I) I t := by
    have h := (hasDerivAt_const (x := t) (c := (a : ℂ))).add
      ((Complex.ofRealCLM.hasDerivAt (x := t)).mul_const I)
    have heq : (fun u : ℝ => (a : ℂ) + u * I) =ᶠ[nhds t]
        ((fun _ : ℝ => (a : ℂ)) + fun u : ℝ => (u : ℂ) * I) := by
      filter_upwards with u
      rfl
    have h' := h.congr_of_eventuallyEq heq
    simpa using h'
  have hcomp : HasDerivAt (fun u : ℝ => f ((a : ℂ) + u * I))
      (deriv f ((a : ℂ) + t * I) * I) t := by
    exact hd.comp t hpath
  have hlog := hasDerivAt_log_norm_comp hcomp hne
  convert hlog using 1
  rw [show deriv f ((a : ℂ) + t * I) * I / f ((a : ℂ) + t * I) =
      I * (deriv f ((a : ℂ) + t * I) / f ((a : ℂ) + t * I)) by
        field_simp]
  simp [logDeriv_apply, Complex.mul_re]

/-- Integration by parts on a vertical edge.  The endpoint terms exposed here are exactly those
cancelled by the unweighted horizontal real-part terms in the fixed-contour identity. -/
theorem integral_id_mul_neg_im_logDeriv_vertical
    {f : ℂ → ℂ} {a T₁ T₂ : ℝ}
    (hd : ∀ t ∈ Set.uIcc T₁ T₂,
      HasDerivAt f (deriv f ((a : ℂ) + t * I)) ((a : ℂ) + t * I))
    (hne : ∀ t ∈ Set.uIcc T₁ T₂, f ((a : ℂ) + t * I) ≠ 0)
    (hint : IntervalIntegrable
      (fun t : ℝ => -(logDeriv f ((a : ℂ) + t * I)).im) volume T₁ T₂) :
    (∫ t in T₁..T₂, t * (-(logDeriv f ((a : ℂ) + t * I)).im)) =
      T₂ * Real.log ‖f ((a : ℂ) + T₂ * I)‖
        - T₁ * Real.log ‖f ((a : ℂ) + T₁ * I)‖
        - ∫ t in T₁..T₂, Real.log ‖f ((a : ℂ) + t * I)‖ := by
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := fun t : ℝ => t) (v := fun t : ℝ => Real.log ‖f ((a : ℂ) + t * I)‖)
    (u' := fun _ : ℝ => 1)
    (v' := fun t : ℝ => -(logDeriv f ((a : ℂ) + t * I)).im)
    (fun t _ => hasDerivAt_id t)
    (fun t ht => hasDerivAt_log_norm_vertical (hd t ht) (hne t ht))
    intervalIntegrable_const hint
  simpa using hibp

/-- **Fixed-contour, branch-free Littlewood identity.**  An exact weighted argument-principle
value, continuity of the logarithmic derivative on the four edges, and boundary nonvanishing give
the analytic-multiplicity-weighted first horizontal zero moment.  Interior zeros are not excluded.
-/
theorem weighted_littlewood_from_rectIntegral
    {f : ℂ → ℂ} {c d T₁ T₂ : ℝ} {Z : Finset ℂ} {m : ℂ → ℕ}
    (hval : rectIntegral (fun z => (z - (c : ℂ)) * logDeriv f z)
        ((c : ℂ) + T₁ * I) ((d : ℂ) + T₂ * I) =
      2 * Real.pi * I * ∑ w ∈ Z, ((m w : ℕ) : ℂ) * (w - (c : ℂ)))
    (hqbot : ContinuousOn (fun x : ℝ => logDeriv f ((x : ℂ) + T₁ * I)) (Set.uIcc c d))
    (hqtop : ContinuousOn (fun x : ℝ => logDeriv f ((x : ℂ) + T₂ * I)) (Set.uIcc c d))
    (hqright : ContinuousOn (fun t : ℝ => logDeriv f ((d : ℂ) + t * I)) (Set.uIcc T₁ T₂))
    (hqleft : ContinuousOn (fun t : ℝ => logDeriv f ((c : ℂ) + t * I)) (Set.uIcc T₁ T₂))
    (hdbot : ∀ x ∈ Set.uIcc c d,
      HasDerivAt f (deriv f ((x : ℂ) + T₁ * I)) ((x : ℂ) + T₁ * I))
    (hdtop : ∀ x ∈ Set.uIcc c d,
      HasDerivAt f (deriv f ((x : ℂ) + T₂ * I)) ((x : ℂ) + T₂ * I))
    (hdright : ∀ t ∈ Set.uIcc T₁ T₂,
      HasDerivAt f (deriv f ((d : ℂ) + t * I)) ((d : ℂ) + t * I))
    (hdleft : ∀ t ∈ Set.uIcc T₁ T₂,
      HasDerivAt f (deriv f ((c : ℂ) + t * I)) ((c : ℂ) + t * I))
    (hnebot : ∀ x ∈ Set.uIcc c d, f ((x : ℂ) + T₁ * I) ≠ 0)
    (hnetop : ∀ x ∈ Set.uIcc c d, f ((x : ℂ) + T₂ * I) ≠ 0)
    (hneright : ∀ t ∈ Set.uIcc T₁ T₂, f ((d : ℂ) + t * I) ≠ 0)
    (hneleft : ∀ t ∈ Set.uIcc T₁ T₂, f ((c : ℂ) + t * I) ≠ 0) :
    2 * Real.pi * (∑ w ∈ Z, (m w : ℝ) * (w.re - c)) =
      (∫ t in T₁..T₂, Real.log ‖f ((c : ℂ) + t * I)‖)
        - (∫ t in T₁..T₂, Real.log ‖f ((d : ℂ) + t * I)‖)
        + (d - c) * (∫ t in T₁..T₂, (logDeriv f ((d : ℂ) + t * I)).re)
        + (∫ x in c..d, (x - c) * (logDeriv f ((x : ℂ) + T₁ * I)).im)
        - ∫ x in c..d, (x - c) * (logDeriv f ((x : ℂ) + T₂ * I)).im := by
  let F : ℂ → ℂ := fun z => (z - (c : ℂ)) * logDeriv f z
  have hqbotRe : IntervalIntegrable
      (fun x : ℝ => (logDeriv f ((x : ℂ) + T₁ * I)).re) volume c d := by
    exact (Complex.continuous_re.comp_continuousOn hqbot).intervalIntegrable
  have hqtopRe : IntervalIntegrable
      (fun x : ℝ => (logDeriv f ((x : ℂ) + T₂ * I)).re) volume c d := by
    exact (Complex.continuous_re.comp_continuousOn hqtop).intervalIntegrable
  have hqbotIm : IntervalIntegrable
      (fun x : ℝ => (logDeriv f ((x : ℂ) + T₁ * I)).im) volume c d := by
    exact (Complex.continuous_im.comp_continuousOn hqbot).intervalIntegrable
  have hqtopIm : IntervalIntegrable
      (fun x : ℝ => (logDeriv f ((x : ℂ) + T₂ * I)).im) volume c d := by
    exact (Complex.continuous_im.comp_continuousOn hqtop).intervalIntegrable
  have hqrightRe : IntervalIntegrable
      (fun t : ℝ => (logDeriv f ((d : ℂ) + t * I)).re) volume T₁ T₂ := by
    exact (Complex.continuous_re.comp_continuousOn hqright).intervalIntegrable
  have hqrightNegIm : IntervalIntegrable
      (fun t : ℝ => -(logDeriv f ((d : ℂ) + t * I)).im) volume T₁ T₂ := by
    exact (Complex.continuous_im.comp_continuousOn hqright).neg.intervalIntegrable
  have hqleftNegIm : IntervalIntegrable
      (fun t : ℝ => -(logDeriv f ((c : ℂ) + t * I)).im) volume T₁ T₂ := by
    exact (Complex.continuous_im.comp_continuousOn hqleft).neg.intervalIntegrable
  have hFbot : IntervalIntegrable
      (fun x : ℝ => F ((x : ℂ) + T₁ * I)) volume c d := by
    apply ContinuousOn.intervalIntegrable
    exact (by fun_prop : Continuous fun x : ℝ => ((x : ℂ) + T₁ * I - (c : ℂ))).continuousOn.mul hqbot
  have hFtop : IntervalIntegrable
      (fun x : ℝ => F ((x : ℂ) + T₂ * I)) volume c d := by
    apply ContinuousOn.intervalIntegrable
    exact (by fun_prop : Continuous fun x : ℝ => ((x : ℂ) + T₂ * I - (c : ℂ))).continuousOn.mul hqtop
  have hFright : IntervalIntegrable
      (fun t : ℝ => F ((d : ℂ) + t * I)) volume T₁ T₂ := by
    apply ContinuousOn.intervalIntegrable
    exact (by fun_prop : Continuous fun t : ℝ => ((d : ℂ) + t * I - (c : ℂ))).continuousOn.mul hqright
  have hFleft : IntervalIntegrable
      (fun t : ℝ => F ((c : ℂ) + t * I)) volume T₁ T₂ := by
    apply ContinuousOn.intervalIntegrable
    exact (by fun_prop : Continuous fun t : ℝ => ((c : ℂ) + t * I - (c : ℂ))).continuousOn.mul hqleft
  have hedge0 := two_pi_mul_weighted_re_sum_eq_edges
    (F := F) (z₁ := (c : ℂ) + T₁ * I) (z₂ := (d : ℂ) + T₂ * I)
    (Z := Z) (m := m) (g := fun z => z - (c : ℂ)) hval
      (by simpa using hFbot) (by simpa using hFtop)
      (by simpa using hFright) (by simpa using hFleft)
  have hedge :
      2 * Real.pi * (∑ w ∈ Z, (m w : ℝ) * (w.re - c)) =
        (∫ x in c..d, (F ((x : ℂ) + T₁ * I)).im)
          - (∫ x in c..d, (F ((x : ℂ) + T₂ * I)).im)
          + (∫ t in T₁..T₂, (F ((d : ℂ) + t * I)).re)
          - ∫ t in T₁..T₂, (F ((c : ℂ) + t * I)).re := by
    simpa [F] using hedge0
  have hbotFTC :
      (∫ x in c..d, (logDeriv f ((x : ℂ) + T₁ * I)).re) =
        Real.log ‖f ((d : ℂ) + T₁ * I)‖ - Real.log ‖f ((c : ℂ) + T₁ * I)‖ := by
    simpa [logDeriv_apply] using
      (integral_re_logDeriv_horizontal hdbot hnebot hqbotRe)
  have htopFTC :
      (∫ x in c..d, (logDeriv f ((x : ℂ) + T₂ * I)).re) =
        Real.log ‖f ((d : ℂ) + T₂ * I)‖ - Real.log ‖f ((c : ℂ) + T₂ * I)‖ := by
    simpa [logDeriv_apply] using
      (integral_re_logDeriv_horizontal hdtop hnetop hqtopRe)
  have hrightIBP := integral_id_mul_neg_im_logDeriv_vertical
    hdright hneright hqrightNegIm
  have hleftIBP := integral_id_mul_neg_im_logDeriv_vertical
    hdleft hneleft hqleftNegIm
  have hbotEdge :
      (∫ x in c..d, (F ((x : ℂ) + T₁ * I)).im) =
        (∫ x in c..d, (x - c) * (logDeriv f ((x : ℂ) + T₁ * I)).im)
          + T₁ * (Real.log ‖f ((d : ℂ) + T₁ * I)‖
            - Real.log ‖f ((c : ℂ) + T₁ * I)‖) := by
    calc
      _ = ∫ x in c..d, ((x - c) * (logDeriv f ((x : ℂ) + T₁ * I)).im
          + T₁ * (logDeriv f ((x : ℂ) + T₁ * I)).re) := by
        apply intervalIntegral.integral_congr
        intro x _
        simp [F, Complex.mul_im]
      _ = (∫ x in c..d, (x - c) * (logDeriv f ((x : ℂ) + T₁ * I)).im)
          + ∫ x in c..d, T₁ * (logDeriv f ((x : ℂ) + T₁ * I)).re := by
        rw [intervalIntegral.integral_add]
        · exact (((by fun_prop : Continuous fun x : ℝ => x - c).continuousOn.mul
            (Complex.continuous_im.comp_continuousOn hqbot))).intervalIntegrable
        · exact hqbotRe.const_mul T₁
      _ = _ := by rw [intervalIntegral.integral_const_mul, hbotFTC]
  have htopEdge :
      (∫ x in c..d, (F ((x : ℂ) + T₂ * I)).im) =
        (∫ x in c..d, (x - c) * (logDeriv f ((x : ℂ) + T₂ * I)).im)
          + T₂ * (Real.log ‖f ((d : ℂ) + T₂ * I)‖
            - Real.log ‖f ((c : ℂ) + T₂ * I)‖) := by
    calc
      _ = ∫ x in c..d, ((x - c) * (logDeriv f ((x : ℂ) + T₂ * I)).im
          + T₂ * (logDeriv f ((x : ℂ) + T₂ * I)).re) := by
        apply intervalIntegral.integral_congr
        intro x _
        simp [F, Complex.mul_im]
      _ = (∫ x in c..d, (x - c) * (logDeriv f ((x : ℂ) + T₂ * I)).im)
          + ∫ x in c..d, T₂ * (logDeriv f ((x : ℂ) + T₂ * I)).re := by
        rw [intervalIntegral.integral_add]
        · exact (((by fun_prop : Continuous fun x : ℝ => x - c).continuousOn.mul
            (Complex.continuous_im.comp_continuousOn hqtop))).intervalIntegrable
        · exact hqtopRe.const_mul T₂
      _ = _ := by rw [intervalIntegral.integral_const_mul, htopFTC]
  have hrightEdge :
      (∫ t in T₁..T₂, (F ((d : ℂ) + t * I)).re) =
        (d - c) * (∫ t in T₁..T₂, (logDeriv f ((d : ℂ) + t * I)).re)
          + (T₂ * Real.log ‖f ((d : ℂ) + T₂ * I)‖
            - T₁ * Real.log ‖f ((d : ℂ) + T₁ * I)‖
            - ∫ t in T₁..T₂, Real.log ‖f ((d : ℂ) + t * I)‖) := by
    calc
      _ = ∫ t in T₁..T₂, ((d - c) * (logDeriv f ((d : ℂ) + t * I)).re
          + t * (-(logDeriv f ((d : ℂ) + t * I)).im)) := by
        apply intervalIntegral.integral_congr
        intro t _
        simp [F, Complex.mul_re]
        ring
      _ = (∫ t in T₁..T₂, (d - c) * (logDeriv f ((d : ℂ) + t * I)).re)
          + ∫ t in T₁..T₂, t * (-(logDeriv f ((d : ℂ) + t * I)).im) := by
        rw [intervalIntegral.integral_add]
        · exact hqrightRe.const_mul (d - c)
        · exact (((by fun_prop : Continuous fun t : ℝ => t).continuousOn.mul
            (Complex.continuous_im.comp_continuousOn hqright).neg)).intervalIntegrable
      _ = _ := by
        rw [intervalIntegral.integral_const_mul, hrightIBP]
  have hleftEdge :
      (∫ t in T₁..T₂, (F ((c : ℂ) + t * I)).re) =
        T₂ * Real.log ‖f ((c : ℂ) + T₂ * I)‖
          - T₁ * Real.log ‖f ((c : ℂ) + T₁ * I)‖
          - ∫ t in T₁..T₂, Real.log ‖f ((c : ℂ) + t * I)‖ := by
    calc
      _ = ∫ t in T₁..T₂, t * (-(logDeriv f ((c : ℂ) + t * I)).im) := by
        apply intervalIntegral.integral_congr
        intro t _
        simp [F, Complex.mul_re]
      _ = _ := hleftIBP
  rw [hbotEdge, htopEdge, hrightEdge, hleftEdge] at hedge
  linear_combination hedge

/-- A first horizontal moment controls every right-hand weighted count.  This is the fixed-packet
replacement for the layer-cake count step: analytic multiplicities stay attached to their zeros,
and coincident abscissae cause no loss. -/
theorem weighted_count_mul_le_firstMoment
    {α : Type*} [DecidableEq α] (Z : Finset α) (m : α → ℕ) (β : α → ℝ)
    {c σ : ℝ} (hleft : ∀ z ∈ Z, c ≤ β z) :
    (σ - c) * (∑ z ∈ Z.filter fun z => σ ≤ β z, (m z : ℝ)) ≤
      ∑ z ∈ Z, (m z : ℝ) * (β z - c) := by
  calc
    _ = ∑ z ∈ Z.filter (fun z => σ ≤ β z), (σ - c) * (m z : ℝ) := by
      rw [Finset.mul_sum]
    _ ≤ ∑ z ∈ Z.filter (fun z => σ ≤ β z), (m z : ℝ) * (β z - c) := by
      apply Finset.sum_le_sum
      intro z hz
      have hzσ : σ ≤ β z := (Finset.mem_filter.mp hz).2
      rw [mul_comm (σ - c)]
      exact mul_le_mul_of_nonneg_left (sub_le_sub_right hzσ c) (Nat.cast_nonneg _)
    _ ≤ _ := by
      refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_
      intro z hzZ _
      exact mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr (hleft z hzZ))

end RHTower
