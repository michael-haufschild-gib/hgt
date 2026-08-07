import Mathlib

/-!
# The half-log Cesàro average and its derivative

For a profile `F` on the half-line write

`Y(L) = ∫_0^L F`,  `P F(L) = 2L F(L) − Y(L)`,  `A(L) = Y(L) / (2√L)`.

The average `A` is normalised so that a profile `F ~ β/√L` gives `Y ~ 2β√L` and hence `A → β`, the
same limit as the half-log trace `H(L) = √L F(L)`.  Differentiating `A` produces the operator `P`
divided by a pure power:

`A'(L) = P F(L) / (4 L^{3/2})`.

So the source equation controls `A'`, an integrable quantity against `L^{-3/2}`, and convergence of
`A` follows.  This is the mechanism that produces the averaged trace.
-/

open MeasureTheory intervalIntegral

namespace GaloisForLFunctions.HTGeometry

/-- The primitive of a profile on the half-line. -/
noncomputable def halfLinePrimitive (F : ℝ → ℝ) (L : ℝ) : ℝ := ∫ x in (0 : ℝ)..L, F x

/-- The logarithmic Dirichlet operator `P F(L) = 2L F(L) − Y(L)`. -/
noncomputable def logDirichlet (F : ℝ → ℝ) (L : ℝ) : ℝ :=
  2 * L * F L - halfLinePrimitive F L

/-- The half-log Cesàro average `A(L) = Y(L)/(2√L)`. -/
noncomputable def halfLogAverage (F : ℝ → ℝ) (L : ℝ) : ℝ :=
  halfLinePrimitive F L / (2 * Real.sqrt L)

/-- The primitive differentiates to the profile. -/
theorem hasDerivAt_halfLinePrimitive {F : ℝ → ℝ} (hF : Continuous F) (L : ℝ) :
    HasDerivAt (halfLinePrimitive F) (F L) L :=
  intervalIntegral.integral_hasDerivAt_right (hF.intervalIntegrable _ _)
    (hF.stronglyMeasurableAtFilter _ _) hF.continuousAt

/-- **The derivative of the half-log average.**  Differentiating `Y/(2√L)` produces exactly the
logarithmic Dirichlet operator over `4L^{3/2}`. -/
theorem hasDerivAt_halfLogAverage {F : ℝ → ℝ} (hF : Continuous F) {L : ℝ} (hL : 0 < L) :
    HasDerivAt (halfLogAverage F)
      (logDirichlet F L / (4 * L * Real.sqrt L)) L := by
  have hsqrt : 0 < Real.sqrt L := Real.sqrt_pos.mpr hL
  have hY : HasDerivAt (halfLinePrimitive F) (F L) L := hasDerivAt_halfLinePrimitive hF L
  have hs : HasDerivAt (fun t : ℝ => Real.sqrt t) (1 / (2 * Real.sqrt L)) L :=
    Real.hasDerivAt_sqrt (ne_of_gt hL)
  have hden : HasDerivAt (fun t : ℝ => 2 * Real.sqrt t) (2 * (1 / (2 * Real.sqrt L))) L :=
    hs.const_mul 2
  have hne : 2 * Real.sqrt L ≠ 0 := by positivity
  have hdiv := hY.div hden hne
  have hval : (F L * (2 * Real.sqrt L) -
      halfLinePrimitive F L * (2 * (1 / (2 * Real.sqrt L)))) / (2 * Real.sqrt L) ^ 2
      = logDirichlet F L / (4 * L * Real.sqrt L) := by
    unfold logDirichlet
    have hsq2 : Real.sqrt L ^ 2 = L := Real.sq_sqrt hL.le
    field_simp
    linear_combination 4 * halfLinePrimitive F L * hsq2
  rwa [hval] at hdiv

/-- The average is the primitive against the half-log weight. -/
theorem halfLogAverage_eq {F : ℝ → ℝ} (L : ℝ) :
    halfLogAverage F L = halfLinePrimitive F L / (2 * Real.sqrt L) := rfl

/-! ## The average is a genuine average of the half-log trace

Writing `F(t) = H(t) t^{-1/2}` exhibits `Y(L)` as the pairing of `H` against the weight `t^{-1/2}`,
whose mass on `[0,L]` is exactly `2√L`.  So `A(L)` is a probability-weighted average of `H`, and
any pointwise bound on `H` passes to `A`.  This is what forces the limit of `A` to lie between the
lower and upper limits of `H`.
-/

/-- The mass of the half-log weight on `[0,L]` is `2√L`. -/
theorem integral_rpow_neg_half (L : ℝ) :
    (∫ t in (0 : ℝ)..L, t ^ (-(1 : ℝ) / 2)) = 2 * Real.sqrt L := by
  rw [integral_rpow (Or.inl (by norm_num))]
  have hexp : -(1 : ℝ) / 2 + 1 = 1 / 2 := by ring
  rw [hexp, Real.zero_rpow (by norm_num), ← Real.sqrt_eq_rpow]
  ring

/-- **A pointwise upper bound on the half-log trace passes to the average.** -/
theorem halfLogAverage_le {F : ℝ → ℝ} (hF : Continuous F) {L c : ℝ} (hL : 0 < L)
    (hH : ∀ t ∈ Set.Ioc (0 : ℝ) L, Real.sqrt t * F t ≤ c) :
    halfLogAverage F L ≤ c := by
  have hsqrt : 0 < Real.sqrt L := Real.sqrt_pos.mpr hL
  have hwint : IntervalIntegrable (fun t : ℝ => c * t ^ (-(1 : ℝ) / 2)) volume 0 L := by
    refine IntervalIntegrable.const_mul ?_ c
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hL.le]
    rw [intervalIntegral.integrableOn_Ioo_rpow_iff hL]
    norm_num
  have hmono : (∫ t in (0 : ℝ)..L, F t) ≤ ∫ t in (0 : ℝ)..L, c * t ^ (-(1 : ℝ) / 2) := by
    refine intervalIntegral.integral_mono_ae_restrict hL.le
      (hF.intervalIntegrable _ _) hwint ?_
    have hnull : ∀ᵐ t : ℝ, t ≠ 0 := by
      rw [MeasureTheory.ae_iff]
      simp
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc,
      MeasureTheory.ae_restrict_of_ae hnull] with t htmem ht0
    have h0 : 0 < t := lt_of_le_of_ne htmem.1 (Ne.symm ht0)
    have hst : 0 < Real.sqrt t := Real.sqrt_pos.mpr h0
    have hb := hH t ⟨h0, htmem.2⟩
    have hrw : t ^ (-(1 : ℝ) / 2) = 1 / Real.sqrt t := by
      rw [Real.sqrt_eq_rpow, one_div, ← Real.rpow_neg h0.le]
      norm_num
    rw [hrw, mul_one_div, le_div_iff₀ hst]
    linarith [hb]
  have hval : (∫ t in (0 : ℝ)..L, c * t ^ (-(1 : ℝ) / 2)) = c * (2 * Real.sqrt L) := by
    rw [intervalIntegral.integral_const_mul, integral_rpow_neg_half L]
  unfold halfLogAverage halfLinePrimitive
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * Real.sqrt L)]
  calc (∫ t in (0 : ℝ)..L, F t) ≤ ∫ t in (0 : ℝ)..L, c * t ^ (-(1 : ℝ) / 2) := hmono
    _ = c * (2 * Real.sqrt L) := hval


/-- **A pointwise lower bound on the half-log trace passes to the average.** -/
theorem le_halfLogAverage {F : ℝ → ℝ} (hF : Continuous F) {L c : ℝ} (hL : 0 < L)
    (hH : ∀ t ∈ Set.Ioc (0 : ℝ) L, c ≤ Real.sqrt t * F t) :
    c ≤ halfLogAverage F L := by
  have hsqrt : 0 < Real.sqrt L := Real.sqrt_pos.mpr hL
  have hwint : IntervalIntegrable (fun t : ℝ => c * t ^ (-(1 : ℝ) / 2)) volume 0 L := by
    refine IntervalIntegrable.const_mul ?_ c
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hL.le]
    rw [intervalIntegral.integrableOn_Ioo_rpow_iff hL]
    norm_num
  have hmono : (∫ t in (0 : ℝ)..L, c * t ^ (-(1 : ℝ) / 2)) ≤ ∫ t in (0 : ℝ)..L, F t := by
    refine intervalIntegral.integral_mono_ae_restrict hL.le hwint
      (hF.intervalIntegrable _ _) ?_
    have hnull : ∀ᵐ t : ℝ, t ≠ 0 := by
      rw [MeasureTheory.ae_iff]
      simp
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc,
      MeasureTheory.ae_restrict_of_ae hnull] with t htmem ht0
    have h0 : 0 < t := lt_of_le_of_ne htmem.1 (Ne.symm ht0)
    have hst : 0 < Real.sqrt t := Real.sqrt_pos.mpr h0
    have hb := hH t ⟨h0, htmem.2⟩
    have hrw : t ^ (-(1 : ℝ) / 2) = 1 / Real.sqrt t := by
      rw [Real.sqrt_eq_rpow, one_div, ← Real.rpow_neg h0.le]
      norm_num
    rw [hrw, mul_one_div, div_le_iff₀ hst]
    linarith [hb]
  have hval : (∫ t in (0 : ℝ)..L, c * t ^ (-(1 : ℝ) / 2)) = c * (2 * Real.sqrt L) := by
    rw [intervalIntegral.integral_const_mul, integral_rpow_neg_half L]
  unfold halfLogAverage halfLinePrimitive
  rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 * Real.sqrt L)]
  calc c * (2 * Real.sqrt L) = ∫ t in (0 : ℝ)..L, c * t ^ (-(1 : ℝ) / 2) := hval.symm
    _ ≤ ∫ t in (0 : ℝ)..L, F t := hmono

/-! ## The assembly engine

An integrable derivative on a terminal ray forces the primitive to converge.  This is the step that
turns the source equation — which controls `A'` — into existence of the averaged trace `α`, and
with the comparison above into the two-sided bound on the half-log trace.
-/

open Filter Set in
/-- **An integrable derivative on a ray forces convergence.**  The primitive of an integrable
derivative tends to its total integral offset by the initial value. -/
theorem tendsto_of_integrableOn_deriv {A A' : ℝ → ℝ} {L₀ : ℝ}
    (hcont : ContinuousOn A (Ici L₀))
    (hderiv : ∀ x ∈ Ioi L₀, HasDerivAt A (A' x) x)
    (hint : IntegrableOn A' (Ioi L₀)) :
    Tendsto A atTop (nhds (A L₀ + ∫ x in Ioi L₀, A' x)) := by
  have hkey : ∀ L : ℝ, L₀ ≤ L → A L = A L₀ + ∫ x in L₀..L, A' x := by
    intro L hL
    have hsub : IntervalIntegrable A' volume L₀ L := by
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hL]
      exact hint.mono_set fun x hx => hx.1
    have hIcc : ContinuousOn A (Icc L₀ L) := hcont.mono (Icc_subset_Ici_self)
    have hdw : ∀ x ∈ Ioo L₀ L, HasDerivWithinAt A (A' x) (Ioi x) x := fun x hx =>
      (hderiv x hx.1).hasDerivWithinAt
    have := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hL hIcc hdw hsub
    linarith [this]
  have hEv : (fun L => A L) =ᶠ[atTop] fun L => A L₀ + ∫ x in L₀..L, A' x := by
    filter_upwards [eventually_ge_atTop L₀] with L hL
    exact hkey L hL
  refine Tendsto.congr' hEv.symm ?_
  exact tendsto_const_nhds.add
    (MeasureTheory.intervalIntegral_tendsto_integral_Ioi L₀ hint tendsto_id)

/-- The primitive of a continuous profile is continuous. -/
theorem continuous_halfLinePrimitive {F : ℝ → ℝ} (hF : Continuous F) :
    Continuous (halfLinePrimitive F) :=
  continuous_iff_continuousAt.mpr fun L => (hasDerivAt_halfLinePrimitive hF L).continuousAt

open Filter Set in
/-- **The averaged trace exists.**  This is `(12)`: whenever the source equation makes `A'`
integrable on a terminal ray, the half-log Cesàro average converges. -/
theorem tendsto_halfLogAverage {F : ℝ → ℝ} (hF : Continuous F) {L₀ : ℝ} (hL₀ : 0 < L₀)
    (hint : IntegrableOn (fun L => logDirichlet F L / (4 * L * Real.sqrt L)) (Ioi L₀)) :
    Tendsto (halfLogAverage F) atTop
      (nhds (halfLogAverage F L₀ +
        ∫ x in Ioi L₀, logDirichlet F x / (4 * x * Real.sqrt x))) := by
  have hYc : Continuous (halfLinePrimitive F) := continuous_halfLinePrimitive hF
  have hcont : ContinuousOn (halfLogAverage F) (Ici L₀) := by
    refine ContinuousOn.div hYc.continuousOn (by fun_prop) fun x hx => ?_
    have hxpos : 0 < x := lt_of_lt_of_le hL₀ hx
    have : 0 < Real.sqrt x := Real.sqrt_pos.mpr hxpos
    positivity
  have hderiv : ∀ x ∈ Ioi L₀,
      HasDerivAt (halfLogAverage F) (logDirichlet F x / (4 * x * Real.sqrt x)) x := fun x hx =>
    hasDerivAt_halfLogAverage hF (lt_trans hL₀ hx)
  exact tendsto_of_integrableOn_deriv hcont hderiv hint

/-! ## The squeeze

A two-sided bound between the lower and upper limits does not by itself produce a limit.  What
closes the gap is a family of approximants: if for every tolerance the profile is uniformly within
that tolerance of *some* function converging to the same value, then the profile itself converges.
This is what the mollified family supplies, the tolerance being the order of the commutator defect.
-/

open Filter in
/-- **The squeeze.**  A profile uniformly approximable, to every tolerance, by functions converging
to a common value converges to that value.  Note the approximants must share the limit; that is
exactly what the mollified family provides, since mollification does not move the averaged
trace. -/
theorem tendsto_of_forall_uniform_approx {H : ℝ → ℝ} {α : ℝ}
    (h : ∀ δ : ℝ, 0 < δ → ∃ G : ℝ → ℝ,
      Tendsto G atTop (nhds α) ∧ ∀ L, |H L - G L| ≤ δ) :
    Tendsto H atTop (nhds α) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨G, hGlim, hGapp⟩ := h (ε / 4) (by linarith)
  rw [Metric.tendsto_atTop] at hGlim
  obtain ⟨N, hN⟩ := hGlim (ε / 4) (by linarith)
  refine ⟨N, fun L hL => ?_⟩
  have h1 : |H L - G L| ≤ ε / 4 := hGapp L
  have h2 : |G L - α| < ε / 4 := by
    have := hN L hL
    rwa [Real.dist_eq] at this
  have hsplit : H L - α = (H L - G L) + (G L - α) := by ring
  rw [Real.dist_eq, hsplit]
  calc |(H L - G L) + (G L - α)| ≤ |H L - G L| + |G L - α| := abs_add_le _ _
    _ < ε := by linarith

/-! ## Mollification does not move the averaged trace

The averaged trace divides by `√L`, so any bound on the mollification defect that is uniform in `L`
is washed out as `L → ∞`.  Hence the mollified averages share the limit of the unmollified one —
the hypothesis the squeeze requires.
-/

open Filter in
/-- A vanishing difference transports a limit. -/
theorem tendsto_of_sub_tendsto_zero {G H : ℝ → ℝ} {α : ℝ}
    (hH : Tendsto H atTop (nhds α))
    (hd : Tendsto (fun L => G L - H L) atTop (nhds 0)) :
    Tendsto G atTop (nhds α) := by
  have hsum := hH.add hd
  rw [add_zero] at hsum
  exact hsum.congr fun L => by ring

open Filter in
/-- A defect bounded by a constant over `√L` vanishes. -/
theorem tendsto_const_div_sqrt_atTop (C : ℝ) :
    Tendsto (fun L : ℝ => C / Real.sqrt L) atTop (nhds 0) :=
  Filter.Tendsto.div_atTop tendsto_const_nhds Real.tendsto_sqrt_atTop

open Filter in
/-- **Mollification does not move the averaged trace.**  A defect uniform in `L` is divided by
`√L`, so the mollified average converges to the same limit.  This is the hypothesis
`tendsto_of_forall_uniform_approx` needs of its approximating family. -/
theorem tendsto_of_defect_div_sqrt {G H : ℝ → ℝ} {α C : ℝ}
    (hH : Tendsto H atTop (nhds α))
    (hbd : ∀ L, |G L - H L| ≤ C / Real.sqrt L) :
    Tendsto G atTop (nhds α) := by
  refine tendsto_of_sub_tendsto_zero hH ?_
  refine squeeze_zero_norm (fun L => ?_) (tendsto_const_div_sqrt_atTop C)
  rw [Real.norm_eq_abs]
  exact hbd L

end GaloisForLFunctions.HTGeometry
