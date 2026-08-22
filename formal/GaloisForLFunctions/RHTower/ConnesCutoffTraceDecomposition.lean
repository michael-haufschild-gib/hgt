import GaloisForLFunctions.RHTower.ConnesCutoffBesovMass

/-!
# §VII (30) = (31) + (32) + (33): the exact cut-off decomposition

§VII (30)-(33) of

  A. Connes, *Trace formula in noncommutative geometry and the zeros of the Riemann zeta
  function*, arXiv:math/9811068.

The cut-off trace of Theorem 4 is

  `Trace(R_Λ T) = ∑_q ∫_{|u| ≤ Λ²} ĝ_q(u) (2 log' Λ − log|u|) du`,            (30)

which Connes splits into the constant term (31), the logarithmic term (32) and the error term
(33).  The split is *exact*, and rests on a single pointwise identity: with
`ε_Λ(u) = (log|u| − 2 log' Λ)^+ = connesCutoffExcess`,

  `1_{log|u| ≤ L}(u) · (L − log|u|) = (L − log|u|) + ε_L(u)`   for every `u`,

because both sides vanish outside the cut-off ball and agree inside it.  Integrating gives

  `∫_{|u| ≤ Λ²} ĝ(u)(2 log Λ − log|u|) du
      = 2 log Λ ∫ ĝ − ∫ ĝ(u) log|u| du + ∫ ĝ(u) ε_Λ(u) du`,

whose three terms are exactly (31), (32) and (33).  `ConnesCutoffBesovMass` and
`ConnesBesovCutoffDecay` show the third is `O(Λ^{-N})` for every `N`.

No hypothesis beyond the integrability of `ĝ` and of `ĝ · log|·|` is used: the integrability of
the error term is *derived*, since the excess is dominated by `|log|u|| + L`.
-/

open MeasureTheory Real Set

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- **The pointwise cut-off identity.**  The truncated logarithmic weight is the full logarithmic
weight plus the excess. -/
theorem connes_cutoffWeight_split (L x : ℝ) :
    Set.indicator {u : ℝ | Real.log |u| ≤ L} (fun u : ℝ => L - Real.log |u|) x
      = (L - Real.log |x|) + connesCutoffExcess L x := by
  by_cases hx : Real.log |x| ≤ L
  · have hmem : x ∈ {u : ℝ | Real.log |u| ≤ L} := hx
    rw [Set.indicator_of_mem hmem]
    have hz : connesCutoffExcess L x = 0 := max_eq_right (by linarith)
    rw [hz, add_zero]
  · have hnot : x ∉ {u : ℝ | Real.log |u| ≤ L} := hx
    have hlt : L < Real.log |x| := lt_of_not_ge hx
    rw [Set.indicator_of_notMem hnot]
    have hz : connesCutoffExcess L x = Real.log |x| - L := max_eq_left (by linarith)
    rw [hz]
    ring

/-- The cut-off excess is dominated by `|log|x|| + L`. -/
theorem connes_cutoffExcess_le_abs_log {L : ℝ} (hL : 0 ≤ L) (x : ℝ) :
    connesCutoffExcess L x ≤ abs (Real.log |x|) + L := by
  have hself := le_abs_self (Real.log |x|)
  have habs : (0 : ℝ) ≤ abs (Real.log |x|) := abs_nonneg _
  refine max_le ?_ (by linarith)
  linarith

/-- The error-term integrand is integrable as soon as the function and its logarithmic moment
are. -/
theorem connes_excess_integrable {G : ℝ → ℂ} {L : ℝ} (hL : 0 ≤ L) (hG : Integrable G)
    (hGlog : Integrable fun u : ℝ => G u * ((Real.log |u| : ℝ) : ℂ)) :
    Integrable fun u : ℝ => G u * ((connesCutoffExcess L u : ℝ) : ℂ) := by
  have hmaj : Integrable fun u : ℝ =>
      ‖G u * ((Real.log |u| : ℝ) : ℂ)‖ + L * ‖G u‖ := by
    exact hGlog.norm.add (hG.norm.const_mul L)
  refine Integrable.mono' hmaj ?_ (Filter.Eventually.of_forall fun u => ?_)
  · refine hG.aestronglyMeasurable.mul ?_
    exact (Complex.continuous_ofReal.measurable.comp
      (connes_cutoffExcess_measurable L)).aestronglyMeasurable
  · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (connesCutoffExcess_nonneg L u)]
    have hb := connes_cutoffExcess_le_abs_log hL u
    have hstep : ‖G u‖ * connesCutoffExcess L u
        ≤ ‖G u‖ * (abs (Real.log |u|) + L) :=
      mul_le_mul_of_nonneg_left hb (norm_nonneg _)
    refine le_trans hstep (le_of_eq ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    ring

/-- **§VII (30) = (31) + (32) + (33), the exact decomposition.** -/
theorem connes_cutoffTrace_split (G : ℝ → ℂ) {L : ℝ} (hL : 0 ≤ L) (hG : Integrable G)
    (hGlog : Integrable fun u : ℝ => G u * ((Real.log |u| : ℝ) : ℂ)) :
    (∫ u in {u : ℝ | Real.log |u| ≤ L}, G u * (((L - Real.log |u| : ℝ)) : ℂ))
      = (L : ℂ) * (∫ u : ℝ, G u) - (∫ u : ℝ, G u * ((Real.log |u| : ℝ) : ℂ))
        + ∫ u : ℝ, G u * ((connesCutoffExcess L u : ℝ) : ℂ) := by
  have hmeas : MeasurableSet {u : ℝ | Real.log |u| ≤ L} :=
    measurableSet_le (Real.measurable_log.comp measurable_abs) measurable_const
  have hexc : Integrable fun u : ℝ => G u * ((connesCutoffExcess L u : ℝ) : ℂ) :=
    connes_excess_integrable hL hG hGlog
  have hLG : Integrable fun u : ℝ => (L : ℂ) * G u := hG.const_mul _
  have hstep : (∫ u in {u : ℝ | Real.log |u| ≤ L}, G u * (((L - Real.log |u| : ℝ)) : ℂ))
      = ∫ u : ℝ, ((L : ℂ) * G u - G u * ((Real.log |u| : ℝ) : ℂ)
          + G u * ((connesCutoffExcess L u : ℝ) : ℂ)) := by
    rw [← MeasureTheory.integral_indicator hmeas]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    have hind : Set.indicator {v : ℝ | Real.log |v| ≤ L}
          (fun v : ℝ => G v * (((L - Real.log |v| : ℝ)) : ℂ)) u
        = G u * ((Set.indicator {v : ℝ | Real.log |v| ≤ L}
            (fun v : ℝ => L - Real.log |v|) u : ℝ) : ℂ) := by
      by_cases hu : u ∈ {v : ℝ | Real.log |v| ≤ L}
      · rw [Set.indicator_of_mem hu, Set.indicator_of_mem hu]
      · rw [Set.indicator_of_notMem hu, Set.indicator_of_notMem hu]
        simp
    rw [hind, connes_cutoffWeight_split]
    push_cast
    ring
  have h1 : (∫ u : ℝ, ((L : ℂ) * G u - G u * ((Real.log |u| : ℝ) : ℂ)
          + G u * ((connesCutoffExcess L u : ℝ) : ℂ)))
      = (∫ u : ℝ, ((L : ℂ) * G u - G u * ((Real.log |u| : ℝ) : ℂ)))
        + ∫ u : ℝ, G u * ((connesCutoffExcess L u : ℝ) : ℂ) :=
    MeasureTheory.integral_add (hLG.sub hGlog) hexc
  have h2 : (∫ u : ℝ, ((L : ℂ) * G u - G u * ((Real.log |u| : ℝ) : ℂ)))
      = (∫ u : ℝ, (L : ℂ) * G u) - ∫ u : ℝ, G u * ((Real.log |u| : ℝ) : ℂ) :=
    MeasureTheory.integral_sub hLG hGlog
  rw [hstep, h1, h2, MeasureTheory.integral_const_mul]

/-- The cut-off ball of the trace formula is the logarithmic sublevel set. -/
theorem connes_logBall_eq {Λ : ℝ} (hΛ : 1 ≤ Λ) :
    {u : ℝ | Real.log |u| ≤ 2 * Real.log Λ} = {u : ℝ | |u| ≤ Λ ^ 2} := by
  have hΛ0 : (0 : ℝ) < Λ := lt_of_lt_of_le zero_lt_one hΛ
  have hsq : (0 : ℝ) < Λ ^ 2 := by positivity
  have hlogsq : Real.log (Λ ^ 2) = 2 * Real.log Λ := by
    rw [Real.log_pow]
    push_cast
    ring
  ext u
  simp only [Set.mem_setOf_eq]
  rcases eq_or_ne u 0 with hu | hu
  · subst hu
    have h2 : (0 : ℝ) ≤ 2 * Real.log Λ := by
      have := Real.log_nonneg hΛ
      linarith
    simp only [abs_zero, Real.log_zero]
    constructor
    · intro _; positivity
    · intro _; exact h2
  · have hupos : (0 : ℝ) < |u| := abs_pos.mpr hu
    rw [← hlogsq, Real.log_le_log_iff hupos hsq]

/-- **§VII (30) = (31) + (32) + (33), in the cut-off `Λ` of Theorem 4.** -/
theorem connes_cutoffTrace_expansion (G : ℝ → ℂ) {Λ : ℝ} (hΛ : 1 ≤ Λ) (hG : Integrable G)
    (hGlog : Integrable fun u : ℝ => G u * ((Real.log |u| : ℝ) : ℂ)) :
    (∫ u in {u : ℝ | |u| ≤ Λ ^ 2}, G u * (((2 * Real.log Λ - Real.log |u| : ℝ)) : ℂ))
      = ((2 * Real.log Λ : ℝ) : ℂ) * (∫ u : ℝ, G u)
        - (∫ u : ℝ, G u * ((Real.log |u| : ℝ) : ℂ))
        + ∫ u : ℝ, G u * ((connesCutoffExcess (2 * Real.log Λ) u : ℝ) : ℂ) := by
  have hL : (0 : ℝ) ≤ 2 * Real.log Λ := by
    have := Real.log_nonneg hΛ
    linarith
  rw [← connes_logBall_eq hΛ]
  exact connes_cutoffTrace_split G hL hG hGlog

end

end GaloisForLFunctions.RHTower
