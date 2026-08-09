import GaloisForLFunctions.RHTower.BurnolReflectedPotential

/-!
# The Bockstein limit of the crossing correlation

For negative lag the aperture-crossing correlation collapses the other way: the head now sits at
the shifted argument, giving `W_G(s) = conj(c) e^{s/2} ∫_{1/2}^{e^{-s}/2} g`.  Together with the
positive-lag collapse this bounds the whole correlation by `‖c‖ M e^{-s/2}`, hence

`‖q^{-n} W_G(nL + r)‖ ≤ ‖c‖ M e^{-r/2}` uniformly in `n`,

which is an integrable majorant against `|κ̇|`.  Dominated convergence therefore turns the pointwise
depth profile into the Bockstein limit `𝔅_n(G) → Res_{1/2}(G)`.
-/

open Complex Real MeasureTheory Set Filter Topology

noncomputable section

namespace RHTower

/-! ## The negative-lag collapse -/

theorem burnolCrossingWeight_eq_indicator_neg {s : ℝ} (hs : s < 0) (v : ℝ) :
    burnolCrossingWeight s v =
      Set.indicator (Ioc burnolApertureLog (burnolApertureLog - s)) (fun _ => (1 : ℝ)) v := by
  rw [burnolCrossingWeight]
  by_cases h1 : v ≤ burnolApertureLog
  · have h3 : v + s ≤ burnolApertureLog := by linarith
    have hmem : v ∉ Ioc burnolApertureLog (burnolApertureLog - s) := fun hc => absurd hc.1
      (not_lt.mpr h1)
    rw [if_pos h3, if_pos h1, Set.indicator_of_notMem hmem]
    norm_num
  · by_cases h3 : v + s ≤ burnolApertureLog
    · have hmem : v ∈ Ioc burnolApertureLog (burnolApertureLog - s) :=
        ⟨not_le.mp h1, by linarith⟩
      rw [if_pos h3, if_neg h1, Set.indicator_of_mem hmem]
      norm_num
    · have hmem : v ∉ Ioc burnolApertureLog (burnolApertureLog - s) := by
        intro hc
        exact h3 (by linarith [hc.2])
      rw [if_neg h3, if_neg h1, Set.indicator_of_notMem hmem]
      norm_num

theorem burnolCrossingCorrelationW_eq_window_neg {g : ℝ → ℂ} {s : ℝ} (hs : s < 0) :
    burnolCrossingCorrelationW g s =
      ∫ v in Ioc burnolApertureLog (burnolApertureLog - s),
        (starRingEnd ℂ) (burnolLogLift g (v + s)) * burnolLogLift g v := by
  rw [burnolCrossingCorrelationW]
  have hpt : ∀ v : ℝ,
      (starRingEnd ℂ) (burnolLogLift g (v + s)) * ((burnolCrossingWeight s v : ℝ) : ℂ) *
          burnolLogLift g v =
        Set.indicator (Ioc burnolApertureLog (burnolApertureLog - s))
          (fun w : ℝ => (starRingEnd ℂ) (burnolLogLift g (w + s)) * burnolLogLift g w) v := by
    intro v
    rw [burnolCrossingWeight_eq_indicator_neg hs v]
    by_cases hv : v ∈ Ioc burnolApertureLog (burnolApertureLog - s)
    · rw [Set.indicator_of_mem hv, Set.indicator_of_mem hv]
      push_cast
      ring
    · rw [Set.indicator_of_notMem hv, Set.indicator_of_notMem hv]
      push_cast
      ring
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt),
    MeasureTheory.integral_indicator measurableSet_Ioc]

theorem burnolCrossingCorrelationW_eq_of_head_neg {g : ℝ → ℂ} {c : ℂ}
    (hhead : BurnolApertureHead g c) {s : ℝ} (hs : s < 0) :
    burnolCrossingCorrelationW g s =
      (starRingEnd ℂ) c * ((Real.exp (s / 2) : ℝ) : ℂ) *
        ∫ t in Ioc (1 / 2 : ℝ) (Real.exp (-s) / 2), g t := by
  rw [burnolCrossingCorrelationW_eq_window_neg hs]
  have hint : ∀ v ∈ Ioc burnolApertureLog (burnolApertureLog - s),
      (starRingEnd ℂ) (burnolLogLift g (v + s)) * burnolLogLift g v =
        ((starRingEnd ℂ) c * ((Real.exp (s / 2) : ℝ) : ℂ)) *
          (Real.exp (v + 0) • g (Real.exp (v + 0))) := by
    intro v hv
    have hle : v + s ≤ burnolApertureLog := by linarith [hv.2]
    rw [burnolLogLift_of_apertureHead hhead hle, burnolLogLift, map_mul, Complex.conj_ofReal,
      Complex.real_smul]
    have hexp : ((Real.exp ((v + s) / 2) : ℝ) : ℂ) * ((Real.exp (v / 2) : ℝ) : ℂ) =
        ((Real.exp (s / 2) : ℝ) : ℂ) * ((Real.exp (v + 0) : ℝ) : ℂ) := by
      rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Real.exp_add, ← Real.exp_add]
      congr 2
      ring
    calc ((Real.exp ((v + s) / 2) : ℝ) : ℂ) * (starRingEnd ℂ) c *
            (((Real.exp (v / 2) : ℝ) : ℂ) * g (Real.exp v))
        = (((Real.exp ((v + s) / 2) : ℝ) : ℂ) * ((Real.exp (v / 2) : ℝ) : ℂ)) *
            ((starRingEnd ℂ) c * g (Real.exp v)) := by ring
      _ = _ := by
            rw [hexp]
            simp only [add_zero]
            ring
  rw [setIntegral_congr_fun measurableSet_Ioc hint, MeasureTheory.integral_const_mul,
    ← integral_burnolExpShiftSubstitution g burnolApertureLog (burnolApertureLog - s) 0]
  have h1 : Real.exp (burnolApertureLog + 0) = 1 / 2 := by
    rw [add_zero, exp_burnolApertureLog]
  have h2 : Real.exp (burnolApertureLog - s + 0) = Real.exp (-s) / 2 := by
    rw [add_zero, show burnolApertureLog - s = burnolApertureLog + (-s) by ring, Real.exp_add,
      exp_burnolApertureLog]
    ring
  rw [h1, h2]

/-! ## The uniform bound -/

theorem burnolCrossingCorrelationW_zero (g : ℝ → ℂ) : burnolCrossingCorrelationW g 0 = 0 := by
  rw [burnolCrossingCorrelationW]
  have hpt : ∀ v : ℝ,
      (starRingEnd ℂ) (burnolLogLift g (v + 0)) * ((burnolCrossingWeight 0 v : ℝ) : ℂ) *
        burnolLogLift g v = 0 := by
    intro v
    have hw : burnolCrossingWeight 0 v = 0 := by
      rw [burnolCrossingWeight, add_zero]
      ring
    rw [hw]
    push_cast
    ring
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt),
    MeasureTheory.integral_zero]

theorem norm_setIntegral_le_burnolTotal {g : ℝ → ℂ} (hIoi : IntegrableOn g (Ioi (1 / 2 : ℝ)))
    {X : ℝ} : ‖∫ t in Ioc (1 / 2 : ℝ) X, g t‖ ≤ ∫ t in Ioi (1 / 2 : ℝ), ‖g t‖ := by
  have hsub : Ioc (1 / 2 : ℝ) X ⊆ Ioi (1 / 2 : ℝ) := fun t ht => mem_Ioi.mpr ht.1
  refine le_trans (MeasureTheory.norm_integral_le_integral_norm _) ?_
  refine MeasureTheory.setIntegral_mono_set hIoi.norm
    (Filter.Eventually.of_forall fun t => norm_nonneg _)
    (Filter.Eventually.of_forall hsub)

/-- **A uniform bound on the crossing correlation.** -/
theorem norm_burnolCrossingCorrelationW_le {g : ℝ → ℂ} {c : ℂ} (hhead : BurnolApertureHead g c)
    (hIoi : IntegrableOn g (Ioi (1 / 2 : ℝ))) (s : ℝ) :
    ‖burnolCrossingCorrelationW g s‖ ≤
      ‖c‖ * (∫ t in Ioi (1 / 2 : ℝ), ‖g t‖) * Real.exp (-s / 2) := by
  set M : ℝ := ∫ t in Ioi (1 / 2 : ℝ), ‖g t‖ with hM
  have hM0 : 0 ≤ M := MeasureTheory.setIntegral_nonneg measurableSet_Ioi
    (fun t _ => norm_nonneg _)
  rcases lt_trichotomy s 0 with hs | hs | hs
  · rw [burnolCrossingCorrelationW_eq_of_head_neg hhead hs, norm_mul, norm_mul,
      Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    have hb := norm_setIntegral_le_burnolTotal (g := g) hIoi (X := Real.exp (-s) / 2)
    have hexp : Real.exp (s / 2) ≤ Real.exp (-s / 2) := by
      refine Real.exp_le_exp.mpr ?_
      linarith
    have hstep1 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ ‖c‖ * Real.exp (s / 2))
    have hstep2 : ‖c‖ * Real.exp (s / 2) * M ≤ ‖c‖ * M * Real.exp (-s / 2) := by
      nlinarith [hexp, mul_nonneg (norm_nonneg c) hM0, norm_nonneg c, hM0]
    linarith
  · rw [hs, burnolCrossingCorrelationW_zero, norm_zero]
    positivity
  · rw [burnolCrossingCorrelationW_eq_of_head hhead hs, norm_mul, norm_mul, norm_neg,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have hb : ‖∫ t in Ioc (1 / 2 : ℝ) (Real.exp s / 2), (starRingEnd ℂ) (g t)‖ ≤ M := by
      rw [integral_conj, Complex.norm_conj]
      exact norm_setIntegral_le_burnolTotal hIoi
    have hstep1 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ ‖c‖ * Real.exp (-s / 2))
    have hval : ‖c‖ * Real.exp (-s / 2) * M = ‖c‖ * M * Real.exp (-s / 2) := by ring
    linarith

end RHTower
