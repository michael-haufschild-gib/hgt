import GaloisForLFunctions.HTGeometry.KleinGordonBandStateUniform

/-!
# The energy converges uniformly on an observation window

The energy is the square of the energy norm of the state, and squaring is uniformly continuous on
bounded sets. Both the band states and the true state are bounded on `[0, T]` by the sharp estimate —
by the same constant, since the band data are contractions of the data — so

`|E_R(t) − E(t)| = |‖v_R(t)‖ − ‖v(t)‖|·(‖v_R(t)‖ + ‖v(t)‖) ≤ 2M‖v_R(t) − v(t)‖`

on the window, and the uniform convergence of the state passes to the energy.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

section EnergyUniform

variable {W₀ : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E)} {b : ℝ}

/-- The energy is the square of the energy norm of the state. -/
theorem kgFieldEnergy_eq_norm_sq
    (W : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E))
    (g h : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    ‖kgFieldGrad W g h t‖ ^ 2 + ‖kgFieldVel W g h t‖ ^ 2 = ‖kgFieldState W g h t‖ ^ 2 := by
  rw [← kgEnergy_eq_norm_sq, kgEnergy, kgFieldState, kgPair_fst, kgPair_snd]

/-- **The band states are bounded on the window by the data of the true problem.** -/
theorem norm_kgFieldState_band_le (hb0 : 0 ≤ b) (hW : ‖W₀‖ ≤ b)
    (g y : Lp ℂ 2 (volume : Measure E)) (R : ℝ) {T t : ℝ} (ht0 : 0 ≤ t) (htT : t ≤ T) :
    ‖kgFieldState (kgBandOp W₀ R) (kgLowPassOp R g) (kgLowPassOp R y) t‖
      ≤ (‖g‖ + ‖y‖) * Real.exp (b * T) := by
  have habs : |t| = t := abs_of_nonneg ht0
  have hbound : ‖kgFieldState (kgBandOp W₀ R) (kgLowPassOp R g) (kgLowPassOp R y) t‖
      ≤ ‖kgPair E (kgLowPassOp R g, kgLowPassOp R y)‖ * Real.exp (b * |t|) := by
    rw [kgFieldState_eq_kgStateMild hb0 (norm_kgBandOp_le hb0 hW R)]
    exact norm_kgStateMild_le hb0 (norm_kgBandOp_le hb0 hW R) _ _ t
  have hdata : ‖kgPair E (kgLowPassOp R g, kgLowPassOp R y)‖ ≤ ‖g‖ + ‖y‖ := by
    refine (norm_kgPair_le (E := E) (kgLowPassOp R g, kgLowPassOp R y)).trans ?_
    have h1 : ‖kgLowPassOp (E := E) R g‖ ≤ ‖g‖ := norm_kgLowPassOp_apply_le R g
    have h2 : ‖kgLowPassOp (E := E) R y‖ ≤ ‖y‖ := norm_kgLowPassOp_apply_le R y
    linarith
  have hexp : Real.exp (b * |t|) ≤ Real.exp (b * T) := by
    rw [habs]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left htT hb0)
  refine hbound.trans ?_
  exact mul_le_mul hdata hexp (Real.exp_pos _).le (by positivity)

/-- **The true state is bounded on the window by the same constant.** -/
theorem norm_kgFieldState_le_window (hb0 : 0 ≤ b) (hW : ‖W₀‖ ≤ b)
    (g y : Lp ℂ 2 (volume : Measure E)) {T t : ℝ} (ht0 : 0 ≤ t) (htT : t ≤ T) :
    ‖kgFieldState W₀ g y t‖ ≤ (‖g‖ + ‖y‖) * Real.exp (b * T) := by
  have habs : |t| = t := abs_of_nonneg ht0
  have hbound : ‖kgFieldState W₀ g y t‖ ≤ ‖kgPair E (g, y)‖ * Real.exp (b * |t|) := by
    rw [kgFieldState_eq_kgStateMild hb0 hW]
    exact norm_kgStateMild_le hb0 hW _ _ t
  have hexp : Real.exp (b * |t|) ≤ Real.exp (b * T) := by
    rw [habs]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left htT hb0)
  refine hbound.trans ?_
  exact mul_le_mul (norm_kgPair_le (E := E) (g, y)) hexp (Real.exp_pos _).le (by positivity)

/-- **The energy converges uniformly on a finite observation window.** -/
theorem tendstoUniformlyOn_kgFieldEnergy_band (hb0 : 0 ≤ b) (hW : ‖W₀‖ ≤ b)
    (g y : Lp ℂ 2 (volume : Measure E)) (T : ℝ) :
    TendstoUniformlyOn
      (fun R : ℝ => fun t : ℝ =>
        ‖kgFieldGrad (kgBandOp W₀ R) (kgLowPassOp R g) (kgLowPassOp R y) t‖ ^ 2
          + ‖kgFieldVel (kgBandOp W₀ R) (kgLowPassOp R g) (kgLowPassOp R y) t‖ ^ 2)
      (fun t : ℝ => ‖kgFieldGrad W₀ g y t‖ ^ 2 + ‖kgFieldVel W₀ g y t‖ ^ 2)
      atTop (Set.Icc 0 T) := by
  set M : ℝ := (‖g‖ + ‖y‖) * Real.exp (b * T) with hM
  have hM0 : (0 : ℝ) ≤ M := by rw [hM]; positivity
  have hstate := tendstoUniformlyOn_kgFieldState_band hb0 hW g y T
  rw [Metric.tendstoUniformlyOn_iff] at hstate ⊢
  intro ε hε
  have hδ : (0 : ℝ) < ε / (2 * M + 1) := by positivity
  filter_upwards [hstate _ hδ] with R hR t ht
  set a : ℝ := ‖kgFieldState W₀ g y t‖ with ha
  set c : ℝ := ‖kgFieldState (kgBandOp W₀ R) (kgLowPassOp R g) (kgLowPassOp R y) t‖ with hc
  have hdst := hR t ht
  rw [dist_eq_norm] at hdst
  have hgap : |a - c| ≤ ‖kgFieldState W₀ g y t
      - kgFieldState (kgBandOp W₀ R) (kgLowPassOp R g) (kgLowPassOp R y) t‖ :=
    abs_norm_sub_norm_le _ _
  have hgap' : |a - c| < ε / (2 * M + 1) := lt_of_le_of_lt hgap hdst
  have hab : a ≤ M := norm_kgFieldState_le_window hb0 hW g y ht.1 ht.2
  have hcb : c ≤ M := norm_kgFieldState_band_le hb0 hW g y R ht.1 ht.2
  have ha0 : (0 : ℝ) ≤ a := norm_nonneg _
  have hc0 : (0 : ℝ) ≤ c := norm_nonneg _
  have hsq : |a ^ 2 - c ^ 2| = |a - c| * (a + c) := by
    have hfac : a ^ 2 - c ^ 2 = (a - c) * (a + c) := by ring
    rw [hfac, abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ a + c)]
  have hle : |a ^ 2 - c ^ 2| ≤ |a - c| * (2 * M) := by
    rw [hsq]
    exact mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
  have hfin : |a - c| * (2 * M) < ε := by
    have hpos : (0 : ℝ) < 2 * M + 1 := by linarith
    have hkey : |a - c| * (2 * M + 1) < ε := by
      rw [lt_div_iff₀ hpos] at hgap'
      exact hgap'
    nlinarith [abs_nonneg (a - c), hM0]
  rw [Real.dist_eq, kgFieldEnergy_eq_norm_sq, kgFieldEnergy_eq_norm_sq, ← ha, ← hc]
  exact lt_of_le_of_lt hle hfin

end EnergyUniform

end GaloisForLFunctions.HTGeometry
