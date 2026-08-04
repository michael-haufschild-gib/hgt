import GaloisForLFunctions.HTGeometry.KleinGordonFieldRegularAlways

/-!
# A bound on the velocity of the field solution

The field itself obeys `‖u(t)‖ ≤ (‖f‖+‖h‖)e^{‖W‖|t|}` (statement 85). Its velocity was so far
unbounded by anything, although the closed formula of statement 97 makes the estimate immediate: the
two propagator terms are contractions of the data, and the Duhamel term is controlled by the bound on
the field itself.

Estimating the Duhamel integral by the supremum of its integrand on the interval gives a factor
`‖W‖|t|`, and `1 + x ≤ eˣ` absorbs it into a second exponential. So the velocity obeys the same shape
of bound as the field, with the rate doubled.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

section Bound

variable {W : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E)} {b : ℝ}

/-- The field is bounded by the norms of the raw data. -/
theorem norm_kgFieldMild_le_data (hb0 : 0 ≤ b) (hW : ‖W‖ ≤ b)
    (g h : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    ‖kgFieldMild W (kgFreqInvOp g) h t‖ ≤ (‖g‖ + ‖h‖) * Real.exp (b * |t|) := by
  refine le_trans (norm_kgFieldMild_le hb0 hW (kgFreqInvOp g) h t) ?_
  have hg : ‖kgFreqInvOp (E := E) g‖ ≤ ‖g‖ := by
    have h1 := (kgFreqInvOp (E := E)).le_of_opNorm_le norm_kgFreqInvOp_le g
    rwa [one_mul] at h1
  have hexp : (0 : ℝ) < Real.exp (b * |t|) := Real.exp_pos _
  exact mul_le_mul_of_nonneg_right (by linarith) (le_of_lt hexp)

/-- **The velocity of the field solution obeys an exponential bound.** -/
theorem norm_deriv_kgFieldMild_le (hb0 : 0 ≤ b) (hW : ‖W‖ ≤ b)
    (g h : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    ‖deriv (kgFieldMild W (kgFreqInvOp g) h) t‖
      ≤ (‖g‖ + ‖h‖) * Real.exp (2 * (b * |t|)) := by
  set u := kgFieldMild W (kgFreqInvOp g) h with hu
  set D : ℝ := ‖g‖ + ‖h‖ with hD
  have hD0 : 0 ≤ D := by
    rw [hD]
    positivity
  have hbound : ∀ s ∈ Set.uIoc (0 : ℝ) t,
      ‖kgCosOp (t - s) (W (u s))‖ ≤ b * (D * Real.exp (b * |t|)) := by
    intro s hs
    have habs : |s| ≤ |t| := abs_le_abs_of_mem_uIoc_zero hs
    have h1 : ‖kgCosOp (E := E) (t - s) (W (u s))‖ ≤ ‖W (u s)‖ :=
      norm_kgCosOp_apply_le _ _
    have h2 : ‖W (u s)‖ ≤ b * ‖u s‖ := W.le_of_opNorm_le hW _
    have h3 : ‖u s‖ ≤ D * Real.exp (b * |s|) := norm_kgFieldMild_le_data hb0 hW g h s
    have h4 : Real.exp (b * |s|) ≤ Real.exp (b * |t|) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left habs hb0)
    have h5 : ‖u s‖ ≤ D * Real.exp (b * |t|) :=
      h3.trans (mul_le_mul_of_nonneg_left h4 hD0)
    calc ‖kgCosOp (E := E) (t - s) (W (u s))‖ ≤ ‖W (u s)‖ := h1
      _ ≤ b * ‖u s‖ := h2
      _ ≤ b * (D * Real.exp (b * |t|)) := mul_le_mul_of_nonneg_left h5 hb0
  have hint : ‖∫ s in (0 : ℝ)..t, kgCosOp (t - s) (W (u s))‖
      ≤ b * (D * Real.exp (b * |t|)) * |t| := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const hbound
    simpa using h
  have hfree : ‖-(kgSinOp (E := E) t g) + kgCosOp t h‖ ≤ D := by
    refine le_trans (norm_add_le _ _) ?_
    rw [norm_neg]
    have h1 := norm_kgSinOp_apply_le (E := E) t g
    have h2 := norm_kgCosOp_apply_le (E := E) t h
    rw [hD]
    linarith
  have hsplit : ‖deriv u t‖ ≤ D + b * (D * Real.exp (b * |t|)) * |t| := by
    rw [hu, deriv_kgFieldMild hb0 hW g h t]
    refine le_trans (norm_add_le _ _) ?_
    exact add_le_add hfree hint
  refine hsplit.trans ?_
  have hx : (0 : ℝ) ≤ b * |t| := by positivity
  have hlin : 1 + b * |t| ≤ Real.exp (b * |t|) := by
    have := Real.add_one_le_exp (b * |t|)
    linarith
  have hexp2 : Real.exp (2 * (b * |t|)) = Real.exp (b * |t|) * Real.exp (b * |t|) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hpos : (0 : ℝ) < Real.exp (b * |t|) := Real.exp_pos _
  rw [hexp2]
  have hstep : D + b * (D * Real.exp (b * |t|)) * |t|
      ≤ D * Real.exp (b * |t|) + D * (b * |t|) * Real.exp (b * |t|) := by
    have h1 : D ≤ D * Real.exp (b * |t|) := by
      nlinarith [Real.one_le_exp hx]
    nlinarith [Real.exp_pos (b * |t|)]
  refine hstep.trans ?_
  have hfac : D * Real.exp (b * |t|) + D * (b * |t|) * Real.exp (b * |t|)
      = D * (1 + b * |t|) * Real.exp (b * |t|) := by ring
  rw [hfac]
  have hmul : D * (1 + b * |t|) ≤ D * Real.exp (b * |t|) :=
    mul_le_mul_of_nonneg_left hlin hD0
  rw [← mul_assoc]
  exact mul_le_mul_of_nonneg_right hmul (le_of_lt hpos)

end Bound

end GaloisForLFunctions.HTGeometry
