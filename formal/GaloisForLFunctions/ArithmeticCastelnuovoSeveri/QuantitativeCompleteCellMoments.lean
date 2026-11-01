import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.LogarithmicStepProfiles

/-! # Quantitative mass and pole moments of complete logarithmic cells

The common support window and the pointwise sampling error control all continuous
weighted moments, including both pole coordinates and the square mass.
-/

noncomputable section
open MeasureTheory Set

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri.LogCells

/-- Absolute weight mass on the unchanged logarithmic source window. -/
def cellWindowWeight (R : ℝ) (B : ℕ) (w : ℝ → ℝ) : ℝ :=
  ∫ u in Icc (-R) (Real.log B - R), |w u|

theorem cellWindowWeight_nonneg (R : ℝ) (B : ℕ) (w : ℝ → ℝ) :
    0 ≤ cellWindowWeight R B w := integral_nonneg fun _ => abs_nonneg _

/-- A bounded measurable source on the cell window has every continuous weighted moment. -/
theorem cellWindow_integrable_abs_le {f w : ℝ → ℝ} (hf : Measurable f)
    (hw : Continuous w) {C : ℝ} (hb : ∀ u, |f u| ≤ C)
    (R : ℝ) (B : ℕ)
    (hs : ∀ u, u ≤ -R ∨ Real.log B - R ≤ u → f u = 0) :
    Integrable (fun u => f u * w u) ∧
      |∫ u, f u * w u| ≤ C * cellWindowWeight R B w := by
  let I := Icc (-R) (Real.log B - R)
  let H := I.indicator (fun u => C * |w u|)
  have hH : Integrable H := by
    apply (integrable_indicator_iff measurableSet_Icc).mpr
    exact (continuous_const.mul hw.abs).integrableOn_Icc
  have hdom : ∀ u, ‖f u * w u‖ ≤ H u := by
    intro u
    by_cases hu : u ∈ I
    · rw [show H u = C * |w u| from indicator_of_mem hu _]
      simpa only [norm_mul, Real.norm_eq_abs] using
        mul_le_mul_of_nonneg_right (hb u) (abs_nonneg (w u))
    · have hout : u ≤ -R ∨ Real.log B - R ≤ u := by
        dsimp only [I] at hu
        simp only [mem_Icc, not_and_or, not_le] at hu
        exact hu.elim (fun h => Or.inl h.le) (fun h => Or.inr h.le)
      rw [hs u hout, zero_mul, norm_zero,
        show H u = 0 from indicator_of_notMem hu _]
  have hi : Integrable (fun u => f u * w u) :=
    hH.mono' (hf.mul hw.measurable).aestronglyMeasurable (Filter.Eventually.of_forall hdom)
  refine ⟨hi, ?_⟩
  calc |∫ u, f u * w u| = ‖∫ u, f u * w u‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∫ u, ‖f u * w u‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ u, H u := integral_mono_ae hi.norm hH (Filter.Eventually.of_forall hdom)
    _ = C * cellWindowWeight R B w := by
      rw [show H = I.indicator (fun u => C * |w u|) from rfl,
        integral_indicator measurableSet_Icc, integral_const_mul]
      rfl

/-- The sampling error pays a continuous weighted moment at the exact rate `1/N`. -/
theorem abs_logStep_weightedMoment_sub_le {f w : ℝ → ℝ} {K : NNReal}
    (hK : LipschitzWith K f) (hw : Continuous w) {C : ℝ}
    (hbound : ∀ u, |f u| ≤ C) (R : ℝ) {N B : ℕ} (hN : 1 ≤ N) (hB : 1 ≤ B)
    (hs : ∀ u, u ≤ -R ∨ Real.log B - R ≤ u → f u = 0) :
    |(∫ u, logStep f R N u * w u) - ∫ u, f u * w u| ≤
      (K : ℝ) * cellWindowWeight R B w / N := by
  have hstep : ∀ u, |logStep f R N u| ≤ C := fun u => hbound (logCellPoint R N u)
  have hsstep : ∀ u, u ≤ -R ∨ Real.log B - R ≤ u → logStep f R N u = 0 :=
    fun _ hu => logStep_eq_zero_outside R hN hB hs hu
  have hm := measurable_logStep hK.continuous.measurable R hN
  have hi := (cellWindow_integrable_abs_le hm hw hstep R B hsstep).1
  have hf := (cellWindow_integrable_abs_le hK.continuous.measurable hw hbound R B hs).1
  have he := (cellWindow_integrable_abs_le (hm.sub hK.continuous.measurable) hw
    (abs_logStep_sub_le hK R hN (fun u hu => hs u (Or.inl hu))) R B
    (fun u hu => by simp only [Pi.sub_apply, hsstep u hu, hs u hu, sub_self])).2
  have hid : (fun u => (logStep f R N u - f u) * w u) =
      (fun u => logStep f R N u * w u - f u * w u) := by funext u; ring
  simp only [Pi.sub_apply] at he
  rw [hid, integral_sub hi hf] at he
  calc _ ≤ ((K : ℝ) / N) * cellWindowWeight R B w := he
    _ = _ := by ring

private theorem abs_square_sub_le {a b C e : ℝ} (he : 0 ≤ e)
    (ha : |a| ≤ C) (hb : |b| ≤ C) (hab : |a - b| ≤ e) :
    |a ^ 2 - b ^ 2| ≤ 2 * C * e := by
  calc |a ^ 2 - b ^ 2| = |a - b| * |a + b| := by
        rw [← abs_mul]; congr 1; ring
    _ ≤ e * (C + C) := mul_le_mul hab ((abs_add_le _ _).trans (add_le_add ha hb))
      (abs_nonneg _) he
    _ = _ := by ring

/-- Squaring a pole moment preserves the `1/N` rate because both moments are bounded. -/
theorem abs_logStep_weightedMoment_sq_sub_le {f w : ℝ → ℝ} {K : NNReal}
    (hK : LipschitzWith K f) (hw : Continuous w) {C : ℝ}
    (hbound : ∀ u, |f u| ≤ C) (R : ℝ) {N B : ℕ} (hN : 1 ≤ N) (hB : 1 ≤ B)
    (hs : ∀ u, u ≤ -R ∨ Real.log B - R ≤ u → f u = 0) :
    |(∫ u, logStep f R N u * w u) ^ 2 - (∫ u, f u * w u) ^ 2| ≤
      2 * C * (K : ℝ) * cellWindowWeight R B w ^ 2 / N := by
  have hW := cellWindowWeight_nonneg R B w
  have hf := (cellWindow_integrable_abs_le hK.continuous.measurable hw hbound R B hs).2
  have hg := (cellWindow_integrable_abs_le
    (measurable_logStep hK.continuous.measurable R hN) hw
    (fun u => hbound (logCellPoint R N u)) R B
    (fun _ hu => logStep_eq_zero_outside R hN hB hs hu)).2
  have he := abs_logStep_weightedMoment_sub_le hK hw hbound R hN hB hs
  calc _ ≤ 2 * (C * cellWindowWeight R B w) *
        ((K : ℝ) * cellWindowWeight R B w / N) :=
      abs_square_sub_le (by positivity) hg hf he
    _ = _ := by ring

/-- Square mass is recovered at rate `2 C Lip(f) log(B)/N`. -/
theorem abs_logStep_mass_sub_le {f : ℝ → ℝ} {K : NNReal}
    (hK : LipschitzWith K f) {C : ℝ} (hbound : ∀ u, |f u| ≤ C)
    (R : ℝ) {N B : ℕ} (hN : 1 ≤ N) (hB : 1 ≤ B)
    (hs : ∀ u, u ≤ -R ∨ Real.log B - R ≤ u → f u = 0) :
    |(∫ u, logStep f R N u ^ 2) - ∫ u, f u ^ 2| ≤
      2 * C * (K : ℝ) * Real.log B / N := by
  have hm := measurable_logStep hK.continuous.measurable R hN
  have hsstep : ∀ u, u ≤ -R ∨ Real.log B - R ≤ u → logStep f R N u = 0 :=
    fun _ hu => logStep_eq_zero_outside R hN hB hs hu
  have hsq (u : ℝ) : |f u ^ 2| ≤ C ^ 2 := by
    simpa only [abs_pow, sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hbound u) 2
  have hsqstep (u : ℝ) : |logStep f R N u ^ 2| ≤ C ^ 2 := hsq (logCellPoint R N u)
  have hi := (cellWindow_integrable_abs_le (hm.pow_const 2) (w := fun _ => 1) continuous_const
    hsqstep R B (fun u hu => by rw [hsstep u hu]; norm_num)).1
  have hf := (cellWindow_integrable_abs_le (hK.continuous.measurable.pow_const 2)
    (w := fun _ => 1) continuous_const hsq R B
    (fun u hu => by rw [hs u hu]; norm_num)).1
  have he := (cellWindow_integrable_abs_le
    ((hm.pow_const 2).sub (hK.continuous.measurable.pow_const 2))
    (w := fun _ => 1) continuous_const
    (fun u =>
      abs_square_sub_le (by positivity) (hbound (logCellPoint R N u)) (hbound u)
        (abs_logStep_sub_le hK R hN (fun u hu => hs u (Or.inl hu)) u))
    R B (fun u hu => by simp only [Pi.sub_apply, hsstep u hu, hs u hu, sub_self])).2
  simp only [mul_one, Pi.sub_apply] at hi hf he
  rw [integral_sub hi hf] at he
  have hlog : 0 ≤ Real.log B := Real.log_nonneg (by exact_mod_cast hB)
  have hw : cellWindowWeight R B (fun _ => 1) = Real.log B := by
    simp only [cellWindowWeight, abs_one]
    rw [← integral_indicator measurableSet_Icc, integral_indicator_const 1 measurableSet_Icc,
      Real.volume_real_Icc_of_le (by linarith), smul_eq_mul, mul_one]
    ring
  rw [hw] at he
  calc _ ≤ 2 * C * ((K : ℝ) / N) * Real.log B := he
    _ = _ := by ring

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri.LogCells

#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.LogCells.abs_logStep_weightedMoment_sub_le
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.LogCells.abs_logStep_weightedMoment_sq_sub_le
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.LogCells.abs_logStep_mass_sub_le
