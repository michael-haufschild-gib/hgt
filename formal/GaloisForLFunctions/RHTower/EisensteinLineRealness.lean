import GaloisForLFunctions.RHTower.EisensteinMaassSelbergLineModel
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMLiteralSourceReflection

/-!
# Realness on the critical line and the Maass–Selberg norm formula

The Fourier model is conjugation-symmetric, `conj E*(u; x, Y) = E*(conj u; x, Y)`, and reflection
symmetric, `E*(−u) = E*(u)` (corpus).  On the line `u = it` these combine to `conj E* = E*`: the
completed Eisenstein series and its truncation are real there.  Hence the bilinear diagonal is the
`L²` norm: `∫_𝒟 ‖Λ^Y E*(·, ½+it)‖² dμ = Re (msLineValue t Y)`, and `msLineValue t Y` is real
(its conjugate is itself, by the conjugation symmetry of `Λ` and of `Λ'`).
-/

open Complex MeasureTheory Set Filter Topology UpperHalfPlane ModularGroup
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.RHTower

namespace RHTower

noncomputable section

/-! ## Conjugation of powers with positive real base -/

theorem conj_cpow_of_pos {x : ℝ} (hx : 0 < x) (w : ℂ) :
    (starRingEnd ℂ) (((x : ℝ) : ℂ) ^ w) = ((x : ℝ) : ℂ) ^ ((starRingEnd ℂ) w) := by
  have harg : ((x : ℝ) : ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg hx.le]; exact Real.pi_ne_zero.symm
  rw [Complex.cpow_conj _ _ harg, Complex.conj_ofReal]

theorem conj_natCast_cpow (n : ℕ) (w : ℂ) :
    (starRingEnd ℂ) ((n : ℂ) ^ w) = (n : ℂ) ^ ((starRingEnd ℂ) w) := by
  have harg : (n : ℂ).arg ≠ Real.pi := by
    rw [Complex.natCast_arg]; exact Real.pi_ne_zero.symm
  rw [Complex.cpow_conj _ _ harg, Complex.conj_natCast]

/-! ## Conjugation symmetry of the Fourier model -/

theorem whittakerCoefficient_conj (u : ℂ) (n : D4BMPositiveIndex) :
    (starRingEnd ℂ) (d4BMCompletedEisensteinWhittakerCoefficient u n) =
      d4BMCompletedEisensteinWhittakerCoefficient ((starRingEnd ℂ) u) n := by
  unfold d4BMCompletedEisensteinWhittakerCoefficient
  rw [map_mul, map_sum, conj_natCast_cpow]
  congr 1
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [conj_natCast_cpow]
  congr 1
  rw [map_mul, map_neg, map_ofNat]

theorem fourierPhase_conj (negative : Bool) (N : ℕ) (x : ℝ) :
    (starRingEnd ℂ) (d4BMCompletedEisensteinFourierPhase negative N x) =
      d4BMCompletedEisensteinFourierPhase (!negative) N x := by
  unfold d4BMCompletedEisensteinFourierPhase d4BMFourierSign
  rw [← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I]
  congr 1
  cases negative <;> simp

theorem eisensteinTailTerm_conj (negative : Bool) (x Y : ℝ) (N : ℕ) (u : ℂ) :
    (starRingEnd ℂ) (eisensteinTailTerm negative x Y N u) =
      eisensteinTailTerm (!negative) x Y N ((starRingEnd ℂ) u) := by
  unfold eisensteinTailTerm
  rw [map_mul, map_mul, map_mul, map_mul, map_mul, whittakerCoefficient_conj, fourierPhase_conj,
    Complex.conj_ofReal, ← modifiedBesselKOrder_conj, map_pow, map_pow, Complex.conj_natCast,
    Complex.conj_ofReal]

theorem signedSqrtWhittakerTail_conj (negative : Bool) (x Y : ℝ) (u : ℂ) :
    (starRingEnd ℂ) (d4BMCompletedEisensteinSignedSqrtWhittakerTail u u negative x 0 0 Y) =
      d4BMCompletedEisensteinSignedSqrtWhittakerTail ((starRingEnd ℂ) u) ((starRingEnd ℂ) u)
        (!negative) x 0 0 Y := by
  rw [signedSqrtWhittakerTail_eq_tsum_term, signedSqrtWhittakerTail_eq_tsum_term, Complex.conj_tsum]
  exact tsum_congr fun N => eisensteinTailTerm_conj negative x Y N u

theorem cuspTailPart_conj (u : ℂ) (x Y : ℝ) :
    (starRingEnd ℂ) (d4BMCompletedEisensteinCuspTailPart .scalar u x Y) =
      d4BMCompletedEisensteinCuspTailPart .scalar ((starRingEnd ℂ) u) x Y := by
  rw [cuspTailPart_scalar_eq, cuspTailPart_scalar_eq, map_mul, map_add,
    signedSqrtWhittakerTail_conj, signedSqrtWhittakerTail_conj]
  simp only [Bool.not_false, Bool.not_true, map_ofNat]
  ring

theorem msA_conj (u : ℂ) : (starRingEnd ℂ) (msA u) = msA ((starRingEnd ℂ) u) := by
  unfold msA
  rw [← reflectedCompletedLambda_conj]
  congr 1
  rw [map_add, map_one, map_mul, map_ofNat]

theorem msB_conj (u : ℂ) : (starRingEnd ℂ) (msB u) = msB ((starRingEnd ℂ) u) := by
  unfold msB
  rw [← reflectedCompletedLambda_conj]
  congr 1
  rw [map_mul, map_ofNat]

theorem cuspConstantPart_conj (u : ℂ) {Y : ℝ} (hY : 0 < Y) :
    (starRingEnd ℂ) (d4BMCompletedEisensteinCuspConstantPart .scalar u Y) =
      d4BMCompletedEisensteinCuspConstantPart .scalar ((starRingEnd ℂ) u) Y := by
  rw [cuspConstantPart_eq_msAB, cuspConstantPart_eq_msAB, map_add, map_mul, map_mul, msA_conj,
    msB_conj, conj_cpow_of_pos hY, conj_cpow_of_pos hY, map_sub, map_add, map_div₀, map_one,
    map_ofNat]

/-- **Conjugation symmetry of the Fourier model.** -/
theorem cuspLeg_conj (u : ℂ) (x : ℝ) {Y : ℝ} (hY : 0 < Y) :
    (starRingEnd ℂ) (d4BMCompletedEisensteinCuspLeg .scalar u x Y) =
      d4BMCompletedEisensteinCuspLeg .scalar ((starRingEnd ℂ) u) x Y := by
  unfold d4BMCompletedEisensteinCuspLeg
  rw [map_add, cuspConstantPart_conj u hY, cuspTailPart_conj]

/-! ## Realness on the line -/

theorem conj_I_mul (t : ℝ) : (starRingEnd ℂ) ((t : ℂ) * Complex.I) = -((t : ℂ) * Complex.I) := by
  rw [map_mul, Complex.conj_ofReal, Complex.conj_I]; ring

theorem cuspLeg_line_conj {t : ℝ} (ht : t ≠ 0) (x : ℝ) {Y : ℝ} (hY : 0 < Y) :
    (starRingEnd ℂ) (d4BMCompletedEisensteinCuspLeg .scalar ((t : ℂ) * Complex.I) x Y) =
      d4BMCompletedEisensteinCuspLeg .scalar ((t : ℂ) * Complex.I) x Y := by
  rw [cuspLeg_conj _ x hY, conj_I_mul]
  exact d4BMCompletedEisensteinScalarCuspLeg_neg _ (by simp [ht]) x Y

theorem cuspTailPart_neg (u : ℂ) (x Y : ℝ) :
    d4BMCompletedEisensteinCuspTailPart .scalar (-u) x Y =
      d4BMCompletedEisensteinCuspTailPart .scalar u x Y := by
  unfold d4BMCompletedEisensteinCuspTailPart
  simp only
  rw [d4BMCompletedEisensteinFullSignedZeroWord_neg]

theorem cuspConstantPart_neg {u : ℂ} (hu : u.im ≠ 0) (Y : ℝ) :
    d4BMCompletedEisensteinCuspConstantPart .scalar (-u) Y =
      d4BMCompletedEisensteinCuspConstantPart .scalar u Y := by
  have h := d4BMCompletedEisensteinScalarCuspLeg_neg u hu 0 Y
  unfold d4BMCompletedEisensteinCuspLeg at h
  have h' := h
  simp only [cuspTailPart_neg] at h'
  exact add_right_cancel h'

theorem cuspConstantPart_line_conj {t : ℝ} (ht : t ≠ 0) {Y : ℝ} (hY : 0 < Y) :
    (starRingEnd ℂ) (d4BMCompletedEisensteinCuspConstantPart .scalar ((t : ℂ) * Complex.I) Y) =
      d4BMCompletedEisensteinCuspConstantPart .scalar ((t : ℂ) * Complex.I) Y := by
  rw [cuspConstantPart_conj _ hY, conj_I_mul]
  exact cuspConstantPart_neg (by simp [ht]) Y

/-- **The truncated line model is real on the critical line.** -/
theorem truncatedLineModel_line_conj {t : ℝ} (ht : t ≠ 0) (Y : ℝ) (z : ℍ) :
    (starRingEnd ℂ) (truncatedLineModel ((t : ℂ) * Complex.I) Y z) =
      truncatedLineModel ((t : ℂ) * Complex.I) Y z := by
  unfold truncatedLineModel eisensteinLineModel
  rw [map_sub, cuspLeg_line_conj ht z.re z.im_pos]
  congr 1
  split_ifs
  · exact cuspConstantPart_line_conj ht z.im_pos
  · simp

theorem sq_eq_ofReal_norm_sq_of_conj_eq {w : ℂ} (hw : (starRingEnd ℂ) w = w) :
    w ^ 2 = ((‖w‖ ^ 2 : ℝ) : ℂ) := by
  rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj, hw, sq]

/-- **The bilinear diagonal is the `L²` norm on the line.** -/
theorem truncatedPairing_line_eq_ofReal {t : ℝ} (ht : t ≠ 0) (Y : ℝ) :
    truncatedPairing Y ((t : ℂ) * Complex.I) ((t : ℂ) * Complex.I) =
      ((∫ z in fd, ‖truncatedLineModel ((t : ℂ) * Complex.I) Y z‖ ^ 2 : ℝ) : ℂ) := by
  unfold truncatedPairing
  rw [← integral_complex_ofReal]
  refine setIntegral_congr_fun isClosed_fd.measurableSet fun z _ => ?_
  rw [← sq, sq_eq_ofReal_norm_sq_of_conj_eq (truncatedLineModel_line_conj ht Y z)]

/-! ## `msLineValue` is real -/

theorem hasDerivAt_conj_of_conj_symm {f : ℂ → ℂ}
    (hf : ∀ s, f ((starRingEnd ℂ) s) = (starRingEnd ℂ) (f s)) {s₀ L : ℂ}
    (h : HasDerivAt f L s₀) : HasDerivAt f ((starRingEnd ℂ) L) ((starRingEnd ℂ) s₀) := by
  rw [hasDerivAt_iff_tendsto_slope] at h ⊢
  have hconj : Tendsto (fun s => (starRingEnd ℂ) s) (𝓝[≠] ((starRingEnd ℂ) s₀)) (𝓝[≠] s₀) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have := Complex.continuous_conj.tendsto ((starRingEnd ℂ) s₀)
      rw [Complex.conj_conj] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with s hs
      intro heq
      apply hs
      have := congrArg (starRingEnd ℂ) heq
      rw [Complex.conj_conj] at this
      exact this
  have hslope : ∀ s, slope f ((starRingEnd ℂ) s₀) s =
      (starRingEnd ℂ) (slope f s₀ ((starRingEnd ℂ) s)) := by
    intro s
    rw [slope_def_field, slope_def_field, map_div₀, map_sub, map_sub, hf, hf, Complex.conj_conj,
      Complex.conj_conj]
  have := (Complex.continuous_conj.tendsto L).comp (h.comp hconj)
  refine this.congr fun s => ?_
  simp only [Function.comp]
  exact (hslope s).symm

theorem deriv_reflectedCompletedLambda_conj {s : ℂ} (hs : s.im ≠ 0) :
    deriv reflectedCompletedLambda ((starRingEnd ℂ) s) =
      (starRingEnd ℂ) (deriv reflectedCompletedLambda s) :=
  (hasDerivAt_conj_of_conj_symm reflectedCompletedLambda_conj
    (differentiableAt_reflectedCompletedLambda hs).hasDerivAt).deriv

/-- `msLineValue` is real. -/
theorem msLineValue_conj {t : ℝ} (ht : 0 < t) {Y : ℝ} (hY : 0 < Y) :
    (starRingEnd ℂ) (msLineValue t Y) = msLineValue t Y := by
  have hA : (starRingEnd ℂ) (msA ((t : ℂ) * Complex.I)) = msB ((t : ℂ) * Complex.I) := by
    rw [msA_conj, conj_I_mul]
    unfold msA msB
    have h1 := reflectedCompletedLambda_two_mul_I_eq_conj ht.ne'
    unfold eisLineLambda at h1
    rw [h1, ← reflectedCompletedLambda_conj]
    congr 1
    rw [map_add, map_mul, map_one, map_ofNat, conj_I_mul]
  have hB : (starRingEnd ℂ) (msB ((t : ℂ) * Complex.I)) = msA ((t : ℂ) * Complex.I) := by
    rw [← hA, Complex.conj_conj]
  have hd1 : (starRingEnd ℂ) (deriv reflectedCompletedLambda (1 - 2 * ((t : ℂ) * Complex.I))) =
      deriv reflectedCompletedLambda (1 + 2 * ((t : ℂ) * Complex.I)) := by
    rw [← deriv_reflectedCompletedLambda_conj (by simp [ht.ne'])]
    congr 1
    rw [map_sub, map_one, map_mul, map_ofNat, conj_I_mul]; ring
  have hd2 : (starRingEnd ℂ) (deriv reflectedCompletedLambda (1 + 2 * ((t : ℂ) * Complex.I))) =
      deriv reflectedCompletedLambda (1 - 2 * ((t : ℂ) * Complex.I)) := by
    rw [← deriv_reflectedCompletedLambda_conj (by simp [ht.ne'])]
    congr 1
    rw [map_add, map_one, map_mul, map_ofNat, conj_I_mul]; ring
  have hp1 : (starRingEnd ℂ) ((Y : ℂ) ^ (2 * ((t : ℂ) * Complex.I))) =
      (Y : ℂ) ^ (-(2 * ((t : ℂ) * Complex.I))) := by
    rw [conj_cpow_of_pos hY]; congr 1; rw [map_mul, map_ofNat, conj_I_mul]; ring
  have hp2 : (starRingEnd ℂ) ((Y : ℂ) ^ (-(2 * ((t : ℂ) * Complex.I)))) =
      (Y : ℂ) ^ (2 * ((t : ℂ) * Complex.I)) := by
    rw [conj_cpow_of_pos hY]; congr 1; rw [map_neg, map_mul, map_ofNat, conj_I_mul]; ring
  have hlog : (starRingEnd ℂ) (Complex.log (Y : ℂ)) = Complex.log (Y : ℂ) := by
    rw [← Complex.ofReal_log hY.le, Complex.conj_ofReal]
  unfold msLineValue
  simp only [map_add, map_div₀, map_sub, map_mul, map_pow, map_ofNat, hA, hB, hd1, hd2, hp1, hp2,
    hlog, Complex.conj_I, Complex.conj_ofReal]
  have h2t : (2 : ℂ) * ((t : ℂ) * Complex.I) ≠ 0 := by
    intro h; have := congrArg Complex.im h; simp at this; exact ht.ne' this
  field_simp
  ring

theorem msLineValue_im_eq_zero {t : ℝ} (ht : 0 < t) {Y : ℝ} (hY : 0 < Y) :
    (msLineValue t Y).im = 0 :=
  Complex.conj_eq_iff_im.mp (msLineValue_conj ht hY)

/-- **The Maass–Selberg norm formula on the critical line.** -/
theorem integral_norm_sq_truncatedLineModel_line {t : ℝ} (ht : 0 < t) {Y : ℝ} (hY : 1 ≤ Y) :
    ∫ z in fd, ‖truncatedLineModel ((t : ℂ) * Complex.I) Y z‖ ^ 2 = (msLineValue t Y).re := by
  have h := truncatedPairing_line ht hY
  rw [truncatedPairing_line_eq_ofReal ht.ne'] at h
  have := congrArg Complex.re h
  rw [Complex.ofReal_re] at this
  exact this

end

end RHTower
