import GaloisForLFunctions.OrderSixMetaplecticTheory.TheShiftedFractionalTraceIsASumOverShiftedPoints
import GaloisForLFunctions.OrderSixMetaplecticTheory.TheConstantTermOfTheFractionalTraceReadsTheConjugateTwist

/-!
# The constant term of the shifted fractional trace carries the shift phase

For the projected theta function `θ_s` (Fourier series `Σ_k b(v, k) e(ξ_kz)`) and `b ∈ O`, the shifted points
`θ_s(T_{±b}·)` have the Fourier coefficients `b(v, k)e(±ξ_kb)` (`sourceTheta_shift`). Every pair of the shifted
trace therefore reads the pair of the fractional trace times the **shift phase** `φ_b(k) = e(ξ_k·2b)`
(`shiftPhase`): the cusp `∞` (`integral_shiftSum_source`), the middle cusps (`integral_middle_sum_shift`, the
high points still cancel) and the classes over the cusp `0` (`integral_cuspZero_sum_shift`). Hence
(`integral_sourceShiftTrace`)

`∫_P Tr G^b = |P| (Σ_k φ_b(k) b(v, k)b(v, −k)(N² + N − J + NJ[q ∣ k])
    + N² χ(−4)χ(9)⁻¹ Σ_k φ_b(k) b(v/N, k)b(v/N, −k) g_χ(k))`,

the constant term of the fractional trace with `φ_b` inserted in every frequency.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators Classical MatrixGroups

namespace GaloisForLFunctions.OrderSixMetaplecticTheory

open MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein MetaplecticMobiusDescent.CubicJacobi
  MetaplecticMobiusDescent.CubicEisenstein MetaplecticMobiusDescent.CubicKubota SpectralTheoryOfTheCubicCover
  MetaplecticMobiusDescent.CubicEisenstein.RationalSource

/-- The shift phase `φ_b(k) = e(ξ_k · 2b)`. -/
def shiftPhase (b k : O) : ℂ := tracePhase (cuspFrequency k * (2 * ringComplex b))

theorem norm_shiftPhase (b k : O) : ‖shiftPhase b k‖ = 1 := tracePhase_norm _

/-- Phases at integral translations only depend on the translation modulo `3`. -/
theorem tracePhase_congr_three (k x y : O) (h : (3 : O) ∣ x - y) :
    tracePhase (cuspFrequency k * ringComplex x) = tracePhase (cuspFrequency k * ringComplex y) := by
  obtain ⟨m, hm⟩ := h
  have hx : ringComplex x = ringComplex y + 3 * ringComplex m := by
    rw [show x = y + 3 * m by linear_combination hm, map_add, map_mul, map_ofNat]
  rw [hx, mul_add, AddChar.map_add_eq_mul, cuspFrequency_period, mul_one]

/-- `θ_s(T_b w)` is the cusp series of `θ_s` translated by `b`. -/
theorem sourceTheta_shift (b : O) (z : ℂ) (v : ℝ) (hv : 0 < v) :
    sourceTheta (integralComplexMatrix (integralTranslation b) • upperPoint z v hv) =
      cuspCharacterSeries (rationalSourceModeAmplitude v) (z + ringComplex b) := by
  rw [integralTranslation_action, sourceTheta, cubicSourceResidualFunction_fourier_expansion]

namespace PrimaryPrime

variable (P : PrimaryPrime)

theorem sourceTheta_shift_fracShift (b t : O) (z : ℂ) (v : ℝ) (hv : 0 < v) :
    sourceTheta (integralComplexMatrix (integralTranslation b) • P.fracShift t • upperPoint z v hv) =
      cuspCharacterSeries (rationalSourceModeAmplitude v) (z + (3 * ringComplex t / ringComplex P.p + ringComplex b)) := by
  rw [fracShift, complexTranslation_action, sourceTheta_shift, add_assoc]

/-- **The cusp `∞` of the shifted trace.** `∫_P G^b = |P| Σ_k b(k)b(−k) φ_b(k) N[q ∣ k]`. -/
theorem integral_shiftSum_source (h2 : (2 : P.Res) ≠ 0) (b : O) (v : ℝ) (hv : 0 < v) :
    ∫ z in periodDomain, P.shiftSum sourceTheta b (upperPoint z v hv) =
      periodArea * ∑' k : O, rationalSourceModeAmplitude v k * rationalSourceModeAmplitude v (-k) *
        (shiftPhase b k * (if P.p ∣ k then P.normC else 0)) := by
  set bb := rationalSourceModeAmplitude v
  have hb : Summable (fun h => ‖bb h‖) := rationalSourceModeAmplitude_summable v hv
  have e : ∀ z, P.shiftSum sourceTheta b (upperPoint z v hv) = ∑ x : P.Res,
      cuspCharacterSeries bb (z + (3 * ringComplex (P.lift x) / ringComplex P.p + ringComplex b)) *
        cuspCharacterSeries bb (z + (3 * ringComplex (-P.lift x) / ringComplex P.p + ringComplex (-b))) := by
    intro z
    unfold shiftSum shiftCorrelation
    simp_rw [P.sourceTheta_shift_fracShift]
    rfl
  simp_rw [e]
  rw [integral_sum_translate_mul bb bb hb hb]
  congr 1
  refine tsum_congr fun k => ?_
  congr 1
  have hsum : ∑ x : P.Res, tracePhase (cuspFrequency k *
      ((3 * ringComplex (P.lift x) / ringComplex P.p + ringComplex b) -
        (3 * ringComplex (-P.lift x) / ringComplex P.p + ringComplex (-b)))) =
      shiftPhase b k * ∑ x : P.Res, P.traceChar (x * (2 * P.res k)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [show (3 * ringComplex (P.lift x) / ringComplex P.p + ringComplex b) -
        (3 * ringComplex (-P.lift x) / ringComplex P.p + ringComplex (-b)) =
        3 * ringComplex (2 * P.lift x) / ringComplex P.p + 2 * ringComplex b by
          rw [map_neg, map_neg, map_mul, map_ofNat]; ring,
      mul_add, AddChar.map_add_eq_mul, P.tracePhase_low,
      show P.res (2 * P.lift x) = 2 * x by rw [map_mul, res_lift, map_ofNat], shiftPhase, mul_comm]
    congr 1
    congr 1
    ring
  rw [hsum, P.sum_traceChar_mul, if_congr (P.res_eq_zero_iff_two h2 k) rfl rfl]

/-- The shifted high term `|P| Σ_h b(N(q)v, h)b(v, −q²h) e(ξ_hb) e(−ξ_{q²h}b)`. -/
def highShift (b : O) (v : ℝ) : ℂ :=
  periodArea * ∑' h : O, rationalSourceModeAmplitude (‖ringComplex P.p‖ * (‖ringComplex P.p‖ * v)) h *
    rationalSourceModeAmplitude v (-(h * P.p ^ 2)) *
      (tracePhase (cuspFrequency h * ringComplex b) * tracePhase (cuspFrequency (-(h * P.p ^ 2)) * ringComplex (-b)))

/-- **The shifted high points.** `∫_P θ_b(A_q²w)θ_{−b}(T_uw)` does not depend on `u`. -/
theorem integral_high_mul_shift (b u : O) (v : ℝ) (hv : 0 < v) :
    ∫ z in periodDomain, sourceTheta (integralComplexMatrix (integralTranslation b) •
          P.dilation • P.dilation • upperPoint z v hv) *
        sourceTheta (integralComplexMatrix (integralTranslation (-b)) • P.fracShift u • upperPoint z v hv) =
      P.highShift b v := by
  set a := rationalSourceModeAmplitude (‖ringComplex P.p‖ * (‖ringComplex P.p‖ * v))
  set bb := rationalSourceModeAmplitude v
  have hP := P.ringComplex_ne_zero
  have ha : Summable (fun h => ‖a h‖) :=
    rationalSourceModeAmplitude_summable _ (mul_pos P.norm_pos (mul_pos P.norm_pos hv))
  have hb : Summable (fun h => ‖bb h‖) := rationalSourceModeAmplitude_summable v hv
  set a' : O → ℂ := fun h => a h * tracePhase (cuspFrequency h * ringComplex b)
  set b' : O → ℂ := fun h => bb h * tracePhase (cuspFrequency h * (3 * ringComplex u / ringComplex P.p +
    ringComplex (-b)))
  have ha' : Summable (fun h => ‖a' h‖) := by simpa only [a', norm_mul, tracePhase_norm, mul_one] using ha
  have hb' : Summable (fun h => ‖b' h‖) := by simpa only [b', norm_mul, tracePhase_norm, mul_one] using hb
  have e : ∀ z, sourceTheta (integralComplexMatrix (integralTranslation b) •
        P.dilation • P.dilation • upperPoint z v hv) *
      sourceTheta (integralComplexMatrix (integralTranslation (-b)) • P.fracShift u • upperPoint z v hv) =
      cuspCharacterSeries a' (ringComplex (P.p ^ 2) * z) * cuspCharacterSeries b' z := by
    intro z
    rw [P.dilation_upperPoint, P.dilation_upperPoint, sourceTheta_shift, P.sourceTheta_shift_fracShift,
      cuspCharacterSeries_translate, cuspCharacterSeries_translate]
    congr 2
    rw [map_pow]
    ring
  simp_rw [e]
  rw [integral_cuspCharacterSeries_mul_dilate (P.p ^ 2) a' b' ha' hb', highShift]
  congr 1
  refine tsum_congr fun h => ?_
  simp only [a', b']
  have hph : tracePhase (cuspFrequency (-(h * P.p ^ 2)) * (3 * ringComplex u / ringComplex P.p)) = 1 := by
    rw [show -(h * P.p ^ 2) = -(h * P.p) * P.p by ring, cuspFrequency_mul_right,
      show cuspFrequency (-(h * P.p)) * ringComplex P.p * (3 * ringComplex u / ringComplex P.p) =
        cuspFrequency (-(h * P.p)) * (3 * ringComplex u) by field_simp, cuspFrequency_period]
  rw [mul_add, AddChar.map_add_eq_mul, hph, one_mul]
  ring

/-- The mirrored high points: `∫_P θ_b(T_uw)θ_{−b}(A_q²w)` is the high term of `−b`. -/
theorem integral_high_mul_shift' (b u : O) (v : ℝ) (hv : 0 < v) :
    ∫ z in periodDomain, sourceTheta (integralComplexMatrix (integralTranslation b) • P.fracShift u • upperPoint z v hv) *
        sourceTheta (integralComplexMatrix (integralTranslation (-b)) •
          P.dilation • P.dilation • upperPoint z v hv) =
      P.highShift (-b) v := by
  have h := P.integral_high_mul_shift (-b) u v hv
  rw [neg_neg] at h
  rw [← h]
  simp only [mul_comm]

/-- **One shifted pair over a middle cusp.** -/
theorem integral_shiftCorrelation_middle (h2 : (2 : P.Res) ≠ 0) (b : O) (x : {x : P.Res // x ≠ 0}) (t : P.Res)
    (v : ℝ) (hv : 0 < v) :
    ∫ z in periodDomain, P.shiftCorrelation sourceTheta b (P.lift t)
        (complexMatrix (lowerThree (P.p * P.lift x.1)) • upperPoint z v hv) =
      (if 1 + 9 * t * x.1 = 0 then P.chi 2 * (P.chi (3 * x.1))⁻¹ * P.highShift b v else 0) +
        (if 1 - 9 * t * x.1 = 0 then P.chi 2 * (P.chi (3 * x.1))⁻¹ * P.highShift (-b) v else 0) +
        P.chi (1 - (9 * t * x.1) ^ 2) * (periodArea * ∑' k : O, rationalSourceModeAmplitude v k *
          rationalSourceModeAmplitude v (-k) *
            (shiftPhase b k * P.traceChar (2 * t / (1 - (9 * t * x.1) ^ 2) * P.res k))) := by
  have hb : Summable (fun h => ‖rationalSourceModeAmplitude v h‖) := rationalSourceModeAmplitude_summable v hv
  simp_rw [P.shiftCorrelation_lowerThree sourceTheta sourceTheta_automorphy h2 b x t]
  by_cases h₁ : 1 + 9 * t * x.1 = 0
  · have hsq : (1 : P.Res) - (9 * t * x.1) ^ 2 = 0 := by linear_combination (1 - 9 * t * x.1) * h₁
    have h₂ : ¬ (1 : P.Res) - 9 * t * x.1 = 0 := by
      intro h; apply h2; linear_combination h₁ + h
    simp_rw [if_pos h₁]
    rw [if_neg h₂, hsq, MulChar.map_zero, zero_mul, add_zero, add_zero, integral_const_mul,
      P.integral_high_mul_shift]
  · by_cases h₂ : 1 - 9 * t * x.1 = 0
    · have hsq : (1 : P.Res) - (9 * t * x.1) ^ 2 = 0 := by linear_combination (1 + 9 * t * x.1) * h₂
      simp_rw [if_neg h₁, if_pos h₂]
      rw [hsq, MulChar.map_zero, zero_mul, add_zero, zero_add, integral_const_mul,
        P.integral_high_mul_shift']
    · simp_rw [if_neg h₁, if_neg h₂]
      rw [zero_add, zero_add, integral_const_mul]
      simp_rw [P.sourceTheta_shift_fracShift]
      rw [integral_translate_mul _ _ hb hb]
      congr 2
      refine tsum_congr fun k => ?_
      congr 1
      rw [show (3 * ringComplex (P.lift (t / (1 + 9 * t * x.1))) / ringComplex P.p + ringComplex b) -
          (3 * ringComplex (P.lift (-t / (1 - 9 * t * x.1))) / ringComplex P.p + ringComplex (-b)) =
          3 * ringComplex (P.lift (t / (1 + 9 * t * x.1)) - P.lift (-t / (1 - 9 * t * x.1))) / ringComplex P.p +
            2 * ringComplex b by rw [map_sub, map_neg]; ring,
        mul_add, AddChar.map_add_eq_mul, P.tracePhase_low, map_sub, res_lift, res_lift, shiftPhase, mul_comm]
      congr 1
      have ha : (1 + 9 * t * x.1) ≠ 0 := h₁
      have hb' : (1 - 9 * t * x.1) ≠ 0 := h₂
      have key : t / (1 + 9 * t * x.1) - -t / (1 - 9 * t * x.1) = 2 * t / (1 - (9 * t * x.1) ^ 2) := by
        rw [neg_div, sub_neg_eq_add, div_add_div _ _ ha hb']
        congr 1 <;> ring
      rw [key]

/-- **The shifted middle cusps.** `Σ_{x ≢ 0} ∫_P G^b(L_{qx}w) = |P| Σ_k b(k)b(−k)φ_b(k)(N − J + (J − 1)N[q ∣ k])`. -/
theorem integral_middle_sum_shift (h2 : (2 : P.Res) ≠ 0) (b : O) (v : ℝ) (hv : 0 < v) :
    ∑ x : {x : P.Res // x ≠ 0}, ∫ z in periodDomain,
        P.shiftSum sourceTheta b (complexMatrix (lowerThree (P.p * P.lift x.1)) • upperPoint z v hv) =
      periodArea * ∑' k : O, rationalSourceModeAmplitude v k * rationalSourceModeAmplitude v (-k) *
        (shiftPhase b k * (P.normC - P.fracJacobi + (P.fracJacobi - 1) * (if P.p ∣ k then P.normC else 0))) := by
  set bb := rationalSourceModeAmplitude v with hbdef
  have hb : Summable (fun h => ‖bb h‖) := rationalSourceModeAmplitude_summable v hv
  have h9 := P.nine_ne_zero'
  have hcont : ∀ x : {x : P.Res // x ≠ 0}, ∀ t : P.Res, Continuous (fun z : ℂ => P.shiftCorrelation sourceTheta b
      (P.lift t) (complexMatrix (lowerThree (P.p * P.lift x.1)) • upperPoint z v hv)) := fun x t => by
    unfold shiftCorrelation
    exact ((cubicSourceResidualFunction_continuous.comp (continuous_hyperbolic_action _)).comp
        ((continuous_hyperbolic_action _).comp ((continuous_hyperbolic_action _).comp
          (continuous_upperPoint_z v hv)))).mul
      ((cubicSourceResidualFunction_continuous.comp (continuous_hyperbolic_action _)).comp
        ((continuous_hyperbolic_action _).comp ((continuous_hyperbolic_action _).comp
          (continuous_upperPoint_z v hv))))
  have hsplit : ∀ x : {x : P.Res // x ≠ 0}, ∫ z in periodDomain,
      P.shiftSum sourceTheta b (complexMatrix (lowerThree (P.p * P.lift x.1)) • upperPoint z v hv) =
      ∑ t : P.Res, ∫ z in periodDomain, P.shiftCorrelation sourceTheta b (P.lift t)
        (complexMatrix (lowerThree (P.p * P.lift x.1)) • upperPoint z v hv) := fun x => by
    unfold shiftSum
    exact integral_finsetSum _ (fun t _ => integrableOn_periodDomain_of_continuous _ (hcont x t))
  simp_rw [hsplit, P.integral_shiftCorrelation_middle h2 b _ _ v hv, Finset.sum_add_distrib]
  simp only [← hbdef]
  -- the high points cancel: for each sign one `t` per `x`, and `Σ_x χ(3x)⁻¹ = 0`
  have hcancel : ∀ (H : ℂ) (σ : P.Res), ∑ x : {x : P.Res // x ≠ 0}, ∑ t : P.Res,
      (if 1 + σ * (9 * t * x.1) = 0 then P.chi 2 * (P.chi (3 * x.1))⁻¹ * H else 0) = 0 := by
    intro H σ
    set c0 : ℂ := ∑ s : P.Res, if 1 + σ * s = 0 then (1 : ℂ) else 0
    have hK : ∀ x : {x : P.Res // x ≠ 0}, ∑ t : P.Res,
        (if 1 + σ * (9 * t * x.1) = 0 then P.chi 2 * (P.chi (3 * x.1))⁻¹ * H else 0) =
        P.chi 2 * H * c0 * (P.chi (3 * x.1))⁻¹ := by
      intro x
      have hbij := (mulRight_bijective₀ (9 * x.1) (mul_ne_zero h9 x.2)).sum_comp
        (fun s => if 1 + σ * s = 0 then (1 : ℂ) else 0)
      rw [show P.chi 2 * H * c0 * (P.chi (3 * x.1))⁻¹ = P.chi 2 * (P.chi (3 * x.1))⁻¹ * H * c0 by ring,
        show c0 = ∑ i : P.Res, (if 1 + σ * (i * (9 * x.1)) = 0 then (1 : ℂ) else 0) from hbij.symm, Finset.mul_sum]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [show t * (9 * x.1) = 9 * t * x.1 by ring]
      split_ifs <;> ring
    simp_rw [hK]
    rw [← Finset.mul_sum, P.sum_chi_three_inv, mul_zero]
  have hhigh1 := hcancel (P.highShift b v) 1
  have hhigh2 := hcancel (P.highShift (-b) v) (-1)
  simp only [one_mul, neg_one_mul, ← sub_eq_add_neg] at hhigh1 hhigh2
  rw [hhigh1, hhigh2, zero_add, zero_add]
  have hgen : ∀ x : {x : P.Res // x ≠ 0}, ∑ t : P.Res, P.chi (1 - (9 * t * x.1) ^ 2) *
      (periodArea * ∑' k : O, bb k * bb (-k) * (shiftPhase b k * P.traceChar (2 * t / (1 - (9 * t * x.1) ^ 2) * P.res k))) =
      periodArea * ∑' k : O, bb k * bb (-k) * ∑ t : P.Res, shiftPhase b k * (P.chi (1 - (9 * t * x.1) ^ 2) *
        P.traceChar (2 * t / (1 - (9 * t * x.1) ^ 2) * P.res k)) := by
    intro x
    rw [← sum_tsum_swap bb bb hb hb _ 1 (fun t k => by
      rw [norm_mul, norm_shiftPhase, one_mul]
      exact P.norm_chi_traceChar_le _ _), Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [← tsum_mul_left, ← tsum_mul_left, ← tsum_mul_left]
    exact tsum_congr fun k => by ring
  simp_rw [hgen]
  rw [← Finset.mul_sum, sum_tsum_swap bb bb hb hb _ _ (fun x k => by
    rw [← Finset.mul_sum, norm_mul, norm_shiftPhase, one_mul]
    exact P.norm_sum_chi_traceChar_le _ _)]
  congr 1
  refine tsum_congr fun k => ?_
  congr 1
  simp_rw [← Finset.mul_sum]
  rw [P.jacobi_double_sum h2 (P.res k), if_congr (P.res_eq_zero_iff k) rfl rfl]

/-! ### The classes over the cusp `0` -/

/-- The shifted low point `θ_s(T_bA_q⁻¹T(r)w)` as a cusp series. -/
theorem heckeLow_shift_source (b r : O) (z : ℂ) (v : ℝ) (hv : 0 < v) :
    P.heckeLow (fun w => sourceTheta (integralComplexMatrix (integralTranslation b) • w)) r (upperPoint z v hv) =
      cuspCharacterSeries (rationalSourceModeAmplitude (v / ‖ringComplex P.p‖))
        ((z + 3 * ringComplex r) / ringComplex P.p + ringComplex b) := by
  simp only [heckeLow]
  rw [transThree_smul_upperPoint, P.contraction_upperPoint, sourceTheta_shift]

/-- **The shifted low points of low points, averaged over `O/q²` and integrated.** -/
theorem integral_sum_lowLow_shift (b r₁ r₂ : O) (v : ℝ) (hv : 0 < v) :
    ∫ z in periodDomain, ∑ s : P.Res × P.Res,
        P.heckeLow (fun w => sourceTheta (integralComplexMatrix (integralTranslation b) • w)) r₁
            (P.contraction • complexMatrix (transThree (P.sqLift s)) • upperPoint z v hv) *
          P.heckeLow (fun w => sourceTheta (integralComplexMatrix (integralTranslation (-b)) • w)) r₂
            (P.contraction • complexMatrix (transThree (P.sqLift s)) • upperPoint z v hv) =
      P.normC ^ 2 * (periodArea * ∑' k : O, P.shiftedLow (v / ‖ringComplex P.p‖) (r₂ - r₁) k * shiftPhase b k *
        rationalSourceModeAmplitude (v / ‖ringComplex P.p‖ / ‖ringComplex P.p‖) (-k)) := by
  have hn := P.norm_pos
  have hP := P.ringComplex_ne_zero
  have hv1 : 0 < v / ‖ringComplex P.p‖ := div_pos hv hn
  set b₂ := rationalSourceModeAmplitude (v / ‖ringComplex P.p‖ / ‖ringComplex P.p‖)
  have hb₂ : Summable (fun h => ‖b₂ h‖) := rationalSourceModeAmplitude_summable _ (div_pos hv1 hn)
  set f : O → ℂ := fun k => P.shiftedLow (v / ‖ringComplex P.p‖) (r₂ - r₁) k * shiftPhase b k
  have hf : Summable (fun h => ‖f h‖) := by
    simpa only [f, norm_mul, norm_shiftPhase, mul_one] using P.summable_shiftedLow _ hv1 (r₂ - r₁)
  set g := cuspConv f b₂
  have hg : Summable (fun h => ‖g h‖) := summable_cuspConv hf hb₂
  have hinj : Function.Injective (fun m : O => m * P.p) := fun x y h => mul_right_cancel₀ P.ne_zero h
  set g' : O → ℂ := fun m => g (m * P.p) * tracePhase (cuspFrequency m * (ringComplex P.p * ringComplex (-b)))
  have hg1 : Summable (fun m => ‖g (m * P.p)‖) := hg.comp_injective hinj
  have hg' : Summable (fun m => ‖g' m‖) := by simpa only [g', norm_mul, tracePhase_norm, mul_one] using hg1
  have hg'' : Summable (fun m => ‖g' (m * P.p)‖) := hg'.comp_injective hinj
  have hpt : ∀ z, ∑ s : P.Res × P.Res,
      P.heckeLow (fun w => sourceTheta (integralComplexMatrix (integralTranslation b) • w)) r₁
          (P.contraction • complexMatrix (transThree (P.sqLift s)) • upperPoint z v hv) *
        P.heckeLow (fun w => sourceTheta (integralComplexMatrix (integralTranslation (-b)) • w)) r₂
          (P.contraction • complexMatrix (transThree (P.sqLift s)) • upperPoint z v hv) =
      P.normC ^ 2 * cuspCharacterSeries (fun m => g' (m * P.p)) z := by
    intro z
    have hterm : ∀ s : P.Res × P.Res,
        P.heckeLow (fun w => sourceTheta (integralComplexMatrix (integralTranslation b) • w)) r₁
            (P.contraction • complexMatrix (transThree (P.sqLift s)) • upperPoint z v hv) *
          P.heckeLow (fun w => sourceTheta (integralComplexMatrix (integralTranslation (-b)) • w)) r₂
            (P.contraction • complexMatrix (transThree (P.sqLift s)) • upperPoint z v hv) =
        cuspCharacterSeries g ((((z + 3 * ringComplex (P.lift s.1)) / ringComplex P.p + 3 * ringComplex r₂ +
          ringComplex P.p * ringComplex (-b)) + 3 * ringComplex (P.lift s.2)) / ringComplex P.p) := by
      intro s
      rw [transThree_smul_upperPoint, P.contraction_upperPoint, P.heckeLow_shift_source, P.heckeLow_shift_source]
      have e1 : ((z + 3 * ringComplex (P.sqLift s)) / ringComplex P.p + 3 * ringComplex r₁) / ringComplex P.p +
          ringComplex b = (((z + 3 * ringComplex (P.lift s.1)) / ringComplex P.p + 3 * ringComplex r₂ +
            ringComplex P.p * ringComplex (-b)) + 3 * ringComplex (P.lift s.2)) / ringComplex P.p +
              (-(3 * ringComplex (r₂ - r₁)) / ringComplex P.p + 2 * ringComplex b) := by
        simp only [sqLift, map_add, map_mul, map_sub, map_neg]
        field_simp
        ring
      have e2 : ((z + 3 * ringComplex (P.sqLift s)) / ringComplex P.p + 3 * ringComplex r₂) / ringComplex P.p +
          ringComplex (-b) = (((z + 3 * ringComplex (P.lift s.1)) / ringComplex P.p + 3 * ringComplex r₂ +
            ringComplex P.p * ringComplex (-b)) + 3 * ringComplex (P.lift s.2)) / ringComplex P.p := by
        simp only [sqLift, map_add, map_mul, map_neg]
        field_simp
        ring
      rw [e1, e2, cuspCharacterSeries_translate]
      have hf' : (fun h => b₂ h * tracePhase (cuspFrequency h * (-(3 * ringComplex (r₂ - r₁)) / ringComplex P.p +
          2 * ringComplex b))) = f := by
        funext h
        simp only [f, shiftedLow, shiftPhase, b₂]
        rw [mul_add, AddChar.map_add_eq_mul, mul_assoc]
      rw [hf']
      exact cuspCharacterSeries_mul hf hb₂ _
    simp_rw [hterm]
    rw [Fintype.sum_prod_type]
    have hinner : ∀ s₀ : P.Res, ∑ s₁ : P.Res, cuspCharacterSeries g
        ((((z + 3 * ringComplex (P.lift s₀)) / ringComplex P.p + 3 * ringComplex r₂ +
          ringComplex P.p * ringComplex (-b)) + 3 * ringComplex (P.lift s₁)) / ringComplex P.p) =
        P.normC * cuspCharacterSeries g' ((z + 3 * ringComplex (P.lift s₀)) / ringComplex P.p) := by
      intro s₀
      rw [P.sum_cuspCharacterSeries_low g hg,
        show (z + 3 * ringComplex (P.lift s₀)) / ringComplex P.p + 3 * ringComplex r₂ +
          ringComplex P.p * ringComplex (-b) = ((z + 3 * ringComplex (P.lift s₀)) / ringComplex P.p +
            ringComplex P.p * ringComplex (-b)) + 3 * ringComplex r₂ by ring,
        cuspCharacterSeries_period, cuspCharacterSeries_translate]
    simp_rw [hinner]
    rw [← Finset.mul_sum, P.sum_cuspCharacterSeries_low _ hg']
    ring
  have hcont : Continuous (fun z : ℂ => P.normC ^ 2 * cuspCharacterSeries (fun m => g' (m * P.p)) z) :=
    continuous_const.mul (cuspCharacterSeries_continuous _ hg'')
  simp_rw [hpt]
  rw [integral_const_mul, PrimaryPrime.integral_cuspCharacterSeries _ hg'']
  simp only [g', zero_mul, cuspFrequency, map_zero, zero_div, AddChar.map_zero_eq_one, mul_one, g, cuspConv,
    zero_sub, f]

/-- **The shifted classes over the cusp `0`.** -/
theorem integral_cuspZero_sum_shift (h2 : (2 : P.Res) ≠ 0) (b : O) (v : ℝ) (hv : 0 < v) :
    ∑ s : P.Res × P.Res, ∫ z in periodDomain, P.shiftSum sourceTheta b
        (complexMatrix P.gamma0 • complexMatrix (transThree (P.sqLift s)) • upperPoint z v hv) =
      P.normC ^ 2 * (periodArea * ∑' k : O, rationalSourceModeAmplitude v k * rationalSourceModeAmplitude v (-k) *
        shiftPhase b k) +
        P.normC ^ 2 * (periodArea * (P.chi (-4) * (P.chi 9)⁻¹ *
          ∑' k : O, rationalSourceModeAmplitude (v / ‖ringComplex P.p‖ / ‖ringComplex P.p‖) k *
            rationalSourceModeAmplitude (v / ‖ringComplex P.p‖ / ‖ringComplex P.p‖) (-k) *
              (shiftPhase b k * ∑ u : P.Res, P.chi u * P.traceChar (u * P.res k)))) := by
  have hn := P.norm_pos
  have hv1 : 0 < v / ‖ringComplex P.p‖ := div_pos hv hn
  set bb := rationalSourceModeAmplitude v with hbdef
  set b₂ := rationalSourceModeAmplitude (v / ‖ringComplex P.p‖ / ‖ringComplex P.p‖)
  have hb : Summable (fun h => ‖bb h‖) := rationalSourceModeAmplitude_summable v hv
  have hb₂ : Summable (fun h => ‖b₂ h‖) := rationalSourceModeAmplitude_summable _ (div_pos hv1 hn)
  have hu := continuous_upperPoint_z v hv
  have hT : ∀ (c r : O) (w : HyperbolicSpace), sourceTheta (integralComplexMatrix (integralTranslation c) •
      complexMatrix (transThree r) • w) = sourceTheta (integralComplexMatrix (integralTranslation c) • w) := by
    intro c r w
    rw [conj_smul, sourceTheta_automorphy, complexCharacter_translationConjugate_transThree, one_mul]
  -- the pointwise expansion of the classes over `0`
  have hpt : ∀ z, ∑ s : P.Res × P.Res, P.shiftSum sourceTheta b
      (complexMatrix P.gamma0 • complexMatrix (transThree (P.sqLift s)) • upperPoint z v hv) =
      P.normC ^ 2 * (sourceTheta (integralComplexMatrix (integralTranslation b) • upperPoint z v hv) *
        sourceTheta (integralComplexMatrix (integralTranslation (-b)) • upperPoint z v hv)) +
      ∑ x : {x : P.Res // x ≠ 0}, P.chi (-9 * x.1 ^ 2) * ∑ s : P.Res × P.Res,
        P.heckeLow (fun w => sourceTheta (integralComplexMatrix (integralTranslation b) • w))
            (-P.lowBeta (-P.lift x.1)) (P.contraction • complexMatrix (transThree (P.sqLift s)) • upperPoint z v hv) *
          P.heckeLow (fun w => sourceTheta (integralComplexMatrix (integralTranslation (-b)) • w))
            (-P.lowBeta (P.lift x.1)) (P.contraction • complexMatrix (transThree (P.sqLift s)) • upperPoint z v hv) := by
    intro z
    simp_rw [P.shiftSum_gamma0 sourceTheta sourceTheta_automorphy, hT]
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_prod, nsmul_eq_mul, Finset.sum_comm]
    simp_rw [Finset.mul_sum]
    push_cast
    ring
  have hcS : ∀ s : P.Res × P.Res, Continuous (fun z : ℂ => P.shiftSum sourceTheta b
      (complexMatrix P.gamma0 • complexMatrix (transThree (P.sqLift s)) • upperPoint z v hv)) := fun s => by
    unfold shiftSum shiftCorrelation
    exact continuous_finsetSum _ fun x _ =>
      ((cubicSourceResidualFunction_continuous.comp (continuous_hyperbolic_action _)).comp
        ((continuous_hyperbolic_action _).comp ((continuous_hyperbolic_action _).comp
          ((continuous_hyperbolic_action _).comp hu)))).mul
      ((cubicSourceResidualFunction_continuous.comp (continuous_hyperbolic_action _)).comp
        ((continuous_hyperbolic_action _).comp ((continuous_hyperbolic_action _).comp
          ((continuous_hyperbolic_action _).comp hu))))
  rw [← integral_finsetSum _ (fun s _ => integrableOn_periodDomain_of_continuous _ (hcS s))]
  simp_rw [hpt]
  have hlow : ∀ x : {x : P.Res // x ≠ 0}, Continuous (fun z : ℂ => ∑ s : P.Res × P.Res,
      P.heckeLow (fun w => sourceTheta (integralComplexMatrix (integralTranslation b) • w))
          (-P.lowBeta (-P.lift x.1)) (P.contraction • complexMatrix (transThree (P.sqLift s)) • upperPoint z v hv) *
        P.heckeLow (fun w => sourceTheta (integralComplexMatrix (integralTranslation (-b)) • w))
          (-P.lowBeta (P.lift x.1)) (P.contraction • complexMatrix (transThree (P.sqLift s)) • upperPoint z v hv)) :=
    fun x => continuous_finsetSum _ fun s _ => by
      simp only [heckeLow]
      exact ((cubicSourceResidualFunction_continuous.comp (continuous_hyperbolic_action _)).comp
          ((continuous_hyperbolic_action _).comp ((continuous_hyperbolic_action _).comp
            ((continuous_hyperbolic_action _).comp ((continuous_hyperbolic_action _).comp hu))))).mul
        ((cubicSourceResidualFunction_continuous.comp (continuous_hyperbolic_action _)).comp
          ((continuous_hyperbolic_action _).comp ((continuous_hyperbolic_action _).comp
            ((continuous_hyperbolic_action _).comp ((continuous_hyperbolic_action _).comp hu)))))
  have hc1 : Continuous (fun z : ℂ => P.normC ^ 2 *
      (sourceTheta (integralComplexMatrix (integralTranslation b) • upperPoint z v hv) *
        sourceTheta (integralComplexMatrix (integralTranslation (-b)) • upperPoint z v hv))) :=
    continuous_const.mul (((cubicSourceResidualFunction_continuous.comp (continuous_hyperbolic_action _)).comp hu).mul
      ((cubicSourceResidualFunction_continuous.comp (continuous_hyperbolic_action _)).comp hu))
  have hc2 : ∀ x : {x : P.Res // x ≠ 0}, Continuous (fun z : ℂ => P.chi (-9 * x.1 ^ 2) * ∑ s : P.Res × P.Res,
      P.heckeLow (fun w => sourceTheta (integralComplexMatrix (integralTranslation b) • w))
          (-P.lowBeta (-P.lift x.1)) (P.contraction • complexMatrix (transThree (P.sqLift s)) • upperPoint z v hv) *
        P.heckeLow (fun w => sourceTheta (integralComplexMatrix (integralTranslation (-b)) • w))
          (-P.lowBeta (P.lift x.1)) (P.contraction • complexMatrix (transThree (P.sqLift s)) • upperPoint z v hv)) :=
    fun x => continuous_const.mul (hlow x)
  rw [integral_add (integrableOn_periodDomain_of_continuous _ hc1)
      (integrable_finsetSum _ fun x _ => integrableOn_periodDomain_of_continuous _ (hc2 x)),
    integral_finsetSum _ fun x _ => integrableOn_periodDomain_of_continuous _ (hc2 x),
    integral_const_mul]
  simp_rw [integral_const_mul, P.integral_sum_lowLow_shift, sourceTheta_shift]
  rw [integral_translate_mul bb bb hb hb]
  have hph : ∀ k : O, tracePhase (cuspFrequency k * (ringComplex b - ringComplex (-b))) = shiftPhase b k := by
    intro k
    rw [shiftPhase, map_neg, sub_neg_eq_add, two_mul]
  simp_rw [hph]
  congr 1
  have hg0 : ∀ x : {x : P.Res // x ≠ 0}, ∑' k : O,
      P.shiftedLow (v / ‖ringComplex P.p‖) (-P.lowBeta (P.lift x.1) - -P.lowBeta (-P.lift x.1)) k * shiftPhase b k *
        rationalSourceModeAmplitude (v / ‖ringComplex P.p‖ / ‖ringComplex P.p‖) (-k) =
        ∑' k : O, b₂ k * b₂ (-k) * (shiftPhase b k * P.traceChar (-2 * (9 * x.1)⁻¹ * P.res k)) := by
    intro x
    have hx : ¬ P.p ∣ P.lift x.1 := P.not_dvd_lift x
    have hx' : ¬ P.p ∣ -P.lift x.1 := fun h => hx (dvd_neg.mp h)
    refine tsum_congr fun k => ?_
    have hβ : P.res (-(-P.lowBeta (P.lift x.1) - -P.lowBeta (-P.lift x.1))) = -2 * (9 * x.1)⁻¹ := by
      have h1 := P.res_neg_lowBeta (-P.lift x.1) hx'
      have h2' := P.res_neg_lowBeta (P.lift x.1) hx
      simp only [map_neg, res_lift] at h1 h2'
      simp only [map_neg, map_sub, neg_sub]
      rw [show P.res (P.lowBeta (P.lift x.1)) = -(9 * x.1)⁻¹ by rw [← h2', neg_neg],
        show P.res (P.lowBeta (-P.lift x.1)) = -(9 * -x.1)⁻¹ by rw [← h1, neg_neg], mul_neg, inv_neg]
      ring
    simp only [shiftedLow]
    rw [P.phase_eq_psi, P.psi_eq_traceChar, hβ]
    ring
  simp_rw [hg0]
  have hsw : ∑ x : {x : P.Res // x ≠ 0}, P.chi (-9 * x.1 ^ 2) * (P.normC ^ 2 * (periodArea *
      ∑' k : O, b₂ k * b₂ (-k) * (shiftPhase b k * P.traceChar (-2 * (9 * x.1)⁻¹ * P.res k)))) =
      P.normC ^ 2 * (periodArea * ∑ x : {x : P.Res // x ≠ 0},
        ∑' k : O, b₂ k * b₂ (-k) * (shiftPhase b k * (P.chi (-9 * x.1 ^ 2) * P.traceChar (-2 * (9 * x.1)⁻¹ * P.res k)))) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [← tsum_mul_left]
    exact tsum_congr fun k => by ring
  rw [hsw, sum_tsum_swap b₂ b₂ hb₂ hb₂ _ 1 (fun x k => by
    rw [norm_mul, norm_shiftPhase, one_mul]
    exact P.norm_chi_traceChar_le _ _)]
  congr 2
  rw [← tsum_mul_left]
  refine tsum_congr fun k => ?_
  simp_rw [← Finset.mul_sum]
  rw [P.gauss_low_sum h2 (P.res k)]
  ring

/-! ### The constant term -/

/-- The shifted trace of the projected theta function. -/
abbrev sourceShiftTrace (b : O) : HyperbolicSpace → ℂ := P.shiftTrace sourceTheta b

/-- **The constant term of the shifted trace**: the fractional trace's with `φ_b` in every frequency. -/
theorem integral_sourceShiftTrace (h2 : (2 : P.Res) ≠ 0) (b : O) (v : ℝ) (hv : 0 < v) :
    ∫ z in periodDomain, P.sourceShiftTrace b (upperPoint z v hv) =
      periodArea * (∑' k : O, rationalSourceModeAmplitude v k * rationalSourceModeAmplitude v (-k) *
          (shiftPhase b k * P.fracWeight k) +
        P.normC ^ 2 * (P.chi (-4) * (P.chi 9)⁻¹) *
          ∑' k : O, rationalSourceModeAmplitude (v / ‖ringComplex P.p‖ / ‖ringComplex P.p‖) k *
            rationalSourceModeAmplitude (v / ‖ringComplex P.p‖ / ‖ringComplex P.p‖) (-k) *
              (shiftPhase b k * ∑ u : P.Res, P.chi u * P.traceChar (u * P.res k))) := by
  set bb := rationalSourceModeAmplitude v
  have hb : Summable (fun h => ‖bb h‖) := rationalSourceModeAmplitude_summable v hv
  have hu := continuous_upperPoint_z v hv
  have e : ∀ z, P.sourceShiftTrace b (upperPoint z v hv) = P.shiftSum sourceTheta b (upperPoint z v hv) +
      (∑ x : {x : P.Res // x ≠ 0}, P.shiftSum sourceTheta b
          (complexMatrix (lowerThree (P.p * P.lift x.1)) • upperPoint z v hv) +
        ∑ s : P.Res × P.Res, P.shiftSum sourceTheta b
          (complexMatrix P.gamma0 • complexMatrix (transThree (P.sqLift s)) • upperPoint z v hv)) := fun z =>
    P.shiftTrace_eq sourceTheta sourceTheta_automorphy b _
  simp_rw [e]
  have hS : Continuous (P.shiftSum sourceTheta b) := by
    unfold shiftSum shiftCorrelation
    exact continuous_finsetSum _ fun x _ =>
      ((cubicSourceResidualFunction_continuous.comp (continuous_hyperbolic_action _)).comp
        (continuous_hyperbolic_action _)).mul
      ((cubicSourceResidualFunction_continuous.comp (continuous_hyperbolic_action _)).comp
        (continuous_hyperbolic_action _))
  have hA : Continuous (fun z : ℂ => P.shiftSum sourceTheta b (upperPoint z v hv)) := hS.comp hu
  have hB : ∀ x : {x : P.Res // x ≠ 0}, Continuous (fun z : ℂ => P.shiftSum sourceTheta b
      (complexMatrix (lowerThree (P.p * P.lift x.1)) • upperPoint z v hv)) := fun x =>
    hS.comp ((continuous_hyperbolic_action _).comp hu)
  have hC : ∀ s : P.Res × P.Res, Continuous (fun z : ℂ => P.shiftSum sourceTheta b
      (complexMatrix P.gamma0 • complexMatrix (transThree (P.sqLift s)) • upperPoint z v hv)) := fun s =>
    hS.comp ((continuous_hyperbolic_action _).comp ((continuous_hyperbolic_action _).comp hu))
  have hBs : Continuous (fun z : ℂ => ∑ x : {x : P.Res // x ≠ 0}, P.shiftSum sourceTheta b
      (complexMatrix (lowerThree (P.p * P.lift x.1)) • upperPoint z v hv)) := continuous_finsetSum _ fun x _ => hB x
  have hCs : Continuous (fun z : ℂ => ∑ s : P.Res × P.Res, P.shiftSum sourceTheta b
      (complexMatrix P.gamma0 • complexMatrix (transThree (P.sqLift s)) • upperPoint z v hv)) :=
    continuous_finsetSum _ fun s _ => hC s
  have hBC : Continuous (fun z : ℂ => ∑ x : {x : P.Res // x ≠ 0}, P.shiftSum sourceTheta b
      (complexMatrix (lowerThree (P.p * P.lift x.1)) • upperPoint z v hv) + ∑ s : P.Res × P.Res,
        P.shiftSum sourceTheta b (complexMatrix P.gamma0 • complexMatrix (transThree (P.sqLift s)) • upperPoint z v hv)) :=
    hBs.add hCs
  rw [integral_add (integrableOn_periodDomain_of_continuous _ hA) (integrableOn_periodDomain_of_continuous _ hBC),
    integral_add (integrableOn_periodDomain_of_continuous _ hBs) (integrableOn_periodDomain_of_continuous _ hCs),
    integral_finsetSum _ fun x _ => integrableOn_periodDomain_of_continuous _ (hB x),
    integral_finsetSum _ fun s _ => integrableOn_periodDomain_of_continuous _ (hC s),
    P.integral_shiftSum_source h2 b v hv, P.integral_middle_sum_shift h2 b v hv, P.integral_cuspZero_sum_shift h2 b v hv]
  have hφ₁ : ∀ k : O, ‖shiftPhase b k * (if P.p ∣ k then P.normC else 0)‖ ≤ ‖P.normC‖ := by
    intro k
    rw [norm_mul, norm_shiftPhase, one_mul]
    split_ifs <;> simp
  have hφ₂ : ∀ k : O, ‖shiftPhase b k * (P.normC - P.fracJacobi + (P.fracJacobi - 1) *
      (if P.p ∣ k then P.normC else 0))‖ ≤ ‖P.normC - P.fracJacobi‖ + ‖P.fracJacobi - 1‖ * ‖P.normC‖ := by
    intro k
    rw [norm_mul, norm_shiftPhase, one_mul]
    refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
    rw [norm_mul]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    split_ifs <;> simp
  have hφ₃ : ∀ k : O, ‖shiftPhase b k‖ ≤ 1 := fun k => (norm_shiftPhase b k).le
  have s₁ := summable_mul_neg_bdd hb hb _ _ hφ₁
  have s₂ := summable_mul_neg_bdd hb hb _ _ hφ₂
  have s₃ : Summable (fun k => P.normC ^ 2 * (bb k * bb (-k) * shiftPhase b k)) :=
    (summable_mul_neg_bdd hb hb _ _ hφ₃).mul_left _
  have hsum : (∑' k : O, bb k * bb (-k) * (shiftPhase b k * (if P.p ∣ k then P.normC else 0))) +
      (∑' k : O, bb k * bb (-k) * (shiftPhase b k * (P.normC - P.fracJacobi + (P.fracJacobi - 1) *
        (if P.p ∣ k then P.normC else 0)))) +
      P.normC ^ 2 * ∑' k : O, bb k * bb (-k) * shiftPhase b k =
      ∑' k : O, bb k * bb (-k) * (shiftPhase b k * P.fracWeight k) := by
    rw [← s₁.tsum_add s₂, ← tsum_mul_left, ← (s₁.add s₂).tsum_add s₃]
    refine tsum_congr fun k => ?_
    simp only [fracWeight]
    split_ifs <;> ring
  linear_combination periodArea * hsum

end PrimaryPrime

end GaloisForLFunctions.OrderSixMetaplecticTheory
