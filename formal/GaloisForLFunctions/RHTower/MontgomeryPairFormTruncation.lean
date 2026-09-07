import GaloisForLFunctions.RHTower.MontgomeryTruncationIntegrals

/-!
# Truncation of the Montgomery pair form to a window of heights

For `x ≥ 1` and `T ≥ 0` let `S(x,t) = Σ_ρ x^{ρ−1/2}/(1+(t+i(ρ−½))²)` be the full Lorentzian zero sum
and `S_T(x,t)` its restriction to the window `0 < γ ≤ T`.  This module proves

`|∫_0^T |S(x,t)|² dt − ∫_ℝ |S_T(x,t)|² dt| ≤ 131072 · x · (L² (3 log(1+T) + 2) + 64)`,

`L = C + log(2T+5)`, with `C` the explicit constant of the bound `‖ξ'/ξ(2+it)‖ ≤ C + log(|t|+4)`.
Since `∫_ℝ |S_T|² = (π/2) F(x,T)` is Montgomery's pair form of the window, this is the
truncation lemma of the unconditional pair-correlation theorem with the crude bound
`|x^{ρ−½}| ≤ √x` (no zero-free region is used), which loses nothing for `x ≤ T^{1−ε}`.

The three pieces: inside `[0,T]` the complement sum is `O(√x L (1/(1+T−t) + 1/(1+t)))` and the
window sum `O(√x L)`; outside `[0,T]` the window sum decays like `√x log/(1 + dist)` and its square
is integrated by the logarithmic majorant lemma.
-/

open Complex MeasureTheory Set Filter Topology

namespace RHTower

/-- `|‖a+b‖² − ‖a‖²| ≤ ‖b‖ (2‖a‖ + ‖b‖)`. -/
theorem abs_normSq_add_sub_normSq_le (a b : ℂ) :
    |‖a + b‖ ^ 2 - ‖a‖ ^ 2| ≤ ‖b‖ * (2 * ‖a‖ + ‖b‖) := by
  have h1 : ‖a + b‖ ≤ ‖a‖ + ‖b‖ := norm_add_le a b
  have h2 : ‖a‖ - ‖a + b‖ ≤ ‖b‖ := by
    have := abs_norm_sub_norm_le a (a + b)
    rw [show a - (a + b) = -b by ring, norm_neg] at this
    exact (le_abs_self _).trans this
  have hu := norm_nonneg (a + b)
  have hv := norm_nonneg a
  have hw := norm_nonneg b
  rw [abs_le]
  constructor
  · have := mul_le_mul h2 (show ‖a‖ + ‖a + b‖ ≤ 2 * ‖a‖ + ‖b‖ by linarith) (by positivity)
      (by positivity)
    nlinarith
  · nlinarith [mul_le_mul h1 h1 hu (by positivity)]

section

variable {x T : ℝ}

/-- The window sum as a function of the height. -/
noncomputable def windowSum (T x : ℝ) (t : ℝ) : ℂ := ∑ q ∈ zeroWindow T, zeroSumTerm x t q

theorem continuous_windowSum (T x : ℝ) : Continuous (windowSum T x) := by
  unfold windowSum
  refine continuous_finsetSum _ fun q _ => ?_
  have hβ0 := xiZeroCopy_re_pos q
  have hβ1 := xiZeroCopy_re_lt_one q
  exact continuous_const.mul (continuous_lorentzShift (lorentzCentre_mem_unitStrip ⟨hβ0, hβ1⟩))

/-- The Lorentzian majorant of the window sum. -/
noncomputable def windowMass (T : ℝ) (t : ℝ) : ℝ := ∑ q ∈ zeroWindow T, lorentzMassTerm t q

theorem norm_windowSum_le (hx : 1 ≤ x) (T t : ℝ) :
    ‖windowSum T x t‖ ≤ 16 * Real.sqrt x * windowMass T t := by
  unfold windowSum windowMass
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun q _ => norm_zeroSumTerm_le hx t q

theorem windowMass_nonneg (T t : ℝ) : 0 ≤ windowMass T t :=
  Finset.sum_nonneg fun q _ => lorentzMassTerm_nonneg t q

theorem windowMass_le_card (T t : ℝ) : windowMass T t ≤ (zeroWindow T).card := by
  unfold windowMass
  calc ∑ q ∈ zeroWindow T, lorentzMassTerm t q ≤ ∑ _q ∈ zeroWindow T, (1 : ℝ) :=
        Finset.sum_le_sum fun q _ => lorentzMassTerm_le_one t q
    _ = (zeroWindow T).card := by simp

theorem integrable_lorentzMassTerm_height (q : XiZeroCopy) :
    Integrable (fun t : ℝ => lorentzMassTerm t q) := by
  have := integrable_inv_one_add_sq.comp_sub_right (q.1 : ℂ).im
  refine this.congr (Eventually.of_forall fun t => ?_)
  simp [lorentzMassTerm, one_div]

theorem integrable_windowMass (T : ℝ) : Integrable (windowMass T) := by
  unfold windowMass
  exact integrable_finsetSum _ fun q _ => integrable_lorentzMassTerm_height q

theorem continuous_windowMass (T : ℝ) : Continuous (windowMass T) := by
  unfold windowMass
  refine continuous_finsetSum _ fun q _ => ?_
  unfold lorentzMassTerm
  apply Continuous.div continuous_const (by fun_prop)
  intro t; positivity

/-- `|S_T(x,·)|²` is integrable on the whole line. -/
theorem integrable_normSq_windowSum (hx : 1 ≤ x) (T : ℝ) :
    Integrable (fun t : ℝ => ‖windowSum T x t‖ ^ 2) := by
  have hm := integrable_windowMass T
  have hprod : Integrable (fun t : ℝ => (16 * Real.sqrt x * windowMass T t)
      * (16 * Real.sqrt x * windowMass T t)) := by
    refine (hm.const_mul (16 * Real.sqrt x)).bdd_mul (c := 16 * Real.sqrt x * (zeroWindow T).card)
      ((continuous_windowMass T).const_mul _).aestronglyMeasurable
      (Eventually.of_forall fun t => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by positivity) (windowMass_nonneg T t))]
    have := windowMass_le_card T t
    have hsx : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
    nlinarith
  refine Integrable.mono' hprod
    (((continuous_windowSum T x).norm.pow 2).aestronglyMeasurable)
    (Eventually.of_forall fun t => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have h := norm_windowSum_le hx T t
  have h0 := norm_nonneg (windowSum T x t)
  have hh : 0 ≤ 16 * Real.sqrt x * windowMass T t :=
    mul_nonneg (by positivity) (windowMass_nonneg T t)
  nlinarith [mul_le_mul h h h0 hh]

/-- `|S(x,·)|²` is integrable on `[0, T]`. -/
theorem integrableOn_normSq_lorentzZeroSumAll (hx : 1 ≤ x) (T : ℝ) :
    IntegrableOn (fun t : ℝ => ‖lorentzZeroSumAll x t‖ ^ 2) (Icc 0 T) :=
  ((continuousOn_lorentzZeroSumAll hx T).norm.pow 2).integrableOn_Icc

/-! ## The three estimates -/

/-- The abbreviation `L = C + log(2T + 5)`. -/
noncomputable def truncationLog (T : ℝ) : ℝ := xiLineTwoLogDerivConstant + Real.log (2 * T + 5)

theorem truncationLog_nonneg (hT : 0 ≤ T) : 0 ≤ truncationLog T := by
  unfold truncationLog
  have := xiLineTwoLogDerivConstant_nonneg
  have : 0 ≤ Real.log (2 * T + 5) := Real.log_nonneg (by linarith)
  linarith

/-- Inside the window of heights: `|‖S‖² − ‖S_T‖²| ≤ 196608 x L² (1/(1+(T−t)) + 1/(1+t))`. -/
theorem abs_normSq_sub_le_inside (hx : 1 ≤ x) {t : ℝ} (ht : 0 ≤ t) (htT : t ≤ T) :
    |‖lorentzZeroSumAll x t‖ ^ 2 - ‖windowSum T x t‖ ^ 2|
      ≤ 196608 * x * truncationLog T ^ 2 * (1 / (1 + (T - t)) + 1 / (1 + t)) := by
  have hsplit := lorentzZeroSumAll_eq_window_add_out hx T t
  rw [hsplit]
  have hO := norm_zeroSumOut_le hx ht htT
  have hW : ‖windowSum T x t‖ ≤ 128 * Real.sqrt x * truncationLog T := by
    refine (norm_sum_zeroWindow_le_log hx T t).trans ?_
    unfold truncationLog
    have : Real.log (|t| + 4) ≤ Real.log (2 * T + 5) :=
      Real.log_le_log (by positivity) (by rw [abs_of_nonneg ht]; linarith)
    have hsx : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
    nlinarith
  set D := 1 / (1 + (T - t)) + 1 / (1 + t) with hD
  have hD0 : 0 ≤ D := montgomeryWindowWeight_nonneg ht htT
  have hD2 : D ≤ 2 := windowWeight_le_two ht htT
  have hL := truncationLog_nonneg (by linarith : 0 ≤ T)
  have hsx : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  have hsq : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt (by linarith)
  set W := windowSum T x t
  set O := zeroSumOut T x t
  have hWO : (∑ q ∈ zeroWindow T, zeroSumTerm x t q) = W := rfl
  rw [hWO]
  refine (abs_normSq_add_sub_normSq_le W O).trans ?_
  have hO' : ‖O‖ ≤ 256 * Real.sqrt x * truncationLog T * D := by
    simpa [truncationLog, hD] using hO
  have hO0 := norm_nonneg O
  have hW0 := norm_nonneg W
  calc ‖O‖ * (2 * ‖W‖ + ‖O‖)
      ≤ (256 * Real.sqrt x * truncationLog T * D)
        * (2 * (128 * Real.sqrt x * truncationLog T) + 256 * Real.sqrt x * truncationLog T * D) := by
        exact mul_le_mul hO' (by linarith) (by positivity) (by positivity)
    _ = 65536 * (Real.sqrt x * Real.sqrt x) * truncationLog T ^ 2 * (D + D ^ 2) := by ring
    _ = 65536 * x * truncationLog T ^ 2 * (D + D ^ 2) := by rw [hsq]
    _ ≤ 65536 * x * truncationLog T ^ 2 * (3 * D) := by
        gcongr
        nlinarith
    _ = 196608 * x * truncationLog T ^ 2 * D := by ring

/-- Above the window: `‖S_T(x,t)‖² ≤ 65536 x ((A + log(1+(t−T)))/(1+(t−T)))²` with
`A = C + log(T+5)`. -/
theorem normSq_windowSum_le_above (hx : 1 ≤ x) (hT : 0 ≤ T) {t : ℝ} (ht : T < t) :
    ‖windowSum T x t‖ ^ 2 ≤ 65536 * x *
      (((xiLineTwoLogDerivConstant + Real.log (T + 5)) + Real.log (1 + (t - T)))
        / (1 + (t - T))) ^ 2 := by
  have h := norm_sum_zeroWindow_le_of_ge hx hT ht.le
  have hlog : Real.log (t + 5) ≤ Real.log (T + 5) + Real.log (1 + (t - T)) := by
    rw [← Real.log_mul (by linarith) (by linarith)]
    apply Real.log_le_log (by linarith)
    nlinarith
  have hden : 0 < 1 + (t - T) := by linarith
  have h' : ‖windowSum T x t‖ ≤ 256 * Real.sqrt x *
      (((xiLineTwoLogDerivConstant + Real.log (T + 5)) + Real.log (1 + (t - T))) / (1 + (t - T))) := by
    refine h.trans ?_
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right (by linarith) hden.le)
      (by positivity)
  have hsq : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt (by linarith)
  have hR : 0 ≤ ((xiLineTwoLogDerivConstant + Real.log (T + 5)) + Real.log (1 + (t - T)))
      / (1 + (t - T)) := by
    have := xiLineTwoLogDerivConstant_nonneg
    have : 0 ≤ Real.log (T + 5) := Real.log_nonneg (by linarith)
    have : 0 ≤ Real.log (1 + (t - T)) := Real.log_nonneg (by linarith)
    positivity
  calc ‖windowSum T x t‖ ^ 2 ≤ (256 * Real.sqrt x * (((xiLineTwoLogDerivConstant + Real.log (T + 5))
        + Real.log (1 + (t - T))) / (1 + (t - T)))) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h' 2
    _ = 65536 * (Real.sqrt x * Real.sqrt x) * (((xiLineTwoLogDerivConstant + Real.log (T + 5))
        + Real.log (1 + (t - T))) / (1 + (t - T))) ^ 2 := by ring
    _ = 65536 * x * (((xiLineTwoLogDerivConstant + Real.log (T + 5))
        + Real.log (1 + (t - T))) / (1 + (t - T))) ^ 2 := by rw [hsq]

/-- Below the window: `‖S_T(x,t)‖² ≤ 65536 x ((A + log(1+(0−t)))/(1+(0−t)))²` with
`A = C + log 5`. -/
theorem normSq_windowSum_le_below (hx : 1 ≤ x) {t : ℝ} (ht : t ≤ 0) :
    ‖windowSum T x t‖ ^ 2 ≤ 65536 * x *
      (((xiLineTwoLogDerivConstant + Real.log 5) + Real.log (1 + (0 - t))) / (1 + (0 - t))) ^ 2 := by
  have h := norm_sum_zeroWindow_le_of_le hx (T := T) ht
  have habs : |t| = 0 - t := by rw [abs_of_nonpos ht]; ring
  rw [habs] at h
  have hlog : Real.log (0 - t + 5) ≤ Real.log 5 + Real.log (1 + (0 - t)) := by
    rw [← Real.log_mul (by norm_num) (by linarith)]
    apply Real.log_le_log (by linarith)
    nlinarith
  have hden : 0 < 1 + (0 - t) := by linarith
  have h' : ‖windowSum T x t‖ ≤ 256 * Real.sqrt x *
      (((xiLineTwoLogDerivConstant + Real.log 5) + Real.log (1 + (0 - t))) / (1 + (0 - t))) := by
    refine h.trans ?_
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right (by linarith) hden.le)
      (by positivity)
  have hsq : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt (by linarith)
  calc ‖windowSum T x t‖ ^ 2 ≤ (256 * Real.sqrt x * (((xiLineTwoLogDerivConstant + Real.log 5)
        + Real.log (1 + (0 - t))) / (1 + (0 - t)))) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h' 2
    _ = 65536 * (Real.sqrt x * Real.sqrt x) * (((xiLineTwoLogDerivConstant + Real.log 5)
        + Real.log (1 + (0 - t))) / (1 + (0 - t))) ^ 2 := by ring
    _ = 65536 * x * (((xiLineTwoLogDerivConstant + Real.log 5)
        + Real.log (1 + (0 - t))) / (1 + (0 - t))) ^ 2 := by rw [hsq]

theorem integral_Ioi_normSq_windowSum_le (hx : 1 ≤ x) (hT : 0 ≤ T) :
    ∫ t in Ioi T, ‖windowSum T x t‖ ^ 2 ≤ 65536 * x * (2 * truncationLog T ^ 2 + 64) := by
  have hmeas : AEStronglyMeasurable (fun t : ℝ => ‖windowSum T x t‖ ^ 2) (volume.restrict (Ioi T)) :=
    ((continuous_windowSum T x).norm.pow 2).aestronglyMeasurable
  obtain ⟨_, hval⟩ := integral_Ioi_le_of_log_bound (K := 65536 * x)
    (A := xiLineTwoLogDerivConstant + Real.log (T + 5)) (by positivity) hmeas
    (fun t _ => by positivity) (fun t ht => normSq_windowSum_le_above hx hT ht)
  refine hval.trans ?_
  have hA : xiLineTwoLogDerivConstant + Real.log (T + 5) ≤ truncationLog T := by
    unfold truncationLog
    have := Real.log_le_log (by linarith : (0 : ℝ) < T + 5) (by linarith : T + 5 ≤ 2 * T + 5)
    linarith
  have hA0 : 0 ≤ xiLineTwoLogDerivConstant + Real.log (T + 5) := by
    have := xiLineTwoLogDerivConstant_nonneg
    have : 0 ≤ Real.log (T + 5) := Real.log_nonneg (by linarith)
    linarith
  gcongr

theorem integral_Iic_normSq_windowSum_le (hx : 1 ≤ x) (hT : 0 ≤ T) :
    ∫ t in Iic 0, ‖windowSum T x t‖ ^ 2 ≤ 65536 * x * (2 * truncationLog T ^ 2 + 64) := by
  have hmeas : AEStronglyMeasurable (fun t : ℝ => ‖windowSum T x t‖ ^ 2) (volume.restrict (Iic 0)) :=
    ((continuous_windowSum T x).norm.pow 2).aestronglyMeasurable
  obtain ⟨_, hval⟩ := integral_Iic_le_of_log_bound (K := 65536 * x)
    (A := xiLineTwoLogDerivConstant + Real.log 5) (by positivity) hmeas
    (fun t _ => by positivity) (fun t ht => normSq_windowSum_le_below hx ht)
  refine hval.trans ?_
  have hA : xiLineTwoLogDerivConstant + Real.log 5 ≤ truncationLog T := by
    unfold truncationLog
    have := Real.log_le_log (by norm_num : (0 : ℝ) < 5) (by linarith : (5 : ℝ) ≤ 2 * T + 5)
    linarith
  have hA0 : 0 ≤ xiLineTwoLogDerivConstant + Real.log 5 := by
    have := xiLineTwoLogDerivConstant_nonneg
    have : 0 ≤ Real.log 5 := Real.log_nonneg (by norm_num)
    linarith
  gcongr

theorem integral_Icc_abs_normSq_sub_le (hx : 1 ≤ x) (hT : 0 ≤ T) :
    |∫ t in Icc 0 T, (‖lorentzZeroSumAll x t‖ ^ 2 - ‖windowSum T x t‖ ^ 2)|
      ≤ 393216 * x * truncationLog T ^ 2 * Real.log (1 + T) := by
  have hS := integrableOn_normSq_lorentzZeroSumAll hx T
  have hW := (integrable_normSq_windowSum hx T).integrableOn (s := Icc 0 T)
  have hint : IntegrableOn (fun t : ℝ => ‖lorentzZeroSumAll x t‖ ^ 2 - ‖windowSum T x t‖ ^ 2)
      (Icc 0 T) := hS.sub hW
  have hmaj : IntegrableOn (fun t : ℝ => 196608 * x * truncationLog T ^ 2
      * (1 / (1 + (T - t)) + 1 / (1 + t))) (Icc 0 T) :=
    (integrableOn_windowWeight T).const_mul _
  calc |∫ t in Icc 0 T, (‖lorentzZeroSumAll x t‖ ^ 2 - ‖windowSum T x t‖ ^ 2)|
      ≤ ∫ t in Icc 0 T, |‖lorentzZeroSumAll x t‖ ^ 2 - ‖windowSum T x t‖ ^ 2| := by
        have := norm_integral_le_integral_norm (μ := volume.restrict (Icc 0 T))
          (fun t : ℝ => ‖lorentzZeroSumAll x t‖ ^ 2 - ‖windowSum T x t‖ ^ 2)
        simpa [Real.norm_eq_abs] using this
    _ ≤ ∫ t in Icc 0 T, 196608 * x * truncationLog T ^ 2 * (1 / (1 + (T - t)) + 1 / (1 + t)) :=
        setIntegral_mono_on hint.norm hmaj measurableSet_Icc
          fun t ht => abs_normSq_sub_le_inside hx ht.1 ht.2
    _ = 393216 * x * truncationLog T ^ 2 * Real.log (1 + T) := by
        rw [integral_const_mul, integral_Icc_windowWeight T hT]; ring

/-! ## The truncation theorem -/

theorem compl_Icc_eq (T : ℝ) : (Icc (0 : ℝ) T)ᶜ = Iio 0 ∪ Ioi T := by
  ext t
  simp only [mem_compl_iff, mem_Icc, mem_union, mem_Iio, mem_Ioi, not_and_or, not_le]

/-- **Truncation of the pair form (crude form).** For `x ≥ 1`, `T ≥ 0`,
`|∫_0^T |S(x,t)|² dt − ∫_ℝ |S_T(x,t)|² dt| ≤ 131072 x (L² (3 log(1+T) + 2) + 64)`,
`L = C + log(2T+5)`. -/
theorem integral_normSq_lorentzZeroSumAll_sub_le (hx : 1 ≤ x) (hT : 0 ≤ T) :
    |(∫ t in Icc 0 T, ‖lorentzZeroSumAll x t‖ ^ 2) - ∫ t : ℝ, ‖windowSum T x t‖ ^ 2|
      ≤ 131072 * x * (truncationLog T ^ 2 * (3 * Real.log (1 + T) + 2) + 64) := by
  have hW := integrable_normSq_windowSum hx T
  have hS := integrableOn_normSq_lorentzZeroSumAll hx T
  -- split the line integral
  have hsplit := integral_add_compl (μ := volume) (measurableSet_Icc (a := (0 : ℝ)) (b := T)) hW
  have hdisj : Disjoint (Iio (0 : ℝ)) (Ioi T) := by
    rw [Set.disjoint_left]; intro t h1 h2
    simp only [mem_Iio] at h1; simp only [mem_Ioi] at h2; linarith
  have hunion := setIntegral_union (μ := volume) (f := fun t : ℝ => ‖windowSum T x t‖ ^ 2)
    hdisj measurableSet_Ioi hW.integrableOn hW.integrableOn
  rw [← compl_Icc_eq] at hunion
  have hsub := integral_sub (μ := volume.restrict (Icc 0 T)) hS.integrable hW.integrableOn
  have hIio : ∫ t in Iio 0, ‖windowSum T x t‖ ^ 2 = ∫ t in Iic 0, ‖windowSum T x t‖ ^ 2 :=
    (integral_Iic_eq_integral_Iio).symm
  have h1 := integral_Icc_abs_normSq_sub_le hx hT
  have h2 := integral_Ioi_normSq_windowSum_le hx hT
  have h3 := integral_Iic_normSq_windowSum_le hx hT
  have h2' : 0 ≤ ∫ t in Ioi T, ‖windowSum T x t‖ ^ 2 :=
    setIntegral_nonneg measurableSet_Ioi fun t _ => by positivity
  have h3' : 0 ≤ ∫ t in Iic 0, ‖windowSum T x t‖ ^ 2 :=
    setIntegral_nonneg measurableSet_Iic fun t _ => by positivity
  have hL := truncationLog_nonneg hT
  have hlogT : 0 ≤ Real.log (1 + T) := Real.log_nonneg (by linarith)
  have hkey : (∫ t in Icc 0 T, ‖lorentzZeroSumAll x t‖ ^ 2) - ∫ t : ℝ, ‖windowSum T x t‖ ^ 2
      = (∫ t in Icc 0 T, (‖lorentzZeroSumAll x t‖ ^ 2 - ‖windowSum T x t‖ ^ 2))
        - ((∫ t in Iic 0, ‖windowSum T x t‖ ^ 2) + ∫ t in Ioi T, ‖windowSum T x t‖ ^ 2) := by
    rw [hsub, ← hsplit, hunion, hIio]; ring
  rw [hkey]
  calc |(∫ t in Icc 0 T, (‖lorentzZeroSumAll x t‖ ^ 2 - ‖windowSum T x t‖ ^ 2))
        - ((∫ t in Iic 0, ‖windowSum T x t‖ ^ 2) + ∫ t in Ioi T, ‖windowSum T x t‖ ^ 2)|
      ≤ |∫ t in Icc 0 T, (‖lorentzZeroSumAll x t‖ ^ 2 - ‖windowSum T x t‖ ^ 2)|
        + |(∫ t in Iic 0, ‖windowSum T x t‖ ^ 2) + ∫ t in Ioi T, ‖windowSum T x t‖ ^ 2| :=
        abs_sub _ _
    _ ≤ 393216 * x * truncationLog T ^ 2 * Real.log (1 + T)
        + 2 * (65536 * x * (2 * truncationLog T ^ 2 + 64)) := by
        gcongr
        rw [abs_of_nonneg (by linarith)]
        linarith
    _ = 131072 * x * (truncationLog T ^ 2 * (3 * Real.log (1 + T) + 2) + 64) := by ring

/-- The window sum is the finite-family Lorentzian zero sum, so `∫_ℝ |S_T|² = (π/2) Re F(x,T)`. -/
theorem integral_normSq_windowSum_eq (hx : 1 ≤ x) (T : ℝ) :
    ∫ t : ℝ, ‖windowSum T x t‖ ^ 2
      = (Real.pi / 2) * (montgomeryForm (zeroWindow T) (fun q : XiZeroCopy => (q.1 : ℂ)) x).re := by
  rw [montgomeryForm_re_eq_integral_height _ _ (by linarith)
    (fun q _ => ⟨xiZeroCopy_re_pos q, xiZeroCopy_re_lt_one q⟩)]
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  have : (fun t : ℝ => ‖lorentzZeroSum (zeroWindow T) (fun q : XiZeroCopy => (q.1 : ℂ)) x t‖ ^ 2)
      = fun t => ‖windowSum T x t‖ ^ 2 := by
    funext t; rw [lorentzZeroSum_zeroWindow]; rfl
  rw [this]
  field_simp

/-- **BGSTB Lemma 4, crude form.**  `∫_0^T |S(x,t)|² dt = (π/2) F(x,T) + O(x L² log T)`. -/
theorem integral_normSq_lorentzZeroSumAll_sub_montgomeryForm_le (hx : 1 ≤ x) (hT : 0 ≤ T) :
    |(∫ t in Icc 0 T, ‖lorentzZeroSumAll x t‖ ^ 2)
        - (Real.pi / 2) * (montgomeryForm (zeroWindow T) (fun q : XiZeroCopy => (q.1 : ℂ)) x).re|
      ≤ 131072 * x * (truncationLog T ^ 2 * (3 * Real.log (1 + T) + 2) + 64) := by
  rw [← integral_normSq_windowSum_eq hx T]
  exact integral_normSq_lorentzZeroSumAll_sub_le hx hT

/-- The zero side of Montgomery's lemma has `‖Σ_ρ 2x^ρ/((ρ−a_t)(ρ−b_t))‖² = 4x ‖S(x,t)‖²`. -/
theorem normSq_tsum_montgomeryZeroTerm (hx : 1 ≤ x) (t : ℝ) :
    ‖∑' q : XiZeroCopy, montgomeryZeroTerm x t q‖ ^ 2 = 4 * x * ‖lorentzZeroSumAll x t‖ ^ 2 := by
  rw [tsum_montgomeryZeroTerm_eq hx t, norm_mul, norm_mul, mul_pow, mul_pow,
    Complex.norm_cpow_eq_rpow_re_of_pos (by linarith)]
  simp only [Complex.ofReal_re, norm_neg, Complex.norm_ofNat]
  rw [← Real.sqrt_eq_rpow, Real.sq_sqrt (by linarith)]
  ring

end

end RHTower
