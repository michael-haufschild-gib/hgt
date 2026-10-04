import GaloisForLFunctions.RHTower.LiClockThetaInverseClass

/-!
# Exact ratios of the literal theta forcing and the inverse-shape obstruction

At the odd degree `2j-1` the derivative forcing `g = -J_S'` and the kernel `K` have coefficients in
the exact ratio `α_j = 2jω² + M₀ - δ_j`, `δ_j = ν_{j+1}/((2j+1)ν_j)`.  The score recurrence gives
`0 < δ_j ≤ 16/303 + 1/(303(2j+1)) ≤ 49/909` (`j ≥ 1`), so the ratios increase with uniform increment
`α_{j+1} - α_j = 2ω² + δ_j - δ_{j+1} > 6047/22725`, and `α_1 = 2ω² + 2M₁/M₀ > 8/25`.  Hence `g/K` is
strictly increasing on positive clocks and `g'K - gK' > 0`.

These properties do not orient the inverse.  With `h = K + tK'` (response `F`), every input
`A(K + εh)` has coefficient ratios `A(1 + 2jε)`, strictly increasing pointwise ratio to `K`, and
response `A(r + εF)` in the strict sub-`1/300` class; at a negative clock of `r` and small `ε` the
response is negative while the input keeps the actual slope `g'(0)` and the floor `α₁K > K/4`.

Finally the first-crossing laws of the actual history `y = -S`: `y + K ⋆ y = g` and
`y' = g' - K' ⋆ y`.
-/

open Set Filter Topology MeasureTheory GaloisForLFunctions.HTGeometry
open scoped ContDiff

noncomputable section

namespace RHTower

/-! ## The exact coefficient ratios -/

/-- `δ_j = ν_{j+1}/((2j+1)ν_j)`. -/
def liClockThetaMomentRatio (j : ℕ) : ℝ :=
  thetaCuspNormalizedEvenMoment (j + 1) / ((2 * j + 1) * thetaCuspNormalizedEvenMoment j)

/-- `α_j = 2jω² + M₀ - δ_j`, the ratio of the degree-`(2j-1)` coefficients of `g` and `K`. -/
def liClockThetaForcingRatio (j : ℕ) : ℝ :=
  2 * j * liEvenCrossActualClockGreenRate ^ 2 + normalizedPrimeArchMoment 0 -
    liClockThetaMomentRatio j

theorem neg_liClockThetaForcingTaylorCoeff_eq (j : ℕ) :
    -liClockThetaForcingTaylorCoeff j = liClockThetaForcingRatio j * liClockThetaGeneratorCoeff j := by
  have hν := (thetaCuspNormalizedEvenMoment_pos j).ne'
  have hf0 : ((2 * j).factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have hj1 : (2 * (j : ℝ) + 1) ≠ 0 := by positivity
  unfold liClockThetaForcingTaylorCoeff liClockThetaForcingCoeff liClockThetaForcingRatio
    liClockThetaMomentRatio liClockThetaGeneratorCoeff
  field_simp
  ring

theorem liClockThetaMomentRatio_pos (j : ℕ) : 0 < liClockThetaMomentRatio j :=
  div_pos (thetaCuspNormalizedEvenMoment_pos _)
    (mul_pos (by positivity) (thetaCuspNormalizedEvenMoment_pos _))

/-- `δ_j ≤ 16/303 + 1/(303(2j+1))`. -/
theorem liClockThetaMomentRatio_le (j : ℕ) :
    liClockThetaMomentRatio j ≤ 16 / 303 + 1 / (303 * (2 * j + 1)) := by
  have hscore := thetaCuspNormalizedEvenMoment_succ_le_score j
  have hν := thetaCuspNormalizedEvenMoment_pos j
  have hpos : (0 : ℝ) < 2 * j + 1 := by positivity
  unfold liClockThetaMomentRatio
  rw [div_le_iff₀ (mul_pos hpos hν)]
  have e : (16 / 303 + 1 / (303 * (2 * (j : ℝ) + 1))) * ((2 * j + 1) *
      thetaCuspNormalizedEvenMoment j) = (32 * j + 17) / 303 * thetaCuspNormalizedEvenMoment j := by
    field_simp; ring
  rw [e]
  linarith

theorem liClockThetaMomentRatio_le_of_one_le {j : ℕ} (hj : 1 ≤ j) :
    liClockThetaMomentRatio j ≤ 49 / 909 := by
  refine (liClockThetaMomentRatio_le j).trans ?_
  have hj' : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have : 1 / (303 * (2 * (j : ℝ) + 1)) ≤ 1 / 909 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  linarith

theorem liClockThetaForcingRatio_succ_sub (j : ℕ) :
    liClockThetaForcingRatio (j + 1) - liClockThetaForcingRatio j =
      2 * liEvenCrossActualClockGreenRate ^ 2 + liClockThetaMomentRatio j -
        liClockThetaMomentRatio (j + 1) := by
  unfold liClockThetaForcingRatio; push_cast; ring

/-- **Uniform increment.**  `α_{j+1} - α_j > 6047/22725` for every `j ≥ 1`. -/
theorem liClockThetaForcingRatio_increment_gt {j : ℕ} (hj : 1 ≤ j) :
    6047 / 22725 < liClockThetaForcingRatio (j + 1) - liClockThetaForcingRatio j := by
  rw [liClockThetaForcingRatio_succ_sub]
  have h1 := liClockThetaMomentRatio_pos j
  have h2 := liClockThetaMomentRatio_le_of_one_le (j := j + 1) (by omega)
  have hω := liEvenCrossActualClockGreenRate_sq_gt
  linarith

theorem liClockThetaForcingRatio_zero : liClockThetaForcingRatio 0 = 0 := by
  unfold liClockThetaForcingRatio liClockThetaMomentRatio
  rw [normalizedPrimeArchMoment_zero_eq_thetaCuspNormalizedEvenMoment,
    thetaCuspNormalizedEvenMoment_zero]
  simp

/-- **Origin ratio.**  `α₁ = 2ω² + 2M₁/M₀ > 8/25`. -/
theorem liClockThetaForcingRatio_one :
    liClockThetaForcingRatio 1 = 2 * liEvenCrossActualClockGreenRate ^ 2 +
      2 * normalizedPrimeArchMoment 1 / normalizedPrimeArchMoment 0 := by
  have hν := (thetaCuspNormalizedEvenMoment_pos 1).ne'
  unfold liClockThetaForcingRatio liClockThetaMomentRatio
  rw [normalizedPrimeArchMoment_one_eq_thetaCuspNormalizedEvenMoment,
    normalizedPrimeArchMoment_zero_eq_thetaCuspNormalizedEvenMoment]
  field_simp
  push_cast
  ring

theorem eight_div_twentyFive_lt_liClockThetaForcingRatio_one :
    8 / 25 < liClockThetaForcingRatio 1 := by
  rw [liClockThetaForcingRatio_one]
  have hM1 := normalizedPrimeArchMoment_one_pos
  have hM0 : 0 < normalizedPrimeArchMoment 0 := by
    rw [normalizedPrimeArchMoment_zero_eq_thetaCuspNormalizedEvenMoment]
    exact thetaCuspNormalizedEvenMoment_pos 1
  have hω := liEvenCrossActualClockGreenRate_sq_gt
  have : 0 < 2 * normalizedPrimeArchMoment 1 / normalizedPrimeArchMoment 0 := by positivity
  linarith

theorem liClockThetaForcingRatio_strictMono : StrictMono liClockThetaForcingRatio := by
  refine strictMono_nat_of_lt_succ fun j => ?_
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · rw [liClockThetaForcingRatio_zero]
    linarith [eight_div_twentyFive_lt_liClockThetaForcingRatio_one]
  · linarith [liClockThetaForcingRatio_increment_gt (j := j) hj]

theorem liClockThetaForcingRatio_pos {j : ℕ} (hj : 1 ≤ j) : 0 < liClockThetaForcingRatio j := by
  have := liClockThetaForcingRatio_strictMono.monotone hj
  linarith [eight_div_twentyFive_lt_liClockThetaForcingRatio_one]

/-! ## Positivity, slope and monotone ratio of `g` -/

/-- `g' = Σ_m (-e_{m+1}) t^{2m}/(2m)!`. -/
def liClockThetaForcingInputDeriv (t : ℝ) : ℝ :=
  evenFactorialSeries (fun m => -liClockThetaForcingTaylorCoeff (m + 1)) t

private theorem hγ : GeometricCoeffBound (fun m => -liClockThetaForcingTaylorCoeff (m + 1))
    ((2 + 2 * liEvenCrossActualClockGreenRate ^ 2 + normalizedPrimeArchMoment 0) * 1) 1 :=
  fun m => by rw [abs_neg]; exact geometricCoeffBound_liClockThetaForcingTaylorCoeff.shift m

private theorem hκ : GeometricCoeffBound (fun m => liClockThetaGeneratorCoeff (m + 1))
    (1 * (32 / 303)) (32 / 303) := geometricCoeffBound_liClockThetaGeneratorCoeff.shift

theorem hasDerivAt_liClockThetaForcingInput (t : ℝ) :
    HasDerivAt liClockThetaForcingInput (liClockThetaForcingInputDeriv t) t :=
  hasDerivAt_oddFactorialSeries (by norm_num) hγ t

theorem liClockThetaForcingInput_coeff_pos (m : ℕ) : 0 < -liClockThetaForcingTaylorCoeff (m + 1) := by
  rw [neg_liClockThetaForcingTaylorCoeff_eq]
  exact mul_pos (liClockThetaForcingRatio_pos (by omega)) (liClockThetaGeneratorCoeff_pos _)

/-- `g' > 0` at every real clock. -/
theorem liClockThetaForcingInputDeriv_pos (t : ℝ) : 0 < liClockThetaForcingInputDeriv t := by
  unfold liClockThetaForcingInputDeriv evenFactorialSeries
  refine (summable_evenFactorialSeries_term (by norm_num) hγ t).tsum_pos (fun m => ?_) 0 ?_
  · have := liClockThetaForcingInput_coeff_pos m
    rw [pow_mul]; positivity
  · simpa using liClockThetaForcingInput_coeff_pos 0

theorem liClockThetaForcingInput_zero : liClockThetaForcingInput 0 = 0 :=
  oddFactorialSeries_zero _

theorem liClockThetaForcingInput_pos {t : ℝ} (ht : 0 < t) : 0 < liClockThetaForcingInput t :=
  (div_pos (liClockThetaKernel_pos ht) (by norm_num)).trans (liClockThetaForcingInput_gt ht)

/-- **Actual slopes.**  `a = g'(0) = ω²M₀ + M₁` and `b = K'(0) = ν₁/2 = M₀/2`. -/
theorem liClockThetaForcingInputDeriv_zero :
    liClockThetaForcingInputDeriv 0 =
      liEvenCrossActualClockGreenRate ^ 2 * normalizedPrimeArchMoment 0 +
        normalizedPrimeArchMoment 1 := by
  have hM0 : normalizedPrimeArchMoment 0 ≠ 0 := by
    rw [normalizedPrimeArchMoment_zero_eq_thetaCuspNormalizedEvenMoment]
    exact (thetaCuspNormalizedEvenMoment_pos 1).ne'
  unfold liClockThetaForcingInputDeriv
  rw [evenFactorialSeries_zero, zero_add, neg_liClockThetaForcingTaylorCoeff_eq,
    liClockThetaForcingRatio_one, liClockThetaGeneratorCoeff_one,
    ← normalizedPrimeArchMoment_zero_eq_thetaCuspNormalizedEvenMoment]
  field_simp

theorem liClockThetaKernelDeriv_zero :
    liClockThetaKernelDeriv 0 = thetaCuspNormalizedEvenMoment 1 / 2 := by
  unfold liClockThetaKernelDeriv
  rw [evenFactorialSeries_zero, zero_add, liClockThetaGeneratorCoeff_one]

private theorem ratio_mono_coeff (i j : ℕ) (hij : i ≤ j) :
    -liClockThetaForcingTaylorCoeff (i + 1) * liClockThetaGeneratorCoeff (j + 1) ≤
      -liClockThetaForcingTaylorCoeff (j + 1) * liClockThetaGeneratorCoeff (i + 1) := by
  rw [neg_liClockThetaForcingTaylorCoeff_eq, neg_liClockThetaForcingTaylorCoeff_eq]
  have h := liClockThetaForcingRatio_strictMono.monotone (by omega : i + 1 ≤ j + 1)
  have hc := mul_pos (liClockThetaGeneratorCoeff_pos (i + 1)) (liClockThetaGeneratorCoeff_pos (j + 1))
  nlinarith

private theorem ratio_strict_coeff :
    -liClockThetaForcingTaylorCoeff (0 + 1) * liClockThetaGeneratorCoeff (1 + 1) <
      -liClockThetaForcingTaylorCoeff (1 + 1) * liClockThetaGeneratorCoeff (0 + 1) := by
  rw [neg_liClockThetaForcingTaylorCoeff_eq, neg_liClockThetaForcingTaylorCoeff_eq]
  have h := liClockThetaForcingRatio_strictMono (show 0 + 1 < 1 + 1 by norm_num)
  have hc := mul_pos (liClockThetaGeneratorCoeff_pos (0 + 1)) (liClockThetaGeneratorCoeff_pos (1 + 1))
  nlinarith

/-- **Strictly increasing pointwise ratio.**  `g/K` is strictly increasing on positive clocks. -/
theorem liClockThetaForcingInput_div_kernel_strictMonoOn :
    StrictMonoOn (fun t => liClockThetaForcingInput t / liClockThetaKernel t) (Ioi 0) := by
  intro s hs t _ hst
  have hs' : (0 : ℝ) < s := hs
  have h := oddFactorialSeries_ratio_strictMono (by norm_num) (by norm_num) hγ hκ
    (fun j => liClockThetaGeneratorCoeff_pos _) ratio_mono_coeff (by norm_num : 0 < 1)
    ratio_strict_coeff hs' hst
  have hKs := liClockThetaKernel_pos hs'
  have hKt := liClockThetaKernel_pos (hs'.trans hst)
  rw [div_lt_div_iff₀ hKs hKt]
  exact h

/-- **Strict derivative cross inequality.**  `g'K - gK' > 0` on positive clocks. -/
theorem liClockThetaForcingInput_deriv_cross_pos {t : ℝ} (ht : 0 < t) :
    0 < liClockThetaForcingInputDeriv t * liClockThetaKernel t -
      liClockThetaForcingInput t * liClockThetaKernelDeriv t := by
  have h := oddFactorialSeries_deriv_cross_pos (by norm_num) (by norm_num) hγ hκ ratio_mono_coeff
    (by norm_num : 0 < 1) ratio_strict_coeff ht
  unfold liClockThetaForcingInputDeriv liClockThetaForcingInput liClockThetaKernelDeriv
    liClockThetaKernel
  linarith

/-! ## Growth-class closure under linear combinations -/

theorem LiClockEveryExpType.add {f g : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hf' : LiClockEveryExpType f) (hg' : LiClockEveryExpType g) :
    LiClockEveryExpType fun t => f t + g t := by
  intro ε hε m
  obtain ⟨C, hC⟩ := hf' ε hε m
  obtain ⟨D, hD⟩ := hg' ε hε m
  refine ⟨C + D, fun t => ?_⟩
  have e := iteratedDeriv_add (n := m) (x := t) (hf.contDiffAt.of_le (natCast_lt_infty m).le)
    (hg.contDiffAt.of_le (natCast_lt_infty m).le)
  rw [show (fun t => f t + g t) = f + g from rfl, e]
  calc |iteratedDeriv m f t + iteratedDeriv m g t| ≤ |iteratedDeriv m f t| + |iteratedDeriv m g t| :=
        abs_add_le _ _
    _ ≤ C * Real.exp (ε * |t|) + D * Real.exp (ε * |t|) := add_le_add (hC t) (hD t)
    _ = (C + D) * Real.exp (ε * |t|) := by ring

theorem LiClockEveryExpType.const_mul (c : ℝ) {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hf' : LiClockEveryExpType f) : LiClockEveryExpType fun t => c * f t := by
  intro ε hε m
  obtain ⟨C, hC⟩ := hf' ε hε m
  refine ⟨|c| * C, fun t => ?_⟩
  rw [iteratedDeriv_const_mul c (hf.contDiffAt.of_le (natCast_lt_infty m).le), abs_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (hC t) (abs_nonneg c)

/-! ## The inverse-shape obstruction -/

/-- The shape input `A(K + εh)`, `h = K + tK'`. -/
def liClockThetaShapeInput (A ε : ℝ) (t : ℝ) : ℝ :=
  A * (liClockThetaKernel t + ε * liClockThetaClockInput t)

/-- The shape response `A(r + εF)`. -/
def liClockThetaShapeResponse (A ε : ℝ) (t : ℝ) : ℝ :=
  A * (liClockThetaResolvent t + ε * liEvenCrossActualClockResponse t)

theorem liClockThetaShapeResponse_volterra (A ε t : ℝ) :
    liClockThetaShapeResponse A ε t +
        volterraConv (liClockThetaShapeResponse A ε) liClockThetaKernel t =
      liClockThetaShapeInput A ε t := by
  have hr := continuous_liClockThetaResolvent
  have hF : Continuous liEvenCrossActualClockResponse := continuous_liEvenCrossActualClockResponse
  have hK := continuous_liClockThetaKernel
  have hlin : volterraConv (liClockThetaShapeResponse A ε) liClockThetaKernel t =
      A * (volterraConv liClockThetaResolvent liClockThetaKernel t +
        ε * volterraConv liEvenCrossActualClockResponse liClockThetaKernel t) := by
    unfold liClockThetaShapeResponse
    rw [volterraConv_smul_left, volterraConv_comm, show (fun s => liClockThetaResolvent s +
      ε * liEvenCrossActualClockResponse s) = liClockThetaResolvent +
        fun s => ε * liEvenCrossActualClockResponse s from rfl,
      volterraConv_add_right hK hr (hF.const_mul ε), volterraConv_smul_right,
      volterraConv_comm liClockThetaKernel, volterraConv_comm liClockThetaKernel]
  rw [hlin]
  unfold liClockThetaShapeResponse liClockThetaShapeInput
  have h1 := liClockThetaResolvent_volterra t
  have h2 := liEvenCrossActualClockResponse_volterra_kernel t
  linear_combination A * h1 + A * ε * h2

theorem liClockThetaShapeInput_eq_oddFactorialSeries (A ε : ℝ) :
    liClockThetaShapeInput A ε =
      oddFactorialSeries fun m => A * (1 + ε * (2 * m + 2)) * liClockThetaGeneratorCoeff (m + 1) := by
  funext t
  have hb : GeometricCoeffBound (fun m => (2 * (m : ℝ) + 2) * liClockThetaGeneratorCoeff (m + 1))
      (2 * (1 / 2) ^ 2 * Real.exp (32 / (303 * (1 / 2) ^ 2))) 1 := fun m => by
    have := abs_kernelClockCoeff_le_pow (ρ := 1 / 2) (by norm_num) m
    simpa using this
  have h1 := (summable_oddFactorialSeries_term (by norm_num) hκ t).hasSum
  have h2 := (summable_oddFactorialSeries_term (by norm_num) hb t).hasSum
  unfold liClockThetaShapeInput
  rw [liClockThetaClockInput_eq_oddFactorialSeries]
  unfold liClockThetaKernel oddFactorialSeries
  rw [← ((h1.add (h2.mul_left ε)).mul_left A).tsum_eq]
  exact tsum_congr fun m => by ring

private theorem hφ (A ε : ℝ) : GeometricCoeffBound
    (fun m => A * (1 + ε * (2 * m + 2)) * liClockThetaGeneratorCoeff (m + 1))
    (|A| * (1 + |ε|) * (2 * (1 / 2) ^ 2 * Real.exp (32 / (303 * (1 / 2) ^ 2)) + 1)) 1 := by
  intro m
  have hc := (liClockThetaGeneratorCoeff_pos (m + 1)).le
  have h1 : (2 * (m : ℝ) + 2) * liClockThetaGeneratorCoeff (m + 1) ≤
      2 * (1 / 2) ^ 2 * Real.exp (32 / (303 * (1 / 2) ^ 2)) := by
    have := abs_kernelClockCoeff_le_pow (ρ := 1 / 2) (by norm_num) m
    rw [show (2 : ℝ) * (1 / 2) = 1 by norm_num, one_pow, mul_one,
      abs_of_nonneg (by positivity)] at this
    exact this
  have hc1 : liClockThetaGeneratorCoeff (m + 1) ≤ 1 := by
    refine (liClockThetaGeneratorCoeff_le _).trans ?_
    rw [div_le_one (by exact_mod_cast Nat.factorial_pos _)]
    exact (pow_le_one₀ (by norm_num) (by norm_num)).trans
      (by exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.factorial_ne_zero _))
  simp only [one_pow, mul_one]
  rw [abs_mul, abs_mul, abs_of_nonneg hc]
  have hE : 0 ≤ 2 * (1 / 2 : ℝ) ^ 2 * Real.exp (32 / (303 * (1 / 2) ^ 2)) := by positivity
  have h3 : |1 + ε * (2 * (m : ℝ) + 2)| * liClockThetaGeneratorCoeff (m + 1) ≤
      (1 + |ε|) * (2 * (1 / 2) ^ 2 * Real.exp (32 / (303 * (1 / 2) ^ 2)) + 1) := by
    calc |1 + ε * (2 * (m : ℝ) + 2)| * liClockThetaGeneratorCoeff (m + 1) ≤
        (1 + |ε| * (2 * (m : ℝ) + 2)) * liClockThetaGeneratorCoeff (m + 1) := by
          refine mul_le_mul_of_nonneg_right ?_ hc
          refine (abs_add_le _ _).trans ?_
          rw [abs_one, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * (m : ℝ) + 2)]
      _ = liClockThetaGeneratorCoeff (m + 1) +
          |ε| * ((2 * (m : ℝ) + 2) * liClockThetaGeneratorCoeff (m + 1)) := by ring
      _ ≤ 1 + |ε| * (2 * (1 / 2) ^ 2 * Real.exp (32 / (303 * (1 / 2) ^ 2))) := by
          gcongr
      _ ≤ (1 + |ε|) * (2 * (1 / 2) ^ 2 * Real.exp (32 / (303 * (1 / 2) ^ 2)) + 1) := by
          nlinarith [abs_nonneg ε]
  calc |A| * |1 + ε * (2 * (m : ℝ) + 2)| * liClockThetaGeneratorCoeff (m + 1) =
      |A| * (|1 + ε * (2 * (m : ℝ) + 2)| * liClockThetaGeneratorCoeff (m + 1)) := by ring
    _ ≤ |A| * ((1 + |ε|) * (2 * (1 / 2) ^ 2 * Real.exp (32 / (303 * (1 / 2) ^ 2)) + 1)) :=
        mul_le_mul_of_nonneg_left h3 (abs_nonneg A)
    _ = _ := by ring

/-- The shape input's slope at the origin is `A(1 + 2ε) K'(0)`. -/
theorem hasDerivAt_liClockThetaShapeInput_zero (A ε : ℝ) :
    HasDerivAt (liClockThetaShapeInput A ε)
      (A * (1 + 2 * ε) * liClockThetaGeneratorCoeff 1) 0 := by
  rw [liClockThetaShapeInput_eq_oddFactorialSeries]
  have h := hasDerivAt_oddFactorialSeries (by norm_num) (hφ A ε) 0
  rw [evenFactorialSeries_zero] at h
  convert h using 1
  push_cast; ring

/-- The coefficient ratios of the shape input to `K` are `A(1 + 2jε)`, strictly increasing. -/
theorem liClockThetaShapeInput_coeff_ratio (A ε : ℝ) (m : ℕ) :
    A * (1 + ε * (2 * m + 2)) * liClockThetaGeneratorCoeff (m + 1) /
        liClockThetaGeneratorCoeff (m + 1) = A * (1 + ε * (2 * m + 2)) :=
  mul_div_cancel_right₀ _ (liClockThetaGeneratorCoeff_pos _).ne'

/-- **Strictly increasing pointwise ratio of the shape input.** -/
theorem liClockThetaShapeInput_div_kernel_strictMonoOn {A ε : ℝ} (hA : 0 < A) (hε : 0 < ε) :
    StrictMonoOn (fun t => liClockThetaShapeInput A ε t / liClockThetaKernel t) (Ioi 0) := by
  intro s hs t _ hst
  have hs' : (0 : ℝ) < s := hs
  have hmono : ∀ i j : ℕ, i ≤ j → A * (1 + ε * (2 * i + 2)) * liClockThetaGeneratorCoeff (i + 1) *
      liClockThetaGeneratorCoeff (j + 1) ≤ A * (1 + ε * (2 * j + 2)) *
        liClockThetaGeneratorCoeff (j + 1) * liClockThetaGeneratorCoeff (i + 1) := by
    intro i j hij
    have hij' : (i : ℝ) ≤ j := by exact_mod_cast hij
    have hc := mul_pos (liClockThetaGeneratorCoeff_pos (i + 1)) (liClockThetaGeneratorCoeff_pos (j + 1))
    have key : A * (1 + ε * (2 * i + 2)) ≤ A * (1 + ε * (2 * j + 2)) := by
      have : ε * (2 * (i : ℝ) + 2) ≤ ε * (2 * j + 2) := by nlinarith
      nlinarith
    calc A * (1 + ε * (2 * i + 2)) * liClockThetaGeneratorCoeff (i + 1) *
          liClockThetaGeneratorCoeff (j + 1) = (A * (1 + ε * (2 * i + 2))) *
            (liClockThetaGeneratorCoeff (i + 1) * liClockThetaGeneratorCoeff (j + 1)) := by ring
      _ ≤ (A * (1 + ε * (2 * j + 2))) *
            (liClockThetaGeneratorCoeff (i + 1) * liClockThetaGeneratorCoeff (j + 1)) :=
          mul_le_mul_of_nonneg_right key hc.le
      _ = _ := by ring
  have hstr : A * (1 + ε * (2 * ((0 : ℕ) : ℝ) + 2)) * liClockThetaGeneratorCoeff (0 + 1) *
      liClockThetaGeneratorCoeff (1 + 1) < A * (1 + ε * (2 * ((1 : ℕ) : ℝ) + 2)) *
        liClockThetaGeneratorCoeff (1 + 1) * liClockThetaGeneratorCoeff (0 + 1) := by
    have hc := mul_pos (liClockThetaGeneratorCoeff_pos (0 + 1)) (liClockThetaGeneratorCoeff_pos (1 + 1))
    push_cast
    nlinarith [mul_pos hA hε]
  have h := oddFactorialSeries_ratio_strictMono (by norm_num) (by norm_num) (hφ A ε) hκ
    (fun j => liClockThetaGeneratorCoeff_pos _) hmono (by norm_num : 0 < 1) hstr hs' hst
  have hKs := liClockThetaKernel_pos hs'
  have hKt := liClockThetaKernel_pos (hs'.trans hst)
  simp only [liClockThetaShapeInput_eq_oddFactorialSeries]
  rw [div_lt_div_iff₀ hKs hKt]
  exact h

/-- The shape input dominates `A(1 + 2ε) K` on nonnegative clocks. -/
theorem liClockThetaShapeInput_ge {A ε : ℝ} (hA : 0 < A) (hε : 0 < ε) {t : ℝ} (ht : 0 ≤ t) :
    A * (1 + 2 * ε) * liClockThetaKernel t ≤ liClockThetaShapeInput A ε t := by
  have hcb : GeometricCoeffBound (fun m => A * (1 + 2 * ε) * liClockThetaGeneratorCoeff (m + 1))
      (A * (1 + 2 * ε) * (1 * (32 / 303))) (32 / 303) := fun m => by
    have hc := (liClockThetaGeneratorCoeff_pos (m + 1)).le
    have hk := hκ m
    simp only [abs_of_nonneg hc] at hk
    rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ A * (1 + 2 * ε) *
      liClockThetaGeneratorCoeff (m + 1))]
    calc A * (1 + 2 * ε) * liClockThetaGeneratorCoeff (m + 1) ≤
        A * (1 + 2 * ε) * (1 * (32 / 303) * (32 / 303) ^ m) :=
          mul_le_mul_of_nonneg_left hk (by positivity)
      _ = _ := by ring
  have h := oddFactorialSeries_le_of_le (by norm_num) (by norm_num) hcb (hφ A ε) (fun m => by
    have hc := (liClockThetaGeneratorCoeff_pos (m + 1)).le
    have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    have key : A * (1 + 2 * ε) ≤ A * (1 + ε * (2 * m + 2)) := by
      have : 2 * ε ≤ ε * (2 * (m : ℝ) + 2) := by nlinarith
      nlinarith
    exact mul_le_mul_of_nonneg_right key hc) ht
  have e : oddFactorialSeries (fun m => A * (1 + 2 * ε) * liClockThetaGeneratorCoeff (m + 1)) t =
      A * (1 + 2 * ε) * liClockThetaKernel t := by
    unfold liClockThetaKernel oddFactorialSeries
    rw [← tsum_mul_left]
    exact tsum_congr fun j => by ring
  rw [e, ← liClockThetaShapeInput_eq_oddFactorialSeries] at h
  exact h

theorem contDiff_liClockThetaShapeInput (A ε : ℝ) : ContDiff ℝ ∞ (liClockThetaShapeInput A ε) := by
  rw [liClockThetaShapeInput_eq_oddFactorialSeries]
  exact contDiff_oddFactorialSeries (by norm_num) (hφ A ε)

theorem liClockEveryExpType_liClockThetaShapeInput (A ε : ℝ) :
    LiClockEveryExpType (liClockThetaShapeInput A ε) := by
  have hK := liClockEveryExpType_liClockThetaKernel
  have hh := liClockEveryExpType_liClockThetaClockInput
  have h1 := LiClockEveryExpType.const_mul ε contDiff_liClockThetaClockInput hh
  have h2 := LiClockEveryExpType.add contDiff_liClockThetaKernel
    (contDiff_const.mul contDiff_liClockThetaClockInput) hK h1
  exact LiClockEveryExpType.const_mul A
    (contDiff_liClockThetaKernel.add (contDiff_const.mul contDiff_liClockThetaClockInput)) h2

/-- The shape response is the causal inverse of the shape input and lies in the strict
sub-`1/300` class. -/
theorem liClockSubGammaClass_liClockThetaShapeResponse (A ε : ℝ) :
    LiClockSubGammaClass (liClockThetaShapeResponse A ε) := by
  have hcont : Continuous (liClockThetaShapeResponse A ε) := by
    unfold liClockThetaShapeResponse
    exact (continuous_liClockThetaResolvent.add
      (continuous_liEvenCrossActualClockResponse.const_mul ε)).const_mul A
  have heq := eq_liClockThetaInverse (y := liClockThetaShapeResponse A ε)
    (contDiff_liClockThetaShapeInput A ε).continuous hcont (liClockThetaShapeResponse_volterra A ε)
  rw [heq]
  exact liClockSubGammaClass_liClockThetaInverse (contDiff_liClockThetaShapeInput A ε)
    (liClockEveryExpType_liClockThetaShapeInput A ε)

/-- **Inverse-shape obstruction.**  For some positive clock `T` and `ε > 0`, the input
`A(K + εh)`, `A = g'(0)/(K'(0)(1 + 2ε))`, has the actual slope `g'(0)`, strictly increasing
coefficient and pointwise ratios to `K`, the floor `α₁K > K/4`, and its causal inverse
`A(r + εF)` (strict sub-`1/300` class) is negative at `T`. -/
theorem exists_liClockThetaShapeCounterInput :
    ∃ T : ℝ, 0 < T ∧ ∃ ε : ℝ, 0 < ε ∧
      liClockThetaShapeResponse
        (liClockThetaForcingInputDeriv 0 / (liClockThetaGeneratorCoeff 1 * (1 + 2 * ε))) ε T < 0 ∧
      HasDerivAt (liClockThetaShapeInput
        (liClockThetaForcingInputDeriv 0 / (liClockThetaGeneratorCoeff 1 * (1 + 2 * ε))) ε)
        (liClockThetaForcingInputDeriv 0) 0 ∧
      StrictMonoOn (fun t => liClockThetaShapeInput
        (liClockThetaForcingInputDeriv 0 / (liClockThetaGeneratorCoeff 1 * (1 + 2 * ε))) ε t /
          liClockThetaKernel t) (Ioi 0) ∧
      (∀ t, 0 ≤ t → liClockThetaForcingRatio 1 * liClockThetaKernel t ≤ liClockThetaShapeInput
        (liClockThetaForcingInputDeriv 0 / (liClockThetaGeneratorCoeff 1 * (1 + 2 * ε))) ε t) ∧
      (∀ t, 0 < t → liClockThetaKernel t / 4 < liClockThetaShapeInput
        (liClockThetaForcingInputDeriv 0 / (liClockThetaGeneratorCoeff 1 * (1 + 2 * ε))) ε t) ∧
      LiClockSubGammaClass (liClockThetaShapeResponse
        (liClockThetaForcingInputDeriv 0 / (liClockThetaGeneratorCoeff 1 * (1 + 2 * ε))) ε) := by
  obtain ⟨T, hT, hrT⟩ := exists_liClockThetaResolvent_neg
  set F := liEvenCrossActualClockResponse T
  set ε := -liClockThetaResolvent T / (2 * (|F| + 1)) with hεdef
  have hε : 0 < ε := div_pos (by linarith) (by positivity)
  have hc1 := liClockThetaGeneratorCoeff_pos 1
  have ha := liClockThetaForcingInputDeriv_pos 0
  set A := liClockThetaForcingInputDeriv 0 / (liClockThetaGeneratorCoeff 1 * (1 + 2 * ε)) with hAdef
  have hA : 0 < A := div_pos ha (by positivity)
  have hAε : A * (1 + 2 * ε) = liClockThetaForcingRatio 1 := by
    have h1 : liClockThetaForcingInputDeriv 0 =
        liClockThetaForcingRatio 1 * liClockThetaGeneratorCoeff 1 := by
      unfold liClockThetaForcingInputDeriv
      rw [evenFactorialSeries_zero, zero_add, neg_liClockThetaForcingTaylorCoeff_eq]
    rw [hAdef, h1]
    field_simp
  refine ⟨T, hT, ε, hε, ?_, ?_, liClockThetaShapeInput_div_kernel_strictMonoOn hA hε, ?_, ?_,
    liClockSubGammaClass_liClockThetaShapeResponse A ε⟩
  · unfold liClockThetaShapeResponse
    have hεF : ε * F ≤ ε * |F| := mul_le_mul_of_nonneg_left (le_abs_self F) hε.le
    have hεF' : ε * |F| < -liClockThetaResolvent T / 2 := by
      rw [hεdef, div_mul_eq_mul_div, div_lt_div_iff₀ (by positivity) (by norm_num)]
      nlinarith [abs_nonneg F]
    exact mul_neg_of_pos_of_neg hA (by linarith)
  · have h := hasDerivAt_liClockThetaShapeInput_zero A ε
    convert h using 1
    rw [hAdef]
    field_simp
  · intro t ht
    rw [← hAε]
    exact liClockThetaShapeInput_ge hA hε ht
  · intro t ht
    have h := liClockThetaShapeInput_ge hA hε ht.le
    rw [hAε] at h
    have hK := liClockThetaKernel_pos ht
    have h1 := eight_div_twentyFive_lt_liClockThetaForcingRatio_one
    nlinarith

/-! ## First-crossing laws of the actual history -/

theorem neg_liEvenCrossActualClockMassiveSource_volterra (t : ℝ) :
    -liEvenCrossActualClockMassiveSource t +
        volterraConv liClockThetaKernel (fun s => -liEvenCrossActualClockMassiveSource s) t =
      liClockThetaForcingInput t := by
  have h := liEvenCrossActualClockMassiveSource_volterra t
  rw [volterraConv_neg_right]
  linarith

/-- **History law at a zero.**  If `y = -S` vanishes at `T` then `g(T) = (y ⋆ K)(T)`. -/
theorem liClockThetaForcingInput_eq_history_of_zero {T : ℝ}
    (hT : liEvenCrossActualClockMassiveSource T = 0) :
    liClockThetaForcingInput T =
      volterraConv (fun s => -liEvenCrossActualClockMassiveSource s) liClockThetaKernel T := by
  have h := neg_liEvenCrossActualClockMassiveSource_volterra T
  rw [hT, neg_zero, zero_add, volterraConv_comm] at h
  exact h.symm

/-- **Derivative history law.**  `y' = g' - y ⋆ K'` at every real clock (`K(0) = 0`). -/
theorem hasDerivAt_neg_liEvenCrossActualClockMassiveSource (T : ℝ) :
    HasDerivAt (fun t => -liEvenCrossActualClockMassiveSource t)
      (liClockThetaForcingInputDeriv T -
        volterraConv (fun s => -liEvenCrossActualClockMassiveSource s) liClockThetaKernelDeriv T) T := by
  have hy : Continuous fun s => -liEvenCrossActualClockMassiveSource s :=
    continuous_liEvenCrossActualClockMassiveSource.neg
  have h1 := hasDerivAt_volterraConv (f := liClockThetaKernel) (f' := liClockThetaKernelDeriv)
    (g := fun s => -liEvenCrossActualClockMassiveSource s) hasDerivAt_liClockThetaKernel
    (continuous_iff_continuousAt.2 fun t => (hasDerivAt_liClockThetaKernelDeriv t).continuousAt)
    hy T
  have hK0 : liClockThetaKernel 0 = 0 := by simp [liClockThetaKernel, oddFactorialSeries_zero]
  rw [hK0, zero_mul, zero_add] at h1
  have h2 := (hasDerivAt_liClockThetaForcingInput T).sub h1
  have h3 : (fun t => -liEvenCrossActualClockMassiveSource t) =ᶠ[𝓝 T]
      (liClockThetaForcingInput -
        volterraConv liClockThetaKernel fun s => -liEvenCrossActualClockMassiveSource s) :=
    Eventually.of_forall fun t => by
      simp only [Pi.sub_apply]
      linarith [neg_liEvenCrossActualClockMassiveSource_volterra t]
  rw [volterraConv_comm (fun s => -liEvenCrossActualClockMassiveSource s)]
  exact h2.congr_of_eventuallyEq h3

end RHTower
