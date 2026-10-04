import GaloisForLFunctions.RHTower.LiClockThetaGeneratorLogSlope
import GaloisForLFunctions.RHTower.LiClockThetaForcingHistoryMajorant
import GaloisForLFunctions.RHTower.LiEvenCrossActualClockBorelCorrection
import GaloisForLFunctions.RHTower.PrimeArchThetaThermalSusceptibility

/-!
# The exact theta ratio band and its correction inverse

**Narrowing band.**  Likelihood order of the first theta atom gives `δ_j ≤ δ^{(1)}_j`, the first-atom
adjacent ratio, and the first atom's Ward identity with an arbitrarily coercive score gives
`δ^{(1)}_j ≤ 1/(2H) + C_H/(H(2j+1))` for every `H > 0`.  Hence `δ_j → 0`, so
`α_j - 2jω² → M₀` and `α_{j+1} - α_j → 2ω²`.

**Correction.**  With `h = K + tK'`, the correction `D = h'' = Σ_j δ_j k_j t^{2j-1}` satisfies
`g = ω²h + M₀K - D`, `0 < D ≤ (49/909) K` on positive clocks and `D/K → 0`.

**Correction inverse.**  Twice differentiating `F + F ⋆ K = h` gives `F'' + F'' ⋆ K = D - M₀K`, so
`v = F'' + M₀ r` solves `v + v ⋆ K = D`, i.e. `v = D - r ⋆ D`, and `-S = ω²F + M₀ r - v`.  Its slope
at the origin is `v'(0) = M₀²/2 - M₁ = ν₂/6 > 0`.  Nevertheless `v` is negative at arbitrarily large
clocks: if `v ≥ 0` after some clock, then `v ≤ D + C K` there, its Laplace transform equals
`W(1/p)`, `W(z) = (Φ'(z)/z - M₀)/Φ(z)`, and the compact-prefix estimate
`v̂(q) ≤ v̂(p) + (q - p) ∫_0^T t|v|` forces `z W(z)` bounded, whereas `W(z) → 0` and
`zW(z) = Φ'(z)/Φ(z) - M₀z/Φ(z) → ∞`.
-/

open Set Filter Topology MeasureTheory GaloisForLFunctions.HTGeometry
open scoped ContDiff

noncomputable section

namespace RHTower

/-! ## The first-atom ratio transfer and the narrowing band -/

/-- The first-atom adjacent ratio `δ^{(1)}_j = A_{j+1}/((2j+1) A_j)`. -/
def liClockThetaFirstAtomMomentRatio (j : ℕ) : ℝ :=
  thetaCuspAtomRawEvenMoment (j + 1) 1 / ((2 * j + 1) * thetaCuspAtomRawEvenMoment j 1)

theorem liClockThetaMomentRatio_eq_raw (j : ℕ) :
    liClockThetaMomentRatio j =
      thetaCuspRawEvenMoment (j + 1) / ((2 * j + 1) * thetaCuspRawEvenMoment j) := by
  have h0 := (thetaCuspRawEvenMoment_pos 0).ne'
  have hj := (thetaCuspRawEvenMoment_pos j).ne'
  unfold liClockThetaMomentRatio thetaCuspNormalizedEvenMoment
  field_simp

/-- **Likelihood transfer.**  `δ_j ≤ δ^{(1)}_j`. -/
theorem liClockThetaMomentRatio_le_firstAtom (j : ℕ) :
    liClockThetaMomentRatio j ≤ liClockThetaFirstAtomMomentRatio j := by
  have h := thetaCuspRawFirst_rawEvenMoment_cross_le j 1
  have hA := thetaCuspAtomRawEvenMoment_pos_of_nat_pos j one_pos
  have hR := thetaCuspRawEvenMoment_pos j
  have hj : (0 : ℝ) < 2 * j + 1 := by positivity
  rw [liClockThetaMomentRatio_eq_raw]
  unfold liClockThetaFirstAtomMomentRatio
  rw [div_le_div_iff₀ (mul_pos hj hR) (mul_pos hj hA)]
  nlinarith

/-- **Ward fence.**  For every `H > 0` some `C ≥ 0` gives
`δ^{(1)}_j ≤ 1/(2H) + C/(H(2j+1))` for all `j`. -/
theorem exists_liClockThetaFirstAtomMomentRatio_le {H : ℝ} (hH : 0 < H) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ j : ℕ,
      liClockThetaFirstAtomMomentRatio j ≤ 1 / (2 * H) + C / (H * (2 * j + 1)) := by
  obtain ⟨C, hC, h⟩ := thetaCuspFirstAtomRawEvenMoment_arbitrarySlope hH
  refine ⟨C, hC, fun j => ?_⟩
  have hA := thetaCuspAtomRawEvenMoment_pos_of_nat_pos j one_pos
  have hj : (0 : ℝ) < 2 * j + 1 := by positivity
  have hj' := h j
  push_cast at hj'
  unfold liClockThetaFirstAtomMomentRatio
  rw [div_le_iff₀ (mul_pos hj hA)]
  have e : (1 / (2 * H) + C / (H * (2 * j + 1))) * ((2 * j + 1) * thetaCuspAtomRawEvenMoment j 1) =
      ((2 * j + 1) / 2 + C) * thetaCuspAtomRawEvenMoment j 1 / H := by
    field_simp
  rw [e, le_div_iff₀ hH]
  linarith

/-- **Narrowing band.**  `α_j - 2jω² → M₀` and `α_{j+1} - α_j → 2ω²`. -/
theorem tendsto_liClockThetaForcingRatio_sub :
    Tendsto (fun j : ℕ => liClockThetaForcingRatio j - 2 * j * liEvenCrossActualClockGreenRate ^ 2)
      atTop (𝓝 (normalizedPrimeArchMoment 0)) := by
  have h := (tendsto_const_nhds (x := normalizedPrimeArchMoment 0)).sub tendsto_liClockThetaMomentRatio
  rw [sub_zero] at h
  refine h.congr fun j => ?_
  unfold liClockThetaForcingRatio; ring

theorem tendsto_liClockThetaForcingRatio_increment :
    Tendsto (fun j : ℕ => liClockThetaForcingRatio (j + 1) - liClockThetaForcingRatio j)
      atTop (𝓝 (2 * liEvenCrossActualClockGreenRate ^ 2)) := by
  have h1 := tendsto_liClockThetaMomentRatio
  have h2 := tendsto_liClockThetaMomentRatio.comp (tendsto_add_atTop_nat 1)
  have h := ((tendsto_const_nhds (x := 2 * liEvenCrossActualClockGreenRate ^ 2)).add h1).sub h2
  rw [add_zero, sub_zero] at h
  refine h.congr fun j => ?_
  rw [liClockThetaForcingRatio_succ_sub]
  rfl

/-- The band `2jω² + ν₁ - 49/909 ≤ α_j < 2jω² + ν₁` for `j ≥ 1`. -/
theorem liClockThetaForcingRatio_mem_band {j : ℕ} (hj : 1 ≤ j) :
    2 * j * liEvenCrossActualClockGreenRate ^ 2 + thetaCuspNormalizedEvenMoment 1 - 49 / 909 ≤
        liClockThetaForcingRatio j ∧
      liClockThetaForcingRatio j < 2 * j * liEvenCrossActualClockGreenRate ^ 2 +
        thetaCuspNormalizedEvenMoment 1 := by
  have h1 := liClockThetaMomentRatio_le_of_one_le hj
  have h2 := liClockThetaMomentRatio_pos j
  unfold liClockThetaForcingRatio
  rw [normalizedPrimeArchMoment_zero_eq_thetaCuspNormalizedEvenMoment]
  constructor <;> linarith

/-! ## The correction `D = (K + tK')''` -/

private theorem hκ : GeometricCoeffBound (fun m => liClockThetaGeneratorCoeff (m + 1))
    (1 * (32 / 303)) (32 / 303) := geometricCoeffBound_liClockThetaGeneratorCoeff.shift

private theorem hclock : GeometricCoeffBound
    (fun m => (2 * (m : ℝ) + 2) * liClockThetaGeneratorCoeff (m + 1))
    (2 * (1 / 2) ^ 2 * Real.exp (32 / (303 * (1 / 2) ^ 2))) 1 := fun m => by
  have := abs_kernelClockCoeff_le_pow (ρ := 1 / 2) (by norm_num) m
  rw [show (2 : ℝ) * (1 / 2) = 1 by norm_num, one_pow] at this
  rw [one_pow]
  exact this

theorem liClockThetaClockInput_eq_borelKernel :
    (fun x => deriv liEvenCrossActualClockBorelKernel x +
      x * iteratedDeriv 2 liEvenCrossActualClockBorelKernel x) = liClockThetaClockInput := by
  funext x
  have hd : deriv liEvenCrossActualClockBorelKernel = liClockThetaKernel :=
    funext deriv_liEvenCrossActualClockBorelKernel_eq
  rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one, hd,
    (hasDerivAt_liClockThetaKernel x).deriv]
  rfl

/-- `D = h''`, `h = K + tK'`. -/
theorem liEvenCrossActualClockBorelCorrection_eq_iteratedDeriv (t : ℝ) :
    liEvenCrossActualClockBorelCorrection t = iteratedDeriv 2 liClockThetaClockInput t := by
  unfold liEvenCrossActualClockBorelCorrection
  rw [liClockThetaClockInput_eq_borelKernel]

/-- The correction coefficients `δ_{m+1} c_{m+1}`. -/
def liClockThetaCorrectionCoeff (m : ℕ) : ℝ :=
  liClockThetaMomentRatio (m + 1) * liClockThetaGeneratorCoeff (m + 1)

theorem liClockThetaCorrectionCoeff_pos (m : ℕ) : 0 < liClockThetaCorrectionCoeff m :=
  mul_pos (liClockThetaMomentRatio_pos _) (liClockThetaGeneratorCoeff_pos _)

theorem liClockThetaCorrectionCoeff_le (m : ℕ) :
    liClockThetaCorrectionCoeff m ≤ 49 / 909 * liClockThetaGeneratorCoeff (m + 1) :=
  mul_le_mul_of_nonneg_right (liClockThetaMomentRatio_le_of_one_le (by omega))
    (liClockThetaGeneratorCoeff_pos _).le

private theorem hcorr : GeometricCoeffBound liClockThetaCorrectionCoeff
    (49 / 909 * (1 * (32 / 303))) (32 / 303) := fun m => by
  rw [abs_of_pos (liClockThetaCorrectionCoeff_pos m)]
  refine (liClockThetaCorrectionCoeff_le m).trans ?_
  have := hκ m
  rw [abs_of_pos (liClockThetaGeneratorCoeff_pos _)] at this
  calc 49 / 909 * liClockThetaGeneratorCoeff (m + 1) ≤ 49 / 909 * (1 * (32 / 303) * (32 / 303) ^ m) :=
        mul_le_mul_of_nonneg_left this (by norm_num)
    _ = _ := by ring

/-- **Exact correction series.**  `D = Σ_m δ_{m+1} c_{m+1} t^{2m+1}/(2m+1)!`. -/
theorem liEvenCrossActualClockBorelCorrection_eq_oddFactorialSeries :
    liEvenCrossActualClockBorelCorrection = oddFactorialSeries liClockThetaCorrectionCoeff := by
  funext t
  rw [liEvenCrossActualClockBorelCorrection_eq_iteratedDeriv, liClockThetaClockInput_eq_oddFactorialSeries,
    iteratedDeriv_two_oddFactorialSeries (by norm_num) hclock]
  unfold oddFactorialSeries liClockThetaCorrectionCoeff
  refine tsum_congr fun m => ?_
  rw [liClockThetaMomentRatio_mul_coeff (m + 1)]

theorem liClockThetaKernel_eq_hasSum (t : ℝ) :
    HasSum (fun m => liClockThetaGeneratorCoeff (m + 1) * t ^ (2 * m + 1) /
      ((2 * m + 1).factorial : ℝ)) (liClockThetaKernel t) :=
  (summable_oddFactorialSeries_term (by norm_num) hκ t).hasSum

/-- **Band decomposition of the forcing.**  `g = ω² h + M₀ K - D`. -/
theorem liClockThetaForcingInput_eq_band (t : ℝ) :
    liClockThetaForcingInput t = liEvenCrossActualClockGreenRate ^ 2 * liClockThetaClockInput t +
      normalizedPrimeArchMoment 0 * liClockThetaKernel t - liEvenCrossActualClockBorelCorrection t := by
  have hγ : GeometricCoeffBound (fun m => -liClockThetaForcingTaylorCoeff (m + 1))
      ((2 + 2 * liEvenCrossActualClockGreenRate ^ 2 + normalizedPrimeArchMoment 0) * 1) 1 :=
    fun m => by rw [abs_neg]; exact geometricCoeffBound_liClockThetaForcingTaylorCoeff.shift m
  have h1 := (summable_oddFactorialSeries_term (by norm_num) hclock t).hasSum
  have h2 := liClockThetaKernel_eq_hasSum t
  have h3 := (summable_oddFactorialSeries_term (by norm_num) hcorr t).hasSum
  have hsum := ((h1.mul_left (liEvenCrossActualClockGreenRate ^ 2)).add
    (h2.mul_left (normalizedPrimeArchMoment 0))).sub h3
  rw [liClockThetaClockInput_eq_oddFactorialSeries, liEvenCrossActualClockBorelCorrection_eq_oddFactorialSeries]
  unfold liClockThetaForcingInput oddFactorialSeries
  rw [← hsum.tsum_eq]
  refine tsum_congr fun m => ?_
  dsimp only
  rw [neg_liClockThetaForcingTaylorCoeff_eq]
  unfold liClockThetaForcingRatio liClockThetaCorrectionCoeff
  push_cast; ring

theorem liEvenCrossActualClockBorelCorrection_le {t : ℝ} (ht : 0 ≤ t) :
    liEvenCrossActualClockBorelCorrection t ≤ 49 / 909 * liClockThetaKernel t := by
  have hb : GeometricCoeffBound (fun m => 49 / 909 * liClockThetaGeneratorCoeff (m + 1))
      (49 / 909 * (1 * (32 / 303))) (32 / 303) := fun m => by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 49 / 909), mul_assoc]
    exact mul_le_mul_of_nonneg_left (hκ m) (by norm_num)
  have h := oddFactorialSeries_le_of_le (by norm_num) (by norm_num) hcorr hb
    liClockThetaCorrectionCoeff_le ht
  rw [← liEvenCrossActualClockBorelCorrection_eq_oddFactorialSeries] at h
  refine h.trans (le_of_eq ?_)
  unfold liClockThetaKernel oddFactorialSeries
  rw [← tsum_mul_left]
  exact tsum_congr fun j => by ring

/-- **Vanishing relative correction.**  `D/K → 0` as `t → ∞`. -/
theorem tendsto_liEvenCrossActualClockBorelCorrection_div_kernel :
    Tendsto (fun t => liEvenCrossActualClockBorelCorrection t / liClockThetaKernel t) atTop (𝓝 0) := by
  have h := tendsto_liEvenCrossActualClockBorelCorrection_div_deriv
  refine h.congr fun t => ?_
  rw [deriv_liEvenCrossActualClockBorelKernel_eq]

/-- `g/K - ω²(1 + tK'/K) - M₀ = -D/K → 0`. -/
theorem tendsto_liClockThetaForcingInput_div_kernel_sub :
    Tendsto (fun t => liClockThetaForcingInput t / liClockThetaKernel t -
      liEvenCrossActualClockGreenRate ^ 2 * (1 + t * liClockThetaKernelDeriv t / liClockThetaKernel t) -
        normalizedPrimeArchMoment 0) atTop (𝓝 0) := by
  have h := tendsto_liEvenCrossActualClockBorelCorrection_div_kernel.neg
  rw [neg_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  have hK := (liClockThetaKernel_pos ht).ne'
  rw [liClockThetaForcingInput_eq_band]
  unfold liClockThetaClockInput
  field_simp
  ring

/-- For every `ε > 0`, eventually `0 ≤ ω²h + M₀K - g ≤ εK`. -/
theorem eventually_band_le (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ t in atTop, 0 ≤ liEvenCrossActualClockGreenRate ^ 2 * liClockThetaClockInput t +
        normalizedPrimeArchMoment 0 * liClockThetaKernel t - liClockThetaForcingInput t ∧
      liEvenCrossActualClockGreenRate ^ 2 * liClockThetaClockInput t +
        normalizedPrimeArchMoment 0 * liClockThetaKernel t - liClockThetaForcingInput t ≤
          ε * liClockThetaKernel t := by
  have h := tendsto_liEvenCrossActualClockBorelCorrection_div_kernel.eventually
    (gt_mem_nhds hε)
  filter_upwards [h, eventually_gt_atTop (0 : ℝ)] with t h1 ht
  have hK := liClockThetaKernel_pos ht
  have hD := liEvenCrossActualClockBorelCorrection_pos ht
  rw [liClockThetaForcingInput_eq_band]
  constructor
  · linarith
  · rw [div_lt_iff₀ hK] at h1; linarith

/-! ## The correction inverse `v = F'' + M₀ r` -/

/-- `v = F'' + M₀ r`. -/
def liClockThetaCorrectionInverse (t : ℝ) : ℝ :=
  iteratedDeriv 2 liEvenCrossActualClockResponse t +
    normalizedPrimeArchMoment 0 * liClockThetaResolvent t

private theorem hf : GeometricCoeffBound liClockResponseCoeff (xiShiftAbsoluteMass 0) (1 / 150) :=
  geometricCoeffBound_liClockResponseCoeff

theorem iteratedDeriv_two_liEvenCrossActualClockResponse_eq :
    iteratedDeriv 2 liEvenCrossActualClockResponse =
      oddFactorialSeries fun j => liClockResponseCoeff (j + 1) := by
  funext t
  rw [liEvenCrossActualClockResponse_eq_oddFactorialSeries,
    iteratedDeriv_two_oddFactorialSeries (by norm_num) hf]

/-- `F'' + F'' ⋆ K = D - M₀ K`. -/
theorem iteratedDeriv_two_liEvenCrossActualClockResponse_volterra (t : ℝ) :
    iteratedDeriv 2 liEvenCrossActualClockResponse t +
        volterraConv (iteratedDeriv 2 liEvenCrossActualClockResponse) liClockThetaKernel t =
      liEvenCrossActualClockBorelCorrection t - normalizedPrimeArchMoment 0 * liClockThetaKernel t := by
  have hK := continuous_liClockThetaKernel
  set F1 := evenFactorialSeries liClockResponseCoeff
  set F2 := oddFactorialSeries fun j => liClockResponseCoeff (j + 1)
  have hF := liEvenCrossActualClockResponse_eq_oddFactorialSeries
  have hF1c : Continuous F1 := continuous_iff_continuousAt.2 fun s =>
    (hasDerivAt_evenFactorialSeries (by norm_num) hf s).continuousAt
  have hF2c : Continuous F2 := continuous_iff_continuousAt.2 fun s =>
    (hasDerivAt_oddFactorialSeries (by norm_num) hf.shift s).continuousAt
  have hE : liClockThetaClockInput = fun s => liEvenCrossActualClockResponse s +
      volterraConv liEvenCrossActualClockResponse liClockThetaKernel s :=
    funext fun s => (liEvenCrossActualClockResponse_volterra_kernel s).symm
  have hFd : ∀ x, HasDerivAt liEvenCrossActualClockResponse (F1 x) x := by
    intro x
    rw [hF]
    exact hasDerivAt_oddFactorialSeries (by norm_num) hf x
  have hd1 : ∀ s, HasDerivAt (fun s => liEvenCrossActualClockResponse s +
      volterraConv liEvenCrossActualClockResponse liClockThetaKernel s) (F1 s + volterraConv F1 liClockThetaKernel s) s := by
    intro s
    have h1 := hFd s
    have h2 := hasDerivAt_volterraConv (f := liEvenCrossActualClockResponse) (f' := F1)
      (g := liClockThetaKernel) hFd hF1c hK s
    rw [hF, oddFactorialSeries_zero, zero_mul, zero_add, ← hF] at h2
    exact h1.add h2
  have hd2 : ∀ s, HasDerivAt (fun s => F1 s + volterraConv F1 liClockThetaKernel s)
      (F2 s + (normalizedPrimeArchMoment 0 * liClockThetaKernel s + volterraConv F2 liClockThetaKernel s)) s := by
    intro s
    have h1 : HasDerivAt F1 (F2 s) s := hasDerivAt_evenFactorialSeries (by norm_num) hf s
    have h2 := hasDerivAt_volterraConv (f := F1) (f' := F2) (g := liClockThetaKernel)
      (fun x => hasDerivAt_evenFactorialSeries (by norm_num) hf x) hF2c hK s
    have hf0 : F1 0 = normalizedPrimeArchMoment 0 := by
      simp only [F1]; rw [evenFactorialSeries_zero]; simp [liClockResponseCoeff]
    rw [hf0] at h2
    exact h1.add h2
  have hdh : deriv liClockThetaClockInput = fun s => F1 s + volterraConv F1 liClockThetaKernel s := by
    rw [hE]; exact funext fun s => (hd1 s).deriv
  have hD : liEvenCrossActualClockBorelCorrection t =
      F2 t + (normalizedPrimeArchMoment 0 * liClockThetaKernel t + volterraConv F2 liClockThetaKernel t) := by
    rw [liEvenCrossActualClockBorelCorrection_eq_iteratedDeriv, show (2 : ℕ) = 1 + 1 from rfl,
      iteratedDeriv_succ, iteratedDeriv_one, hdh]
    exact (hd2 t).deriv
  rw [iteratedDeriv_two_liEvenCrossActualClockResponse_eq, hD]
  ring

theorem continuous_iteratedDeriv_two_liEvenCrossActualClockResponse :
    Continuous (iteratedDeriv 2 liEvenCrossActualClockResponse) := by
  rw [iteratedDeriv_two_liEvenCrossActualClockResponse_eq]
  exact continuous_iff_continuousAt.2 fun s =>
    (hasDerivAt_oddFactorialSeries (by norm_num) hf.shift s).continuousAt

theorem continuous_liClockThetaCorrectionInverse : Continuous liClockThetaCorrectionInverse :=
  continuous_iteratedDeriv_two_liEvenCrossActualClockResponse.add
    (continuous_liClockThetaResolvent.const_mul _)

/-- **Correction inverse.**  `v + v ⋆ K = D`. -/
theorem liClockThetaCorrectionInverse_volterra (t : ℝ) :
    liClockThetaCorrectionInverse t +
        volterraConv liClockThetaCorrectionInverse liClockThetaKernel t =
      liEvenCrossActualClockBorelCorrection t := by
  have hK := continuous_liClockThetaKernel
  have hF2 := continuous_iteratedDeriv_two_liEvenCrossActualClockResponse
  have hr := continuous_liClockThetaResolvent
  have hlin : volterraConv liClockThetaCorrectionInverse liClockThetaKernel t =
      volterraConv (iteratedDeriv 2 liEvenCrossActualClockResponse) liClockThetaKernel t +
        normalizedPrimeArchMoment 0 * volterraConv liClockThetaResolvent liClockThetaKernel t := by
    unfold liClockThetaCorrectionInverse
    rw [volterraConv_comm, show (fun s => iteratedDeriv 2 liEvenCrossActualClockResponse s +
      normalizedPrimeArchMoment 0 * liClockThetaResolvent s) =
        iteratedDeriv 2 liEvenCrossActualClockResponse +
          fun s => normalizedPrimeArchMoment 0 * liClockThetaResolvent s from rfl,
      volterraConv_add_right hK hF2 (hr.const_mul _), volterraConv_smul_right,
      volterraConv_comm liClockThetaKernel, volterraConv_comm liClockThetaKernel]
  rw [hlin]
  unfold liClockThetaCorrectionInverse
  have h1 := iteratedDeriv_two_liEvenCrossActualClockResponse_volterra t
  have h2 := liClockThetaResolvent_volterra t
  linear_combination h1 + normalizedPrimeArchMoment 0 * h2

theorem contDiff_liEvenCrossActualClockBorelCorrection :
    ContDiff ℝ ∞ liEvenCrossActualClockBorelCorrection := by
  rw [liEvenCrossActualClockBorelCorrection_eq_oddFactorialSeries]
  exact contDiff_oddFactorialSeries (by norm_num) hcorr

/-- `v = D - r ⋆ D`. -/
theorem liClockThetaCorrectionInverse_eq_inverse :
    liClockThetaCorrectionInverse = liClockThetaInverse liEvenCrossActualClockBorelCorrection :=
  eq_liClockThetaInverse contDiff_liEvenCrossActualClockBorelCorrection.continuous
    continuous_liClockThetaCorrectionInverse liClockThetaCorrectionInverse_volterra

/-- **Exact decomposition.**  `-S = ω² F + M₀ r - v` and `M₀ r - v = -F''`. -/
theorem neg_liEvenCrossActualClockMassiveSource_eq_band (t : ℝ) :
    -liEvenCrossActualClockMassiveSource t = liEvenCrossActualClockGreenRate ^ 2 *
        liEvenCrossActualClockResponse t + normalizedPrimeArchMoment 0 * liClockThetaResolvent t -
      liClockThetaCorrectionInverse t ∧
    normalizedPrimeArchMoment 0 * liClockThetaResolvent t - liClockThetaCorrectionInverse t =
      -iteratedDeriv 2 liEvenCrossActualClockResponse t := by
  unfold liEvenCrossActualClockMassiveSource liClockThetaCorrectionInverse
  constructor <;> ring

/-- The correction inverse is in the strict sub-`1/300` class. -/
theorem liClockSubGammaClass_liClockThetaCorrectionInverse :
    LiClockSubGammaClass liClockThetaCorrectionInverse := by
  rw [liClockThetaCorrectionInverse_eq_inverse]
  refine liClockSubGammaClass_liClockThetaInverse contDiff_liEvenCrossActualClockBorelCorrection ?_
  rw [liEvenCrossActualClockBorelCorrection_eq_oddFactorialSeries,
    oddFactorialSeries_eq_borelSeries (by norm_num) hcorr]
  refine liClockEveryExpType_borelSeries fun R hR => ⟨_, geometricCoeffBound_oddSpread_of_le
    (M := 49 / 909 * (Real.exp (32 / (303 * R ^ 2)) * R ^ 2)) hR fun k => ?_⟩
  rw [abs_of_pos (liClockThetaCorrectionCoeff_pos k)]
  refine (liClockThetaCorrectionCoeff_le k).trans ?_
  have := liClockThetaGeneratorCoeff_le_pow hR (k + 1)
  rw [show 2 * (k + 1) = 2 + 2 * k by ring, pow_add] at this
  calc 49 / 909 * liClockThetaGeneratorCoeff (k + 1) ≤
      49 / 909 * (Real.exp (32 / (303 * R ^ 2)) * (R ^ 2 * R ^ (2 * k))) :=
        mul_le_mul_of_nonneg_left this (by norm_num)
    _ = _ := by ring

/-! ## Positivity of `v` near the origin -/

theorem liClockThetaCorrectionInverse_zero : liClockThetaCorrectionInverse 0 = 0 := by
  unfold liClockThetaCorrectionInverse
  rw [iteratedDeriv_two_liEvenCrossActualClockResponse_eq, oddFactorialSeries_zero,
    liClockThetaResolvent_zero, mul_zero, add_zero]

/-- **Origin slope.**  `v'(0) = M₀²/2 - M₁ = ν₂/6 > 0`. -/
theorem hasDerivAt_liClockThetaCorrectionInverse_zero :
    HasDerivAt liClockThetaCorrectionInverse (thetaCuspNormalizedEvenMoment 2 / 6) 0 := by
  have h1 : HasDerivAt (iteratedDeriv 2 liEvenCrossActualClockResponse)
      (-normalizedPrimeArchMoment 1) 0 := by
    rw [iteratedDeriv_two_liEvenCrossActualClockResponse_eq]
    have h := hasDerivAt_oddFactorialSeries (by norm_num) hf.shift 0
    have e : liClockResponseCoeff (0 + 1) = -normalizedPrimeArchMoment 1 := by
      simp [liClockResponseCoeff]
    rw [evenFactorialSeries_zero, e] at h
    exact h
  have h2 := hasDerivAt_liClockThetaResolvent_zero.const_mul (normalizedPrimeArchMoment 0)
  have h := h1.add h2
  have e : thetaCuspNormalizedEvenMoment 2 / 6 = -normalizedPrimeArchMoment 1 +
      normalizedPrimeArchMoment 0 * (thetaCuspNormalizedEvenMoment 1 / 2) := by
    rw [normalizedPrimeArchMoment_one_eq_thetaCuspNormalizedEvenMoment,
      normalizedPrimeArchMoment_zero_eq_thetaCuspNormalizedEvenMoment]
    ring
  rw [e]
  exact h

theorem exists_liClockThetaCorrectionInverse_pos :
    ∃ ε > 0, ∀ t ∈ Ioc (0 : ℝ) ε, 0 < liClockThetaCorrectionInverse t := by
  have hν : 0 < thetaCuspNormalizedEvenMoment 2 / 6 := by
    have := thetaCuspNormalizedEvenMoment_pos 2; positivity
  have h := hasDerivAt_liClockThetaCorrectionInverse_zero.tendsto_slope_zero_right
  have hev := h.eventually_const_lt hν
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hev
  refine ⟨u / 2, half_pos hu, fun t ht => ?_⟩
  have htu : t ∈ Ioo 0 u := ⟨ht.1, by linarith [ht.2, (show (0 : ℝ) < u from hu)]⟩
  have hs := hsub htu
  simp only [mem_setOf_eq, zero_add, liClockThetaCorrectionInverse_zero, sub_zero,
    smul_eq_mul] at hs
  have ht0 : 0 < t := ht.1
  have := mul_pos hs ht0
  rwa [inv_mul_eq_div, div_mul_cancel₀ _ ht0.ne'] at this

/-! ## Cofinal negativity of the correction inverse -/

private theorem hcorr_small {R : ℝ} (hR : 0 < R) (k : ℕ) :
    |liClockThetaCorrectionCoeff k| ≤ 49 / 909 * (Real.exp (32 / (303 * R ^ 2)) * R ^ 2) *
      R ^ (2 * k) := by
  rw [abs_of_pos (liClockThetaCorrectionCoeff_pos k)]
  refine (liClockThetaCorrectionCoeff_le k).trans ?_
  have := liClockThetaGeneratorCoeff_le_pow hR (k + 1)
  rw [show 2 * (k + 1) = 2 + 2 * k by ring, pow_add] at this
  calc 49 / 909 * liClockThetaGeneratorCoeff (k + 1) ≤
      49 / 909 * (Real.exp (32 / (303 * R ^ 2)) * (R ^ 2 * R ^ (2 * k))) :=
        mul_le_mul_of_nonneg_left this (by norm_num)
    _ = _ := by ring

theorem hasSum_integral_Ioi_liEvenCrossActualClockBorelCorrection {p : ℝ} (hp : 0 < p) :
    HasSum (fun m : ℕ => liClockThetaCorrectionCoeff m * (p ^ (2 * m + 2))⁻¹)
      (∫ t in Ioi (0 : ℝ), liEvenCrossActualClockBorelCorrection t * Real.exp (-(p * t))) := by
  rw [liEvenCrossActualClockBorelCorrection_eq_oddFactorialSeries]
  exact hasSum_integral_Ioi_oddFactorialSeries_mul_exp_neg (by norm_num) hcorr
    (geometricCoeffBound_oddSpread_of_le (half_pos hp) (hcorr_small (half_pos hp))) (by positivity)
    (by linarith)

private theorem integrableOn_correction {p : ℝ} (hp : 0 < p) :
    IntegrableOn (fun t => Real.exp (-(p * t)) * liEvenCrossActualClockBorelCorrection t) (Ioi 0) := by
  have h : IntegrableOn (fun t => liEvenCrossActualClockBorelCorrection t * Real.exp (-(p * t)))
      (Ioi 0) := by
    rw [liEvenCrossActualClockBorelCorrection_eq_oddFactorialSeries,
      oddFactorialSeries_eq_borelSeries (by norm_num) hcorr]
    exact integrableOn_borelSeries_mul_exp_neg
      (geometricCoeffBound_oddSpread_of_le (half_pos hp) (hcorr_small (half_pos hp))) (by linarith)
  exact h.congr_fun (fun t _ => mul_comm _ _) measurableSet_Ioi

private theorem integrableOn_kernel' {p : ℝ} (hp : 0 < p) :
    IntegrableOn (fun t => Real.exp (-(p * t)) * liClockThetaKernel t) (Ioi 0) :=
  (integrableOn_liClockThetaKernel_mul_exp_neg hp).congr_fun (fun _ _ => mul_comm _ _)
    measurableSet_Ioi

/-- `1 + K̂(p) = Φ(1/p)`. -/
theorem one_add_integral_kernel_eq {p : ℝ} (hp : 0 < p) :
    1 + ∫ t in Ioi (0 : ℝ), Real.exp (-(p * t)) * liClockThetaKernel t =
      liClockThetaGeneratorReal p⁻¹ := by
  have hK := hasSum_integral_Ioi_liClockThetaKernel_mul_exp_neg hp
  have hΦ := (summable_liClockThetaGeneratorReal_term p⁻¹).hasSum
  rw [← hasSum_nat_add_iff' 1] at hΦ
  simp only [Finset.range_one, Finset.sum_singleton, liClockThetaGeneratorCoeff_zero, mul_zero,
    pow_zero, mul_one] at hΦ
  have e : ∫ t in Ioi (0 : ℝ), Real.exp (-(p * t)) * liClockThetaKernel t =
      ∫ t in Ioi (0 : ℝ), liClockThetaKernel t * Real.exp (-(p * t)) :=
    setIntegral_congr_fun measurableSet_Ioi fun t _ => mul_comm _ _
  have h2 := hK.unique (hΦ.congr_fun fun k => by rw [inv_pow, show 2 * (k + 1) = 2 * k + 2 by ring])
  unfold liClockThetaGeneratorReal
  rw [e, h2]
  ring

/-- `D̂(p) = Φ'(1/p) p - M₀`. -/
theorem integral_correction_eq {p : ℝ} (hp : 0 < p) :
    ∫ t in Ioi (0 : ℝ), Real.exp (-(p * t)) * liEvenCrossActualClockBorelCorrection t =
      liClockThetaGeneratorRealDeriv p⁻¹ * p - normalizedPrimeArchMoment 0 := by
  have hD := hasSum_integral_Ioi_liEvenCrossActualClockBorelCorrection hp
  have hs := (summable_liClockThetaGeneratorRealDeriv_div p⁻¹).hasSum
  rw [← hasSum_nat_add_iff' 1] at hs
  have hδ0 : liClockThetaMomentRatio 0 * liClockThetaGeneratorCoeff 0 = normalizedPrimeArchMoment 0 := by
    rw [liClockThetaGeneratorCoeff_zero, mul_one, normalizedPrimeArchMoment_zero_eq_thetaCuspNormalizedEvenMoment]
    unfold liClockThetaMomentRatio
    simp
  simp only [Finset.range_one, Finset.sum_singleton, hδ0, mul_zero, pow_zero, mul_one] at hs
  have e : ∫ t in Ioi (0 : ℝ), Real.exp (-(p * t)) * liEvenCrossActualClockBorelCorrection t =
      ∫ t in Ioi (0 : ℝ), liEvenCrossActualClockBorelCorrection t * Real.exp (-(p * t)) :=
    setIntegral_congr_fun measurableSet_Ioi fun t _ => mul_comm _ _
  have h2 := hD.unique (hs.congr_fun fun k => by
    unfold liClockThetaCorrectionCoeff
    rw [inv_pow, show 2 * (k + 1) = 2 * k + 2 by ring])
  rw [e, h2, liClockThetaGeneratorRealDeriv_eq_mul]
  have hp0 : p ≠ 0 := hp.ne'
  field_simp

/-- `W(z) = (Φ'(z)/z - M₀)/Φ(z) → 0` as `z → ∞`. -/
theorem tendsto_liClockThetaCorrectionSymbol :
    Tendsto (fun z => (liClockThetaGeneratorRealDeriv z / z - normalizedPrimeArchMoment 0) /
      liClockThetaGeneratorReal z) atTop (𝓝 0) := by
  have hΦ : Tendsto liClockThetaGeneratorReal atTop atTop := by
    refine tendsto_atTop_mono' atTop ?_ ((tendsto_pow_atTop (two_ne_zero)).const_mul_atTop
      (liClockThetaGeneratorCoeff_pos 1))
    filter_upwards with z
    have := liClockThetaGeneratorCoeff_mul_le_real 1 z
    simpa using this
  have h1 := tendsto_liClockThetaGeneratorRealDeriv_div
  have h2 := (hΦ.inv_tendsto_atTop).const_mul (normalizedPrimeArchMoment 0)
  rw [mul_zero] at h2
  have h := h1.sub h2
  rw [sub_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with z hz
  have hΦz : 0 < liClockThetaGeneratorReal z := by linarith [one_le_liClockThetaGeneratorReal z]
  simp only [Pi.inv_apply]
  field_simp

/-- `z W(z) = Φ'(z)/Φ(z) - M₀z/Φ(z) → ∞` as `z → ∞`. -/
theorem tendsto_mul_liClockThetaCorrectionSymbol :
    Tendsto (fun z => z * ((liClockThetaGeneratorRealDeriv z / z - normalizedPrimeArchMoment 0) /
      liClockThetaGeneratorReal z)) atTop atTop := by
  have hc1 := liClockThetaGeneratorCoeff_pos 1
  have h2 : Tendsto (fun z => normalizedPrimeArchMoment 0 * z / liClockThetaGeneratorReal z) atTop
      (𝓝 0) := by
    have hb : Tendsto (fun z : ℝ => normalizedPrimeArchMoment 0 / liClockThetaGeneratorCoeff 1 * z⁻¹)
        atTop (𝓝 0) := by
      have := tendsto_inv_atTop_zero.const_mul (normalizedPrimeArchMoment 0 /
        liClockThetaGeneratorCoeff 1)
      rwa [mul_zero] at this
    have hM0 : 0 ≤ normalizedPrimeArchMoment 0 := by
      rw [normalizedPrimeArchMoment_zero_eq_thetaCuspNormalizedEvenMoment]
      exact (thetaCuspNormalizedEvenMoment_pos 1).le
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hb ?_ ?_
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with z hz
      have hΦz : 0 < liClockThetaGeneratorReal z := by linarith [one_le_liClockThetaGeneratorReal z]
      positivity
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with z hz
      have hΦz := liClockThetaGeneratorCoeff_mul_le_real 1 z
      have hΦ0 : 0 < liClockThetaGeneratorReal z := by linarith [one_le_liClockThetaGeneratorReal z]
      simp only [mul_one] at hΦz
      rw [div_le_iff₀ hΦ0]
      have : normalizedPrimeArchMoment 0 / liClockThetaGeneratorCoeff 1 * z⁻¹ *
          (liClockThetaGeneratorCoeff 1 * z ^ 2) = normalizedPrimeArchMoment 0 * z := by
        field_simp
      nlinarith [mul_le_mul_of_nonneg_left hΦz (by positivity : (0 : ℝ) ≤
        normalizedPrimeArchMoment 0 / liClockThetaGeneratorCoeff 1 * z⁻¹)]
  have h := tendsto_liClockThetaGeneratorRealDeriv_div_atTop.atTop_add h2.neg
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with z hz
  have hΦz : 0 < liClockThetaGeneratorReal z := by linarith [one_le_liClockThetaGeneratorReal z]
  field_simp
  ring

private theorem complex_integral_eq_ofReal3 (p : ℝ) (f : ℝ → ℝ) :
    ∫ t in Ioi (0 : ℝ), Complex.exp (-((p : ℂ) * t)) * (f t : ℂ) =
      ((∫ t in Ioi (0 : ℝ), Real.exp (-(p * t)) * f t : ℝ) : ℂ) := by
  have h1 : ∫ t in Ioi (0 : ℝ), Complex.exp (-((p : ℂ) * t)) * (f t : ℂ) =
      ∫ t in Ioi (0 : ℝ), ((Real.exp (-(p * t)) * f t : ℝ) : ℂ) :=
    setIntegral_congr_fun measurableSet_Ioi fun t _ => by push_cast; ring_nf
  rw [h1]
  exact integral_ofReal

/-- **Cofinal negativity.**  The correction inverse `v = F'' + M₀ r` is negative at arbitrarily
large clocks. -/
theorem exists_liClockThetaCorrectionInverse_neg (T : ℝ) :
    ∃ t, T < t ∧ liClockThetaCorrectionInverse t < 0 := by
  by_contra hcon
  simp only [not_exists, not_and, not_lt] at hcon
  set v := liClockThetaCorrectionInverse
  have hv : Continuous v := continuous_liClockThetaCorrectionInverse
  have hK := continuous_liClockThetaKernel
  set T' := max T 0 + 1
  have hT' : 0 < T' := by positivity
  have hTT : T < T' := by linarith [le_max_left T 0]
  have hnn : ∀ t, T' ≤ t → 0 ≤ v t := fun t ht => hcon t (by linarith)
  set C1 := ∫ s in (0 : ℝ)..T', |v s|
  have hC1 : 0 ≤ C1 := intervalIntegral.integral_nonneg hT'.le fun s _ => abs_nonneg _
  set C2 := ∫ s in (0 : ℝ)..T', s * |v s|
  have hC2 : 0 ≤ C2 := intervalIntegral.integral_nonneg hT'.le fun s hs =>
    mul_nonneg hs.1 (abs_nonneg _)
  -- (i) the causal bound on the tail
  have hup : ∀ t, T' ≤ t → v t ≤ liEvenCrossActualClockBorelCorrection t + C1 * liClockThetaKernel t := by
    intro t ht
    have heq := liClockThetaCorrectionInverse_volterra t
    rw [volterraConv_comm] at heq
    have hcK : Continuous fun s => liClockThetaKernel (t - s) * v s :=
      (hK.comp (continuous_const.sub continuous_id)).mul hv
    have hsplit := intervalIntegral.integral_add_adjacent_intervals
      (hcK.intervalIntegrable (μ := volume) 0 T') (hcK.intervalIntegrable (μ := volume) T' t)
    have htail : 0 ≤ ∫ s in T'..t, liClockThetaKernel (t - s) * v s :=
      intervalIntegral.integral_nonneg ht fun s hs =>
        mul_nonneg (liClockThetaKernel_nonneg (by linarith [hs.2])) (hnn s hs.1)
    have hhead : -(liClockThetaKernel t * C1) ≤ ∫ s in (0 : ℝ)..T', liClockThetaKernel (t - s) * v s := by
      rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_neg]
      refine intervalIntegral.integral_mono_on hT'.le
        ((hv.abs.const_mul _).neg.intervalIntegrable _ _) (hcK.intervalIntegrable _ _) fun s hs => ?_
      have hK1 : 0 ≤ liClockThetaKernel (t - s) := liClockThetaKernel_nonneg (by linarith [hs.2])
      have hK2 : liClockThetaKernel (t - s) ≤ liClockThetaKernel t :=
        monotone_liClockThetaKernel (by linarith [hs.1])
      have := neg_abs_le (v s)
      have := le_abs_self (v s)
      nlinarith [abs_nonneg (v s)]
    unfold volterraConv at heq
    linarith
  -- (ii) weighted absolute integrability
  have hint : ∀ p, 0 < p → IntegrableOn (fun t => Real.exp (-(p * t)) * |v t|) (Ioi 0) := by
    intro p hp
    have h1 : IntegrableOn (fun t => Real.exp (-(p * t)) * |v t|) (Ioc 0 T') :=
      ((by fun_prop : Continuous fun t : ℝ => Real.exp (-(p * t))).mul hv.abs).integrableOn_Ioc
    have hdom : IntegrableOn (fun t => Real.exp (-(p * t)) * liEvenCrossActualClockBorelCorrection t +
        C1 * (Real.exp (-(p * t)) * liClockThetaKernel t)) (Ioi T') :=
      ((integrableOn_correction hp).add ((integrableOn_kernel' hp).const_mul C1)).mono_set
        (Ioi_subset_Ioi hT'.le)
    have h2 : IntegrableOn (fun t => Real.exp (-(p * t)) * |v t|) (Ioi T') := by
      refine hdom.mono' ((by fun_prop : Continuous fun t : ℝ => Real.exp (-(p * t))).mul
        hv.abs).aestronglyMeasurable (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_)
      have ht' : T' ≤ t := le_of_lt ht
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), abs_abs, abs_of_nonneg (hnn t ht')]
      have := hup t ht'
      have he := (Real.exp_pos (-(p * t))).le
      nlinarith
    have := h1.union h2
    rwa [Ioc_union_Ioi_eq_Ioi hT'.le] at this
  -- (iii) the Laplace identity `v̂ = D̂/(1 + K̂) = W(1/p)`
  have hlap : ∀ p, 0 < p → ∫ t in Ioi (0 : ℝ), Real.exp (-(p * t)) * v t =
      (liClockThetaGeneratorRealDeriv p⁻¹ / p⁻¹ - normalizedPrimeArchMoment 0) /
        liClockThetaGeneratorReal p⁻¹ := by
    intro p hp
    have hfi : IntegrableOn (fun t => Real.exp (-((p : ℂ).re * t)) * |v t|) (Ioi 0) := by
      simpa using hint p hp
    have hgi : IntegrableOn (fun t => Real.exp (-((p : ℂ).re * t)) * |liClockThetaKernel t|)
        (Ioi 0) := (integrableOn_kernel' hp).congr_fun (fun t ht => by
          simp only [Complex.ofReal_re]
          rw [abs_of_nonneg (liClockThetaKernel_nonneg (le_of_lt ht))]) measurableSet_Ioi
    have hconv := integral_Ioi_cexp_mul_volterraConv hv hK hfi hgi
    rw [complex_integral_eq_ofReal3, complex_integral_eq_ofReal3, complex_integral_eq_ofReal3,
      ← Complex.ofReal_mul] at hconv
    have hreal := Complex.ofReal_injective hconv
    have hvi : IntegrableOn (fun t => Real.exp (-(p * t)) * v t) (Ioi 0) :=
      (hint p hp).mono' ((by fun_prop : Continuous fun t : ℝ => Real.exp (-(p * t))).mul
        hv).aestronglyMeasurable (ae_restrict_of_forall_mem measurableSet_Ioi fun t _ => by
          rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)])
    have hsub : (fun t => Real.exp (-(p * t)) * volterraConv v liClockThetaKernel t) =
        fun t => Real.exp (-(p * t)) * liEvenCrossActualClockBorelCorrection t -
          Real.exp (-(p * t)) * v t := by
      funext t
      have := liClockThetaCorrectionInverse_volterra t
      rw [show volterraConv v liClockThetaKernel t =
        liEvenCrossActualClockBorelCorrection t - v t by linarith]
      ring
    rw [hsub, integral_sub (integrableOn_correction hp) hvi] at hreal
    have hD := integral_correction_eq hp
    have hKΦ := one_add_integral_kernel_eq hp
    have hΦpos : 0 < liClockThetaGeneratorReal p⁻¹ := by
      linarith [one_le_liClockThetaGeneratorReal p⁻¹]
    rw [eq_div_iff hΦpos.ne', ← hKΦ]
    have hp0 : p ≠ 0 := hp.ne'
    rw [show liClockThetaGeneratorRealDeriv p⁻¹ / p⁻¹ = liClockThetaGeneratorRealDeriv p⁻¹ * p by
      field_simp, mul_add, mul_one]
    linarith
  -- (iv) the compact-prefix comparison
  have hcmp : ∀ p q, 0 < p → p < q → ∫ t in Ioi (0 : ℝ), Real.exp (-(q * t)) * v t ≤
      (∫ t in Ioi (0 : ℝ), Real.exp (-(p * t)) * v t) + (q - p) * C2 := by
    intro p q hp hpq
    have hq : 0 < q := hp.trans hpq
    have hvi : ∀ r, 0 < r → IntegrableOn (fun t => Real.exp (-(r * t)) * v t) (Ioi 0) :=
      fun r hr => (hint r hr).mono' ((by fun_prop : Continuous fun t : ℝ =>
        Real.exp (-(r * t))).mul hv).aestronglyMeasurable
          (ae_restrict_of_forall_mem measurableSet_Ioi fun t _ => by
            rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)])
    have hdiff : (∫ t in Ioi (0 : ℝ), Real.exp (-(p * t)) * v t) -
        ∫ t in Ioi (0 : ℝ), Real.exp (-(q * t)) * v t =
          ∫ t in Ioi (0 : ℝ), (Real.exp (-(p * t)) - Real.exp (-(q * t))) * v t := by
      rw [← integral_sub (hvi p hp) (hvi q hq)]
      exact setIntegral_congr_fun measurableSet_Ioi fun t _ => by ring
    have hwi : IntegrableOn (fun t => (Real.exp (-(p * t)) - Real.exp (-(q * t))) * v t) (Ioi 0) :=
      ((hvi p hp).sub (hvi q hq)).congr_fun (fun t _ => by simp only [Pi.sub_apply]; ring)
        measurableSet_Ioi
    have hsplit := setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
      (hwi.mono_set Ioc_subset_Ioi_self) (hwi.mono_set (Ioi_subset_Ioi hT'.le))
    rw [Ioc_union_Ioi_eq_Ioi hT'.le] at hsplit
    have hgap : ∀ t, 0 ≤ t → 0 ≤ Real.exp (-(p * t)) - Real.exp (-(q * t)) ∧
        Real.exp (-(p * t)) - Real.exp (-(q * t)) ≤ (q - p) * t := by
      intro t ht
      have h1 : Real.exp (-(q * t)) ≤ Real.exp (-(p * t)) := Real.exp_le_exp.2 (by nlinarith)
      have h2 : Real.exp (-(p * t)) - Real.exp (-(q * t)) =
          Real.exp (-(p * t)) * (1 - Real.exp (-((q - p) * t))) := by
        rw [mul_sub, mul_one, ← Real.exp_add]; ring_nf
      have h3 : 1 - Real.exp (-((q - p) * t)) ≤ (q - p) * t := by
        linarith [Real.add_one_le_exp (-((q - p) * t))]
      have h4 : Real.exp (-(p * t)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
      have h5 : 0 ≤ 1 - Real.exp (-((q - p) * t)) := by
        have : Real.exp (-((q - p) * t)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
        linarith
      refine ⟨by linarith, ?_⟩
      rw [h2]
      calc Real.exp (-(p * t)) * (1 - Real.exp (-((q - p) * t))) ≤ 1 * (1 - Real.exp (-((q - p) * t))) :=
            mul_le_mul_of_nonneg_right h4 h5
        _ ≤ (q - p) * t := by linarith
    have hhead : -((q - p) * C2) ≤ ∫ t in Ioc (0 : ℝ) T',
        (Real.exp (-(p * t)) - Real.exp (-(q * t))) * v t := by
      have hC2' : C2 = ∫ t in Ioc (0 : ℝ) T', t * |v t| := intervalIntegral.integral_of_le hT'.le
      rw [hC2', ← integral_const_mul, ← integral_neg]
      refine setIntegral_mono_on (((continuous_id.mul hv.abs).const_mul _).neg.integrableOn_Ioc)
        (hwi.mono_set Ioc_subset_Ioi_self) measurableSet_Ioc fun t ht => ?_
      obtain ⟨g1, g2⟩ := hgap t ht.1.le
      have := neg_abs_le (v t)
      have := le_abs_self (v t)
      nlinarith [abs_nonneg (v t), mul_nonneg (sub_nonneg.2 hpq.le) ht.1.le]
    have htail : 0 ≤ ∫ t in Ioi T', (Real.exp (-(p * t)) - Real.exp (-(q * t))) * v t :=
      setIntegral_nonneg measurableSet_Ioi fun t ht =>
        mul_nonneg (hgap t (by linarith [show T' < t from ht])).1 (hnn t (le_of_lt ht))
    linarith
  -- (v) letting `p ↓ 0`
  have hW := tendsto_liClockThetaCorrectionSymbol
  have hbound : ∀ q, 0 < q → ∫ t in Ioi (0 : ℝ), Real.exp (-(q * t)) * v t ≤ q * C2 := by
    intro q hq
    have hlim : Tendsto (fun p => ∫ t in Ioi (0 : ℝ), Real.exp (-(p * t)) * v t) (𝓝[>] 0) (𝓝 0) := by
      have h := hW.comp tendsto_inv_nhdsGT_zero
      refine h.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with p hp
      exact (hlap p hp).symm
    have hlim2 : Tendsto (fun p => (∫ t in Ioi (0 : ℝ), Real.exp (-(p * t)) * v t) + (q - p) * C2)
        (𝓝[>] 0) (𝓝 (0 + (q - 0) * C2)) :=
      hlim.add ((tendsto_const_nhds.sub (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id)).mul
        tendsto_const_nhds)
    rw [zero_add, sub_zero] at hlim2
    have hev : ∀ᶠ p in 𝓝[>] (0 : ℝ), ∫ t in Ioi (0 : ℝ), Real.exp (-(q * t)) * v t ≤
        (∫ t in Ioi (0 : ℝ), Real.exp (-(p * t)) * v t) + (q - p) * C2 := by
      filter_upwards [Ioo_mem_nhdsGT hq] with p hp
      exact hcmp p q hp.1 hp.2
    exact ge_of_tendsto hlim2 hev
  -- (vi) contradiction with `z W(z) → ∞`
  obtain ⟨z, hz1, hz2⟩ := ((tendsto_mul_liClockThetaCorrectionSymbol.eventually
    (eventually_gt_atTop C2)).and (eventually_gt_atTop (0 : ℝ))).exists
  have h := hbound z⁻¹ (inv_pos.2 hz2)
  rw [hlap z⁻¹ (inv_pos.2 hz2), inv_inv] at h
  have h' := mul_le_mul_of_nonneg_left h hz2.le
  rw [← mul_assoc, mul_inv_cancel₀ hz2.ne', one_mul] at h'
  linarith

end RHTower
