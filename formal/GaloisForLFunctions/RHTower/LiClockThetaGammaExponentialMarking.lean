import GaloisForLFunctions.RHTower.LiClockThetaGammaQuantileReserve
import GaloisForLFunctions.RHTower.LiEvenCrossActualClockMarking
import GaloisForLFunctions.RHTower.LiClockThetaSignedGammaCoupling

/-!
# One exponential marking of the actual Gamma jump intensities

Fix `r > 0` with `a = p - r` in the reserve domain `D`, and let `Exp_r` be the exponential law of
rate `r`.  The marked intensities `τ̄_p^± = τ_p^± ∗ Exp_r` satisfy:

* (D13) `τ̄^±` have the continuous convolution densities `g^±(t) = ∫_0^t r e^{-r(t-u)} τ^±(u) du`,
  and `g⁺(t) - g⁻(t) = κ(t) = r e^{-rt} D_a(t)` for `t > 0`, `0` for `t ≤ 0`; hence
  `τ̄⁺ = τ̄⁻ + κ` with `κ` a positive finite measure;
* (D14) `κ(t) > r e^{-rt} δ(a) F_{1,a}(t) > 0`, `κ` has mass `H(p)` and all moments, and the lower
  bound has mass `δ(a) a²/p²`;
* (D15) `∫ e^{-st} dκ = r H(p+s)/(r+s)` for `s ≥ 0`;
* (D16) for every real time `v ≥ 0`, `CP(v τ̄⁺) = CP(v τ̄⁻) ∗ CP(v κ)`, so `CP(v τ̄⁺)` dominates
  `CP(v τ̄⁻)` on bounded increasing tests;
* (D17) `∫ e^{-st} dCP(vκ) = exp(v (r H(p+s)/(r+s) - H(p)))`;
* (D18) `h(s) = r H(p+s)/(r+s)` is strictly completely monotone on `s > -r`, the compensated sums
  `Σ_{k≤n} (r+s)^k (-1)^k H^{(k)}(p+s)/k!` are positive, and
  `∫ e^{2εt} d(τ̄⁺ + τ̄⁻) = r/(r - 2ε) Σ_j |ℓ_j(p - 2ε)|`.
-/

open Set Filter Topology MeasureTheory GaloisForLFunctions.HTGeometry ProbabilityTheory
open scoped ENNReal

noncomputable section

namespace RHTower

local notation "P" => liEvenCrossActualClockPrimitive
local notation "ℓ" => liClockThetaLogJumpCoefficient
local notation "δ" => liClockThetaGammaReserve
local notation "W" => liClockThetaWideThreshold
local notation "F" => liClockThetaGammaRowCDF
local notation "τ" => liClockThetaGammaJumpMeasure
local notation "Λ" => liClockThetaJumpMass
local notation "H" => liClockThetaReciprocalLog
local notation "β" => liEvenCrossActualClockMaxGrowthRate
local notation "D" => liEvenCrossActualClockDampedCutoff
local notation "M₁" => normalizedPrimeArchMoment 1
local notation "Lap" => GaloisForLFunctions.HTGeometry.laplace
local notation "CP" => GaloisForLFunctions.HTGeometry.compoundPoisson

/-! ## The source normalizer and the reserve domain -/

/-- `Φ(1/p) = XiC(-i/p)/XiC(0)`: the Gamma normalizer is the real generator at `1/p`. -/
theorem liClockThetaGammaNormalizer_eq_generatorReal (p : ℝ) :
    liClockThetaGammaNormalizer p = liClockThetaGeneratorReal p⁻¹ := by
  unfold liClockThetaGammaNormalizer
  rw [← liClockThetaGenerator_eq_XiC, show ((p : ℂ))⁻¹ = ((p⁻¹ : ℝ) : ℂ) by push_cast; rfl,
    liClockThetaGenerator_ofReal, Complex.ofReal_re]

/-- `H(p) = log Φ(1/p)`. -/
theorem liClockThetaReciprocalLog_eq_log_generatorReal (p : ℝ) :
    H p = Real.log (liClockThetaGeneratorReal p⁻¹) := by
  rw [liClockThetaReciprocalLog, liClockThetaGammaNormalizer_eq_generatorReal]

theorem one_div_three_hundred_lt_wideThreshold : 1 / 300 < W := by
  unfold liClockThetaWideThreshold
  rw [Real.lt_sqrt (by norm_num)]
  norm_num

/-- On the reserve domain the damping lies above the maximal growth rate. -/
theorem LiClockThetaGammaReserveDomain.maxGrowthRate_lt {a : ℝ}
    (ha : LiClockThetaGammaReserveDomain a) : β < a :=
  liEvenCrossActualClockMaxGrowthRate_lt_of_lt (one_div_three_hundred_lt_wideThreshold.trans ha.wide)

/-- **(D3)** The signed Gamma density `σ_p = e^{-pt} P(t)/t` on `t > 0`, `0` on `t ≤ 0`, is
continuous. -/
theorem continuous_liClockThetaSignedGammaDensity {p : ℝ} (hp : W < p) :
    Continuous (liClockThetaSignedGammaDensity p) := by
  have e : liClockThetaSignedGammaDensity p =
      fun t => if t ≤ 0 then 0 else Real.exp (-(p * t)) * (P t / t) := funext fun t => by
    rw [liClockThetaSignedGammaDensity_eq_primitive_wide hp]
    by_cases ht : t ≤ 0
    · rw [if_pos ht, indicator_of_notMem (show t ∉ Ioi (0 : ℝ) from not_lt.2 ht)]
    · rw [if_neg ht, indicator_of_mem (show t ∈ Ioi (0 : ℝ) from not_le.1 ht), mul_div_assoc]
  rw [e]
  refine Continuous.if_le continuous_const
    ((by fun_prop : Continuous fun t : ℝ => Real.exp (-(p * t))).mul
      continuous_liEvenCrossActualClockPrimitive_div) continuous_id continuous_const
    fun t ht => ?_
  rw [show t = 0 from ht, div_zero, mul_zero]

/-! ## The exponential mark and the marked Gamma intensities -/

private def expK (r x : ℝ) : ℝ := (Ici (0 : ℝ)).indicator (fun x => r * Real.exp (-r * x)) x

private theorem exponentialPDF_eq_expK (r x : ℝ) :
    exponentialPDF r x = ENNReal.ofReal (expK r x) := by
  rw [exponentialPDF_eq, expK]
  congr 1
  by_cases hx : 0 ≤ x
  · rw [if_pos hx, indicator_of_mem (mem_Ici.2 hx), neg_mul]
  · rw [if_neg hx, indicator_of_notMem (by simpa using hx)]

private theorem measurable_expK (r : ℝ) : Measurable (expK r) :=
  Measurable.indicator (by fun_prop) measurableSet_Ici

private theorem expK_nonneg {r : ℝ} (hr : 0 ≤ r) (x : ℝ) : 0 ≤ expK r x := by
  unfold expK
  by_cases hx : x ∈ Ici (0 : ℝ)
  · rw [indicator_of_mem hx]; positivity
  · rw [indicator_of_notMem hx]

private theorem expK_le {r : ℝ} (hr : 0 ≤ r) (x : ℝ) : expK r x ≤ r := by
  unfold expK
  by_cases hx : x ∈ Ici (0 : ℝ)
  · rw [indicator_of_mem hx]
    exact mul_le_of_le_one_right hr (Real.exp_le_one_iff.2 (by nlinarith [mem_Ici.1 hx]))
  · rw [indicator_of_notMem hx]; exact hr

/-- The marked intensity `τ̄_p^± = τ_p^± ∗ Exp_r`. -/
def liClockThetaMarkedGammaJumpMeasure (p r : ℝ) (b : Bool) : Measure ℝ :=
  τ p b ∗ expMeasure r

/-- The marked density `g^±(t) = ∫_0^t r e^{-r(t-u)} τ^±(u) du`. -/
def liClockThetaMarkedGammaJumpDensity (p r : ℝ) (b : Bool) (t : ℝ) : ℝ :=
  volterraConv (fun s => r * Real.exp (-r * s)) (liClockThetaGammaJumpDensity p b) t

/-- The marked source measure with density `κ(t) = r e^{-rt} D_{p-r}(t)` on `t > 0`. -/
def liClockThetaMarkedSourceMeasure (p r : ℝ) : Measure ℝ :=
  volume.withDensity fun t => ENNReal.ofReal ((Ioi (0 : ℝ)).indicator (liClockMarkedDensity p r) t)

local notation "τ̄" => liClockThetaMarkedGammaJumpMeasure
local notation "gm" => liClockThetaMarkedGammaJumpDensity
local notation "κ" => liClockThetaMarkedSourceMeasure

theorem liClockThetaMarkedGammaJumpDensity_of_nonpos (p r : ℝ) (b : Bool) {t : ℝ} (ht : t ≤ 0) :
    gm p r b t = 0 := by
  unfold liClockThetaMarkedGammaJumpDensity volterraConv
  rw [intervalIntegral.integral_of_ge ht, setIntegral_eq_zero_of_forall_eq_zero fun s hs => by
      rw [liClockThetaGammaJumpDensity_of_nonpos p b hs.2, mul_zero], neg_zero]

theorem liClockThetaMarkedGammaJumpDensity_nonneg {p r : ℝ} (hp : W < p) (hr : 0 ≤ r) (b : Bool)
    (t : ℝ) : 0 ≤ gm p r b t := by
  rcases le_or_gt t 0 with ht | ht
  · rw [liClockThetaMarkedGammaJumpDensity_of_nonpos p r b ht]
  · exact intervalIntegral.integral_nonneg ht.le fun s _ =>
      mul_nonneg (by positivity) (((liClockThetaGammaJumpDensity_admission_wide hp).1 b).2.1 s)

private theorem integral_jump_mul_expK_eq (p r : ℝ) (b : Bool) (t : ℝ) :
    ∫ y, liClockThetaGammaJumpDensity p b y * expK r (t - y) = gm p r b t := by
  rcases le_or_gt t 0 with ht | ht
  · rw [liClockThetaMarkedGammaJumpDensity_of_nonpos p r b ht]
    refine integral_eq_zero_of_ae (ae_of_all _ fun y => ?_)
    rcases le_or_gt y 0 with hy | hy
    · simp [liClockThetaGammaJumpDensity_of_nonpos p b hy]
    · simp [expK, indicator_of_notMem (show t - y ∉ Ici (0 : ℝ) by
        simp only [mem_Ici, not_le]; linarith)]
  · rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ioc 0 t) fun y hy => ?_]
    · unfold liClockThetaMarkedGammaJumpDensity volterraConv
      rw [intervalIntegral.integral_of_le ht.le]
      refine setIntegral_congr_fun measurableSet_Ioc fun y hy => ?_
      simp only [expK, indicator_of_mem (show t - y ∈ Ici (0 : ℝ) from
        mem_Ici.2 (sub_nonneg.2 hy.2))]
      ring
    · simp only [mem_Ioc, not_and_or, not_lt, not_le] at hy
      rcases hy with hy | hy
      · simp [liClockThetaGammaJumpDensity_of_nonpos p b hy]
      · simp [expK, indicator_of_notMem (show t - y ∉ Ici (0 : ℝ) by
          simp only [mem_Ici, not_le]; linarith)]

theorem liClockThetaMarkedGammaJumpDensity_eq_exp_mul (p r : ℝ) (b : Bool) (t : ℝ) :
    gm p r b t = r * Real.exp (-r * t) *
      ∫ s in (0 : ℝ)..t, Real.exp (r * s) * liClockThetaGammaJumpDensity p b s := by
  unfold liClockThetaMarkedGammaJumpDensity volterraConv
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun s _ => ?_
  simp only
  rw [show -r * (t - s) = -r * t + r * s by ring, Real.exp_add]
  ring

/-- **(D13)** The marked densities are continuous. -/
theorem continuous_liClockThetaMarkedGammaJumpDensity {p r : ℝ} (hp : W < p) (b : Bool) :
    Continuous (gm p r b) := by
  have e : gm p r b = fun t => r * Real.exp (-r * t) *
      ∫ s in (0 : ℝ)..t, Real.exp (r * s) * liClockThetaGammaJumpDensity p b s :=
    funext (liClockThetaMarkedGammaJumpDensity_eq_exp_mul p r b)
  rw [e]
  exact (by fun_prop : Continuous fun t : ℝ => r * Real.exp (-r * t)).mul
    (intervalIntegral.continuous_primitive (fun _ _ =>
      (((liClockThetaGammaJumpDensity_admission_wide hp).1 b).1.intervalIntegrable).continuousOn_mul (by fun_prop)) 0)

/-- **(D13)** `τ̄_p^±` has density `g^±`. -/
theorem liClockThetaMarkedGammaJumpMeasure_eq_withDensity {p r : ℝ} (hp : W < p) (hr : 0 ≤ r)
    (b : Bool) :
    τ̄ p r b = volume.withDensity fun t => ENNReal.ofReal (gm p r b t) := by
  obtain ⟨hi, hnn, -, he⟩ := (liClockThetaGammaJumpDensity_admission_wide hp).1 b
  have hexp : expMeasure r = volume.withDensity (exponentialPDF r) := rfl
  rw [liClockThetaMarkedGammaJumpMeasure, he, hexp, conv_withDensity_eq_lconvolution
    (measurable_liClockThetaGammaJumpDensity p b).ennreal_ofReal
    (show Measurable (exponentialPDF r) from (measurable_exponentialPDFReal r).ennreal_ofReal)]
  congr 1
  funext t
  rw [lconvolution_def]
  have hint : Integrable (fun y => liClockThetaGammaJumpDensity p b y * expK r (t - y)) :=
    hi.mul_bdd ((measurable_expK r).comp (measurable_const.sub measurable_id)).aestronglyMeasurable
      (ae_of_all _ fun y => by
        rw [Real.norm_eq_abs, abs_of_nonneg (expK_nonneg hr _)]; exact expK_le hr _)
  rw [← integral_jump_mul_expK_eq p r b t, ofReal_integral_eq_lintegral_ofReal hint
    (ae_of_all _ fun y => mul_nonneg (hnn y) (expK_nonneg hr _))]
  refine lintegral_congr fun y => ?_
  rw [exponentialPDF_eq_expK, ENNReal.ofReal_mul (hnn y), neg_add_eq_sub]

/-- `τ_p⁺(t) - τ_p⁻(t) = σ_p(t)` pointwise. -/
theorem liClockThetaGammaJumpDensity_sub {p : ℝ} (hp : W < p) (t : ℝ) :
    liClockThetaGammaJumpDensity p true t - liClockThetaGammaJumpDensity p false t =
      liClockThetaSignedGammaDensity p t := by
  have hp0 : 0 < p := liClockThetaWideThreshold_pos.trans hp
  have habs := (liClockThetaLogJumpCoefficient_admission_wide hp).1
  have hrow : ∀ j, liClockThetaGammaRowDensity p j t ≤ p := fun j => by
    rcases le_or_gt t 0 with ht | ht
    · have h0 : liClockThetaGammaRowDensity p j t = 0 := by
        unfold liClockThetaGammaRowDensity
        split_ifs
        · rfl
        · exact indicator_of_notMem (show t ∉ Ioi (0 : ℝ) from not_lt.2 ht) _
      rw [h0]; exact hp0.le
    · exact liClockThetaGammaRowDensity_le_rate hp0 j ht
  have hs : ∀ b, Summable fun j => liClockThetaJumpPart p b j * liClockThetaGammaRowDensity p j t :=
    fun b => Summable.of_nonneg_of_le
      (fun j => mul_nonneg (liClockThetaJumpPart_nonneg p b j)
        (liClockThetaGammaRowDensity_nonneg hp0 j t))
      (fun j => mul_le_mul (liClockThetaJumpPart_le_abs p b j) (hrow j)
        (liClockThetaGammaRowDensity_nonneg hp0 j t) (abs_nonneg _))
      (habs.mul_right p)
  unfold liClockThetaGammaJumpDensity liClockThetaSignedGammaDensity
  rw [← (hs true).tsum_sub (hs false)]
  exact tsum_congr fun j => by rw [← sub_mul, liClockThetaJumpPart_sub]

/-- **(D13)** Pointwise `g⁺(t) - g⁻(t) = κ(t)`, with `κ(t) = r e^{-rt} D_{p-r}(t)` for `t > 0` and
`0` for `t ≤ 0`. -/
theorem liClockThetaMarkedGammaJumpDensity_sub {p r : ℝ} (hp : W < p) (t : ℝ) :
    gm p r true t - gm p r false t = (Ioi (0 : ℝ)).indicator (liClockMarkedDensity p r) t := by
  have hii : ∀ b, IntervalIntegrable (fun s => r * Real.exp (-r * (t - s)) *
      liClockThetaGammaJumpDensity p b s) volume 0 t := fun b =>
    (((liClockThetaGammaJumpDensity_admission_wide hp).1 b).1.intervalIntegrable).continuousOn_mul (by fun_prop)
  unfold liClockThetaMarkedGammaJumpDensity volterraConv
  rw [← intervalIntegral.integral_sub (hii true) (hii false)]
  have hσ : ∀ s, liClockThetaGammaJumpDensity p true s - liClockThetaGammaJumpDensity p false s =
      (Ioi (0 : ℝ)).indicator (liClockMarkedSource p) s := fun s => by
    rw [liClockThetaGammaJumpDensity_sub hp, liClockThetaSignedGammaDensity_eq_primitive_wide hp]
    by_cases hs : s ∈ Ioi (0 : ℝ)
    · rw [indicator_of_mem hs, indicator_of_mem hs, liClockMarkedSource, neg_mul]
    · rw [indicator_of_notMem hs, indicator_of_notMem hs]
  have e : ∀ s, r * Real.exp (-r * (t - s)) * liClockThetaGammaJumpDensity p true s -
      r * Real.exp (-r * (t - s)) * liClockThetaGammaJumpDensity p false s =
        r * Real.exp (-r * (t - s)) * (Ioi (0 : ℝ)).indicator (liClockMarkedSource p) s :=
    fun s => by rw [← mul_sub, hσ]
  simp only [e]
  rcases le_or_gt t 0 with ht | ht
  · rw [indicator_of_notMem (show t ∉ Ioi (0 : ℝ) from not_lt.2 ht),
      intervalIntegral.integral_of_ge ht, setIntegral_eq_zero_of_forall_eq_zero fun s hs => by
          rw [indicator_of_notMem (show s ∉ Ioi (0 : ℝ) from not_lt.2 hs.2), mul_zero],
      neg_zero]
  · rw [indicator_of_mem (show t ∈ Ioi (0 : ℝ) from ht), liClockMarkedDensity_eq_volterraConv]
    unfold volterraConv
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [uIcc_of_le ht.le] at hs
    simp only
    rcases hs.1.eq_or_lt with rfl | hs0
    · rw [indicator_of_notMem (show (0 : ℝ) ∉ Ioi (0 : ℝ) from fun h => lt_irrefl (0 : ℝ) (mem_Ioi.1 h))]
      simp [liClockMarkedSource]
    · rw [indicator_of_mem (show s ∈ Ioi (0 : ℝ) from hs0)]

/-- **(D13)** On the marking domain the density `κ` is positive on `t > 0`. -/
theorem liClockMarkedDensity_pos_of_reserveDomain {p r : ℝ} (hr : 0 < r)
    (ha : LiClockThetaGammaReserveDomain (p - r)) {t : ℝ} (ht : 0 < t) :
    0 < liClockMarkedDensity p r t :=
  liClockMarkedDensity_pos hr ha.maxGrowthRate_lt.le ht

theorem LiClockThetaGammaReserveDomain.wide_add {p r : ℝ} (hr : 0 < r)
    (ha : LiClockThetaGammaReserveDomain (p - r)) : W < p := by
  have := ha.wide
  linarith

/-- **(D13)** `τ̄_p⁺ = τ̄_p⁻ + κ`. -/
theorem liClockThetaMarkedGammaJumpMeasure_true_eq {p r : ℝ} (hr : 0 < r)
    (ha : LiClockThetaGammaReserveDomain (p - r)) : τ̄ p r true = τ̄ p r false + κ p r := by
  have hp := ha.wide_add hr
  rw [liClockThetaMarkedGammaJumpMeasure_eq_withDensity hp hr.le,
    liClockThetaMarkedGammaJumpMeasure_eq_withDensity hp hr.le, liClockThetaMarkedSourceMeasure,
    ← withDensity_add_left
      (continuous_liClockThetaMarkedGammaJumpDensity hp false).measurable.ennreal_ofReal]
  congr 1
  funext t
  have hk : 0 ≤ (Ioi (0 : ℝ)).indicator (liClockMarkedDensity p r) t := by
    by_cases ht : t ∈ Ioi (0 : ℝ)
    · rw [indicator_of_mem ht]; exact (liClockMarkedDensity_pos_of_reserveDomain hr ha ht).le
    · rw [indicator_of_notMem ht]
  simp only [Pi.add_apply]
  rw [← ENNReal.ofReal_add (liClockThetaMarkedGammaJumpDensity_nonneg hp hr.le false t) hk,
    ← liClockThetaMarkedGammaJumpDensity_sub hp t, add_sub_cancel]

theorem LiClockThetaGammaReserveDomain.mono {a p : ℝ} (ha : LiClockThetaGammaReserveDomain a)
    (hap : a ≤ p) : LiClockThetaGammaReserveDomain p := by
  refine ⟨ha.1.trans_le hap, ha.2.trans_le ?_⟩
  have := ha.1
  nlinarith

/-! ## (D14) The explicit positive lower bound and the mass of the mark -/

/-- **(D14)** For `t > 0` and `a = p - r ∈ D`: `0 < r e^{-rt} δ(a) F_{1,a}(t) < κ(t)`, and retaining the
negative second row, `κ(t) ≥ r e^{-rt} (δ(a) F_{1,a}(t) + (M₁/(4a⁴)) e^{-at}((at)²/2 + (at)³/6))`. -/
theorem liClockMarkedDensity_gt_gammaReserve {p r : ℝ} (hr : 0 < r)
    (ha : LiClockThetaGammaReserveDomain (p - r)) {t : ℝ} (ht : 0 < t) :
    0 < r * Real.exp (-r * t) * (δ (p - r) * F (p - r) 1 t) ∧
      r * Real.exp (-r * t) * (δ (p - r) * F (p - r) 1 t) < liClockMarkedDensity p r t ∧
      r * Real.exp (-r * t) * (δ (p - r) * F (p - r) 1 t + M₁ / (4 * (p - r) ^ 4) *
        (Real.exp (-((p - r) * t)) * (((p - r) * t) ^ 2 / 2 + ((p - r) * t) ^ 3 / 6))) ≤
        liClockMarkedDensity p r t := by
  obtain ⟨h0, h1⟩ := liEvenCrossActualClockDampedCutoff_gt_gammaReserve ha ht
  have h2 := liEvenCrossActualClockDampedCutoff_ge_gammaReserve ha.wide ht.le
  have hk : 0 < r * Real.exp (-r * t) := by positivity
  unfold liClockMarkedDensity
  exact ⟨mul_pos hk h0, mul_lt_mul_of_pos_left h1 hk, mul_le_mul_of_nonneg_left h2 hk.le⟩

private theorem powExp_integrable {c : ℝ} (hc : 0 < c) (m : ℕ) :
    IntegrableOn (fun t : ℝ => t ^ m * Real.exp (-(c * t))) (Ioi 0) := by
  have hm : (-1 : ℝ) < (m : ℝ) := by
    have hm0 : 0 ≤ (m : ℝ) := by positivity
    linarith
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := (m : ℝ)) (b := c) hm
    (by norm_num) hc
  simpa only [Real.rpow_one, Real.rpow_natCast, neg_mul] using h

private theorem powExp_integral {c : ℝ} (hc : 0 < c) (m : ℕ) :
    (∫ t in Ioi 0, t ^ m * Real.exp (-(c * t))) = (m.factorial : ℝ) / c ^ (m + 1) := by
  have hm : (-1 : ℝ) < (m : ℝ) := by
    have hm0 : 0 ≤ (m : ℝ) := by positivity
    linarith
  have hcm : (m : ℝ) + 1 = ((m + 1 : ℕ) : ℝ) := by norm_num
  have h := integral_rpow_mul_exp_neg_mul_rpow (p := 1) (q := (m : ℝ)) (b := c) (by norm_num) hm hc
  calc
    _ = c ^ (-((m : ℝ) + 1)) * Real.Gamma ((m : ℝ) + 1) := by
      simpa only [Real.rpow_one, Real.rpow_natCast, div_one, mul_one, neg_mul] using h
    _ = (c ^ (m + 1))⁻¹ * (m.factorial : ℝ) := by
      rw [Real.rpow_neg hc.le, Real.Gamma_nat_eq_factorial, hcm, Real.rpow_natCast]
    _ = _ := by rw [div_eq_mul_inv]; ring

/-- **(D14)** The lower bound has mass `∫_0^∞ r e^{-rt} δ(a) F_{1,a}(t) dt = δ(a) a²/p²`. -/
theorem integral_liClockMarked_gammaReserve {p r : ℝ} (hr : 0 < r) (hpr : r < p) :
    ∫ t in Ioi (0 : ℝ), r * Real.exp (-r * t) * (δ (p - r) * F (p - r) 1 t) =
      δ (p - r) * (p - r) ^ 2 / p ^ 2 := by
  have hp : 0 < p := hr.trans hpr
  set a := p - r with ha
  have key : ∀ t, r * Real.exp (-r * t) * (δ a * F a 1 t) =
      δ a * r * (t ^ 0 * Real.exp (-(r * t))) - δ a * r * (t ^ 0 * Real.exp (-(p * t))) -
        δ a * r * a * (t ^ 1 * Real.exp (-(p * t))) := fun t => by
    have e1 : Real.exp (-(p * t)) = Real.exp (-r * t) * Real.exp (-(a * t)) := by
      rw [← Real.exp_add]; congr 1; rw [ha]; ring
    rw [liClockThetaGammaRowCDF_one, e1, neg_mul]
    ring
  simp only [key]
  have i0 := (powExp_integrable hr 0).const_mul (δ a * r)
  have i1 := (powExp_integrable hp 0).const_mul (δ a * r)
  have i2 := (powExp_integrable hp 1).const_mul (δ a * r * a)
  have i01 : IntegrableOn (fun t => δ a * r * (t ^ 0 * Real.exp (-(r * t))) -
      δ a * r * (t ^ 0 * Real.exp (-(p * t)))) (Ioi 0) := i0.sub i1
  rw [integral_sub i01 i2, integral_sub i0 i1, integral_const_mul, integral_const_mul,
    integral_const_mul, powExp_integral hr, powExp_integral hp, powExp_integral hp]
  simp only [Nat.factorial_zero, Nat.factorial_one, Nat.cast_one, zero_add, pow_one]
  field_simp
  rw [ha]
  ring

private theorem measurable_indicator_marked (p r : ℝ) :
    Measurable ((Ioi (0 : ℝ)).indicator (liClockMarkedDensity p r)) :=
  (continuous_liClockMarkedDensity p r).measurable.indicator measurableSet_Ioi

private theorem indicator_marked_nonneg {p r : ℝ} (hr : 0 < r)
    (ha : LiClockThetaGammaReserveDomain (p - r)) (t : ℝ) :
    0 ≤ (Ioi (0 : ℝ)).indicator (liClockMarkedDensity p r) t := by
  by_cases ht : t ∈ Ioi (0 : ℝ)
  · rw [indicator_of_mem ht]; exact (liClockMarkedDensity_pos_of_reserveDomain hr ha ht).le
  · rw [indicator_of_notMem ht]

private theorem integrableOn_exp_mul_marked {p r : ℝ} (hr : 0 < r)
    (ha : LiClockThetaGammaReserveDomain (p - r)) (n : ℕ) {s : ℝ} (hs : -r < s) :
    IntegrableOn (fun t => t ^ n * Real.exp (-(s * t)) * liClockMarkedDensity p r t) (Ioi 0) :=
  integrableOn_liClockMarkedDensity_moment hr.le n (by
    rw [max_eq_right (sub_nonpos.2 ha.maxGrowthRate_lt.le)]; linarith)

/-- **(D15)** `∫ e^{-st} dκ = r H(p+s)/(r+s)` for every `s > -r`, in particular for `s ≥ 0`. -/
theorem laplace_liClockThetaMarkedSourceMeasure {p r : ℝ} (hr : 0 < r)
    (ha : LiClockThetaGammaReserveDomain (p - r)) {s : ℝ} (hs : -r < s) :
    Lap (κ p r) s = ENNReal.ofReal (r / (r + s) * H (p + s)) := by
  have hint := integrableOn_exp_mul_marked hr ha 0 hs
  simp only [pow_zero, one_mul] at hint
  have hind : Integrable ((Ioi (0 : ℝ)).indicator
      fun t => Real.exp (-(s * t)) * liClockMarkedDensity p r t) :=
    (integrable_indicator_iff measurableSet_Ioi).2 hint
  have hfun : ∀ t, (Ioi (0 : ℝ)).indicator (liClockMarkedDensity p r) t *
      Real.exp (-(s * t)) = (Ioi (0 : ℝ)).indicator
        (fun t => Real.exp (-(s * t)) * liClockMarkedDensity p r t) t := fun t => by
    by_cases ht : t ∈ Ioi (0 : ℝ)
    · rw [indicator_of_mem ht, indicator_of_mem ht, mul_comm]
    · rw [indicator_of_notMem ht, indicator_of_notMem ht, zero_mul]
  unfold GaloisForLFunctions.HTGeometry.laplace liClockThetaMarkedSourceMeasure
  rw [lintegral_withDensity_eq_lintegral_mul _ (measurable_indicator_marked p r).ennreal_ofReal
    (measurable_laplaceKernel s)]
  have e : ∀ t, ((fun t => ENNReal.ofReal ((Ioi (0 : ℝ)).indicator (liClockMarkedDensity p r) t)) *
      fun t => ENNReal.ofReal (Real.exp (-(s * t)))) t = ENNReal.ofReal ((Ioi (0 : ℝ)).indicator
        (fun t => Real.exp (-(s * t)) * liClockMarkedDensity p r t) t) := fun t => by
    simp only [Pi.mul_apply]
    rw [← ENNReal.ofReal_mul (indicator_marked_nonneg hr ha t), hfun]
  simp only [e]
  rw [← ofReal_integral_eq_lintegral_ofReal hind (ae_of_all _ fun t => by
      rw [← hfun]; exact mul_nonneg (indicator_marked_nonneg hr ha t) (Real.exp_pos _).le),
    integral_indicator measurableSet_Ioi, integral_exp_mul_liClockMarkedDensity hr hs (by
      linarith [ha.maxGrowthRate_lt]), liClockThetaReciprocalLog_eq_log_generatorReal]

/-- **(D14)** `κ` is a positive finite measure of mass `H(p)`. -/
theorem liClockThetaMarkedSourceMeasure_univ {p r : ℝ} (hr : 0 < r)
    (ha : LiClockThetaGammaReserveDomain (p - r)) : κ p r univ = ENNReal.ofReal (H p) := by
  rw [← laplace_zero, laplace_liClockThetaMarkedSourceMeasure hr ha (by linarith), add_zero,
    add_zero, div_self hr.ne', one_mul]

theorem isFiniteMeasure_liClockThetaMarkedSourceMeasure {p r : ℝ} (hr : 0 < r)
    (ha : LiClockThetaGammaReserveDomain (p - r)) : IsFiniteMeasure (κ p r) :=
  ⟨by rw [liClockThetaMarkedSourceMeasure_univ hr ha]; exact ENNReal.ofReal_lt_top⟩

theorem ae_pos_liClockThetaMarkedSourceMeasure (p r : ℝ) : ∀ᵐ t ∂κ p r, 0 < t := by
  rw [liClockThetaMarkedSourceMeasure,
    ae_withDensity_iff (measurable_indicator_marked p r).ennreal_ofReal]
  refine ae_of_all _ fun t ht => ?_
  by_contra hle
  exact ht (by rw [indicator_of_notMem (show t ∉ Ioi (0 : ℝ) from hle), ENNReal.ofReal_zero])

/-- **(D14)** Every polynomial moment of `κ` is finite. -/
theorem integrable_pow_liClockThetaMarkedSourceMeasure {p r : ℝ} (hr : 0 < r)
    (ha : LiClockThetaGammaReserveDomain (p - r)) (n : ℕ) :
    Integrable (fun t => t ^ n) (κ p r) := by
  unfold liClockThetaMarkedSourceMeasure
  rw [integrable_withDensity_iff_integrable_smul' (measurable_indicator_marked p r).ennreal_ofReal
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  have h := integrableOn_exp_mul_marked hr ha n (s := 0) (by linarith)
  simp only [zero_mul, neg_zero, Real.exp_zero, mul_one] at h
  refine ((integrable_indicator_iff measurableSet_Ioi).2 h).congr (ae_of_all _ fun t => ?_)
  simp only [smul_eq_mul]
  rw [ENNReal.toReal_ofReal (indicator_marked_nonneg hr ha t)]
  by_cases ht : t ∈ Ioi (0 : ℝ)
  · rw [indicator_of_mem ht, indicator_of_mem ht, mul_comm]
  · rw [indicator_of_notMem ht, indicator_of_notMem ht, zero_mul]

/-! ## (D15) Laplace transforms of the mark and the marked intensities -/

/-- `∫ e^{-sx} dExp_r(x) = r/(r+s)` for `s > -r`. -/
theorem laplace_expMeasure {r s : ℝ} (hr : 0 < r) (hs : -r < s) :
    Lap (expMeasure r) s = ENNReal.ofReal (r / (r + s)) := by
  have hrs : 0 < r + s := by linarith
  have hfun : ∀ x, expK r x * Real.exp (-(s * x)) =
      (Ici (0 : ℝ)).indicator (fun x => r * Real.exp (-(r + s) * x)) x := fun x => by
    unfold expK
    by_cases hx : x ∈ Ici (0 : ℝ)
    · rw [indicator_of_mem hx, indicator_of_mem hx, mul_assoc, ← Real.exp_add]
      congr 2; ring
    · rw [indicator_of_notMem hx, indicator_of_notMem hx, zero_mul]
  have hio : IntegrableOn (fun x => r * Real.exp (-(r + s) * x)) (Ici 0) :=
    (integrableOn_Ici_iff_integrableOn_Ioi (by simp)).2
      ((exp_neg_integrableOn_Ioi 0 hrs).const_mul r)
  have hind := (integrable_indicator_iff measurableSet_Ici).2 hio
  have hexp : expMeasure r = volume.withDensity (exponentialPDF r) := rfl
  unfold GaloisForLFunctions.HTGeometry.laplace
  rw [hexp, lintegral_withDensity_eq_lintegral_mul _
    (show Measurable (exponentialPDF r) from (measurable_exponentialPDFReal r).ennreal_ofReal)
    (measurable_laplaceKernel s)]
  have e : ∀ x, (exponentialPDF r * fun x => ENNReal.ofReal (Real.exp (-(s * x)))) x =
      ENNReal.ofReal ((Ici (0 : ℝ)).indicator (fun x => r * Real.exp (-(r + s) * x)) x) :=
    fun x => by
      simp only [Pi.mul_apply]
      rw [exponentialPDF_eq_expK, ← ENNReal.ofReal_mul (expK_nonneg hr.le x), hfun]
  simp only [e]
  rw [← ofReal_integral_eq_lintegral_ofReal hind (ae_of_all _ fun x => by
      rw [← hfun]; exact mul_nonneg (expK_nonneg hr.le x) (Real.exp_pos _).le),
    integral_indicator measurableSet_Ici, integral_Ici_eq_integral_Ioi, integral_const_mul,
    integral_exp_mul_Ioi (by linarith : -(r + s) < 0) 0]
  congr 1
  rw [mul_zero, Real.exp_zero]
  field_simp

/-- **(D15)** `L τ̄_p^±(s) = L τ_p^±(s) · r/(r+s)` for `s > -r`. -/
theorem laplace_liClockThetaMarkedGammaJumpMeasure (p : ℝ) {r s : ℝ} (hr : 0 < r) (hs : -r < s)
    (b : Bool) : Lap (τ̄ p r b) s = Lap (τ p b) s * ENNReal.ofReal (r / (r + s)) := by
  haveI := isProbabilityMeasure_expMeasure hr
  rw [liClockThetaMarkedGammaJumpMeasure, laplace_conv, laplace_expMeasure hr hs]

/-- **(D13)** `τ̄_p^±` is finite of mass `Λ^±`. -/
theorem liClockThetaMarkedGammaJumpMeasure_univ {p r : ℝ} (hp : W < p) (hr : 0 < r) (b : Bool) :
    τ̄ p r b univ = ENNReal.ofReal (Λ p b) := by
  rw [← laplace_zero, laplace_liClockThetaMarkedGammaJumpMeasure p hr (by linarith), laplace_zero,
    ((liClockThetaJumpMeasure_admission_wide hp).2 b).2.2.2.2.1, add_zero, div_self hr.ne',
    ENNReal.ofReal_one, mul_one]

theorem isFiniteMeasure_liClockThetaMarkedGammaJumpMeasure {p r : ℝ} (hp : W < p) (hr : 0 < r)
    (b : Bool) : IsFiniteMeasure (τ̄ p r b) :=
  ⟨by rw [liClockThetaMarkedGammaJumpMeasure_univ hp hr b]; exact ENNReal.ofReal_lt_top⟩

/-- **(D15)** The source transforms on `s ≥ 0`: `∫ e^{-st} σ_p = H(p+s)`,
`log L μ_p(s) = H(p+s) - H(p)` for the actual Gamma mixture `μ_p`, and `L κ(s) = r H(p+s)/(r+s)`. -/
theorem liClockThetaGammaExponentialMarking_laplace {p r : ℝ} (hr : 0 < r)
    (ha : LiClockThetaGammaReserveDomain (p - r)) {s : ℝ} (hs : 0 ≤ s) :
    (∫ t, Real.exp (-(s * t)) * liClockThetaSignedGammaDensity p t) = H (p + s) ∧
      Real.log (Lap (liClockThetaGammaMixture p) s).toReal = H (p + s) - H p ∧
      Lap (κ p r) s = ENNReal.ofReal (r / (r + s) * H (p + s)) := by
  have h := liClockThetaSignedGammaDensity_laplace_wide (ha.wide_add hr) hs
  exact ⟨h.2.1, h.2.2.1, laplace_liClockThetaMarkedSourceMeasure hr ha (by linarith)⟩

/-! ## (D16, D17) Compound Poisson coupling at every real time -/

private theorem conv_ae_nonneg (μ ν : Measure ℝ) [SFinite ν]
    (hμ : ∀ᵐ x ∂μ, 0 ≤ x) (hν : ∀ᵐ x ∂ν, 0 ≤ x) : ∀ᵐ x ∂μ ∗ ν, 0 ≤ x := by
  rw [Measure.conv]
  apply (ae_map_iff (by fun_prop) measurableSet_Ici).2
  apply (Measure.ae_prod_iff_ae_ae (by measurability)).2
  filter_upwards [hμ] with x hx
  filter_upwards [hν] with y hy
  exact add_nonneg hx hy

private theorem laplace_le_univ (μ : Measure ℝ) (hμ : ∀ᵐ x ∂μ, 0 ≤ x) {s : ℝ} (hs : 0 ≤ s) :
    Lap μ s ≤ μ univ := by
  unfold GaloisForLFunctions.HTGeometry.laplace
  calc ∫⁻ x, ENNReal.ofReal (Real.exp (-(s * x))) ∂μ ≤ ∫⁻ _, 1 ∂μ :=
        lintegral_mono_ae (hμ.mono fun x hx => by
          rw [ENNReal.ofReal_le_one]
          exact Real.exp_le_one_iff.2 (by nlinarith))
    _ = μ univ := lintegral_one

private theorem laplace_add_measure (μ ν : Measure ℝ) (s : ℝ) : Lap (μ + ν) s = Lap μ s + Lap ν s := by
  unfold GaloisForLFunctions.HTGeometry.laplace
  exact lintegral_add_measure _ _ _

/-- Compound Poisson laws of finite half-line intensities add under convolution: for `v ≥ 0`,
`CP(v(η + ξ)) = CP(vη) ∗ CP(vξ)`, with `CP(vη) = CP_{v m}(η/m)` for `η` of mass `m`. -/
theorem compoundPoisson_intensity_add (η ξ : Measure ℝ) [IsFiniteMeasure η] [IsFiniteMeasure ξ]
    {m n v : ℝ} (hm : 0 < m) (hn : 0 < n) (hηm : η univ = ENNReal.ofReal m)
    (hξn : ξ univ = ENNReal.ofReal n) (hη : ∀ᵐ x ∂η, 0 ≤ x) (hξ : ∀ᵐ x ∂ξ, 0 ≤ x) (hv : 0 ≤ v) :
    CP (v * (m + n)) ((ENNReal.ofReal (m + n))⁻¹ • (η + ξ)) =
      CP (v * m) ((ENNReal.ofReal m)⁻¹ • η) ∗ CP (v * n) ((ENNReal.ofReal n)⁻¹ • ξ) := by
  have hmn : 0 < m + n := add_pos hm hn
  have hsum : (η + ξ) univ = ENNReal.ofReal (m + n) := by
    rw [Measure.add_apply, hηm, hξn, ENNReal.ofReal_add hm.le hn.le]
  have hηξ : ∀ᵐ x ∂(η + ξ), 0 ≤ x := ae_add_measure_iff.2 ⟨hη, hξ⟩
  haveI := isProbabilityMeasure_inv_ofReal_smul η hm hηm
  haveI := isProbabilityMeasure_inv_ofReal_smul ξ hn hξn
  haveI := isProbabilityMeasure_inv_ofReal_smul (η + ξ) hmn hsum
  haveI := isProbabilityMeasure_compoundPoisson (v * m) (mul_nonneg hv hm.le)
    ((ENNReal.ofReal m)⁻¹ • η)
  haveI := isProbabilityMeasure_compoundPoisson (v * n) (mul_nonneg hv hn.le)
    ((ENNReal.ofReal n)⁻¹ • ξ)
  haveI := isProbabilityMeasure_compoundPoisson (v * (m + n)) (mul_nonneg hv hmn.le)
    ((ENNReal.ofReal (m + n))⁻¹ • (η + ξ))
  refine finite_halfLine_laplace_ext _ _
    (compoundPoisson_ae_nonneg _ (Measure.ae_smul_measure hηξ _) _)
    (conv_ae_nonneg _ _ (compoundPoisson_ae_nonneg _ (Measure.ae_smul_measure hη _) _)
      (compoundPoisson_ae_nonneg _ (Measure.ae_smul_measure hξ _) _)) fun s hs => ?_
  have hfη : Lap η s ≠ ∞ := ne_top_of_le_ne_top (by rw [hηm]; exact ENNReal.ofReal_ne_top)
    (laplace_le_univ η hη hs)
  have hfξ : Lap ξ s ≠ ∞ := ne_top_of_le_ne_top (by rw [hξn]; exact ENNReal.ofReal_ne_top)
    (laplace_le_univ ξ hξ hs)
  rw [laplace_conv, laplace_normalized_compoundPoisson _ hmn hsum hηξ hv hs,
    laplace_normalized_compoundPoisson _ hm hηm hη hv hs,
    laplace_normalized_compoundPoisson _ hn hξn hξ hv hs,
    ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, laplace_add_measure,
    ENNReal.toReal_add hfη hfξ]
  congr 2
  ring

theorem liClockThetaReciprocalLog_pos_of_reserveDomain {p : ℝ}
    (hp : LiClockThetaGammaReserveDomain p) : 0 < H p :=
  (liClockThetaGammaReserve_pos hp).trans (liClockThetaGammaReserve_add_le_reciprocalLog hp.wide).2

private theorem expMeasure_ae_nonneg (r : ℝ) : ∀ᵐ x ∂expMeasure r, 0 ≤ x := by
  have hexp : expMeasure r = volume.withDensity (exponentialPDF r) := rfl
  rw [hexp, ae_withDensity_iff
    (show Measurable (exponentialPDF r) from (measurable_exponentialPDFReal r).ennreal_ofReal)]
  refine ae_of_all _ fun x hx => ?_
  by_contra hneg
  exact hx (exponentialPDF_of_neg (not_le.1 hneg))

theorem liClockThetaMarkedGammaJumpMeasure_ae_nonneg {p r : ℝ} (hp : W < p) (hr : 0 < r)
    (b : Bool) : ∀ᵐ x ∂τ̄ p r b, 0 ≤ x :=
  haveI := isProbabilityMeasure_expMeasure hr
  conv_ae_nonneg _ _ ((((liClockThetaJumpMeasure_admission_wide hp).2 b).2.2.2.2.2.2).mono
    fun _ hx => hx.le) (expMeasure_ae_nonneg r)

/-- **(D16)** For every real time `v ≥ 0`, `CP(v τ̄⁺) = CP(v τ̄⁻) ∗ CP(v κ)`. -/
theorem liClockThetaMarkedCompoundPoisson_coupling {p r : ℝ} (hr : 0 < r)
    (ha : LiClockThetaGammaReserveDomain (p - r)) {v : ℝ} (hv : 0 ≤ v) :
    CP (v * Λ p true) ((ENNReal.ofReal (Λ p true))⁻¹ • τ̄ p r true) =
      CP (v * Λ p false) ((ENNReal.ofReal (Λ p false))⁻¹ • τ̄ p r false) ∗
        CP (v * H p) ((ENNReal.ofReal (H p))⁻¹ • κ p r) := by
  have hp := ha.wide_add hr
  have hH : 0 < H p := liClockThetaReciprocalLog_pos_of_reserveDomain (ha.mono (by linarith))
  have hΛ : Λ p true = Λ p false + H p := by
    linarith [(liClockThetaJumpMeasure_admission_wide hp).1]
  haveI := isFiniteMeasure_liClockThetaMarkedGammaJumpMeasure hp hr false
  haveI := isFiniteMeasure_liClockThetaMarkedSourceMeasure hr ha
  rw [hΛ, liClockThetaMarkedGammaJumpMeasure_true_eq hr ha]
  exact compoundPoisson_intensity_add _ _ ((liClockThetaJumpMeasure_admission_wide hp).2 false).1 hH
    (liClockThetaMarkedGammaJumpMeasure_univ hp hr false) (liClockThetaMarkedSourceMeasure_univ hr ha)
    (liClockThetaMarkedGammaJumpMeasure_ae_nonneg hp hr false)
    ((ae_pos_liClockThetaMarkedSourceMeasure p r).mono fun _ hx => hx.le) hv

private theorem cp_isProbability {μ : Measure ℝ} [IsFiniteMeasure μ] {m v : ℝ} (hm : 0 < m)
    (hμ : μ univ = ENNReal.ofReal m) (hv : 0 ≤ v) :
    IsProbabilityMeasure (CP (v * m) ((ENNReal.ofReal m)⁻¹ • μ)) := by
  haveI := isProbabilityMeasure_inv_ofReal_smul μ hm hμ
  exact isProbabilityMeasure_compoundPoisson _ (mul_nonneg hv hm.le) _

/-- **(D16)** The independent product coupling: under `CP(v τ̄⁻) ⊗ CP(v κ)` the first coordinate has
law `CP(v τ̄⁻)`, the sum has law `CP(v τ̄⁺)`, and the sum dominates the first coordinate. -/
theorem liClockThetaMarkedCompoundPoisson_product_coupling {p r : ℝ} (hr : 0 < r)
    (ha : LiClockThetaGammaReserveDomain (p - r)) {v : ℝ} (hv : 0 ≤ v) :
    let μ : Measure (ℝ × ℝ) :=
      (CP (v * Λ p false) ((ENNReal.ofReal (Λ p false))⁻¹ • τ̄ p r false)).prod
        (CP (v * H p) ((ENNReal.ofReal (H p))⁻¹ • κ p r))
    IsProbabilityMeasure μ ∧
      μ.map Prod.fst = CP (v * Λ p false) ((ENNReal.ofReal (Λ p false))⁻¹ • τ̄ p r false) ∧
      μ.map (fun xy => xy.1 + xy.2) =
        CP (v * Λ p true) ((ENNReal.ofReal (Λ p true))⁻¹ • τ̄ p r true) ∧
      ∀ᵐ xy ∂μ, xy.1 ≤ xy.1 + xy.2 := by
  have hp := ha.wide_add hr
  have hH : 0 < H p := liClockThetaReciprocalLog_pos_of_reserveDomain (ha.mono (by linarith))
  haveI := isFiniteMeasure_liClockThetaMarkedGammaJumpMeasure hp hr false
  haveI := isFiniteMeasure_liClockThetaMarkedSourceMeasure hr ha
  haveI := cp_isProbability ((liClockThetaJumpMeasure_admission_wide hp).2 false).1
    (liClockThetaMarkedGammaJumpMeasure_univ hp hr false) hv
  haveI := cp_isProbability hH (liClockThetaMarkedSourceMeasure_univ hr ha) hv
  have hκ := compoundPoisson_ae_nonneg _ (Measure.ae_smul_measure
    ((ae_pos_liClockThetaMarkedSourceMeasure p r).mono fun _ hx => hx.le)
      (ENNReal.ofReal (H p))⁻¹) (v * H p)
  refine ⟨inferInstance, ?_, ?_, ?_⟩
  · rw [Measure.map_fst_prod, measure_univ, one_smul]
  · rw [liClockThetaMarkedCompoundPoisson_coupling hr ha hv]
    rfl
  · exact (Measure.quasiMeasurePreserving_snd.ae hκ).mono fun xy hxy =>
      le_add_of_nonneg_right hxy

private theorem integral_le_integral_conv (μ ν : Measure ℝ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (hν : ∀ᵐ y ∂ν, 0 ≤ y) {h : ℝ → ℝ} (hh : Measurable h)
    (hmono : Monotone h) (hb : ∃ C, ∀ x, |h x| ≤ C) :
    ∫ x, h x ∂μ ≤ ∫ x, h x ∂(μ ∗ ν) := by
  obtain ⟨C, hC⟩ := hb
  haveI : IsFiniteMeasure (μ ∗ ν) := ⟨by
    rw [← laplace_zero, laplace_conv, laplace_zero, laplace_zero, measure_univ, measure_univ,
      one_mul]
    exact ENNReal.one_lt_top⟩
  have hbd : ∀ (ρ : Measure ℝ) [IsFiniteMeasure ρ] {f : ℝ → ℝ}, Measurable f →
      (∀ x, |f x| ≤ C) → Integrable f ρ := fun ρ _ f hf hfC =>
    (integrable_const C).mono' hf.aestronglyMeasurable
      (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hfC x)
  rw [integral_conv (hbd _ hh hC)]
  have hinner : ∀ x, h x ≤ ∫ y, h (x + y) ∂ν := fun x => by
    have e : ∫ _, h x ∂ν = h x := by simp
    rw [← e]
    exact integral_mono_ae (integrable_const _)
      (hbd ν (hh.comp (measurable_const.add measurable_id)) fun y => hC _)
      (hν.mono fun y hy => hmono (le_add_of_nonneg_right hy))
  refine integral_mono (hbd μ hh hC) ((integrable_const C).mono' ?_ (ae_of_all _ fun x => ?_))
    hinner
  · exact ((hh.comp (measurable_fst.add measurable_snd)).stronglyMeasurable.integral_prod_right'
      (ν := ν)).aestronglyMeasurable
  · have := norm_integral_le_of_norm_le_const (μ := ν) (f := fun y => h (x + y)) (C := C)
      (ae_of_all _ fun y => by rw [Real.norm_eq_abs]; exact hC _)
    simpa using this

/-- **(D16)** `CP(v τ̄⁺)` stochastically dominates `CP(v τ̄⁻)` at every real time `v ≥ 0`. -/
theorem liClockThetaMarkedCompoundPoisson_monotone_integral {p r : ℝ} (hr : 0 < r)
    (ha : LiClockThetaGammaReserveDomain (p - r)) {v : ℝ} (hv : 0 ≤ v) {h : ℝ → ℝ}
    (hh : Measurable h) (hmono : Monotone h) (hb : ∃ C, ∀ x, |h x| ≤ C) :
    ∫ x, h x ∂CP (v * Λ p false) ((ENNReal.ofReal (Λ p false))⁻¹ • τ̄ p r false) ≤
      ∫ x, h x ∂CP (v * Λ p true) ((ENNReal.ofReal (Λ p true))⁻¹ • τ̄ p r true) := by
  have hp := ha.wide_add hr
  have hH : 0 < H p := liClockThetaReciprocalLog_pos_of_reserveDomain (ha.mono (by linarith))
  haveI := isFiniteMeasure_liClockThetaMarkedGammaJumpMeasure hp hr false
  haveI := isFiniteMeasure_liClockThetaMarkedSourceMeasure hr ha
  haveI := cp_isProbability ((liClockThetaJumpMeasure_admission_wide hp).2 false).1
    (liClockThetaMarkedGammaJumpMeasure_univ hp hr false) hv
  haveI := cp_isProbability hH (liClockThetaMarkedSourceMeasure_univ hr ha) hv
  rw [liClockThetaMarkedCompoundPoisson_coupling hr ha hv]
  exact integral_le_integral_conv _ _ (compoundPoisson_ae_nonneg _ (Measure.ae_smul_measure
    ((ae_pos_liClockThetaMarkedSourceMeasure p r).mono fun _ hx => hx.le) _) _) hh hmono ⟨_, hb.choose_spec⟩

/-- **(D17)** `L CP(vκ)(s) = exp(v (r H(p+s)/(r+s) - H(p)))` for `s ≥ 0`; the exponent equals
`v (r/(r+s) log L μ_p(s) - s/(r+s) H(p))` for the actual Gamma mixture `μ_p`. -/
theorem laplace_liClockThetaMarkedSourcePoisson {p r : ℝ} (hr : 0 < r)
    (ha : LiClockThetaGammaReserveDomain (p - r)) {v : ℝ} (hv : 0 ≤ v) {s : ℝ} (hs : 0 ≤ s) :
    Lap (CP (v * H p) ((ENNReal.ofReal (H p))⁻¹ • κ p r)) s =
        ENNReal.ofReal (Real.exp (v * (r / (r + s) * H (p + s) - H p))) ∧
      v * (r / (r + s) * H (p + s) - H p) =
        v * (r / (r + s) * Real.log (Lap (liClockThetaGammaMixture p) s).toReal -
          s / (r + s) * H p) := by
  have hH : 0 < H p := liClockThetaReciprocalLog_pos_of_reserveDomain (ha.mono (by linarith))
  have hHps : 0 < H (p + s) := liClockThetaReciprocalLog_pos_of_reserveDomain (ha.mono (by linarith))
  have hrs : 0 < r + s := by linarith
  haveI := isFiniteMeasure_liClockThetaMarkedSourceMeasure hr ha
  obtain ⟨-, hlog, hκ⟩ := liClockThetaGammaExponentialMarking_laplace hr ha hs
  refine ⟨?_, ?_⟩
  · rw [laplace_normalized_compoundPoisson _ hH (liClockThetaMarkedSourceMeasure_univ hr ha)
      ((ae_pos_liClockThetaMarkedSourceMeasure p r).mono fun _ hx => hx.le) hv hs, hκ,
      ENNReal.toReal_ofReal (by positivity)]
  · rw [hlog]
    field_simp
    ring

/-- **(D17)** At `s = 0` the transform of `CP(vκ)` equals `1`. -/
theorem laplace_liClockThetaMarkedSourcePoisson_zero {p r : ℝ} (hr : 0 < r)
    (ha : LiClockThetaGammaReserveDomain (p - r)) {v : ℝ} (hv : 0 ≤ v) :
    Lap (CP (v * H p) ((ENNReal.ofReal (H p))⁻¹ • κ p r)) 0 = 1 := by
  rw [(laplace_liClockThetaMarkedSourcePoisson hr ha hv le_rfl).1, add_zero, add_zero,
    div_self hr.ne', one_mul, sub_self, mul_zero, Real.exp_zero, ENNReal.ofReal_one]

/-! ## (D18) Strict complete monotonicity and the compensated source sums -/

/-- `∫ t^n e^{-st} dκ = ∫_0^∞ t^n e^{-st} κ(t) dt`. -/
theorem integral_pow_exp_liClockThetaMarkedSourceMeasure {p r : ℝ} (hr : 0 < r)
    (ha : LiClockThetaGammaReserveDomain (p - r)) (n : ℕ) (s : ℝ) :
    ∫ t, t ^ n * Real.exp (-(s * t)) ∂κ p r = laplaceWeightedMoment (liClockMarkedDensity p r) n s := by
  unfold liClockThetaMarkedSourceMeasure laplaceWeightedMoment
  rw [integral_withDensity_eq_integral_toReal_smul (measurable_indicator_marked p r).ennreal_ofReal
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top), ← integral_indicator measurableSet_Ioi]
  refine integral_congr_ae (ae_of_all _ fun t => ?_)
  simp only [smul_eq_mul]
  rw [ENNReal.toReal_ofReal (indicator_marked_nonneg hr ha t)]
  by_cases ht : t ∈ Ioi (0 : ℝ)
  · rw [indicator_of_mem ht, indicator_of_mem ht]; ring
  · rw [indicator_of_notMem ht, indicator_of_notMem ht, zero_mul]

/-- **(D18)** `h(s) = r H(p+s)/(r+s)` is strictly completely monotone on `s > -r` (in particular at
`s = 0`, two-sidedly): `(-1)^n h^{(n)}(s) = ∫ t^n e^{-st} dκ(t) > 0` for every order `n`. -/
theorem iteratedDeriv_liClockThetaMarkedTransform {p r : ℝ} (hr : 0 < r)
    (ha : LiClockThetaGammaReserveDomain (p - r)) (n : ℕ) {s : ℝ} (hs : -r < s) :
    (-1) ^ n * iteratedDeriv n (fun s => r / (r + s) * H (p + s)) s =
        ∫ t, t ^ n * Real.exp (-(s * t)) ∂κ p r ∧
      0 < ∫ t, t ^ n * Real.exp (-(s * t)) ∂κ p r := by
  have hβ := ha.maxGrowthRate_lt.le
  have hev : (fun s => r / (r + s) * H (p + s)) =ᶠ[𝓝 s]
      laplaceWeightedMoment (liClockMarkedDensity p r) 0 :=
    Filter.eventually_of_mem (Ioi_mem_nhds hs) fun s' hs' => by
      show r / (r + s') * H (p + s') = _
      rw [liClockMarkedLaplace_eq hr hβ hs', liClockThetaReciprocalLog_eq_log_generatorReal,
        add_comm p s', add_comm r s']
      ring
  rw [integral_pow_exp_liClockThetaMarkedSourceMeasure hr ha, hev.iteratedDeriv_eq n,
    iteratedDeriv_liClockMarkedLaplace hr hβ n hs, ← mul_assoc, ← pow_add, ← two_mul, pow_mul,
    neg_one_sq, one_pow, one_mul]
  exact ⟨rfl, laplaceWeightedMoment_liClockMarkedDensity_pos hr hβ n hs⟩

/-- **(D18)** The compensated source sums: for `s > -r` and every `n`,
`Σ_{k≤n} (r+s)^k (-1)^k H^{(k)}(p+s)/k! = (r+s)^{n+1}/(r n!) ∫ t^n e^{-st} dκ > 0`. -/
theorem compensated_liClockThetaReciprocalLog_pos {p r : ℝ} (hr : 0 < r)
    (ha : LiClockThetaGammaReserveDomain (p - r)) (n : ℕ) {s : ℝ} (hs : -r < s) :
    ∑ k ∈ Finset.range (n + 1), (r + s) ^ k * (-1) ^ k * iteratedDeriv k H (p + s) / k.factorial =
        (r + s) ^ (n + 1) / (r * n.factorial) * ∫ t, t ^ n * Real.exp (-(s * t)) ∂κ p r ∧
      0 < ∑ k ∈ Finset.range (n + 1), (r + s) ^ k * (-1) ^ k * iteratedDeriv k H (p + s) /
        k.factorial := by
  have hβ := ha.maxGrowthRate_lt.le
  have hfun : (fun q => Real.log (liClockThetaGeneratorReal q⁻¹)) = H :=
    funext fun q => (liClockThetaReciprocalLog_eq_log_generatorReal q).symm
  have h1 := compensated_liClockMarked_eq hr hβ n hs
  have h2 := compensated_liClockMarked_pos hr hβ n hs
  rw [hfun] at h1 h2
  rw [integral_pow_exp_liClockThetaMarkedSourceMeasure hr ha]
  exact ⟨h1, h2⟩

/-- **(D18)** `|κ| ≤ τ̄⁺ + τ̄⁻`. -/
theorem liClockThetaMarkedSourceMeasure_le {p r : ℝ} (hr : 0 < r)
    (ha : LiClockThetaGammaReserveDomain (p - r)) : κ p r ≤ τ̄ p r true + τ̄ p r false := by
  rw [liClockThetaMarkedGammaJumpMeasure_true_eq hr ha, add_assoc]
  exact Measure.le_add_left (Measure.le_add_right le_rfl)

private theorem rowDensity_mul_exp_eq {p c : ℝ} {j : ℕ} (hj : 0 < j) (x : ℝ) :
    liClockThetaGammaRowDensity p j x * Real.exp (c * x) =
      p ^ (2 * j) / ((2 * j - 1).factorial : ℝ) *
        (Ioi (0 : ℝ)).indicator (fun x => x ^ (2 * j - 1) * Real.exp (-((p - c) * x))) x := by
  by_cases hx : x ∈ Ioi (0 : ℝ)
  · simp only [liClockThetaGammaRowDensity, if_neg (by omega : j ≠ 0), indicator_of_mem hx]
    rw [show -((p - c) * x) = -(p * x) + c * x by ring, Real.exp_add]
    ring
  · simp [liClockThetaGammaRowDensity, show j ≠ 0 by omega, indicator_of_notMem hx]

/-- `∫ e^{cx} dΓ_{2j,p} = (p/(p-c))^{2j}` for `c < p`, `j ≥ 1`. -/
private theorem lintegral_exp_rowLaw {p c : ℝ} (hp : 0 < p) (hc : c < p) {j : ℕ} (hj : 0 < j) :
    ∫⁻ x, ENNReal.ofReal (Real.exp (c * x)) ∂liClockThetaGammaRowLaw p j =
      ENNReal.ofReal ((p / (p - c)) ^ (2 * j)) := by
  have hpc : 0 < p - c := sub_pos.2 hc
  have hint : Integrable (fun x => liClockThetaGammaRowDensity p j x * Real.exp (c * x)) := by
    simp only [rowDensity_mul_exp_eq hj]
    exact ((integrable_indicator_iff measurableSet_Ioi).2 (powExp_integrable hpc _)).const_mul _
  rw [(liClockThetaGammaRowLaw_admission hp j).2.2.2 hj, lintegral_withDensity_eq_lintegral_mul _
    (measurable_liClockThetaGammaRowDensity p j).ennreal_ofReal (by fun_prop)]
  have e : ∀ x, ((fun x => ENNReal.ofReal (liClockThetaGammaRowDensity p j x)) *
      fun x => ENNReal.ofReal (Real.exp (c * x))) x =
        ENNReal.ofReal (liClockThetaGammaRowDensity p j x * Real.exp (c * x)) := fun x => by
    simp only [Pi.mul_apply]
    rw [ENNReal.ofReal_mul (liClockThetaGammaRowDensity_nonneg hp j x)]
  simp only [e]
  rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun x =>
    mul_nonneg (liClockThetaGammaRowDensity_nonneg hp j x) (Real.exp_pos _).le)]
  congr 1
  simp only [rowDensity_mul_exp_eq hj]
  rw [integral_const_mul, integral_indicator measurableSet_Ioi, powExp_integral hpc,
    show 2 * j - 1 + 1 = 2 * j by omega, div_pow]
  have hf : (0 : ℝ) < ((2 * j - 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  field_simp

private theorem logJump_scale {p q : ℝ} (hp : W < p) (hq : W < q) (j : ℕ) :
    ℓ p j * (p / q) ^ (2 * j) = ℓ q j := by
  have hq0 : 0 < q := liClockThetaWideThreshold_pos.trans hq
  have e := (liClockThetaUndampedJumpCoefficient_eq_scaled_wide hp j).symm.trans
    (liClockThetaUndampedJumpCoefficient_eq_scaled_wide hq j)
  rw [div_pow, mul_div_assoc', mul_comm (ℓ p j), e,
    mul_div_cancel_left₀ _ (pow_ne_zero _ hq0.ne')]

private theorem jumpPart_scale {p q : ℝ} (hp : W < p) (hq : W < q) (b : Bool) (j : ℕ) :
    liClockThetaJumpPart p b j * (p / q) ^ (2 * j) = liClockThetaJumpPart q b j := by
  have hk : 0 ≤ (p / q) ^ (2 * j) := by
    have := liClockThetaWideThreshold_pos.trans hp
    have := liClockThetaWideThreshold_pos.trans hq
    positivity
  cases b
  · simp only [liClockThetaJumpPart, Bool.false_eq_true, if_false]
    rw [max_mul_of_nonneg _ _ hk, zero_mul, neg_mul, logJump_scale hp hq]
  · simp only [liClockThetaJumpPart, if_true]
    rw [max_mul_of_nonneg _ _ hk, zero_mul, logJump_scale hp hq]

/-- **(D18)** Exponential tilting of the actual intensities: `∫ e^{ct} dτ_p^± = Λ^±_{p-c}` whenever
`p, p - c > 1/√150`. -/
theorem laplace_neg_liClockThetaGammaJumpMeasure {p c : ℝ} (hp : W < p) (hq : W < p - c)
    (b : Bool) : Lap (τ p b) (-c) = ENNReal.ofReal (Λ (p - c) b) := by
  have hp0 : 0 < p := liClockThetaWideThreshold_pos.trans hp
  have hc : c < p := by linarith [liClockThetaWideThreshold_pos]
  have hsum : Summable (liClockThetaJumpPart (p - c) b) :=
    Summable.of_nonneg_of_le (liClockThetaJumpPart_nonneg _ b)
      (liClockThetaJumpPart_le_abs _ b) (liClockThetaLogJumpCoefficient_admission_wide hq).1
  unfold GaloisForLFunctions.HTGeometry.laplace liClockThetaGammaJumpMeasure liClockThetaJumpMass
  rw [lintegral_sum_measure, ENNReal.ofReal_tsum_of_nonneg (liClockThetaJumpPart_nonneg _ b) hsum]
  refine tsum_congr fun j => ?_
  rw [lintegral_smul_measure, smul_eq_mul]
  have e : (fun x : ℝ => ENNReal.ofReal (Real.exp (-(-c * x)))) =
      fun x => ENNReal.ofReal (Real.exp (c * x)) := funext fun x => by rw [neg_mul, neg_neg]
  rw [e]
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · have h0 : ∀ q, liClockThetaJumpPart q b 0 = 0 := fun q => by
      cases b <;> simp [liClockThetaJumpPart, liClockThetaLogJumpCoefficient]
    rw [h0, h0, ENNReal.ofReal_zero, zero_mul]
  · rw [lintegral_exp_rowLaw hp0 hc hj, ← ENNReal.ofReal_mul (liClockThetaJumpPart_nonneg p b j),
      jumpPart_scale hp hq b j]

/-- **(D18)** The exponential `L¹` neighbourhood: for `0 < 2ε < r` with `p - 2ε > 1/√150`,
`∫ e^{2εt} d(τ̄⁺ + τ̄⁻)(t) = r/(r - 2ε) Σ_j |ℓ_j(p - 2ε)| < ∞`. -/
theorem laplace_neg_liClockThetaMarkedGammaJumpMeasure_add {p r ε : ℝ} (hp : W < p) (hr : 0 < r)
    (hεr : 2 * ε < r) (hq : W < p - 2 * ε) :
    Lap (τ̄ p r true + τ̄ p r false) (-(2 * ε)) =
      ENNReal.ofReal (r / (r - 2 * ε) * ∑' j, |ℓ (p - 2 * ε) j|) := by
  have habs := (liClockThetaLogJumpCoefficient_admission_wide hq).1
  have hs : ∀ b, Summable (liClockThetaJumpPart (p - 2 * ε) b) := fun b =>
    Summable.of_nonneg_of_le (liClockThetaJumpPart_nonneg _ b) (liClockThetaJumpPart_le_abs _ b) habs
  have hsumabs : Λ (p - 2 * ε) true + Λ (p - 2 * ε) false = ∑' j, |ℓ (p - 2 * ε) j| := by
    unfold liClockThetaJumpMass
    rw [← (hs true).tsum_add (hs false)]
    refine tsum_congr fun j => ?_
    simp only [liClockThetaJumpPart, if_true, Bool.false_eq_true, if_false]
    exact max_zero_add_max_neg_zero_eq_abs_self _
  have hrε : 0 < r - 2 * ε := by linarith
  have hk : 0 ≤ r / (r - 2 * ε) := by positivity
  rw [laplace_add_measure, laplace_liClockThetaMarkedGammaJumpMeasure p hr (by linarith),
    laplace_liClockThetaMarkedGammaJumpMeasure p hr (by linarith),
    laplace_neg_liClockThetaGammaJumpMeasure hp hq, laplace_neg_liClockThetaGammaJumpMeasure hp hq,
    ← add_mul, ← ENNReal.ofReal_add ((liClockThetaJumpMeasure_admission_wide hq).2 true).1.le
      ((liClockThetaJumpMeasure_admission_wide hq).2 false).1.le, hsumabs,
    ← ENNReal.ofReal_mul (tsum_nonneg fun j => abs_nonneg _), ← sub_eq_add_neg, mul_comm]

end RHTower
