import GaloisForLFunctions.RHTower.EisensteinLineTailParseval
import GaloisForLFunctions.RHTower.EisensteinLineConstantTerm

/-!
# Horizontal slices of the principal-subtraction Eisenstein source

Write `E(x, y) = c(y) + T(x, y)` for the completed Eisenstein series on the line in cusp
coordinates, and let the principal-subtraction source be

`g(x, y) = ‖E(x, y)‖² − 1_{y > H} ‖c(y)‖²`, `H = e²`.

For each height `y ≥ 1/2` this module computes or bounds the integrals of `g` and `g²` over one
horizontal period `[-1/2, 1/2]` in terms of the `ℓ¹` and `ℓ²` mode sums `ℓ¹(y)`, `ℓ²(y)`:

* `∫ g dx = ‖c(y)‖² + 8 ℓ²(y)` for `y ≤ H` and `= 8 ℓ²(y)` for `y > H`;
* `∫ g² dx ≤ 128 ‖Λ‖⁴ y² · 1_{y ≤ H} + 256 ‖Λ‖² y ℓ²(y) · 1_{y > H} + 1024 ℓ¹(y)² ℓ²(y)`;
* `|g(x, y)| ≤ B(t)` uniformly on `y ≥ 1/2`.

Everything rests on Parseval for `T` on a period, the zero mean of `T`, and the pointwise bound
`‖T‖ ≤ 4 ℓ¹`.
-/

open Complex MeasureTheory Set Filter Topology intervalIntegral
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.RHTower

namespace RHTower

noncomputable section

/-! ## The source in cusp coordinates -/

/-- The subtraction height `H = e²`. -/
def sourceHeight : ℝ := Real.exp 2

theorem one_lt_sourceHeight : 1 < sourceHeight := by
  unfold sourceHeight; exact Real.one_lt_exp_iff.mpr (by norm_num)

/-- `E(x, y) = c(y) + T(x, y)`, the completed Eisenstein series on the line at `x + iy`. -/
def eisLineCoord (t : ℝ) (x y : ℝ) : ℂ := eisLineConst t y + eisensteinLineTailPart t y x

theorem eisLineCoord_eq_cuspLeg (t x y : ℝ) :
    eisLineCoord t x y = d4BMCompletedEisensteinCuspLeg .scalar ((t : ℂ) * I) x y := rfl

/-- The principal-subtraction source in cusp coordinates. -/
def eisSourceCoord (t : ℝ) (x y : ℝ) : ℝ :=
  ‖eisLineCoord t x y‖ ^ 2 - (if sourceHeight < y then ‖eisLineConst t y‖ ^ 2 else 0)

/-! ## Periodicity in `x` -/

theorem eisensteinLineTailTerm_periodic (t : ℝ) (negative : Bool) (Y : ℝ) (N : ℕ) :
    Function.Periodic (fun x => eisensteinLineTailTerm t negative x Y N) 1 := by
  intro x
  simp only [eisensteinLineTailTerm_eq_coeff_mul_phase, fourierPhase_eq_exp_rate]
  congr 1
  rw [show eisensteinPhaseRate negative N * ((x + 1 : ℝ) : ℂ) =
      eisensteinPhaseRate negative N * (x : ℂ) + eisensteinPhaseRate negative N by push_cast; ring,
    Complex.exp_add, exp_eisensteinPhaseRate, mul_one]

theorem eisensteinLineTail_periodic (t : ℝ) (negative : Bool) (Y : ℝ) :
    Function.Periodic (eisensteinLineTail t negative Y) 1 := by
  intro x
  unfold eisensteinLineTail
  congr 1
  funext N
  exact eisensteinLineTailTerm_periodic t negative Y N x

theorem eisensteinLineTailPart_periodic (t Y : ℝ) :
    Function.Periodic (eisensteinLineTailPart t Y) 1 := by
  intro x
  rw [eisensteinLineTailPart_eq, eisensteinLineTailPart_eq, eisensteinLineTail_periodic,
    eisensteinLineTail_periodic]

theorem eisLineCoord_add_one (t y x : ℝ) : eisLineCoord t (x + 1) y = eisLineCoord t x y := by
  unfold eisLineCoord
  rw [eisensteinLineTailPart_periodic]

theorem eisLineCoord_periodic (t y : ℝ) : Function.Periodic (fun x => eisLineCoord t x y) 1 :=
  fun x => eisLineCoord_add_one t y x

theorem eisSourceCoord_add_one (t y x : ℝ) : eisSourceCoord t (x + 1) y = eisSourceCoord t x y := by
  unfold eisSourceCoord
  rw [eisLineCoord_add_one]

theorem eisSourceCoord_periodic (t y : ℝ) : Function.Periodic (fun x => eisSourceCoord t x y) 1 :=
  fun x => eisSourceCoord_add_one t y x

/-- A `1`-periodic function has the same integral over `[-1/2, 1/2]` and over `[0, 1]`. -/
theorem intervalIntegral_half_eq_zero_one {f : ℝ → ℝ} (hf : Function.Periodic f 1) :
    ∫ x in (-(1 / 2 : ℝ))..(1 / 2), f x = ∫ x in (0 : ℝ)..1, f x := by
  have h := hf.intervalIntegral_add_eq (-(1 / 2 : ℝ)) 0
  rw [show (-(1 / 2 : ℝ)) + 1 = 1 / 2 by norm_num, zero_add] at h
  exact h

theorem intervalIntegral_half_eq_zero_one' {f : ℝ → ℂ} (hf : Function.Periodic f 1) :
    ∫ x in (-(1 / 2 : ℝ))..(1 / 2), f x = ∫ x in (0 : ℝ)..1, f x := by
  have h := hf.intervalIntegral_add_eq (-(1 / 2 : ℝ)) 0
  rw [show (-(1 / 2 : ℝ)) + 1 = 1 / 2 by norm_num, zero_add] at h
  exact h

/-! ## Continuity in `x` -/

theorem continuous_eisLineCoord_x (t : ℝ) {y : ℝ} (hy : 1 / 2 ≤ y) :
    Continuous (fun x => eisLineCoord t x y) := by
  unfold eisLineCoord
  exact continuous_const.add (continuous_cuspTailPart_x t hy)

theorem continuous_eisSourceCoord_x (t : ℝ) {y : ℝ} (hy : 1 / 2 ≤ y) :
    Continuous (fun x => eisSourceCoord t x y) := by
  unfold eisSourceCoord
  exact ((continuous_eisLineCoord_x t hy).norm.pow 2).sub continuous_const

/-! ## The period integral of `‖E‖²` -/

/-- `‖c + T‖² = ‖c‖² + 2 Re(conj c · T) + ‖T‖²`. -/
theorem normSq_add_eq (c T : ℂ) :
    ‖c + T‖ ^ 2 = ‖c‖ ^ 2 + 2 * ((starRingEnd ℂ) c * T).re + ‖T‖ ^ 2 := by
  rw [Complex.sq_norm, Complex.sq_norm, Complex.sq_norm, Complex.normSq_add]
  have : (c * (starRingEnd ℂ) T).re = ((starRingEnd ℂ) c * T).re := by
    rw [← Complex.conj_re ((starRingEnd ℂ) c * T), map_mul, Complex.conj_conj, mul_comm]
  rw [this]; ring

/-- The cross term integrates to zero over a period. -/
theorem intervalIntegral_cross_eq_zero (t : ℝ) {y : ℝ} (hy : 1 / 2 ≤ y) :
    ∫ x in (0 : ℝ)..1, ((starRingEnd ℂ) (eisLineConst t y) * eisensteinLineTailPart t y x).re = 0 := by
  rw [integral_of_le zero_le_one]
  have hint : Integrable (fun x => (starRingEnd ℂ) (eisLineConst t y) * eisensteinLineTailPart t y x)
      (volume.restrict (Ioc (0 : ℝ) 1)) :=
    (continuous_const.mul (continuous_cuspTailPart_x t hy)).integrableOn_Ioc
  have h := integral_re hint
  simp only [RCLike.re_to_complex] at h
  rw [h, MeasureTheory.integral_const_mul]
  have h0 := setIntegral_Ioc_cuspTailPart t hy
  unfold eisensteinLineTailPart
  rw [h0, mul_zero, Complex.zero_re]

/-- **The period integral of `‖E‖²`:** `∫_0^1 ‖c + T‖² dx = ‖c‖² + 8 ℓ²(y)`. -/
theorem intervalIntegral_normSq_eisLineCoord (t : ℝ) {y : ℝ} (hy : 1 / 2 ≤ y) :
    ∫ x in (0 : ℝ)..1, ‖eisLineCoord t x y‖ ^ 2 =
      ‖eisLineConst t y‖ ^ 2 + 8 * ∑' N : ℕ, eisensteinLineModeSize t y N ^ 2 := by
  have hT := continuous_cuspTailPart_x t hy
  have hT' : Continuous (eisensteinLineTailPart t y) := hT
  simp_rw [eisLineCoord, normSq_add_eq]
  have h1 : IntervalIntegrable (fun x : ℝ => ‖eisLineConst t y‖ ^ 2 +
      2 * ((starRingEnd ℂ) (eisLineConst t y) * eisensteinLineTailPart t y x).re) volume 0 1 :=
    (continuous_const.add (continuous_const.mul (Complex.continuous_re.comp
      (continuous_const.mul hT')))).intervalIntegrable _ _
  have h2 : IntervalIntegrable (fun x : ℝ => ‖eisensteinLineTailPart t y x‖ ^ 2) volume 0 1 :=
    (hT'.norm.pow 2).intervalIntegrable _ _
  have h3 : IntervalIntegrable (fun x : ℝ => 2 *
      ((starRingEnd ℂ) (eisLineConst t y) * eisensteinLineTailPart t y x).re) volume 0 1 :=
    (continuous_const.mul (Complex.continuous_re.comp (continuous_const.mul hT'))).intervalIntegrable _ _
  rw [integral_add h1 h2, integral_add (intervalIntegrable_const (c := ‖eisLineConst t y‖ ^ 2)) h3,
    intervalIntegral.integral_const,
    intervalIntegral.integral_const_mul, intervalIntegral_cross_eq_zero t hy]
  have hP := intervalIntegral_normSq_eisensteinLineTailPart t hy
  unfold eisensteinLineTailPart at hP ⊢
  rw [hP]
  simp

/-! ## Period integrals of the source -/

/-- Below the subtraction height, `∫ g dx = ‖c‖² + 8 ℓ²`. -/
theorem intervalIntegral_eisSourceCoord_of_le (t : ℝ) {y : ℝ} (hy : 1 / 2 ≤ y)
    (hyH : y ≤ sourceHeight) :
    ∫ x in (-(1 / 2 : ℝ))..(1 / 2), eisSourceCoord t x y =
      ‖eisLineConst t y‖ ^ 2 + 8 * ∑' N : ℕ, eisensteinLineModeSize t y N ^ 2 := by
  rw [intervalIntegral_half_eq_zero_one (eisSourceCoord_periodic t y)]
  have : ∀ x, eisSourceCoord t x y = ‖eisLineCoord t x y‖ ^ 2 := by
    intro x; unfold eisSourceCoord; rw [if_neg (not_lt.mpr hyH), sub_zero]
  simp_rw [this]
  exact intervalIntegral_normSq_eisLineCoord t hy

/-- Above the subtraction height, `∫ g dx = 8 ℓ²`. -/
theorem intervalIntegral_eisSourceCoord_of_gt (t : ℝ) {y : ℝ} (hy : 1 / 2 ≤ y)
    (hyH : sourceHeight < y) :
    ∫ x in (-(1 / 2 : ℝ))..(1 / 2), eisSourceCoord t x y =
      8 * ∑' N : ℕ, eisensteinLineModeSize t y N ^ 2 := by
  rw [intervalIntegral_half_eq_zero_one (eisSourceCoord_periodic t y)]
  have : ∀ x, eisSourceCoord t x y = ‖eisLineCoord t x y‖ ^ 2 - ‖eisLineConst t y‖ ^ 2 := by
    intro x; unfold eisSourceCoord; rw [if_pos hyH]
  simp_rw [this]
  have hi : IntervalIntegrable (fun x => ‖eisLineCoord t x y‖ ^ 2) volume 0 1 :=
    ((continuous_eisLineCoord_x t hy).norm.pow 2).intervalIntegrable _ _
  rw [intervalIntegral.integral_sub hi (intervalIntegrable_const (c := ‖eisLineConst t y‖ ^ 2)),
    intervalIntegral.integral_const, intervalIntegral_normSq_eisLineCoord t hy]
  simp

/-! ## Pointwise bounds -/

/-- `‖T(x, y)‖ ≤ 4 ℓ¹(y)`. -/
theorem norm_eisensteinLineTailPart_le (t : ℝ) {y : ℝ} (hy : 1 / 2 ≤ y) (x : ℝ) :
    ‖eisensteinLineTailPart t y x‖ ≤ 4 * ∑' N : ℕ, eisensteinLineModeSize t y N :=
  norm_cuspTailPart_le t hy x

/-- Below the subtraction height, `g² ≤ 8 ‖c‖⁴ + 8 ‖T‖⁴` pointwise. -/
theorem eisSourceCoord_sq_le_of_le (t : ℝ) {y : ℝ} (hyH : y ≤ sourceHeight) (x : ℝ) :
    eisSourceCoord t x y ^ 2 ≤
      8 * ‖eisLineConst t y‖ ^ 4 + 8 * ‖eisensteinLineTailPart t y x‖ ^ 4 := by
  unfold eisSourceCoord
  rw [if_neg (not_lt.mpr hyH), sub_zero]
  have hE : ‖eisLineCoord t x y‖ ≤ ‖eisLineConst t y‖ + ‖eisensteinLineTailPart t y x‖ :=
    norm_add_le _ _
  have hc := norm_nonneg (eisLineConst t y)
  have hT := norm_nonneg (eisensteinLineTailPart t y x)
  have hE0 := norm_nonneg (eisLineCoord t x y)
  have h2 : ‖eisLineCoord t x y‖ ^ 2 ≤ 2 * ‖eisLineConst t y‖ ^ 2 +
      2 * ‖eisensteinLineTailPart t y x‖ ^ 2 := by
    nlinarith [sq_nonneg (‖eisLineConst t y‖ - ‖eisensteinLineTailPart t y x‖)]
  have h3 : (‖eisLineCoord t x y‖ ^ 2) ^ 2 ≤ (2 * ‖eisLineConst t y‖ ^ 2 +
      2 * ‖eisensteinLineTailPart t y x‖ ^ 2) ^ 2 := by
    exact pow_le_pow_left₀ (by positivity) h2 2
  nlinarith [sq_nonneg (‖eisLineConst t y‖ ^ 2 - ‖eisensteinLineTailPart t y x‖ ^ 2)]

/-- Above the subtraction height, `g² ≤ 8 ‖c‖² ‖T‖² + 2 ‖T‖⁴` pointwise. -/
theorem eisSourceCoord_sq_le_of_gt (t : ℝ) {y : ℝ} (hyH : sourceHeight < y) (x : ℝ) :
    eisSourceCoord t x y ^ 2 ≤
      8 * ‖eisLineConst t y‖ ^ 2 * ‖eisensteinLineTailPart t y x‖ ^ 2 +
        2 * ‖eisensteinLineTailPart t y x‖ ^ 4 := by
  unfold eisSourceCoord
  rw [if_pos hyH]
  unfold eisLineCoord
  rw [normSq_add_eq]
  have hre : |((starRingEnd ℂ) (eisLineConst t y) * eisensteinLineTailPart t y x).re| ≤
      ‖eisLineConst t y‖ * ‖eisensteinLineTailPart t y x‖ := by
    refine (Complex.abs_re_le_norm _).trans ?_
    rw [norm_mul, Complex.norm_conj]
  have hc := norm_nonneg (eisLineConst t y)
  have hT := norm_nonneg (eisensteinLineTailPart t y x)
  have hre' := abs_le.mp hre
  have hg : (‖eisLineConst t y‖ ^ 2 + 2 * ((starRingEnd ℂ) (eisLineConst t y) *
      eisensteinLineTailPart t y x).re + ‖eisensteinLineTailPart t y x‖ ^ 2 -
        ‖eisLineConst t y‖ ^ 2) = 2 * ((starRingEnd ℂ) (eisLineConst t y) *
      eisensteinLineTailPart t y x).re + ‖eisensteinLineTailPart t y x‖ ^ 2 := by ring
  rw [hg]
  nlinarith [sq_nonneg (2 * ((starRingEnd ℂ) (eisLineConst t y) * eisensteinLineTailPart t y x).re -
    ‖eisensteinLineTailPart t y x‖ ^ 2), mul_nonneg hc hT]

/-- The uniform pointwise bound of the source below the subtraction height. -/
theorem abs_eisSourceCoord_le_of_le (t : ℝ) {y : ℝ} (hy : 1 / 2 ≤ y) (hyH : y ≤ sourceHeight)
    (x : ℝ) :
    |eisSourceCoord t x y| ≤
      (‖eisLineConst t y‖ + 4 * ∑' N : ℕ, eisensteinLineModeSize t y N) ^ 2 := by
  unfold eisSourceCoord
  rw [if_neg (not_lt.mpr hyH), sub_zero, abs_of_nonneg (by positivity)]
  have hE : ‖eisLineCoord t x y‖ ≤ ‖eisLineConst t y‖ + ‖eisensteinLineTailPart t y x‖ :=
    norm_add_le _ _
  have hT := norm_eisensteinLineTailPart_le t hy x
  have h := norm_nonneg (eisLineCoord t x y)
  exact pow_le_pow_left₀ h (hE.trans (by linarith)) 2

/-- The uniform pointwise bound of the source above the subtraction height. -/
theorem abs_eisSourceCoord_le_of_gt (t : ℝ) {y : ℝ} (hy : 1 / 2 ≤ y) (hyH : sourceHeight < y)
    (x : ℝ) :
    |eisSourceCoord t x y| ≤
      2 * ‖eisLineConst t y‖ * (4 * ∑' N : ℕ, eisensteinLineModeSize t y N) +
        (4 * ∑' N : ℕ, eisensteinLineModeSize t y N) ^ 2 := by
  unfold eisSourceCoord
  rw [if_pos hyH]
  unfold eisLineCoord
  rw [normSq_add_eq]
  have hre : |((starRingEnd ℂ) (eisLineConst t y) * eisensteinLineTailPart t y x).re| ≤
      ‖eisLineConst t y‖ * ‖eisensteinLineTailPart t y x‖ := by
    refine (Complex.abs_re_le_norm _).trans ?_
    rw [norm_mul, Complex.norm_conj]
  have hT := norm_eisensteinLineTailPart_le t hy x
  have hc := norm_nonneg (eisLineConst t y)
  have hT0 := norm_nonneg (eisensteinLineTailPart t y x)
  have hL : 0 ≤ ∑' N : ℕ, eisensteinLineModeSize t y N := tsum_nonneg fun N =>
    eisensteinLineModeSize_nonneg t y N
  have hre' := abs_le.mp hre
  rw [show ‖eisLineConst t y‖ ^ 2 + 2 * ((starRingEnd ℂ) (eisLineConst t y) *
      eisensteinLineTailPart t y x).re + ‖eisensteinLineTailPart t y x‖ ^ 2 -
        ‖eisLineConst t y‖ ^ 2 = 2 * ((starRingEnd ℂ) (eisLineConst t y) *
      eisensteinLineTailPart t y x).re + ‖eisensteinLineTailPart t y x‖ ^ 2 by ring]
  rw [abs_le]
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left hT hc, pow_le_pow_left₀ hT0 hT 2]
  · nlinarith [mul_le_mul_of_nonneg_left hT hc, pow_le_pow_left₀ hT0 hT 2]

/-! ## Period integrals of `g²` -/

theorem intervalIntegral_normSq_tail_eq (t : ℝ) {y : ℝ} (hy : 1 / 2 ≤ y) :
    ∫ x in (0 : ℝ)..1, ‖eisensteinLineTailPart t y x‖ ^ 2 =
      8 * ∑' N : ℕ, eisensteinLineModeSize t y N ^ 2 :=
  intervalIntegral_normSq_eisensteinLineTailPart t hy

/-- `∫_0^1 ‖T‖⁴ dx ≤ 16 ℓ¹(y)² · 8 ℓ²(y)`. -/
theorem intervalIntegral_norm_tail_pow_four_le (t : ℝ) {y : ℝ} (hy : 1 / 2 ≤ y) :
    ∫ x in (0 : ℝ)..1, ‖eisensteinLineTailPart t y x‖ ^ 4 ≤
      16 * (∑' N : ℕ, eisensteinLineModeSize t y N) ^ 2 *
        (8 * ∑' N : ℕ, eisensteinLineModeSize t y N ^ 2) := by
  have hT : Continuous (eisensteinLineTailPart t y) := continuous_cuspTailPart_x t hy
  have hpt : ∀ x ∈ Icc (0 : ℝ) 1, ‖eisensteinLineTailPart t y x‖ ^ 4 ≤
      16 * (∑' N : ℕ, eisensteinLineModeSize t y N) ^ 2 * ‖eisensteinLineTailPart t y x‖ ^ 2 := by
    intro x _
    have h := norm_eisensteinLineTailPart_le t hy x
    have h0 := norm_nonneg (eisensteinLineTailPart t y x)
    have h2 : ‖eisensteinLineTailPart t y x‖ ^ 2 ≤
        (4 * ∑' N : ℕ, eisensteinLineModeSize t y N) ^ 2 := pow_le_pow_left₀ h0 h 2
    calc ‖eisensteinLineTailPart t y x‖ ^ 4 =
          ‖eisensteinLineTailPart t y x‖ ^ 2 * ‖eisensteinLineTailPart t y x‖ ^ 2 := by ring
      _ ≤ (4 * ∑' N : ℕ, eisensteinLineModeSize t y N) ^ 2 *
          ‖eisensteinLineTailPart t y x‖ ^ 2 := by gcongr
      _ = _ := by ring
  calc ∫ x in (0 : ℝ)..1, ‖eisensteinLineTailPart t y x‖ ^ 4
      ≤ ∫ x in (0 : ℝ)..1, 16 * (∑' N : ℕ, eisensteinLineModeSize t y N) ^ 2 *
          ‖eisensteinLineTailPart t y x‖ ^ 2 :=
        integral_mono_on zero_le_one ((hT.norm.pow 4).intervalIntegrable _ _)
          ((continuous_const.mul (hT.norm.pow 2)).intervalIntegrable _ _) hpt
    _ = 16 * (∑' N : ℕ, eisensteinLineModeSize t y N) ^ 2 *
          ∫ x in (0 : ℝ)..1, ‖eisensteinLineTailPart t y x‖ ^ 2 :=
        intervalIntegral.integral_const_mul _ _
    _ = _ := by rw [intervalIntegral_normSq_tail_eq t hy]

/-- Below the subtraction height: `∫ g² dx ≤ 8 ‖c‖⁴ + 1024 ℓ¹² ℓ²`. -/
theorem intervalIntegral_eisSourceCoord_sq_le_of_le (t : ℝ) {y : ℝ} (hy : 1 / 2 ≤ y)
    (hyH : y ≤ sourceHeight) :
    ∫ x in (-(1 / 2 : ℝ))..(1 / 2), eisSourceCoord t x y ^ 2 ≤
      8 * ‖eisLineConst t y‖ ^ 4 + 1024 * (∑' N : ℕ, eisensteinLineModeSize t y N) ^ 2 *
        ∑' N : ℕ, eisensteinLineModeSize t y N ^ 2 := by
  have hper : Function.Periodic (fun x => eisSourceCoord t x y ^ 2) 1 := fun x => by
    simp only [eisSourceCoord_add_one]
  rw [intervalIntegral_half_eq_zero_one hper]
  have hT : Continuous (eisensteinLineTailPart t y) := continuous_cuspTailPart_x t hy
  have hg : Continuous (fun x => eisSourceCoord t x y) := continuous_eisSourceCoord_x t hy
  have hi4 : IntervalIntegrable (fun x => 8 * ‖eisensteinLineTailPart t y x‖ ^ 4) volume 0 1 :=
    (continuous_const.mul (hT.norm.pow 4)).intervalIntegrable _ _
  have hisum : IntervalIntegrable (fun x => 8 * ‖eisLineConst t y‖ ^ 4 +
      8 * ‖eisensteinLineTailPart t y x‖ ^ 4) volume 0 1 :=
    (continuous_const.add (continuous_const.mul (hT.norm.pow 4))).intervalIntegrable _ _
  calc ∫ x in (0 : ℝ)..1, eisSourceCoord t x y ^ 2
      ≤ ∫ x in (0 : ℝ)..1, (8 * ‖eisLineConst t y‖ ^ 4 + 8 * ‖eisensteinLineTailPart t y x‖ ^ 4) :=
        integral_mono_on zero_le_one ((hg.pow 2).intervalIntegrable _ _) hisum
          (fun x _ => eisSourceCoord_sq_le_of_le t hyH x)
    _ = 8 * ‖eisLineConst t y‖ ^ 4 + 8 * ∫ x in (0 : ℝ)..1, ‖eisensteinLineTailPart t y x‖ ^ 4 := by
        rw [integral_add (intervalIntegrable_const (c := 8 * ‖eisLineConst t y‖ ^ 4)) hi4,
          intervalIntegral.integral_const, intervalIntegral.integral_const_mul]
        simp
    _ ≤ 8 * ‖eisLineConst t y‖ ^ 4 + 8 * (16 * (∑' N : ℕ, eisensteinLineModeSize t y N) ^ 2 *
          (8 * ∑' N : ℕ, eisensteinLineModeSize t y N ^ 2)) := by
        gcongr
        exact intervalIntegral_norm_tail_pow_four_le t hy
    _ = _ := by ring

/-- Above the subtraction height: `∫ g² dx ≤ 64 ‖c‖² ℓ² + 256 ℓ¹² ℓ²`. -/
theorem intervalIntegral_eisSourceCoord_sq_le_of_gt (t : ℝ) {y : ℝ} (hy : 1 / 2 ≤ y)
    (hyH : sourceHeight < y) :
    ∫ x in (-(1 / 2 : ℝ))..(1 / 2), eisSourceCoord t x y ^ 2 ≤
      64 * ‖eisLineConst t y‖ ^ 2 * (∑' N : ℕ, eisensteinLineModeSize t y N ^ 2) +
        256 * (∑' N : ℕ, eisensteinLineModeSize t y N) ^ 2 *
          ∑' N : ℕ, eisensteinLineModeSize t y N ^ 2 := by
  have hper : Function.Periodic (fun x => eisSourceCoord t x y ^ 2) 1 := fun x => by
    simp only [eisSourceCoord_add_one]
  rw [intervalIntegral_half_eq_zero_one hper]
  have hT : Continuous (eisensteinLineTailPart t y) := continuous_cuspTailPart_x t hy
  have hg : Continuous (fun x => eisSourceCoord t x y) := continuous_eisSourceCoord_x t hy
  have hi2 : IntervalIntegrable (fun x => 8 * ‖eisLineConst t y‖ ^ 2 *
      ‖eisensteinLineTailPart t y x‖ ^ 2) volume 0 1 :=
    (continuous_const.mul (hT.norm.pow 2)).intervalIntegrable _ _
  have hi4 : IntervalIntegrable (fun x => 2 * ‖eisensteinLineTailPart t y x‖ ^ 4) volume 0 1 :=
    (continuous_const.mul (hT.norm.pow 4)).intervalIntegrable _ _
  have hisum : IntervalIntegrable (fun x => 8 * ‖eisLineConst t y‖ ^ 2 *
      ‖eisensteinLineTailPart t y x‖ ^ 2 + 2 * ‖eisensteinLineTailPart t y x‖ ^ 4) volume 0 1 :=
    ((continuous_const.mul (hT.norm.pow 2)).add
      (continuous_const.mul (hT.norm.pow 4))).intervalIntegrable _ _
  calc ∫ x in (0 : ℝ)..1, eisSourceCoord t x y ^ 2
      ≤ ∫ x in (0 : ℝ)..1, (8 * ‖eisLineConst t y‖ ^ 2 * ‖eisensteinLineTailPart t y x‖ ^ 2 +
          2 * ‖eisensteinLineTailPart t y x‖ ^ 4) :=
        integral_mono_on zero_le_one ((hg.pow 2).intervalIntegrable _ _) hisum
          (fun x _ => eisSourceCoord_sq_le_of_gt t hyH x)
    _ = 8 * ‖eisLineConst t y‖ ^ 2 * (∫ x in (0 : ℝ)..1, ‖eisensteinLineTailPart t y x‖ ^ 2) +
          2 * ∫ x in (0 : ℝ)..1, ‖eisensteinLineTailPart t y x‖ ^ 4 := by
        rw [integral_add hi2 hi4, intervalIntegral.integral_const_mul,
          intervalIntegral.integral_const_mul]
    _ ≤ 8 * ‖eisLineConst t y‖ ^ 2 * (8 * ∑' N : ℕ, eisensteinLineModeSize t y N ^ 2) +
          2 * (16 * (∑' N : ℕ, eisensteinLineModeSize t y N) ^ 2 *
            (8 * ∑' N : ℕ, eisensteinLineModeSize t y N ^ 2)) := by
        rw [intervalIntegral_normSq_tail_eq t hy]
        gcongr
        exact intervalIntegral_norm_tail_pow_four_le t hy
    _ = _ := by ring

end

end RHTower
