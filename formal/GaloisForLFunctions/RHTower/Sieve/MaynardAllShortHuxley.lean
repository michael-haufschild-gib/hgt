import GaloisForLFunctions.RHTower.Sieve.HuxleyLargeValues
import Mathlib.Algebra.Order.Floor.Semifield

/-!
# Maynard's all-short raised-Huxley geometry

After grouping the at most `2k` Heath--Brown factors with `k=60`, every remaining factor has
logarithmic length exponent in `[mu/120, 3mu/120]`, where `4/3 <= mu <= 19/9`.  Relative to the
height `T0`, this is the sharper fixed interval `[1/90,19/360]`.

Choosing the first natural power that reaches exponent `9/16` therefore needs at most **51** copies
(Maynard used the coarser cap 75), and it cannot overshoot `5/8`.  The raised length `Y` lies in
`[T0^(9/16),T0^(5/8)]`.  For `sigma >= 17/18`, its Huxley local window already contains the whole
height `T0`; its diagonal term is at most `T0^(5(1-sigma)/4)`.  If `mu >= 4/3`, this becomes
`x^(15(1-sigma)/16)`, leaving the exact `x^((1-sigma)/16)` reserve that absorbs all fixed divisor
and logarithmic losses away from the Vinogradov--Korobov boundary layer.
-/

namespace RHTower.Sieve

/-- Grouping with `k=60` and `4/3 <= mu <= 19/9` sharpens the relative factor exponent to
`[1/90,19/360]`. -/
theorem maynard_grouped_factor_exponent_window {mu alpha : ℝ}
    (hmu_lo : 4 / 3 ≤ mu) (hmu_hi : mu ≤ 19 / 9)
    (halpha_lo : mu / 120 ≤ alpha) (halpha_hi : alpha ≤ 3 * mu / 120) :
    1 / 90 ≤ alpha ∧ alpha ≤ 19 / 360 := by
  constructor <;> linarith

/-- **Sharp raising exponent.**  Every exponent in `[1/90,19/360]` has a natural multiple between
`9/16` and `5/8`, and the multiplier is at most 51. -/
theorem exists_maynard_raise_multiplier {alpha : ℝ}
    (halpha_lo : 1 / 90 ≤ alpha) (halpha_hi : alpha ≤ 19 / 360) :
    ∃ q : ℕ, q ≤ 51 ∧ 9 / 16 ≤ (q : ℝ) * alpha ∧ (q : ℝ) * alpha ≤ 5 / 8 := by
  have halpha : 0 < alpha := lt_of_lt_of_le (by norm_num) halpha_lo
  let q : ℕ := ⌈(9 / 16 : ℝ) / alpha⌉₊
  have harg0 : 0 ≤ (9 / 16 : ℝ) / alpha := by positivity
  have hqlo : (9 / 16 : ℝ) / alpha ≤ (q : ℝ) := by
    exact Nat.le_ceil _
  have hqhi : (q : ℝ) ≤ (9 / 16 : ℝ) / alpha + 1 :=
    (Nat.ceil_lt_add_one harg0).le
  have hq51 : q ≤ 51 := by
    rw [Nat.ceil_le]
    rw [div_le_iff₀ halpha]
    nlinarith
  refine ⟨q, hq51, ?_, ?_⟩
  · have := mul_le_mul_of_nonneg_right hqlo halpha.le
    rw [div_mul_cancel₀ _ halpha.ne'] at this
    simpa [mul_comm] using this
  · have hmul := mul_le_mul_of_nonneg_right hqhi halpha.le
    have hcancel : (9 / 16 : ℝ) / alpha * alpha = 9 / 16 :=
      div_mul_cancel₀ _ halpha.ne'
    rw [add_mul, hcancel, one_mul] at hmul
    nlinarith

/-- Raising an actual length with exponent in the grouped window reaches Maynard's height window,
with the improved cap `q <= 51`. -/
theorem exists_maynard_raised_length {T A alpha : ℝ} (hT : 1 ≤ T)
    (hA : A = T ^ alpha)
    (halpha_lo : 1 / 90 ≤ alpha) (halpha_hi : alpha ≤ 19 / 360) :
    ∃ q : ℕ, q ≤ 51 ∧ T ^ (9 / 16 : ℝ) ≤ A ^ q ∧ A ^ q ≤ T ^ (5 / 8 : ℝ) := by
  obtain ⟨q, hq, hqlow, hqhigh⟩ :=
    exists_maynard_raise_multiplier halpha_lo halpha_hi
  have hT0 : 0 ≤ T := le_trans (by norm_num) hT
  have hpow : A ^ q = T ^ ((q : ℝ) * alpha) := by
    rw [hA, ← Real.rpow_natCast, ← Real.rpow_mul hT0]
    congr 1
    ring
  refine ⟨q, hq, ?_, ?_⟩
  · rw [hpow]
    exact Real.rpow_le_rpow_of_exponent_le hT hqlow
  · rw [hpow]
    exact Real.rpow_le_rpow_of_exponent_le hT hqhigh

/-- At `sigma >= 17/18`, the raised block's Huxley window contains the complete height `T0`. -/
theorem maynard_raised_huxley_height {T0 Y sigma : ℝ}
    (hT0 : 1 ≤ T0) (hY : T0 ^ (9 / 16 : ℝ) ≤ Y)
    (hsigma_lo : 17 / 18 ≤ sigma) :
    T0 ≤ Y ^ (4 * sigma - 2) := by
  have hT00 : 0 ≤ T0 := le_trans (by norm_num) hT0
  have hY0 : 0 ≤ Y := le_trans (Real.rpow_nonneg hT00 _) hY
  have hexp0 : 0 ≤ 4 * sigma - 2 := by linarith
  have hmono := Real.rpow_le_rpow (Real.rpow_nonneg hT00 _) hY hexp0
  have hcollapse : (T0 ^ (9 / 16 : ℝ)) ^ (4 * sigma - 2)
      = T0 ^ ((9 / 16 : ℝ) * (4 * sigma - 2)) := by
    rw [← Real.rpow_mul hT00]
  rw [hcollapse] at hmono
  have hone : (1 : ℝ) ≤ (9 / 16 : ℝ) * (4 * sigma - 2) := by linarith
  have hbase : T0 = T0 ^ (1 : ℝ) := by rw [Real.rpow_one]
  rw [hbase]
  exact (Real.rpow_le_rpow_of_exponent_le hT0 hone).trans hmono

/-- The diagonal Huxley term at `Y <= T0^(5/8)`. -/
theorem maynard_raised_huxley_diagonal {T0 Y sigma : ℝ}
    (hT0 : 1 ≤ T0) (hY0 : 0 ≤ Y) (hY : Y ≤ T0 ^ (5 / 8 : ℝ))
    (hsigma : sigma ≤ 1) :
    Y ^ (2 - 2 * sigma) ≤ T0 ^ ((5 / 4 : ℝ) * (1 - sigma)) := by
  have hexp0 : 0 ≤ 2 - 2 * sigma := by linarith
  have hmono := Real.rpow_le_rpow hY0 hY hexp0
  have hT00 : 0 ≤ T0 := le_trans (by norm_num) hT0
  have hcollapse : (T0 ^ (5 / 8 : ℝ)) ^ (2 - 2 * sigma)
      = T0 ^ ((5 / 4 : ℝ) * (1 - sigma)) := by
    rw [← Real.rpow_mul hT00]
    congr 1
    ring
  rwa [hcollapse] at hmono

/-- Converting from height to the ambient Maynard scale leaves a fixed sixteenth-power reserve. -/
theorem maynard_height_to_ambient_reserve {T0 x mu sigma : ℝ}
    (hT0 : 1 ≤ T0) (hx : x = T0 ^ mu) (hmu : 4 / 3 ≤ mu) (hsigma : sigma ≤ 1) :
    T0 ^ ((5 / 4 : ℝ) * (1 - sigma))
      ≤ x ^ ((15 / 16 : ℝ) * (1 - sigma)) := by
  have hT00 : 0 ≤ T0 := le_trans (by norm_num) hT0
  have hexp : (5 / 4 : ℝ) * (1 - sigma)
      ≤ mu * ((15 / 16 : ℝ) * (1 - sigma)) := by
    have hs0 : 0 ≤ 1 - sigma := by linarith
    nlinarith
  rw [hx, ← Real.rpow_mul hT00]
  exact Real.rpow_le_rpow_of_exponent_le hT0 hexp

/-- Exact reserve factor: the target exponent is the raised-Huxley exponent plus
`(1-sigma)/16`. -/
theorem maynard_huxley_reserve_identity {x sigma : ℝ} (hx : 0 < x) :
    x ^ ((15 / 16 : ℝ) * (1 - sigma)) * x ^ ((1 / 16 : ℝ) * (1 - sigma))
      = x ^ (1 - sigma) := by
  rw [← Real.rpow_add hx]
  congr 1
  ring

/-! ## Robust greedy-grouping window

Exact three-threshold bin packing is not needed.  A final short remainder may be merged into the
last completed group, giving the robust interval `[mu/120,4mu/120]`.  The wider window still leaves
a positive Route-T exponent reserve.
-/

/-- Greedy groups with upper mass `4mu/120` lie in the absolute exponent window
`[1/90,19/270]`. -/
theorem maynard_greedy_grouped_factor_exponent_window {mu alpha : ℝ}
    (hmu_lo : 4 / 3 ≤ mu) (hmu_hi : mu ≤ 19 / 9)
    (halpha_lo : mu / 120 ≤ alpha) (halpha_hi : alpha ≤ 4 * mu / 120) :
    1 / 90 ≤ alpha ∧ alpha ≤ 19 / 270 := by
  constructor <;> linarith

/-- In the widened greedy window, first crossing `9/16` still takes at most 51 powers and
overshoots only to `1367/2160`. -/
theorem exists_maynard_greedy_raise_multiplier {alpha : ℝ}
    (halpha_lo : 1 / 90 ≤ alpha) (halpha_hi : alpha ≤ 19 / 270) :
    ∃ q : ℕ, q ≤ 51 ∧ 9 / 16 ≤ (q : ℝ) * alpha ∧
      (q : ℝ) * alpha ≤ 1367 / 2160 := by
  have halpha : 0 < alpha := lt_of_lt_of_le (by norm_num) halpha_lo
  let q : ℕ := ⌈(9 / 16 : ℝ) / alpha⌉₊
  have harg0 : 0 ≤ (9 / 16 : ℝ) / alpha := by positivity
  have hqlo : (9 / 16 : ℝ) / alpha ≤ (q : ℝ) := Nat.le_ceil _
  have hqhi : (q : ℝ) ≤ (9 / 16 : ℝ) / alpha + 1 :=
    (Nat.ceil_lt_add_one harg0).le
  have hq51 : q ≤ 51 := by
    rw [Nat.ceil_le, div_le_iff₀ halpha]
    nlinarith
  refine ⟨q, hq51, ?_, ?_⟩
  · have := mul_le_mul_of_nonneg_right hqlo halpha.le
    rw [div_mul_cancel₀ _ halpha.ne'] at this
    simpa [mul_comm] using this
  · have hmul := mul_le_mul_of_nonneg_right hqhi halpha.le
    have hcancel : (9 / 16 : ℝ) / alpha * alpha = 9 / 16 :=
      div_mul_cancel₀ _ halpha.ne'
    rw [add_mul, hcancel, one_mul] at hmul
    nlinarith

/-- Widened raised-length window induced by robust greedy grouping. -/
theorem exists_maynard_greedy_raised_length {T A alpha : ℝ} (hT : 1 ≤ T)
    (hA : A = T ^ alpha)
    (halpha_lo : 1 / 90 ≤ alpha) (halpha_hi : alpha ≤ 19 / 270) :
    ∃ q : ℕ, q ≤ 51 ∧ T ^ (9 / 16 : ℝ) ≤ A ^ q ∧
      A ^ q ≤ T ^ (1367 / 2160 : ℝ) := by
  obtain ⟨q, hq, hqlow, hqhigh⟩ :=
    exists_maynard_greedy_raise_multiplier halpha_lo halpha_hi
  have hT0 : 0 ≤ T := le_trans (by norm_num) hT
  have hpow : A ^ q = T ^ ((q : ℝ) * alpha) := by
    rw [hA, ← Real.rpow_natCast, ← Real.rpow_mul hT0]
    congr 1
    ring
  refine ⟨q, hq, ?_, ?_⟩
  · rw [hpow]
    exact Real.rpow_le_rpow_of_exponent_le hT hqlow
  · rw [hpow]
    exact Real.rpow_le_rpow_of_exponent_le hT hqhigh

/-- Diagonal Huxley term for the widened raised-length ceiling. -/
theorem maynard_greedy_raised_huxley_diagonal {T0 Y sigma : ℝ}
    (hT0 : 1 ≤ T0) (hY0 : 0 ≤ Y) (hY : Y ≤ T0 ^ (1367 / 2160 : ℝ))
    (hsigma : sigma ≤ 1) :
    Y ^ (2 - 2 * sigma) ≤ T0 ^ ((1367 / 1080 : ℝ) * (1 - sigma)) := by
  have hexp0 : 0 ≤ 2 - 2 * sigma := by linarith
  have hmono := Real.rpow_le_rpow hY0 hY hexp0
  have hT00 : 0 ≤ T0 := le_trans (by norm_num) hT0
  have hcollapse : (T0 ^ (1367 / 2160 : ℝ)) ^ (2 - 2 * sigma) =
      T0 ^ ((1367 / 1080 : ℝ) * (1 - sigma)) := by
    rw [← Real.rpow_mul hT00]
    congr 1
    ring
  rwa [hcollapse] at hmono

/-- Robust greedy grouping still leaves the ambient exponent `73/1440`. -/
theorem maynard_greedy_height_to_ambient_reserve {T0 x mu sigma : ℝ}
    (hT0 : 1 ≤ T0) (hx : x = T0 ^ mu) (hmu : 4 / 3 ≤ mu) (hsigma : sigma ≤ 1) :
    T0 ^ ((1367 / 1080 : ℝ) * (1 - sigma)) ≤
      x ^ ((1367 / 1440 : ℝ) * (1 - sigma)) := by
  have hT00 : 0 ≤ T0 := le_trans (by norm_num) hT0
  have hexp : (1367 / 1080 : ℝ) * (1 - sigma) ≤
      mu * ((1367 / 1440 : ℝ) * (1 - sigma)) := by
    have hs0 : 0 ≤ 1 - sigma := by linarith
    nlinarith
  rw [hx, ← Real.rpow_mul hT00]
  exact Real.rpow_le_rpow_of_exponent_le hT0 hexp

/-- Exact reserve identity for the robust greedy window. -/
theorem maynard_greedy_huxley_reserve_identity {x sigma : ℝ} (hx : 0 < x) :
    x ^ ((1367 / 1440 : ℝ) * (1 - sigma)) *
        x ^ ((73 / 1440 : ℝ) * (1 - sigma)) =
      x ^ (1 - sigma) := by
  rw [← Real.rpow_add hx]
  congr 1
  ring

end RHTower.Sieve
