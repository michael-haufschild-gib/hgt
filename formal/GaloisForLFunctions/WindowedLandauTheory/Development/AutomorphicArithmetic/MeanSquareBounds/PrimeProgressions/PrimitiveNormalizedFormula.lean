import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.MeanSquareBounds.PrimeProgressions.PrimitiveZeroReciprocalMass
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.MeanSquareBounds.SmoothedIdentity

/-! Bound the constant term of the primitive Cesàro formula at two points below its first prime. -/

open Complex Finset WindowedLandauTheory.HC
open GaloisForLFunctions.ShortIntervalPrimesInProgressions

noncomputable section

namespace QH.PrimeProgressions

private theorem norm_primitive_zero_sum_le {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ ≠ 1) (hp : χ.IsPrimitive) {B y : ℝ} (hy : 1 < y)
    (hs : Summable (fun q : LZero χ => 1 / (‖q.point‖ * ‖1 - q.point‖)))
    (hmass : ∑' q : LZero χ, 1 / (‖q.point‖ * ‖1 - q.point‖) ≤ B) :
    ‖∑' q : LZero χ, (y : ℂ) ^ q.point / (q.point * (q.point - 1))‖ ≤ y * B := by
  have hy₀ : 0 < y := zero_lt_one.trans hy
  let f (q : LZero χ) := (y : ℂ) ^ q.point / (q.point * (q.point - 1))
  let b (q : LZero χ) := y * (1 / (‖q.point‖ * ‖1 - q.point‖))
  have hf : Summable (fun q => ‖f q‖) := (summable_cpow_div hχ hp (X := y) hy).norm
  have hb : Summable b := hs.mul_left _
  have hcomp (q : LZero χ) : ‖f q‖ ≤ b q := by
    dsimp only [f, b]
    rw [norm_div, norm_mul, norm_sub_rev q.point 1,
      Complex.norm_cpow_eq_rpow_re_of_pos hy₀, mul_one_div]
    have hpow : y ^ q.point.re ≤ y := by
      simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le hy.le (zero_re_mem hχ hp q).2.le
    exact div_le_div_of_nonneg_right hpow (by positivity)
  calc
    ‖∑' q : LZero χ, f q‖ ≤ ∑' q : LZero χ, ‖f q‖ := norm_tsum_le_tsum_norm hf
    _ ≤ ∑' q : LZero χ, b q := Summable.tsum_le_tsum hcomp hf hb
    _ = y * ∑' q : LZero χ, 1 / (‖q.point‖ * ‖1 - q.point‖) := by simp only [b, tsum_mul_left]
    _ ≤ y * B := mul_le_mul_of_nonneg_left hmass hy₀.le

/-- The primitive ramp divided by its argument equals a constant minus its zero sum,
up to a conductor-polynomial multiple of `(1 + log y)/y`. -/
theorem primitive_normalized_formula :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N),
      χ ≠ 1 → χ.IsPrimitive → ∃ K : ℂ, ∀ y : ℝ, 2 ≤ y →
        ‖An.sumLamChi χ y / (y : ℂ) - K + ∑' q : LZero χ, QH.zeroKernel y q.point‖ ≤
          C * (N : ℝ) ^ 3 * (1 + Real.log y) / y := by
  obtain ⟨C₀, hC₀, hmass⟩ := primitive_zero_reciprocal_mass
  refine ⟨26 * C₀ + 42, by positivity, ?_⟩
  intro N _ χ hχ hp
  obtain ⟨hs, hsum⟩ := hmass N χ hχ hp
  obtain ⟨β, hβ⟩ := QH.smoothed_identity hχ hp
  let B := C₀ * (N : ℝ) ^ 3
  have hB : 0 ≤ B := by positivity
  let Z (y : ℝ) := ∑' q : LZero χ, (y : ℂ) ^ q.point / (q.point * (q.point - 1))
  have hZ (y : ℝ) (hy : 1 < y) : ‖Z y‖ ≤ y * B :=
    norm_primitive_zero_sum_le hχ hp hy hs hsum
  have hsmall (y : ℝ) (hy : 1 < y) (hy₂ : y < 2) :
      ‖(y : ℂ) * An.logDerivativeAtOne χ - β‖ ≤ 2 * B + 3 := by
    have hy₀ : 0 < y := by linarith
    have hfloor : ⌊y⌋₊ = 1 := (Nat.floor_eq_iff hy₀.le).mpr (by norm_num; exact ⟨hy.le, hy₂⟩)
    have hS : An.sumLamChi χ y = 0 := by simp [An.sumLamChi, hfloor, An.abelian₂]
    have he := hβ y hy
    rw [An.gChi, if_neg hχ, hS, zero_add] at he
    have hE : ‖(y : ℂ) * An.logDerivativeAtOne χ + Z y -
        (β + efGamma χ * Complex.log y)‖ ≤ 2 :=
      he.trans ((div_le_self efD_nonneg hy.le).trans efD_le_two)
    have hZn : ‖Z y‖ ≤ 2 * B :=
      (hZ y hy).trans (mul_le_mul_of_nonneg_right hy₂.le hB)
    have hl : ‖efGamma χ * Complex.log y‖ ≤ 1 := by
      rw [norm_mul, ← Complex.ofReal_log hy₀.le, norm_real,
        Real.norm_of_nonneg (Real.log_nonneg hy.le)]
      have hl₂ := Real.log_le_log hy₀ hy₂.le
      exact mul_le_one₀ (norm_efGamma_le χ) (Real.log_nonneg hy.le)
        (by linarith only [hl₂, Real.log_two_lt_d9])
    have heq : (y : ℂ) * An.logDerivativeAtOne χ - β =
        ((y : ℂ) * An.logDerivativeAtOne χ + Z y - (β + efGamma χ * Complex.log y)) -
          Z y + efGamma χ * Complex.log y := by ring
    rw [heq]
    exact ((norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)).trans (by
      linarith only [hE, hZn, hl])
  have hβn : ‖β‖ ≤ 26 * B + 39 := by
    have h₁ := hsmall (3 / 2) (by norm_num) (by norm_num)
    have h₂ := hsmall (7 / 4) (by norm_num) (by norm_num)
    have heq : β = 6 * (((7 / 4 : ℝ) : ℂ) * An.logDerivativeAtOne χ - β) -
        7 * (((3 / 2 : ℝ) : ℂ) * An.logDerivativeAtOne χ - β) := by push_cast; ring
    rw [heq]
    refine (norm_sub_le _ _).trans ?_
    simp only [norm_mul, Complex.norm_ofNat]
    linarith only [h₁, h₂]
  refine ⟨-An.logDerivativeAtOne χ, fun y hy => ?_⟩
  have hy₀ : 0 < y := by linarith
  have hy₁ : 1 ≤ y := by linarith
  have hyc : (y : ℂ) ≠ 0 := ofReal_ne_zero.mpr hy₀.ne'
  have hn : (1 : ℝ) ≤ (N : ℝ) ^ 3 := one_le_pow₀ (by exact_mod_cast NeZero.pos N)
  have hl₀ := Real.log_nonneg hy₁
  have he := hβ y (by linarith)
  have hγ : ‖efGamma χ * Complex.log y‖ ≤ Real.log y := by
    rw [norm_mul, ← Complex.ofReal_log hy₀.le, norm_real, Real.norm_of_nonneg hl₀]
    exact mul_le_of_le_one_left hl₀ (norm_efGamma_le χ)
  have htotal : ‖An.gChi χ y + Z y‖ ≤ 26 * B + 41 + Real.log y := by
    have hE : ‖An.gChi χ y + Z y - (β + efGamma χ * Complex.log y)‖ ≤ 2 :=
      he.trans ((div_le_self efD_nonneg hy₁).trans efD_le_two)
    have h := norm_add_le (An.gChi χ y + Z y - (β + efGamma χ * Complex.log y))
      (β + efGamma χ * Complex.log y)
    rw [sub_add_cancel] at h
    exact h.trans (by linarith only [hE, (norm_add_le β _).trans (add_le_add hβn hγ)])
  rw [QH.zeroKernel_sum_eq_div]
  have heq : An.sumLamChi χ y / (y : ℂ) - (-An.logDerivativeAtOne χ) + Z y / y =
      (An.gChi χ y + Z y) / y := by
    rw [An.gChi, if_neg hχ]
    field_simp
    ring
  change ‖An.sumLamChi χ y / (y : ℂ) - (-An.logDerivativeAtOne χ) + Z y / y‖ ≤ _
  rw [heq, norm_div, norm_real, Real.norm_of_nonneg hy₀.le]
  refine div_le_div_of_nonneg_right (htotal.trans ?_) hy₀.le
  have hbase : 26 * B + 41 + Real.log y ≤ (26 * C₀ + 42) * (N : ℝ) ^ 3 +
      (26 * C₀ + 42) * (N : ℝ) ^ 3 * Real.log y := by
    have hc : 1 ≤ (26 * C₀ + 42) * (N : ℝ) ^ 3 := by nlinarith
    dsimp [B]
    nlinarith only [hn, mul_le_mul_of_nonneg_right hc hl₀]
  linarith only [hbase, mul_add ((26 * C₀ + 42) * (N : ℝ) ^ 3) 1 (Real.log y)]

end QH.PrimeProgressions
