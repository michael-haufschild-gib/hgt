import GaloisForLFunctions.HTGeometry.BeukersZetaTwoKernelSeries
import GaloisForLFunctions.HTGeometry.BeukersZetaTwoIntegrationByParts

/-!
# Beukers' linear forms in `1` and `ζ(2)`

With `Pₙ = Σ_r p_r xʳ` the shifted Legendre polynomial and `(1 − y)ⁿ = Σ_s q_s yˢ`, the integral
`Iₙ = ∫₀¹ (y(1 − y))ⁿ ∫₀¹ (x(1 − x))ⁿ/(1 − xy)^{n+1} dx dy` satisfies

* `integral_beukersIntegrand` : `Iₙ = (−1)ⁿ Σ_{r,s} p_r q_s J(r, s)`;
* `integral_beukersIntegrand_le` : `Iₙ ≤ 10⁻ⁿ π²/6`, from `10 x(1−x) y(1−y) ≤ 1 − xy`;
* `integral_beukersIntegrand_ge` : `Iₙ ≥ (9/256)ⁿ/4`;
* `lcm_sq_mul_sum_eq` : with `dₙ = lcm(1, …, n)`,
  `dₙ² Σ_{r,s} p_r q_s J(r, s) = Aₙ π²/6 + Bₙ` for integers `Aₙ, Bₙ`, and `|Aₙ| ≤ dₙ²(n+1)16ⁿ`.
-/

open Polynomial MeasureTheory Set Finset

namespace GaloisForLFunctions.HTGeometry.BeukersZetaTwo

/-- **The key inequality** `10 x(1−x) y(1−y) ≤ 1 − xy` on the unit square. -/
theorem ten_mul_le_one_sub_mul {x y : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy0 : 0 ≤ y)
    (hy1 : y ≤ 1) : 10 * (x * (1 - x) * (y * (1 - y))) ≤ 1 - x * y := by
  set t := Real.sqrt (x * y) with htdef
  have ht : t ^ 2 = x * y := Real.sq_sqrt (mul_nonneg hx0 hy0)
  have ht0 : 0 ≤ t := Real.sqrt_nonneg _
  have hxy1 : x * y ≤ 1 := by nlinarith
  have ht1 : t ≤ 1 := by rw [htdef, Real.sqrt_le_one]; exact hxy1
  have hsum : 2 * t ≤ x + y := by
    have h1 : t = Real.sqrt x * Real.sqrt y := Real.sqrt_mul hx0 y
    nlinarith [sq_nonneg (Real.sqrt x - Real.sqrt y), Real.sq_sqrt hx0, Real.sq_sqrt hy0]
  have hprod : (1 - x) * (1 - y) ≤ (1 - t) ^ 2 := by nlinarith
  have hcubic : 10 * t ^ 2 * (1 - t) ≤ 1 + t := by
    nlinarith [mul_nonneg ht0 (sq_nonneg (t - 3 / 5)), sq_nonneg (t - 13 / 20)]
  have h1 : x * y * ((1 - x) * (1 - y)) ≤ t ^ 2 * (1 - t) ^ 2 := by
    rw [ht]; exact mul_le_mul_of_nonneg_left hprod (mul_nonneg hx0 hy0)
  have h2 : 10 * (t ^ 2 * (1 - t) ^ 2) ≤ (1 - t) * (1 + t) := by
    have := mul_le_mul_of_nonneg_left hcubic (sub_nonneg.mpr ht1)
    nlinarith
  have e : x * (1 - x) * (y * (1 - y)) = x * y * ((1 - x) * (1 - y)) := by ring
  rw [e]
  nlinarith

/-- `∫₀¹ (x(1 − x))ⁿ/(1 − xy)^{n+1} dx`. -/
noncomputable def posInner (n : ℕ) (y : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..1, (x * (1 - x)) ^ n / (1 - x * y) ^ (n + 1)

/-- The integrand `(y(1 − y))ⁿ ∫₀¹ (x(1 − x))ⁿ/(1 − xy)^{n+1} dx` of `Iₙ`. -/
noncomputable def beukersIntegrand (n : ℕ) (y : ℝ) : ℝ := (y * (1 - y)) ^ n * posInner n y

/-- Coefficients `p_r = (−1)ʳ C(n, r) C(n + r, n)` of the shifted Legendre polynomial. -/
def legCoeff (n r : ℕ) : ℤ := (-1) ^ r * n.choose r * (n + r).choose n

/-- Coefficients `q_s = (−1)ˢ C(n, s)` of `(1 − y)ⁿ`. -/
def binCoeff (n s : ℕ) : ℤ := (-1) ^ s * n.choose s

theorem legendreR_eval (n : ℕ) (x : ℝ) :
    (legendreR n).eval x = ∑ r ∈ range (n + 1), (legCoeff n r : ℝ) * x ^ r := by
  rw [legendreR, eval_map, shiftedLegendre, eval₂_finsetSum]
  refine sum_congr rfl fun r _ => ?_
  rw [eval₂_mul, eval₂_C, eval₂_X_pow, eq_intCast]
  rfl

theorem one_sub_pow_eq_sum (n : ℕ) (y : ℝ) :
    (1 - y) ^ n = ∑ s ∈ range (n + 1), (binCoeff n s : ℝ) * y ^ s := by
  rw [sub_eq_add_neg, add_comm, add_pow]
  refine sum_congr rfl fun s _ => ?_
  rw [binCoeff, one_pow, mul_one, neg_pow]
  push_cast
  ring

theorem continuousOn_pow_div_one_sub {r : ℕ} {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y < 1) :
    ContinuousOn (fun x : ℝ => x ^ r / (1 - x * y)) (uIcc 0 1) := by
  refine (continuous_pow r).continuousOn.div (by fun_prop) fun x hx => ?_
  rw [Set.uIcc_of_le zero_le_one] at hx
  exact (one_sub_mul_pos hx.1 hx.2 hy0 hy1).ne'

/-- **Inner identity.**  For `0 ≤ y < 1`,
`(y(1−y))ⁿ ∫₀¹ (x(1−x))ⁿ/(1 − xy)^{n+1} dx = (−1)ⁿ Σ_{r,s} p_r q_s yˢ Σ_k yᵏ/(r+k+1)`. -/
theorem beukersIntegrand_eq (n : ℕ) {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y < 1) :
    beukersIntegrand n y = (-1) ^ n * ∑ r ∈ range (n + 1), ∑ s ∈ range (n + 1),
      (legCoeff n r : ℝ) * binCoeff n s * (y ^ s * kernelInner r y) := by
  have hM2 := integral_legendre_div_one_sub_mul n hy0 hy1
  have hlin : ∫ x in (0 : ℝ)..1, (legendreR n).eval x / (1 - x * y) =
      ∑ r ∈ range (n + 1), (legCoeff n r : ℝ) * kernelInner r y := by
    simp_rw [legendreR_eval, sum_div]
    rw [intervalIntegral.integral_finsetSum fun r _ => by
      simpa [mul_div_assoc] using
        ((continuousOn_pow_div_one_sub (r := r) hy0 hy1).intervalIntegrable).const_mul
          (legCoeff n r : ℝ)]
    refine sum_congr rfl fun r _ => ?_
    simp_rw [mul_div_assoc]
    rw [intervalIntegral.integral_const_mul, integral_pow_div_one_sub_mul hy0 hy1]
  rw [hlin] at hM2
  have hsq : (-1 : ℝ) ^ n * (-1) ^ n = 1 := by rw [← mul_pow]; norm_num
  have hy : y ^ n * posInner n y = (-1) ^ n * ∑ r ∈ range (n + 1),
      (legCoeff n r : ℝ) * kernelInner r y := by
    rw [hM2, posInner]
    linear_combination (-(y ^ n * ∫ x in (0 : ℝ)..1, (x * (1 - x)) ^ n /
      (1 - x * y) ^ (n + 1))) * hsq
  have hsplit : beukersIntegrand n y = (1 - y) ^ n * (y ^ n * posInner n y) := by
    unfold beukersIntegrand; rw [mul_pow]; ring
  rw [hsplit, hy, one_sub_pow_eq_sum]
  simp only [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun s _ => by ring

/-- `kernelPair` is symmetric. -/
theorem kernelPair_comm (r s : ℕ) : kernelPair r s = kernelPair s r := by
  unfold kernelPair
  refine tsum_congr fun k => by ring

theorem ae_ne_one : ∀ᵐ y ∂(volume.restrict (Ioc (0 : ℝ) 1)), y ∈ Ioo (0 : ℝ) 1 := by
  rw [ae_restrict_iff' measurableSet_Ioc]
  have hne : ∀ᵐ y ∂(volume : Measure ℝ), y ≠ 1 := ae_iff.mpr (by simp)
  filter_upwards [hne] with y hy1 hy
  exact ⟨hy.1, lt_of_le_of_ne hy.2 hy1⟩

/-- **Integral of the Beukers integrand.** -/
theorem integrable_and_integral_beukersIntegrand (n : ℕ) :
    Integrable (beukersIntegrand n) (volume.restrict (Ioc (0 : ℝ) 1)) ∧
      ∫ y in Ioc (0 : ℝ) 1, beukersIntegrand n y = (-1) ^ n * ∑ r ∈ range (n + 1),
        ∑ s ∈ range (n + 1), (legCoeff n r : ℝ) * binCoeff n s * kernelPair r s := by
  set g : ℝ → ℝ := fun y => (-1) ^ n * ∑ r ∈ range (n + 1), ∑ s ∈ range (n + 1),
    (legCoeff n r : ℝ) * binCoeff n s * (y ^ s * kernelInner r y) with hg
  have hae : beukersIntegrand n =ᵐ[volume.restrict (Ioc (0 : ℝ) 1)] g := by
    filter_upwards [ae_ne_one] with y hy
    exact beukersIntegrand_eq n hy.1.le hy.2
  have hint : ∀ r s, Integrable (fun y => (legCoeff n r : ℝ) * binCoeff n s *
      (y ^ s * kernelInner r y)) (volume.restrict (Ioc (0 : ℝ) 1)) := fun r s =>
    (integral_pow_mul_kernelInner r s).1.const_mul _
  have hgint : Integrable g (volume.restrict (Ioc (0 : ℝ) 1)) :=
    (integrable_finsetSum _ fun r _ => integrable_finsetSum _ fun s _ => hint r s).const_mul _
  refine ⟨hgint.congr hae.symm, ?_⟩
  rw [integral_congr_ae hae, hg, integral_const_mul, integral_finsetSum _ fun r _ =>
    integrable_finsetSum _ fun s _ => hint r s]
  congr 1
  refine sum_congr rfl fun r _ => ?_
  rw [integral_finsetSum _ fun s _ => hint r s]
  refine sum_congr rfl fun s _ => ?_
  rw [integral_const_mul, (integral_pow_mul_kernelInner r s).2]

/-! ### Size of `Iₙ` -/

theorem posInner_nonneg (n : ℕ) {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1) : 0 ≤ posInner n y := by
  unfold posInner
  refine intervalIntegral.integral_nonneg zero_le_one fun x hx => ?_
  have h1 : 0 ≤ 1 - x * y := by nlinarith [hx.1, hx.2]
  exact div_nonneg (pow_nonneg (mul_nonneg hx.1 (by linarith [hx.2])) _) (pow_nonneg h1 _)

theorem beukersIntegrand_nonneg (n : ℕ) {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    0 ≤ beukersIntegrand n y :=
  mul_nonneg (pow_nonneg (mul_nonneg hy0 (by linarith)) _) (posInner_nonneg n hy0 hy1)

theorem beukersIntegrand_le (n : ℕ) {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y < 1) :
    beukersIntegrand n y ≤ (1 / 10) ^ n * kernelInner 0 y := by
  have hk : kernelInner 0 y = ∫ x in (0 : ℝ)..1, 1 / (1 - x * y) := by
    rw [← integral_pow_div_one_sub_mul (r := 0) hy0 hy1]; simp
  rw [hk, beukersIntegrand, posInner, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_mono_on zero_le_one ?_ ?_ fun x hx => ?_
  · refine ContinuousOn.intervalIntegrable ?_
    refine continuousOn_const.mul (ContinuousOn.div (by fun_prop) (by fun_prop) fun x hx => ?_)
    rw [Set.uIcc_of_le zero_le_one] at hx
    exact pow_ne_zero _ (one_sub_mul_pos hx.1 hx.2 hy0 hy1).ne'
  · refine ContinuousOn.intervalIntegrable ?_
    refine continuousOn_const.mul (ContinuousOn.div (by fun_prop) (by fun_prop) fun x hx => ?_)
    rw [Set.uIcc_of_le zero_le_one] at hx
    exact (one_sub_mul_pos hx.1 hx.2 hy0 hy1).ne'
  · have hpos := one_sub_mul_pos hx.1 hx.2 hy0 hy1
    have hkey := ten_mul_le_one_sub_mul hx.1 hx.2 hy0 hy1.le
    have hxx : 0 ≤ x * (1 - x) := mul_nonneg hx.1 (by linarith [hx.2])
    have hyy : 0 ≤ y * (1 - y) := mul_nonneg hy0 (by linarith)
    have hratio : x * (1 - x) * (y * (1 - y)) / (1 - x * y) ≤ 1 / 10 := by
      rw [div_le_iff₀ hpos]; linarith
    have hr0 : 0 ≤ x * (1 - x) * (y * (1 - y)) / (1 - x * y) := by positivity
    calc (y * (1 - y)) ^ n * ((x * (1 - x)) ^ n / (1 - x * y) ^ (n + 1)) =
        (x * (1 - x) * (y * (1 - y)) / (1 - x * y)) ^ n * (1 / (1 - x * y)) := by
          generalize x * (1 - x) = A
          generalize y * (1 - y) = Y
          generalize 1 - x * y = B
          rw [div_pow, mul_pow, pow_succ]
          ring
      _ ≤ (1 / 10) ^ n * (1 / (1 - x * y)) := by
          gcongr

theorem integral_beukersIntegrand_le (n : ℕ) :
    ∫ y in Ioc (0 : ℝ) 1, beukersIntegrand n y ≤ (1 / 10) ^ n * (Real.pi ^ 2 / 6) := by
  have h00 := integral_pow_mul_kernelInner 0 0
  simp only [pow_zero, one_mul] at h00
  have hJ : kernelPair 0 0 = Real.pi ^ 2 / 6 := by rw [kernelPair_self]; simp
  calc ∫ y in Ioc (0 : ℝ) 1, beukersIntegrand n y ≤
      ∫ y in Ioc (0 : ℝ) 1, (1 / 10) ^ n * kernelInner 0 y := by
        refine integral_mono_of_nonneg ?_ (h00.1.const_mul _) ?_
        · filter_upwards [ae_ne_one] with y hy
          exact beukersIntegrand_nonneg n hy.1.le hy.2.le
        · filter_upwards [ae_ne_one] with y hy
          exact beukersIntegrand_le n hy.1.le hy.2
    _ = (1 / 10) ^ n * (Real.pi ^ 2 / 6) := by rw [integral_const_mul, h00.2, hJ]

theorem integral_pow_mul_one_sub_ge (n : ℕ) :
    (1 / 2) * (3 / 16 : ℝ) ^ n ≤ ∫ x in (0 : ℝ)..1, (x * (1 - x)) ^ n := by
  have hcont : Continuous fun x : ℝ => (x * (1 - x)) ^ n := by fun_prop
  have hnn : ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ 1 → 0 ≤ ∫ x in a..b, (x * (1 - x)) ^ n :=
    fun a b ha hab hb => intervalIntegral.integral_nonneg hab fun x hx =>
      pow_nonneg (mul_nonneg (by linarith [hx.1]) (by linarith [hx.2])) _
  have hsplit := (intervalIntegral.integral_add_adjacent_intervals
    (hcont.intervalIntegrable (μ := volume) 0 (1 / 4))
    (hcont.intervalIntegrable (μ := volume) (1 / 4) 1)).symm
  have hsplit2 := (intervalIntegral.integral_add_adjacent_intervals
    (hcont.intervalIntegrable (μ := volume) (1 / 4) (3 / 4))
    (hcont.intervalIntegrable (μ := volume) (3 / 4) 1)).symm
  have hmid : (3 / 4 - 1 / 4) * (3 / 16 : ℝ) ^ n ≤
      ∫ x in (1 / 4 : ℝ)..(3 / 4), (x * (1 - x)) ^ n := by
    have := intervalIntegral.integral_mono_on (μ := volume) (f := fun _ => (3 / 16 : ℝ) ^ n)
      (g := fun x => (x * (1 - x)) ^ n) (by norm_num : (1 / 4 : ℝ) ≤ 3 / 4)
      (continuous_const.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)
      (fun x hx => pow_le_pow_left₀ (by norm_num)
        (by nlinarith [mul_nonneg (sub_nonneg.2 hx.1) (sub_nonneg.2 hx.2)]) n)
    rw [intervalIntegral.integral_const, smul_eq_mul] at this
    linarith
  have h0 := hnn 0 (1 / 4) le_rfl (by norm_num) (by norm_num)
  have h1 := hnn (3 / 4) 1 (by norm_num) (by norm_num) le_rfl
  rw [hsplit, hsplit2]
  nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 16) n]

theorem posInner_ge (n : ℕ) {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y < 1) :
    (1 / 2) * (3 / 16 : ℝ) ^ n ≤ posInner n y := by
  refine (integral_pow_mul_one_sub_ge n).trans ?_
  unfold posInner
  refine intervalIntegral.integral_mono_on zero_le_one
    ((by fun_prop : Continuous fun x : ℝ => (x * (1 - x)) ^ n).intervalIntegrable _ _) ?_ ?_
  · refine ContinuousOn.intervalIntegrable (ContinuousOn.div (by fun_prop) (by fun_prop) ?_)
    intro x hx
    rw [Set.uIcc_of_le zero_le_one] at hx
    exact pow_ne_zero _ (one_sub_mul_pos hx.1 hx.2 hy0 hy1).ne'
  · intro x hx
    have hpos := one_sub_mul_pos hx.1 hx.2 hy0 hy1
    have hle : (1 - x * y) ^ (n + 1) ≤ 1 := pow_le_one₀ hpos.le (by nlinarith [hx.1])
    have hnn : 0 ≤ (x * (1 - x)) ^ n := pow_nonneg (mul_nonneg hx.1 (by linarith [hx.2])) _
    rw [le_div_iff₀ (pow_pos hpos _)]
    exact mul_le_of_le_one_right hnn hle

theorem integral_beukersIntegrand_ge (n : ℕ) :
    (1 / 4) * (9 / 256 : ℝ) ^ n ≤ ∫ y in Ioc (0 : ℝ) 1, beukersIntegrand n y := by
  have hint := (integrable_and_integral_beukersIntegrand n).1
  have hsub : Icc (1 / 4 : ℝ) (3 / 4) ⊆ Ioc 0 1 := fun y hy =>
    ⟨by linarith [hy.1], by linarith [hy.2]⟩
  have hlow : ∀ y ∈ Icc (1 / 4 : ℝ) (3 / 4),
      (1 / 2) * (9 / 256 : ℝ) ^ n ≤ beukersIntegrand n y := by
    intro y hy
    have h1 : (3 / 16 : ℝ) ≤ y * (1 - y) := by nlinarith [hy.1, hy.2]
    have h2 := posInner_ge n (by linarith [hy.1]) (by linarith [hy.2])
    have h3 : (3 / 16 : ℝ) ^ n ≤ (y * (1 - y)) ^ n := pow_le_pow_left₀ (by norm_num) h1 n
    have e : (1 / 2) * (9 / 256 : ℝ) ^ n = (3 / 16) ^ n * ((1 / 2) * (3 / 16) ^ n) := by
      rw [show (9 / 256 : ℝ) = 3 / 16 * (3 / 16) by norm_num, mul_pow]; ring
    rw [e, beukersIntegrand]
    exact mul_le_mul h3 h2 (by positivity) (pow_nonneg (by nlinarith [hy.1, hy.2]) _)
  have hge := setIntegral_ge_of_const_le (μ := volume) measurableSet_Icc
    (by simp [Real.volume_Icc]) hlow (hint.mono_measure (Measure.restrict_mono hsub le_rfl))
  have hvol : volume.real (Icc (1 / 4 : ℝ) (3 / 4)) = 1 / 2 := by
    rw [Real.volume_real_Icc_of_le (by norm_num)]; norm_num
  rw [hvol, smul_eq_mul] at hge
  have hmono : ∫ y in Icc (1 / 4 : ℝ) (3 / 4), beukersIntegrand n y ≤
      ∫ y in Ioc (0 : ℝ) 1, beukersIntegrand n y := by
    refine setIntegral_mono_set hint ?_ (Filter.Eventually.of_forall hsub)
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
    exact beukersIntegrand_nonneg n hy.1.le hy.2
  calc (1 / 4) * (9 / 256 : ℝ) ^ n = 1 / 2 * ((1 / 2) * (9 / 256 : ℝ) ^ n) := by ring
    _ ≤ _ := hge
    _ ≤ _ := hmono

end GaloisForLFunctions.HTGeometry.BeukersZetaTwo
