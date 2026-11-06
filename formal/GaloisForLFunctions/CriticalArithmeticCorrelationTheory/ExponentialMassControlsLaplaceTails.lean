import GaloisForLFunctions.HTGeometry.IntegralCauchySchwarz
import GaloisForLFunctions.HTGeometry.RealDirichletSeries
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Topology.Algebra.Support
import Mathlib.Tactic.FunProp

/-!
# Exponential mass controls physical and polar tails

Weighted Cauchy–Schwarz bounds every truncated Laplace moment by an
explicit exponential tail. The same estimate controls physical L¹ tails
and the prime terms of the terminal polar source.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped ArithmeticFunction.vonMangoldt
namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory

/-- A truncated absolute Laplace moment is bounded by exponential square mass.
The bound is uniform over the compact support of the source. -/
theorem abs_laplace_tail_sq_le_exponential_mass {H : ℝ → ℝ}
    (hH : Continuous H) (hHc : HasCompactSupport H)
    {p q : ℝ} (hpq : 0 < p + 2 * q) (b : ℝ) :
    (∫ y in Iic b, |H y| * Real.exp (q * y)) ^ 2 ≤
      (∫ y, H y ^ 2 * Real.exp (-(p * y))) *
        (Real.exp ((p + 2 * q) * b) / (p + 2 * q)) := by
  let G : ℝ → ℝ := fun y => Real.exp (-(p * y) / 2) * |H y|
  let B : ℝ → ℝ := (Iic b).indicator fun y => Real.exp ((p + 2 * q) * y / 2)
  have hG : ∀ y, G y ^ 2 = H y ^ 2 * Real.exp (-(p * y)) := by
    intro y
    dsimp only [G]
    rw [mul_pow, sq_abs, ← Real.exp_nat_mul]
    rw [show ((2 : ℕ) : ℝ) * (-(p * y) / 2) = -(p * y) by ring, mul_comm]
  have hB : ∀ y, B y ^ 2 = (Iic b).indicator
      (fun y => Real.exp ((p + 2 * q) * y)) y := by
    intro y
    by_cases hy : y ∈ Iic b
    · simp only [B, indicator_of_mem hy]
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    · simp only [B, indicator_of_notMem hy, zero_pow (by decide : (2 : ℕ) ≠ 0)]
  have hGB : ∀ y, G y * B y = (Iic b).indicator
      (fun y => |H y| * Real.exp (q * y)) y := by
    intro y
    by_cases hy : y ∈ Iic b
    · simp only [G, B, indicator_of_mem hy]
      rw [mul_right_comm, ← Real.exp_add, mul_comm]
      congr 1
      congr 1
      ring
    · simp only [B, indicator_of_notMem hy, mul_zero]
  have hGc : HasCompactSupport (fun y => G y ^ 2) := by
    rw [hasCompactSupport_iff_eventuallyEq] at hHc ⊢
    exact hHc.mono fun y hy => by
      change H y = 0 at hy
      change G y ^ 2 = 0
      rw [hG, hy, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul]
  have hGd : Continuous G := (by fun_prop : Continuous (fun y : ℝ => Real.exp (-(p * y) / 2))).mul hH.abs
  have hBm : AEStronglyMeasurable B volume :=
    (by fun_prop : Continuous (fun y : ℝ => Real.exp ((p + 2 * q) * y / 2))).aestronglyMeasurable.indicator
      measurableSet_Iic
  have iG : Integrable (fun y => G y ^ 2) := (hGd.pow 2).integrable_of_hasCompactSupport hGc
  have iB : Integrable (fun y => B y ^ 2) := by
    simp_rw [hB]
    exact (integrable_indicator_iff measurableSet_Iic).mpr (integrableOn_exp_mul_Iic hpq b)
  have hcs := HTGeometry.sq_integral_mul_le hGd.aestronglyMeasurable hBm iG iB
  simp_rw [hG, hB, hGB] at hcs
  rw [integral_indicator measurableSet_Iic, integral_indicator measurableSet_Iic,
    integral_exp_mul_Iic hpq b] at hcs
  exact hcs

/-- The physical L¹ mass below `-A` decays as `exp(-4A)` in the eighth exponential norm. -/
theorem integral_abs_tail_sq_le_eighth_exponential_mass {H : ℝ → ℝ}
    (hH : Continuous H) (hHc : HasCompactSupport H) (A : ℝ) :
    (∫ y in Iic (-A), |H y|) ^ 2 ≤
      (∫ y, H y ^ 2 * Real.exp (-(8 * y))) * (Real.exp (-(8 * A)) / 8) := by
  have h := abs_laplace_tail_sq_le_exponential_mass hH hHc
    (p := 8) (q := 0) (by norm_num) (-A)
  simpa only [mul_zero, zero_mul, add_zero, Real.exp_zero, mul_one, mul_neg] using h

/-- The two polar Laplace moments have dual squared masses `1/7` and `1/9`. -/
theorem polar_laplace_moments_sq_le_eighth_exponential_mass {H : ℝ → ℝ}
    (hH : Continuous H) (hHc : HasCompactSupport H) :
    (∫ y in Iic 0, |H y| * Real.exp (-(y / 2))) ^ 2 ≤
        (∫ y, H y ^ 2 * Real.exp (-(8 * y))) / 7 ∧
      (∫ y in Iic 0, |H y| * Real.exp (y / 2)) ^ 2 ≤
        (∫ y, H y ^ 2 * Real.exp (-(8 * y))) / 9 := by
  constructor
  · have h := abs_laplace_tail_sq_le_exponential_mass hH hHc
      (p := 8) (q := -(1 / 2)) (by norm_num) 0
    norm_num only [show (8 : ℝ) + 2 * -(1 / 2) = 7 by norm_num,
      mul_zero, Real.exp_zero] at h
    simpa only [show ∀ y : ℝ, -(1 / 2) * y = -(y / 2) by intro y; ring,
      mul_one_div] using h
  · have h := abs_laplace_tail_sq_le_exponential_mass hH hHc
      (p := 8) (q := 1 / 2) (by norm_num) 0
    norm_num only [show (8 : ℝ) + 2 * (1 / 2) = 9 by norm_num,
      mul_zero, Real.exp_zero] at h
    simpa only [show ∀ y : ℝ, (1 / 2) * y = y / 2 by intro y; ring,
      mul_one_div] using h

/-- The prime-indexed polar moment decays as the ninth inverse power after squaring. -/
theorem prime_laplace_tail_sq_le_eighth_exponential_mass {H : ℝ → ℝ}
    (hH : Continuous H) (hHc : HasCompactSupport H) {k : ℝ} (hk : 0 < k) :
    (∫ y in Iic (-Real.log k), |H y| * Real.exp (y / 2)) ^ 2 ≤
      (∫ y, H y ^ 2 * Real.exp (-(8 * y))) / (9 * k ^ 9) := by
  have h := abs_laplace_tail_sq_le_exponential_mass hH hHc
    (p := 8) (q := 1 / 2) (by norm_num) (-Real.log k)
  norm_num only [show (8 : ℝ) + 2 * (1 / 2) = 9 by norm_num] at h
  have he : Real.exp (9 * -Real.log k) = (k ^ 9)⁻¹ := by
    rw [mul_neg, Real.exp_neg,
      show (9 : ℝ) = ((9 : ℕ) : ℝ) from rfl, Real.exp_nat_mul, Real.exp_log hk]
  rw [he] at h
  simpa only [show ∀ y : ℝ, (1 / 2) * y = y / 2 by intro y; ring,
    div_eq_mul_inv, mul_inv_rev, mul_assoc, mul_left_comm, mul_comm, one_mul] using h

/-- The unsquared prime moment has the summable `k⁻⁹ᐟ²` envelope. -/
theorem abs_prime_laplace_tail_le_eighth_exponential_mass {H : ℝ → ℝ}
    (hH : Continuous H) (hHc : HasCompactSupport H) {k : ℝ} (hk : 0 < k) :
    |∫ y in Iic (-Real.log k), H y * Real.exp (y / 2)| ≤
      k ^ (-(9 / 2 : ℝ)) * Real.sqrt (∫ y, H y ^ 2 * Real.exp (-(8 * y))) / 3 := by
  let W : ℝ := ∫ y, H y ^ 2 * Real.exp (-(8 * y))
  have hW : 0 ≤ W := integral_nonneg fun y => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le
  have he : (k ^ (-(9 / 2 : ℝ)) * Real.sqrt W / 3) ^ 2 = W / (9 * k ^ 9) := by
    rw [Real.rpow_def_of_pos hk, div_pow, mul_pow, Real.sq_sqrt hW, ← Real.exp_nat_mul]
    rw [show ((2 : ℕ) : ℝ) * (Real.log k * -(9 / 2)) = -(((9 : ℕ) : ℝ) * Real.log k) by ring,
      Real.exp_neg, Real.exp_nat_mul, Real.exp_log hk]
    field_simp [hk.ne']
    ring
  have hb := prime_laplace_tail_sq_le_eighth_exponential_mass hH hHc hk
  change _ ≤ W / (9 * k ^ 9) at hb
  rw [← he] at hb
  have hA0 : 0 ≤ ∫ y in Iic (-Real.log k), |H y| * Real.exp (y / 2) :=
    integral_nonneg fun y => mul_nonneg (abs_nonneg _) (Real.exp_pos _).le
  have hb' := (sq_le_sq₀ hA0
    (show 0 ≤ k ^ (-(9 / 2 : ℝ)) * Real.sqrt W / 3 by positivity)).mp hb
  refine le_trans ?_ hb'
  simpa only [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)] using
    norm_integral_le_integral_norm (μ := volume.restrict (Iic (-Real.log k)))
      (fun y => H y * Real.exp (y / 2))

/-- The entire prime polar functional is absolutely summable and bounded in the
eighth exponential norm, uniformly over the support of the source. -/
theorem prime_polar_functional_summable_and_bound {H : ℝ → ℝ}
    (hH : Continuous H) (hHc : HasCompactSupport H) :
    Summable (fun k : ℕ => Λ k * ∫ y in Iic (-Real.log k), H y * Real.exp (y / 2)) ∧
      |∑' k : ℕ, Λ k * ∫ y in Iic (-Real.log k), H y * Real.exp (y / 2)| ≤
        (∑' k : ℕ, Λ k * (k : ℝ) ^ (-(9 / 2 : ℝ))) *
          (Real.sqrt (∫ y, H y ^ 2 * Real.exp (-(8 * y))) / 3) := by
  let C := Real.sqrt (∫ y, H y ^ 2 * Real.exp (-(8 * y))) / 3
  let a : ℕ → ℝ := fun k => Λ k * ∫ y in Iic (-Real.log k), H y * Real.exp (y / 2)
  let b : ℕ → ℝ := fun k => (Λ k * (k : ℝ) ^ (-(9 / 2 : ℝ))) * C
  have hb : Summable b := (HTGeometry.summable_vonMangoldt_rpow
    (σ := 9 / 2) (by norm_num)).mul_right C
  have hab (k : ℕ) : ‖a k‖ ≤ b k := by
    rcases eq_or_ne k 0 with rfl | hk
    · simp [a, b]
    · dsimp only [a]
      rw [norm_mul, Real.norm_eq_abs (Λ k),
        abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg, Real.norm_eq_abs]
      have h := mul_le_mul_of_nonneg_left
        (abs_prime_laplace_tail_le_eighth_exponential_mass hH hHc (k := (k : ℝ))
          (by exact_mod_cast Nat.pos_of_ne_zero hk))
        (show 0 ≤ Λ k from ArithmeticFunction.vonMangoldt_nonneg)
      exact h.trans_eq (by dsimp only [b, C]; ring)
  have ha : Summable (fun k => ‖a k‖) :=
    hb.of_nonneg_of_le (fun k => norm_nonneg _) hab
  refine ⟨ha.of_norm, ?_⟩
  have h := (norm_tsum_le_tsum_norm ha).trans (Summable.tsum_mono ha hb hab)
  simpa only [a, b, Real.norm_eq_abs, tsum_mul_right] using h

#print axioms prime_polar_functional_summable_and_bound
#print axioms abs_prime_laplace_tail_le_eighth_exponential_mass
#print axioms polar_laplace_moments_sq_le_eighth_exponential_mass
#print axioms prime_laplace_tail_sq_le_eighth_exponential_mass
#print axioms abs_laplace_tail_sq_le_exponential_mass
#print axioms integral_abs_tail_sq_le_eighth_exponential_mass
end GaloisForLFunctions.CriticalArithmeticCorrelationTheory
