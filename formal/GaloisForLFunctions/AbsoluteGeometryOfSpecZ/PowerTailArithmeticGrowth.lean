import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.PowerTailContactDirichletCoefficients
import GaloisForLFunctions.RHTower.PowerGrowthUnderArithmeticConvolution
import GaloisForLFunctions.HTGeometry.ArithmeticPowerDilation

/-!
# Arithmetic inversion of power-tail contacts

The weights `n⁻ᵃ` are completely multiplicative. Their twists of the
constant and Möbius arithmetic functions are convolution inverses.
This makes the contact convolution invertible within its power-growth class.
-/

noncomputable section

open Finset ArithmeticFunction
open scoped ArithmeticFunction.zeta Moebius ArithmeticFunction.vonMangoldt

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

/-- Multiplicative real power weight, including the zero index. -/
def powerTailWeightHom (a : ℝ) : ℕ →* ℝ where
  toFun := powerTailWeight a
  map_one' := by simp [powerTailWeight]
  map_mul' m n := by
    simp only [powerTailWeight, Nat.cast_mul]
    exact Real.mul_rpow (Nat.cast_nonneg m) (Nat.cast_nonneg n)

/-- Coefficient multiplication by `n⁻ᵃ` preserves arithmetic convolution. -/
def powerTailTwist (a : ℝ) : ArithmeticFunction ℝ →+* ArithmeticFunction ℝ :=
  RHTower.arithmeticTwistRingHom (powerTailWeightHom a)

@[simp] theorem powerTailTwist_apply (a : ℝ) (f : ArithmeticFunction ℝ) (n : ℕ) :
    powerTailTwist a f n = powerTailWeight a n * f n := rfl

/-- Weighted constant arithmetic function. -/
def powerTailZeta (a : ℝ) : ArithmeticFunction ℝ :=
  powerTailTwist a (ζ : ArithmeticFunction ℝ)

/-- Weighted Möbius arithmetic function. -/
def powerTailMoebius (a : ℝ) : ArithmeticFunction ℝ :=
  powerTailTwist a (μ : ArithmeticFunction ℝ)

/-- The weighted constant and Möbius coefficients cancel exactly. -/
theorem powerTailMoebius_mul_powerTailZeta (a : ℝ) :
    powerTailMoebius a * powerTailZeta a = 1 := by
  rw [powerTailMoebius, powerTailZeta, ← map_mul,
    ArithmeticFunction.coe_moebius_mul_coe_zeta, map_one]

@[simp] theorem powerTailZeta_apply {n : ℕ} (hn : n ≠ 0) (a : ℝ) :
    powerTailZeta a n = powerTailWeight a n := by
  simp [powerTailZeta, hn]

/-- A bounded arithmetic coefficient has the usual shifted absolute abscissa. -/
theorem summable_abs_powerTailTwist (f : ArithmeticFunction ℝ) (a σ : ℝ)
    (hf : ∀ n, |f n| ≤ 1) (haσ : 1 < a + σ) :
    Summable (fun n : ℕ => |powerTailTwist a f n| * (n : ℝ) ^ (-σ)) := by
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
    (Real.summable_nat_rpow.2 (show -(a + σ) < -1 by linarith only [haσ]))
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [ArithmeticFunction.map_zero, abs_zero, zero_mul]
    exact Real.rpow_nonneg (Nat.cast_nonneg 0) _
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  rw [powerTailTwist_apply, powerTailWeight, abs_mul,
    abs_of_nonneg (Real.rpow_nonneg hnR.le _)]
  calc
    _ ≤ (n : ℝ) ^ (-a) * 1 * (n : ℝ) ^ (-σ) := by
      gcongr
      exact hf n
    _ = (n : ℝ) ^ (-(a + σ)) := by
      rw [mul_one, ← Real.rpow_add hnR]
      congr 1
      ring

/-- Convolution by `n⁻ᵃ` preserves all strict growth bounds at and above `1-a`.
The reverse implication follows from the equally summable Möbius inverse. -/
theorem partialSumPowerBound_powerTailZeta_mul_iff (a θ : ℝ)
    (hθ : 0 ≤ θ) (haθ : 1 ≤ a + θ) (f : ArithmeticFunction ℝ) :
    RHTower.PartialSumPowerBound (fun n => (powerTailZeta a * f) (n + 1)) θ ↔
      RHTower.PartialSumPowerBound (fun n => f (n + 1)) θ := by
  apply RHTower.partialSumPowerBound_convolution_iff
    (g := powerTailMoebius a) hθ
    (by rw [mul_comm]; exact powerTailMoebius_mul_powerTailZeta a)
  · intro δ hδ
    apply summable_abs_powerTailTwist _ a (θ + δ) _ (by linarith only [haθ, hδ])
    intro n
    by_cases hn : n = 0 <;> simp [hn]
  · intro δ hδ
    apply summable_abs_powerTailTwist _ a (θ + δ) _ (by linarith only [haθ, hδ])
    intro n
    change |(ArithmeticFunction.moebius n : ℝ)| ≤ 1
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := n)

/-- Power-tail contacts are a literal Dirichlet convolution. -/
theorem powerTailContactCoefficient_eq_convolution (a : ℝ) (n : ℕ) :
    powerTailContactCoefficient a n =
      (powerTailZeta (2 * a) * powerTailTwist a ArithmeticFunction.vonMangoldt) n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [powerTailContactCoefficient]
  rw [mul_comm, ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal (fun d m =>
      powerTailTwist a ArithmeticFunction.vonMangoldt d * powerTailZeta (2 * a) m)]
  unfold powerTailContactCoefficient
  rw [Finset.mul_sum]
  apply sum_congr rfl
  intro d hd
  have hdn := (Nat.mem_divisors.mp hd).1
  have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hdn hn
  have hk0 : 0 < n / d := Nat.div_pos (Nat.le_of_dvd hn hdn) hd0
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd0
  have hkR : (0 : ℝ) < (n / d : ℕ) := by exact_mod_cast hk0
  have hnprod : (n : ℝ) = (d : ℝ) * ((n / d : ℕ) : ℝ) := by
    exact_mod_cast (Nat.mul_div_cancel' hdn).symm
  rw [powerTailTwist_apply, powerTailZeta_apply (by omega)]
  simp only [powerTailWeight]
  rw [hnprod, Real.mul_rpow hdR.le hkR.le]
  calc
    _ = ((d : ℝ) ^ (-(2 * a)) * (d : ℝ) ^ a) *
        (((n / d : ℕ) : ℝ) ^ (-(2 * a)) * ArithmeticFunction.vonMangoldt d) := by ring
    _ = _ := by
      rw [← Real.rpow_add hdR, show -(2 * a) + a = -a by ring]
      ring

/-- Power weighting shifts the strict summatory growth threshold. -/
theorem partialSumPowerBound_powerTailTwist_iff (f : ArithmeticFunction ℝ)
    (a θ : ℝ) (hθ : 0 ≤ θ) (hθa : 0 ≤ θ - a) :
    RHTower.PartialSumPowerBound (fun n => powerTailTwist a f (n + 1)) (θ - a) ↔
      RHTower.PartialSumPowerBound (fun n => f (n + 1)) θ := by
  simpa only [powerTailTwist_apply, powerTailWeight, Nat.cast_add, Nat.cast_one,
    mul_comm, sub_eq_add_neg] using
    RHTower.partialSumPowerBound_rpow_weight_iff (g := fun n => f (n + 1))
      (b := -a) hθ hθa

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
