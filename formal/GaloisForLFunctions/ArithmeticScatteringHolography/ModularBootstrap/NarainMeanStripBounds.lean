import GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.NarainMeanNumerator
import GaloisForLFunctions.BlackHoleRingdown.ThePolynomialGrowthOfTheEisensteinFunction

/-!
# Exponential strip decay of the filled Narain mean numerator

The two xi factors and the bounded target powers give the sharp exponential
weight needed for Mellin contour shifts.
-/

open Complex RHTower Set
open GaloisForLFunctions.BlackHoleRingdown
open GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap
set_option autoImplicit false
noncomputable section
namespace GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap

/-- Each filled target constant term has exponential vertical decay on every fixed strip. -/
theorem exists_filledNumeratorMean_strip_bound (Y : Height) {B : ℝ} (hB : 0 ≤ B) :
    ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ u : ℂ, |u.re| ≤ B → 1 ≤ |u.im| →
      ‖filledNumeratorMean Y u‖ ≤
        C * (1 + |u.im|) ^ N * Real.exp (-(Real.pi * |u.im| / 2)) := by
  obtain ⟨C, N, hC, hξ⟩ := exists_norm_xi_sharp (-2 * B) (1 + 2 * B)
  have hY : 0 < Y.val := Y.property
  let P : ℝ := (2 * Y.val) ^ (1 / 2 + (2 + B)) +
    (Y.val / 2) ^ (1 / 2 - (2 + B))
  have hP : 0 ≤ P := by dsimp only [P]; positivity
  refine ⟨4 * (1 + B) * P * (C * 2 ^ N), N + 1, by positivity, ?_⟩
  intro u hu ht
  have hre := abs_le.mp hu
  have hy : Y.val ∈ Icc (Y.val / 2) (2 * Y.val) := by
    constructor <;> linarith only [hY]
  obtain ⟨hp, hm, _⟩ := norm_cpow_jets_le hY hB hy hu
  change ‖(Y.val : ℂ) ^ (1 / 2 + u)‖ ≤ P at hp
  change ‖(Y.val : ℂ) ^ (1 / 2 - u)‖ ≤ P at hm
  obtain ⟨hplus, _, _, hminus, _⟩ := norm_one_add_two_mul_le hu hB
  have hmin : ‖2 * u - 1‖ ≤ 2 * (1 + B) * (1 + |u.im|) := by
    rw [show 2 * u - 1 = -(2 * (1 / 2 - u)) by ring, norm_neg,
      norm_mul, Complex.norm_ofNat]
    nlinarith only [hminus]
  have hx := norm_xi_two_mul_strip_le hC hξ (u := u)
    (by linarith only [hre.1]) (by linarith only [hre.2]) ht
  have hx' := norm_xi_two_mul_strip_le hC hξ (u := u + 1 / 2)
    (by simp; linarith only [hre.1]) (by simp; linarith only [hre.2]) (by simpa using ht)
  rw [show 2 * (u + 1 / 2) = 1 + 2 * u by ring] at hx'
  have him : (u + 1 / 2).im = u.im := by simp
  rw [him] at hx'
  have hp0 : 0 ≤ 1 + |u.im| := by positivity
  calc
    ‖filledNumeratorMean Y u‖ ≤
        ‖2 * u - 1‖ * ‖(Y.val : ℂ) ^ (1 / 2 + u)‖ * ‖xi (1 + 2 * u)‖ +
          ‖1 + 2 * u‖ * ‖xi (2 * u)‖ * ‖(Y.val : ℂ) ^ (1 / 2 - u)‖ := by
      simpa only [filledNumeratorMean, norm_mul] using
        norm_add_le ((2 * u - 1) * (Y.val : ℂ) ^ (1 / 2 + u) * xi (1 + 2 * u))
          ((1 + 2 * u) * xi (2 * u) * (Y.val : ℂ) ^ (1 / 2 - u))
    _ ≤ (2 * (1 + B) * (1 + |u.im|)) * P *
        (C * 2 ^ N * (1 + |u.im|) ^ N * Real.exp (-(Real.pi * |u.im| / 2))) +
        (2 * (1 + B) * (1 + |u.im|)) *
        (C * 2 ^ N * (1 + |u.im|) ^ N * Real.exp (-(Real.pi * |u.im| / 2))) * P := by
      gcongr
    _ = _ := by rw [pow_succ]; ring

#print axioms exists_filledNumeratorMean_strip_bound
end GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap
