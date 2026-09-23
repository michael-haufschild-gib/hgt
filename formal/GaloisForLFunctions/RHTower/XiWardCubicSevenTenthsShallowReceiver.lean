import GaloisForLFunctions.RHTower.XiWardCubicLogMomentHellingerCauchySeparator
import GaloisForLFunctions.RHTower.XiWardSourceWindowMultiplicity

/-!
# Seven-tenths shallow cubic Hellinger receiver

Route T leaves only strict-right zeros with centered horizontal displacement at most `1 / 5`,
up to a density-zero deep packet.  On this smaller interval the cubic Hellinger self-charge is
at least `14375 / (864 h)`, rather than the strip-wide `115 / (108 h)`.  This file propagates
that sharper quantum through a finite multiplicity packet and the shallow/deep `75%` receiver.

This is a quantitative receiver.  It does not assert the missing height-local source upper bound
for the cubic energy.
-/

open Complex
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Cubic Hellinger self-charge on the Route-T shallow interval `0 < a ≤ 1 / 5`. -/
theorem cubicLogMomentHellingerCauchyKernel_self_ge_sevenTenthsShallow
    {h a : ℝ} (hh : 0 < h) (ha : 0 < a) (hshallow : a ≤ 1 / 5) :
    14375 / (864 * h) ≤
      cubicLogMomentHellingerCauchyKernel h a a 0 := by
  have hfactor :
      0 ≤ (1 / 5 - a) * ((1 / 5 : ℝ) ^ (2 : ℕ) + (1 / 5 : ℝ) * a + a ^ (2 : ℕ)) := by
    apply mul_nonneg (sub_nonneg.mpr hshallow)
    nlinarith [sq_nonneg a]
  have hcube : a ^ (3 : ℕ) ≤ (1 / 5 : ℝ) ^ (3 : ℕ) := by
    nlinarith
  have hhorizontal :
      14375 / 864 ≤ cubicLogMomentHellingerHorizontalKernel a a := by
    rw [cubicLogMomentHellingerHorizontalKernel_self ha]
    have hden : 0 < 864 * a ^ (3 : ℕ) := by positivity
    apply (le_div_iff₀ hden).2
    norm_num at hcube ⊢
    nlinarith
  have hinv : 0 ≤ 1 / h := (one_div_pos.mpr hh).le
  rw [cubicLogMomentHellingerCauchyKernel,
    dampedVerticalCauchyKernel]
  have hvertical : h / (h ^ (2 : ℕ) + 0 ^ (2 : ℕ)) = 1 / h := by
    norm_num
    field_simp [hh.ne']
  rw [hvertical]
  have hmul := mul_le_mul_of_nonneg_right hhorizontal hinv
  simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hmul

/-- Positive mixed entries cannot cancel the sharpened Route-T shallow diagonal. -/
theorem finiteCubicLogMomentHellingerCauchyEnergy_ge_sevenTenthsShallowDiagonal
    {n : ℕ} {h : ℝ} (hh : 0 < h)
    {a gamma : Fin n → ℝ} (m : Fin n → ℕ)
    (ha : ∀ j, 0 < a j) (hshallow : ∀ j, a j ≤ 1 / 5) :
    (14375 / (864 * h)) * ∑ j, (m j : ℝ) ^ (2 : ℕ) ≤
      finiteCubicLogMomentHellingerCauchyEnergy h a gamma m := by
  rw [finiteCubicLogMomentHellingerCauchyEnergy]
  calc
    (14375 / (864 * h)) * ∑ j, (m j : ℝ) ^ (2 : ℕ) =
        ∑ j, (m j : ℝ) * (m j : ℝ) * (14375 / (864 * h)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ ≤ ∑ j, (m j : ℝ) * (m j : ℝ) *
        cubicLogMomentHellingerCauchyKernel h (a j) (a j)
          (gamma j - gamma j) := by
      apply Finset.sum_le_sum
      intro j _
      rw [sub_self]
      exact mul_le_mul_of_nonneg_left
        (cubicLogMomentHellingerCauchyKernel_self_ge_sevenTenthsShallow
          hh (ha j) (hshallow j))
        (mul_nonneg (by positivity) (by positivity))
    _ ≤ ∑ j, ∑ k,
        (m j : ℝ) * (m k : ℝ) *
          cubicLogMomentHellingerCauchyKernel h (a j) (a k)
            (gamma j - gamma k) := by
      apply Finset.sum_le_sum
      intro j _
      exact Finset.single_le_sum
        (f := fun k =>
          (m j : ℝ) * (m k : ℝ) *
            cubicLogMomentHellingerCauchyKernel h (a j) (a k)
              (gamma j - gamma k))
        (fun k _ => mul_nonneg (mul_nonneg (by positivity) (by positivity))
          (cubicLogMomentHellingerCauchyKernel_pos hh (ha j) (ha k) _).le)
        (Finset.mem_univ j)

/-- Multiplicity-faithful Route-T shallow census at the sharpened cubic quantum. -/
theorem sum_multiplicity_le_finiteCubicLogMomentHellingerCauchyEnergy_sevenTenthsShallow
    {n : ℕ} {h : ℝ} (hh : 0 < h)
    {a gamma : Fin n → ℝ} (m : Fin n → ℕ)
    (ha : ∀ j, 0 < a j) (hshallow : ∀ j, a j ≤ 1 / 5) :
    (∑ j, (m j : ℝ)) ≤
      (864 * h / 14375) *
        finiteCubicLogMomentHellingerCauchyEnergy h a gamma m := by
  have hdiag :=
    finiteCubicLogMomentHellingerCauchyEnergy_ge_sevenTenthsShallowDiagonal
      (gamma := gamma) hh m ha hshallow
  have hmassSq : (∑ j, (m j : ℝ)) ≤ ∑ j, (m j : ℝ) ^ (2 : ℕ) := by
    apply Finset.sum_le_sum
    intro j _
    by_cases hm0 : m j = 0
    · simp [hm0]
    · have hmone : (1 : ℝ) ≤ m j := by
        exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hm0)
      have hmnonneg : (0 : ℝ) ≤ m j := by positivity
      nlinarith
  have hcoefficient : 0 < 14375 / (864 * h) := by positivity
  have hmassDiagonal :
      (14375 / (864 * h)) * ∑ j, (m j : ℝ) ≤
        finiteCubicLogMomentHellingerCauchyEnergy h a gamma m :=
    (mul_le_mul_of_nonneg_left hmassSq hcoefficient.le).trans hdiag
  rw [show (864 * h / 14375) *
      finiteCubicLogMomentHellingerCauchyEnergy h a gamma m =
      finiteCubicLogMomentHellingerCauchyEnergy h a gamma m /
        (14375 / (864 * h)) by field_simp [hh.ne']]
  exact (le_div_iff₀ hcoefficient).2 (by simpa [mul_comm] using hmassDiagonal)

/-- Actual Route-T shallow Xi packets obey the sharpened cubic count law. -/
theorem xiRight_sevenTenthsShallow_card_le_finiteCubicLogMomentHellingerCauchyEnergy
    {n : ℕ} {h : ℝ} (hh : 0 < h)
    (q : Fin n → XiRightUpperZeroCopy)
    (hshallow : ∀ j, (xiRightCenteredZero (q j).1).re ≤ 1 / 5) :
    (n : ℝ) ≤
      (864 * h / 14375) *
        finiteCubicLogMomentHellingerCauchyEnergy h
          (fun j ↦ (xiRightCenteredZero (q j).1).re)
          (fun j ↦ (xiRightCenteredZero (q j).1).im)
          (fun _ ↦ 1) := by
  have h :=
    sum_multiplicity_le_finiteCubicLogMomentHellingerCauchyEnergy_sevenTenthsShallow
      hh (m := fun _ : Fin n ↦ 1)
      (a := fun j ↦ (xiRightCenteredZero (q j).1).re)
      (gamma := fun j ↦ (xiRightCenteredZero (q j).1).im)
      (fun j ↦ xiRightCenteredZero_re_pos (q j).1) hshallow
  simpa using h

/-- Exact shallow/deep `75%` receiver for the cubic energy. -/
theorem three_quarters_line_of_sevenTenthsShallowCubicEnergy_and_deepCount
    {N N₀ Rsh Rdeep h E : ℝ}
    (hN : 0 ≤ N) (hsplit : N = N₀ + 2 * (Rsh + Rdeep))
    (hshallow : Rsh ≤ (864 * h / 14375) * E)
    (hbudget : (864 * h / 14375) * E + Rdeep ≤ N / 8) :
    3 * N / 4 ≤ N₀ := by
  exact three_quarters_line_of_shallowEnergy_and_deepCount
    hN hsplit hshallow hbudget

end

end RHTower
