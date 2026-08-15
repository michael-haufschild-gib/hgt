import GaloisForLFunctions.RHTower.GaussHigherRatioWeightedDefect
import GaloisForLFunctions.RHTower.GaussDoubleDefect

/-!
# Cubic product cap for triple Gauss defects

The first unresolved propagated iterate contains three squared sampled-ratio defects.  At three
components, cubic AM-GM reduces every mixed ratio monomial to a sum of sixth powers, and the
conserved `2m`-power law controls those sixth powers exactly from `m ≥ 3` onward.
-/

namespace RHTower

noncomputable section

theorem three_mul_mul_mul_le_sum_cubes {x y z : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    3 * x * y * z ≤ x ^ 3 + y ^ 3 + z ^ 3 := by
  have hsum : 0 ≤ x + y + z := by linarith
  have hsquares : 0 ≤ (x - y) ^ 2 + (y - z) ^ 2 + (z - x) ^ 2 := by positivity
  have hprod := mul_nonneg hsum hsquares
  nlinarith

theorem three_mul_le_cube_add_two {x : ℝ} (hx : 0 ≤ x) :
    3 * x ≤ x ^ 3 + 2 := by
  have hprod : 0 ≤ (x - 1) ^ 2 * (x + 2) :=
    mul_nonneg (sq_nonneg _) (by linarith)
  nlinarith

theorem triple_one_add_product_le_cube_sum {x y z : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    (x + 1) * (y + 1) * (z + 1) ≤
      4 + (4 / 3 : ℝ) * (x ^ 3 + y ^ 3 + z ^ 3) := by
  have hxyz := three_mul_mul_mul_le_sum_cubes hx hy hz
  have hxy := three_mul_mul_mul_le_sum_cubes hx hy (by norm_num : (0 : ℝ) ≤ 1)
  have hxz := three_mul_mul_mul_le_sum_cubes hx hz (by norm_num : (0 : ℝ) ≤ 1)
  have hyz := three_mul_mul_mul_le_sum_cubes hy hz (by norm_num : (0 : ℝ) ≤ 1)
  have hx1 := three_mul_le_cube_add_two hx
  have hy1 := three_mul_le_cube_add_two hy
  have hz1 := three_mul_le_cube_add_two hz
  nlinarith

/-- Product cap for three squared defects.  This is the cubic analogue of the existing
double-defect cap and the pointwise arithmetic core of depth-two propagation. -/
theorem norm_gaussSampleRatioDefect_sq_mul_sq_mul_sq_le
    {m : ℕ} (hm3 : 3 ≤ m) (k : Fin m) (p : Nat.Primes) {K : ℝ} (hK : 0 ≤ K)
    (hKb : ∀ a b : ℤ, a ≠ 0 → b ≠ 0 →
      ‖gaussSampleValue k p a‖ ^ (2 * m) * (a.natAbs : ℝ)
        ≤ K * (‖gaussSampleValue k p b‖ ^ (2 * m) * (b.natAbs : ℝ)))
    (I : ℕ) (j l r : ℤ) :
    ‖gaussSampleRatioDefect k p j (I : ℤ)‖ ^ 2 *
        ‖gaussSampleRatioDefect k p l (I : ℤ)‖ ^ 2 *
          ‖gaussSampleRatioDefect k p r (I : ℤ)‖ ^ 2
      ≤ 64 + 12 * K * (I : ℝ) / (((I : ℤ) + j).natAbs : ℝ) +
          12 * K * (I : ℝ) / (((I : ℤ) + l).natAbs : ℝ) +
          12 * K * (I : ℝ) / (((I : ℤ) + r).natAbs : ℝ) := by
  have hm1 : 1 ≤ m := by omega
  set Rj : ℝ := ‖gaussSampleValue k p ((I : ℤ) + j)‖ /
    ‖gaussSampleValue k p (I : ℤ)‖ with hRj
  set Rl : ℝ := ‖gaussSampleValue k p ((I : ℤ) + l)‖ /
    ‖gaussSampleValue k p (I : ℤ)‖ with hRl
  set Rr : ℝ := ‖gaussSampleValue k p ((I : ℤ) + r)‖ /
    ‖gaussSampleValue k p (I : ℤ)‖ with hRr
  have hRj0 : 0 ≤ Rj := by positivity
  have hRl0 : 0 ≤ Rl := by positivity
  have hRr0 : 0 ≤ Rr := by positivity
  have htri : ∀ x : ℤ, ‖gaussSampleRatioDefect k p x (I : ℤ)‖ ≤
      ‖gaussSampleValue k p ((I : ℤ) + x)‖ / ‖gaussSampleValue k p (I : ℤ)‖ + 1 := by
    intro x
    rw [gaussSampleRatioDefect]
    refine (norm_sub_le _ _).trans ?_
    rw [norm_div, norm_gaussSampleRotation (m := m)]
  have hsq : ∀ (x : ℤ) (R : ℝ),
      R = ‖gaussSampleValue k p ((I : ℤ) + x)‖ / ‖gaussSampleValue k p (I : ℤ)‖ →
      ‖gaussSampleRatioDefect k p x (I : ℤ)‖ ^ 2 ≤ 2 * R ^ 2 + 2 := by
    intro x R hR
    have h := htri x
    rw [← hR] at h
    nlinarith [sq_nonneg (R - 1), norm_nonneg (gaussSampleRatioDefect k p x (I : ℤ))]
  have hsqj := hsq j Rj hRj
  have hsql := hsq l Rl hRl
  have hsqr := hsq r Rr hRr
  have hpow6 : ∀ {R : ℝ}, 0 ≤ R → R ^ 6 ≤ 1 + R ^ (2 * m) := by
    intro R hR
    rcases le_or_gt R 1 with h | h
    · have h1 : R ^ 6 ≤ 1 := pow_le_one₀ hR h
      exact h1.trans (le_add_of_nonneg_right (pow_nonneg hR _))
    · have h1 : R ^ 6 ≤ R ^ (2 * m) := pow_le_pow_right₀ h.le (by omega)
      linarith
  have hcapj := norm_gaussSampleRatio_pow_le hm1 k p hKb I j
  have hcapl := norm_gaussSampleRatio_pow_le hm1 k p hKb I l
  have hcapr := norm_gaussSampleRatio_pow_le hm1 k p hKb I r
  have hj6 : Rj ^ 6 ≤ 1 + K * (I : ℝ) / (((I : ℤ) + j).natAbs : ℝ) :=
    (hpow6 hRj0).trans (by linarith)
  have hl6 : Rl ^ 6 ≤ 1 + K * (I : ℝ) / (((I : ℤ) + l).natAbs : ℝ) :=
    (hpow6 hRl0).trans (by linarith)
  have hr6 : Rr ^ 6 ≤ 1 + K * (I : ℝ) / (((I : ℤ) + r).natAbs : ℝ) :=
    (hpow6 hRr0).trans (by linarith)
  have hprod :
      ‖gaussSampleRatioDefect k p j (I : ℤ)‖ ^ 2 *
          ‖gaussSampleRatioDefect k p l (I : ℤ)‖ ^ 2 *
            ‖gaussSampleRatioDefect k p r (I : ℤ)‖ ^ 2
        ≤ (2 * Rj ^ 2 + 2) * (2 * Rl ^ 2 + 2) * (2 * Rr ^ 2 + 2) := by
    have hj0 : 0 ≤ ‖gaussSampleRatioDefect k p j (I : ℤ)‖ ^ 2 := by positivity
    have hl0 : 0 ≤ ‖gaussSampleRatioDefect k p l (I : ℤ)‖ ^ 2 := by positivity
    have hr0 : 0 ≤ ‖gaussSampleRatioDefect k p r (I : ℤ)‖ ^ 2 := by positivity
    have hleft := mul_le_mul hsqj hsql hl0 (by positivity)
    exact mul_le_mul hleft hsqr hr0 (by positivity)
  have hone := triple_one_add_product_le_cube_sum
    (x := Rj ^ 2) (y := Rl ^ 2) (z := Rr ^ 2) (by positivity) (by positivity) (by positivity)
  calc
    ‖gaussSampleRatioDefect k p j (I : ℤ)‖ ^ 2 *
          ‖gaussSampleRatioDefect k p l (I : ℤ)‖ ^ 2 *
            ‖gaussSampleRatioDefect k p r (I : ℤ)‖ ^ 2
        ≤ (2 * Rj ^ 2 + 2) * (2 * Rl ^ 2 + 2) * (2 * Rr ^ 2 + 2) := hprod
    _ = 8 * ((Rj ^ 2 + 1) * (Rl ^ 2 + 1) * (Rr ^ 2 + 1)) := by ring
    _ ≤ 8 * (4 + (4 / 3 : ℝ) * ((Rj ^ 2) ^ 3 + (Rl ^ 2) ^ 3 + (Rr ^ 2) ^ 3)) := by
      exact mul_le_mul_of_nonneg_left hone (by norm_num)
    _ = 32 + (32 / 3 : ℝ) * (Rj ^ 6 + Rl ^ 6 + Rr ^ 6) := by ring
    _ ≤ 32 + (32 / 3 : ℝ) *
        ((1 + K * (I : ℝ) / (((I : ℤ) + j).natAbs : ℝ)) +
         (1 + K * (I : ℝ) / (((I : ℤ) + l).natAbs : ℝ)) +
         (1 + K * (I : ℝ) / (((I : ℤ) + r).natAbs : ℝ))) := by
      gcongr
    _ ≤ 64 + 12 * K * (I : ℝ) / (((I : ℤ) + j).natAbs : ℝ) +
          12 * K * (I : ℝ) / (((I : ℤ) + l).natAbs : ℝ) +
          12 * K * (I : ℝ) / (((I : ℤ) + r).natAbs : ℝ) := by
      set X : ℝ := K * (I : ℝ) / (((I : ℤ) + j).natAbs : ℝ) with hX
      set Y : ℝ := K * (I : ℝ) / (((I : ℤ) + l).natAbs : ℝ) with hY
      set Z : ℝ := K * (I : ℝ) / (((I : ℤ) + r).natAbs : ℝ) with hZ
      have hKj : 0 ≤ X := by
        rw [hX]
        exact div_nonneg (mul_nonneg hK (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
      have hKl : 0 ≤ Y := by
        rw [hY]
        exact div_nonneg (mul_nonneg hK (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
      have hKr : 0 ≤ Z := by
        rw [hZ]
        exact div_nonneg (mul_nonneg hK (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
      have hright : 64 + 12 * K * (I : ℝ) / (((I : ℤ) + j).natAbs : ℝ) +
            12 * K * (I : ℝ) / (((I : ℤ) + l).natAbs : ℝ) +
            12 * K * (I : ℝ) / (((I : ℤ) + r).natAbs : ℝ) =
          64 + 12 * X + 12 * Y + 12 * Z := by
        rw [hX, hY, hZ]
        ring
      rw [hright]
      nlinarith

end

end RHTower
