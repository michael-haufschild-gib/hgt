import GaloisForLFunctions.WindowTowerOfSpecZ.TheEvenFirstOverlapHasPolynomialReciprocalBounds

/-!
# A reciprocal bound at the prime-three boundary

A degree-sixteen polynomial majorizes the reciprocal of
`449/500 − log(1−x²)/2` on the unit half-window. Five homogeneous
polynomial certificates prove the comparison against a finite logarithmic
sum. Reflected pairs stay uniformly away from the inverse determinant pole.
-/

noncomputable section
open Real
namespace GaloisForLFunctions.WindowTowerOfSpecZ

private def v32 (z : ℝ) : ℝ :=
  449 / 500 + ∑ j ∈ Finset.range 32, z ^ (j + 1) / (2 * ((j : ℝ) + 1))

private def q8 (z : ℝ) : ℝ :=
  500 / 449 - (31 / 50) * z + (7 / 200) * z ^ 2 -
    (27 / 500) * z ^ 3 - (3 / 200) * z ^ 4 - z ^ 8 / 10

private def vHom (l u v t : ℝ) : ℝ :=
  (449 / 500 : ℝ) * (v + t) ^ 32 +
    ∑ j ∈ Finset.range 32,
      (l * v + u * t) ^ (j + 1) * (v + t) ^ (31 - j) / (2 * ((j : ℝ) + 1))

private def qHom (l u v t : ℝ) : ℝ :=
  (500 / 449 : ℝ) * (v + t) ^ 8 -
    (31 / 50) * (l * v + u * t) * (v + t) ^ 7 +
    (7 / 200) * (l * v + u * t) ^ 2 * (v + t) ^ 6 -
    (27 / 500) * (l * v + u * t) ^ 3 * (v + t) ^ 5 -
    (3 / 200) * (l * v + u * t) ^ 4 * (v + t) ^ 4 -
    (l * v + u * t) ^ 8 / 10

private def residual (l u v t : ℝ) : ℝ :=
  vHom l u v t * qHom l u v t - (v + t) ^ 40

private theorem cell_one {v t : ℝ} (hv : 0 ≤ v) (ht : 0 ≤ t) :
    0 ≤ residual 0 (1 / 4) v t := by
  unfold residual vHom qHom
  norm_num [Finset.sum_range_succ]
  apply sub_nonneg.mp
  ring_nf
  positivity

private theorem cell_two {v t : ℝ} (hv : 0 ≤ v) (ht : 0 ≤ t) :
    0 ≤ residual (1 / 4) (1 / 2) v t := by
  unfold residual vHom qHom
  norm_num [Finset.sum_range_succ]
  apply sub_nonneg.mp
  ring_nf
  positivity

private theorem cell_three {v t : ℝ} (hv : 0 ≤ v) (ht : 0 ≤ t) :
    0 ≤ residual (1 / 2) (3 / 4) v t := by
  unfold residual vHom qHom
  norm_num [Finset.sum_range_succ]
  apply sub_nonneg.mp
  ring_nf
  positivity

private theorem cell_four {v t : ℝ} (hv : 0 ≤ v) (ht : 0 ≤ t) :
    0 ≤ residual (3 / 4) (7 / 8) v t := by
  unfold residual vHom qHom
  norm_num [Finset.sum_range_succ]
  apply sub_nonneg.mp
  ring_nf
  positivity

private theorem cell_five {v t : ℝ} (hv : 0 ≤ v) (ht : 0 ≤ t) :
    0 ≤ residual (7 / 8) 1 v t := by
  unfold residual vHom qHom
  norm_num [Finset.sum_range_succ]
  apply sub_nonneg.mp
  ring_nf
  positivity

private theorem residual_identity (l u z : ℝ) :
    (u - l) ^ 40 * (v32 z * q8 z - 1) = residual l u (u - z) (z - l) := by
  unfold residual vHom qHom
  rw [show (u - z) + (z - l) = u - l by ring,
    show l * (u - z) + u * (z - l) = z * (u - l) by ring]
  unfold v32 q8
  generalize u - l = s
  norm_num [Finset.sum_range_succ]
  ring

private theorem interval_bound {l u z : ℝ} (hlu : l < u) (hl : l ≤ z) (hu : z ≤ u)
    (h : ∀ v t : ℝ, 0 ≤ v → 0 ≤ t → 0 ≤ residual l u v t) :
    1 ≤ v32 z * q8 z := by
  have hp := h (u - z) (z - l) (sub_nonneg.mpr hu) (sub_nonneg.mpr hl)
  rw [← residual_identity] at hp
  exact sub_nonneg.mp (nonneg_of_mul_nonneg_right hp (pow_pos (sub_pos.mpr hlu) 40))

private theorem product_bound {z : ℝ} (h0 : 0 ≤ z) (h1 : z ≤ 1) :
    1 ≤ v32 z * q8 z := by
  by_cases hq : z ≤ 1 / 4
  · exact interval_bound (by norm_num) h0 hq (fun _ _ hv ht => cell_one hv ht)
  by_cases hh : z ≤ 1 / 2
  · exact interval_bound (by norm_num) (le_of_not_ge hq) hh
      (fun _ _ hv ht => cell_two hv ht)
  by_cases ht : z ≤ 3 / 4
  · exact interval_bound (by norm_num) (le_of_not_ge hh) ht
      (fun _ _ hv ht => cell_three hv ht)
  by_cases he : z ≤ 7 / 8
  · exact interval_bound (by norm_num) (le_of_not_ge ht) he
      (fun _ _ hv ht => cell_four hv ht)
  exact interval_bound (by norm_num) (le_of_not_ge he) h1
    (fun _ _ hv ht => cell_five hv ht)

private theorem v32_pos {z : ℝ} (h0 : 0 ≤ z) : 0 < v32 z := by
  have hs : 0 ≤ ∑ j ∈ Finset.range 32, z ^ (j + 1) / (2 * ((j : ℝ) + 1)) :=
    Finset.sum_nonneg (fun j _ => by positivity)
  dsimp only [v32]
  linarith only [hs]

/-- The finite logarithmic potential for the eighth harmonic gap. -/
def primeThreeEvenPotential (x : ℝ) : ℝ := v32 (x ^ 2)

/-- Polynomial reciprocal majorant on the entire half-window. -/
def primeThreeEvenReciprocal (x : ℝ) : ℝ := q8 (x ^ 2)

/-- The finite potential times the reciprocal polynomial is at least one. -/
theorem primeThreeEvenReciprocal_bound {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    0 < primeThreeEvenReciprocal x ∧
      1 ≤ primeThreeEvenPotential x * primeThreeEvenReciprocal x := by
  have hx : x ^ 2 ≤ 1 := by nlinarith only [h0, h1]
  have hp := product_bound (sq_nonneg x) hx
  refine ⟨?_, hp⟩
  by_contra hn
  have hq : q8 (x ^ 2) ≤ 0 := le_of_not_gt hn
  have hz := mul_nonpos_of_nonneg_of_nonpos (v32_pos (sq_nonneg x)).le hq
  linarith only [hp, hz]

/-- The finite potential lies below the logarithmic boundary term. -/
theorem primeThreeEvenPotential_le_log {x : ℝ} (h0 : 0 ≤ x) (h1 : x < 1) :
    primeThreeEvenPotential x ≤ 449 / 500 - Real.log (1 - x ^ 2) / 2 := by
  have h := firstOverlapEvenPotential_le_log h0 h1
  have he : primeThreeEvenPotential x = firstOverlapEvenPotential x - 3029 / 3000 +
      449 / 500 := by
    unfold primeThreeEvenPotential v32 firstOverlapEvenPotential
    simp_rw [← pow_mul]
    ring
  rw [he]
  linarith only [h]

private theorem reciprocal_quadratic_upper {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    primeThreeEvenReciprocal x ≤ 500 / 449 - (117 / 200) * x ^ 2 := by
  have hx2 : x ^ 2 ≤ 1 := by nlinarith only [h0, h1]
  have hx4 : (x ^ 2) ^ 2 ≤ x ^ 2 := by
    have h := mul_le_mul_of_nonneg_left hx2 (sq_nonneg x)
    nlinarith only [h]
  unfold primeThreeEvenReciprocal q8
  nlinarith only [hx4, pow_nonneg (sq_nonneg x) 3,
    pow_nonneg (sq_nonneg x) 4, pow_nonneg (sq_nonneg x) 8]

/-- Reflected reciprocal products are at most `4/5` near the prime-three boundary. -/
theorem primeThreeEvenReciprocal_pair_bound {x y : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy0 : 0 ≤ y) (hy1 : y ≤ 1)
    (hlo : 63 / 50 ≤ x + y) (hhi : x + y ≤ 127 / 100) :
    primeThreeEvenReciprocal x * primeThreeEvenReciprocal y ≤ 4 / 5 := by
  have hqx := reciprocal_quadratic_upper hx0 hx1
  have hqy := reciprocal_quadratic_upper hy0 hy1
  have hxp := (primeThreeEvenReciprocal_bound hx0 hx1).1
  have hyp := (primeThreeEvenReciprocal_bound hy0 hy1).1
  have hp := mul_le_mul hqx hqy hyp.le (hxp.le.trans hqx)
  have hsumlo := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 63 / 50) hlo 2
  have hsumhi := pow_le_pow_left₀ (add_nonneg hx0 hy0) hhi 2
  have hsum : (63 / 50 : ℝ) ^ 2 / 2 ≤ x ^ 2 + y ^ 2 := by
    nlinarith only [hsumlo, sq_nonneg (x - y)]
  have hxy : x * y ≤ (127 / 100 : ℝ) ^ 2 / 4 := by
    nlinarith only [hsumhi, sq_nonneg (x - y)]
  have hxy2 := pow_le_pow_left₀ (mul_nonneg hx0 hy0) hxy 2
  have hu : (500 / 449 - (117 / 200) * x ^ 2) *
      (500 / 449 - (117 / 200) * y ^ 2) ≤ (4 / 5 : ℝ) := by
    nlinarith only [hsum, hxy2]
  exact hp.trans hu

/-! Raising the constant potential to `1799/2000` permits a smaller reciprocal.
The product comparison has one negative coefficient, paid by `z⁸≤z³`. -/

/-- The logarithmic potential with the stronger Gamma mass allocation. -/
def primeThreeRefinedEvenPotential (x : ℝ) : ℝ :=
  primeThreeEvenPotential x + 3 / 2000

/-- Reciprocal majorant for the potential with constant `1799/2000`. -/
def primeThreeRefinedEvenReciprocal (x : ℝ) : ℝ :=
  2000 / 1799 - (6179 / 10000) * x ^ 2 + (7 / 200) * x ^ 4 -
    (27 / 500) * x ^ 6 - (3 / 200) * x ^ 8 - x ^ 16 / 10

private theorem product_increases {z : ℝ} (h0 : 0 ≤ z) (h1 : z ≤ 1) :
    (449 / 500 + ∑ j ∈ Finset.range 32, z ^ (j + 1) / (2 * ((j : ℝ) + 1))) *
      (500 / 449 - (31 / 50) * z + (7 / 200) * z ^ 2 -
        (27 / 500) * z ^ 3 - (3 / 200) * z ^ 4 - z ^ 8 / 10) ≤
    (1799 / 2000 + ∑ j ∈ Finset.range 32, z ^ (j + 1) / (2 * ((j : ℝ) + 1))) *
      (2000 / 1799 - (6179 / 10000) * z + (7 / 200) * z ^ 2 -
        (27 / 500) * z ^ 3 - (3 / 200) * z ^ 4 - z ^ 8 / 10) := by
  have h38 : z ^ 8 ≤ z ^ 3 := pow_le_pow_of_le_one h0 h1 (by norm_num)
  have hn (n : ℕ) : 0 ≤ z ^ n := pow_nonneg h0 n
  norm_num [Finset.sum_range_succ]
  ring_nf
  linarith only [h38, hn 1, hn 2, hn 3, hn 4, hn 5, hn 6, hn 7,
    hn 9, hn 10, hn 11, hn 12, hn 13, hn 14, hn 15, hn 16, hn 17,
    hn 18, hn 19, hn 20, hn 21, hn 22, hn 23, hn 24, hn 25, hn 26,
    hn 27, hn 28, hn 29, hn 30, hn 31, hn 32, hn 33]

/-- The refined finite potential times its reciprocal polynomial is at least one. -/
theorem primeThreeRefinedEvenReciprocal_bound {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    0 < primeThreeRefinedEvenReciprocal x ∧
      1 ≤ primeThreeRefinedEvenPotential x * primeThreeRefinedEvenReciprocal x := by
  have hx : x ^ 2 ≤ 1 := by nlinarith only [h0, h1]
  have h := product_increases (sq_nonneg x) hx
  have hold := (primeThreeEvenReciprocal_bound h0 h1).2
  have hnew : 1 ≤ primeThreeRefinedEvenPotential x * primeThreeRefinedEvenReciprocal x := by
    have hv : primeThreeRefinedEvenPotential x = 1799 / 2000 +
        ∑ j ∈ Finset.range 32, (x ^ 2) ^ (j + 1) / (2 * ((j : ℝ) + 1)) := by
      change (449 / 500 +
        ∑ j ∈ Finset.range 32, (x ^ 2) ^ (j + 1) / (2 * ((j : ℝ) + 1))) + 3 / 2000 = _
      ring
    have hq : primeThreeRefinedEvenReciprocal x =
        2000 / 1799 - (6179 / 10000) * x ^ 2 + (7 / 200) * (x ^ 2) ^ 2 -
          (27 / 500) * (x ^ 2) ^ 3 - (3 / 200) * (x ^ 2) ^ 4 - (x ^ 2) ^ 8 / 10 := by
      unfold primeThreeRefinedEvenReciprocal
      ring
    rw [hv, hq]
    exact hold.trans h
  have hp : 0 < primeThreeRefinedEvenPotential x := by
    change 0 < (449 / 500 +
      ∑ j ∈ Finset.range 32, (x ^ 2) ^ (j + 1) / (2 * ((j : ℝ) + 1))) + 3 / 2000
    have hn : 0 ≤ ∑ j ∈ Finset.range 32,
        (x ^ 2) ^ (j + 1) / (2 * ((j : ℝ) + 1)) :=
      Finset.sum_nonneg (fun j _ => by positivity)
    linarith only [hn]
  refine ⟨?_, hnew⟩
  by_contra hn
  have hn' := mul_nonpos_of_nonneg_of_nonpos hp.le (le_of_not_gt hn)
  linarith only [hnew, hn']

/-- The finite refined potential lies below the logarithmic boundary potential. -/
theorem primeThreeRefinedEvenPotential_le_log {x : ℝ} (h0 : 0 ≤ x) (h1 : x < 1) :
    primeThreeRefinedEvenPotential x ≤ 1799 / 2000 - Real.log (1 - x ^ 2) / 2 := by
  have h := primeThreeEvenPotential_le_log h0 h1
  dsimp only [primeThreeRefinedEvenPotential]
  linarith only [h]

private theorem refined_reciprocal_quadratic_upper {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    primeThreeRefinedEvenReciprocal x ≤ 2000 / 1799 - (5829 / 10000) * x ^ 2 := by
  have hx2 : x ^ 2 ≤ 1 := by nlinarith only [h0, h1]
  have hx4 : x ^ 4 ≤ x ^ 2 := by
    have h := mul_le_mul_of_nonneg_left hx2 (sq_nonneg x)
    nlinarith only [h]
  unfold primeThreeRefinedEvenReciprocal
  nlinarith only [hx4, pow_nonneg h0 6, pow_nonneg h0 8, pow_nonneg h0 16]

/-- The refined reflected reciprocal product is at most `39/50`. -/
theorem primeThreeRefinedEvenReciprocal_pair_bound {x y : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy0 : 0 ≤ y) (hy1 : y ≤ 1)
    (hlo : 63 / 50 ≤ x + y) (hhi : x + y ≤ 127 / 100) :
    primeThreeRefinedEvenReciprocal x * primeThreeRefinedEvenReciprocal y ≤ 39 / 50 := by
  have hqx := refined_reciprocal_quadratic_upper hx0 hx1
  have hqy := refined_reciprocal_quadratic_upper hy0 hy1
  have hxp := (primeThreeRefinedEvenReciprocal_bound hx0 hx1).1
  have hyp := (primeThreeRefinedEvenReciprocal_bound hy0 hy1).1
  have hp := mul_le_mul hqx hqy hyp.le (hxp.le.trans hqx)
  have hsumlo := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 63 / 50) hlo 2
  have hsumhi := pow_le_pow_left₀ (add_nonneg hx0 hy0) hhi 2
  have hsum : (63 / 50 : ℝ) ^ 2 / 2 ≤ x ^ 2 + y ^ 2 := by
    nlinarith only [hsumlo, sq_nonneg (x - y)]
  have hxy : x * y ≤ (127 / 100 : ℝ) ^ 2 / 4 := by
    nlinarith only [hsumhi, sq_nonneg (x - y)]
  have hxy2 := pow_le_pow_left₀ (mul_nonneg hx0 hy0) hxy 2
  have hu : (2000 / 1799 - (5829 / 10000) * x ^ 2) *
      (2000 / 1799 - (5829 / 10000) * y ^ 2) ≤ (39 / 50 : ℝ) := by
    nlinarith only [hsum, hxy2]
  exact hp.trans hu

end GaloisForLFunctions.WindowTowerOfSpecZ

#print axioms GaloisForLFunctions.WindowTowerOfSpecZ.primeThreeEvenReciprocal_bound
#print axioms GaloisForLFunctions.WindowTowerOfSpecZ.primeThreeEvenPotential_le_log
#print axioms GaloisForLFunctions.WindowTowerOfSpecZ.primeThreeEvenReciprocal_pair_bound

#print axioms GaloisForLFunctions.WindowTowerOfSpecZ.primeThreeRefinedEvenReciprocal_bound
#print axioms GaloisForLFunctions.WindowTowerOfSpecZ.primeThreeRefinedEvenPotential_le_log
#print axioms GaloisForLFunctions.WindowTowerOfSpecZ.primeThreeRefinedEvenReciprocal_pair_bound
