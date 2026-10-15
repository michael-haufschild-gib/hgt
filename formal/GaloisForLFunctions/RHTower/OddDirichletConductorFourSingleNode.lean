import GaloisForLFunctions.RHTower.OddDirichletSingleNodeConductorThreshold
import GaloisForLFunctions.HTGeometry.MidpointRadiusTrigEnclosures

/-!
# The odd single-node threshold is exactly conductor `4`

For an odd primitive character of conductor `q` the archimedean symbol of the explicit formula is
`S_q(τ) = Re ψ(¾ + iτ/2) − log π + log q`, with deficit `c_q = −S_q(0)`.  The corpus shows that the
weight `−c_q√2/2` at the node `2` is Weil-positive for every `q ≥ 5`
(`oddDirichletSingleNodeSymbol_nonneg_two_of_five_le`), and that conductor `3` admits no
single-node weight at any node (`not_forall_oddConductorThree_singleNodeSymbol_nonneg`).

**Theorem** (`oddDirichletSingleNodeSymbol_nonneg_two_conductor_four`).  For conductor `4` the
weight `−c₄√2/2` at the node `2` is Weil-positive: `S₄(τ) + c₄ cos(τ log 2) ≥ 0` for every `τ`.
So the odd single-node threshold is exactly `4`.

Proof.  With `y = |τ|/2` and `G(y) = Re ψ(¾ + iy) − ψ(¾) ≥ Σ_{n<8} y²/((¾+n)((¾+n)² + y²))`
(the Gauss series, `sum_range_le_re_digamma_vertical_sub`), it suffices that
`c₄ (1 − cos(2y log 2)) ≤ Σ_{n<8} y²/((¾+n)((¾+n)² + y²))`.
* `c₄ ≤ 0.86` (`oddDeficit_four_le`): `γ < H₆₄ − log 64` and the corpus bound on `log π`.
* `y ≤ 6/5`: `1 − cos x ≤ x²/2` and each Gauss term is at least `y²` times its value at
  `y² = 36/25`.
* `6/5 ≤ y ≤ 2`: on each of eight intervals `[y_i, y_i + 1/10]` the partial Gauss sum is at least
  its value at `y_i` (each term increases with `y²`), and `cos(2y log 2) ≥ cos(2(y_i + 1/10)·0.6932)`
  (`cos` decreases on `[0, π]`), bounded below by the degree-`18` Taylor polynomial with its
  remainder (`encl_cos`).
* `y ≥ 2`: the partial Gauss sum is at least its value at `y = 2`, which exceeds `2c₄`.
-/

open Complex Real
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-! ### The deficit -/

theorem harmonic_sixtyfour_le : ((harmonic 64 : ℚ) : ℝ) ≤ 47439 / 10000 := by
  simp [harmonic, Finset.sum_range_succ]
  norm_num

/-- `c₄ ≤ 0.86`. -/
theorem oddDeficit_four_le : oddDeficit 4 ≤ 86 / 100 := by
  have hγ := Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' 64
  have hl : Real.log (64 : ℕ) = 6 * Real.log 2 := by
    rw [show ((64 : ℕ) : ℝ) = 2 ^ 6 by norm_num, Real.log_pow]; push_cast; ring
  simp only [Real.eulerMascheroniSeq', show (64 : ℕ) ≠ 0 by norm_num, if_false, hl] at hγ
  have hH := harmonic_sixtyfour_le
  have hl4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
  have hl2 := Real.log_two_gt_d9
  have hπ := Real.pi_gt_d6
  rw [oddDeficit_eq, hl4]
  linarith [log_pi_le]

/-! ### The partial Gauss sum -/

/-- `Σ_{n<8} z/((¾+n)((¾+n)² + z))`. -/
def gaussEight (z : ℝ) : ℝ :=
  ∑ n ∈ Finset.range 8, z / ((3 / 4 + (n : ℝ)) * ((3 / 4 + (n : ℝ)) ^ 2 + z))

theorem gaussTerm_mono {A z₁ z₂ : ℝ} (hA : 0 < A) (h1 : 0 ≤ z₁) (h12 : z₁ ≤ z₂) :
    z₁ / (A * (A ^ 2 + z₁)) ≤ z₂ / (A * (A ^ 2 + z₂)) := by
  have h2 : 0 ≤ z₂ := h1.trans h12
  rw [div_le_div_iff₀ (mul_pos hA (add_pos_of_pos_of_nonneg (pow_pos hA 2) h1))
    (mul_pos hA (add_pos_of_pos_of_nonneg (pow_pos hA 2) h2))]
  have : 0 ≤ A * A ^ 2 * (z₂ - z₁) :=
    mul_nonneg (mul_pos hA (pow_pos hA 2)).le (sub_nonneg.mpr h12)
  nlinarith

theorem gaussEight_mono {z₁ z₂ : ℝ} (h1 : 0 ≤ z₁) (h12 : z₁ ≤ z₂) :
    gaussEight z₁ ≤ gaussEight z₂ :=
  Finset.sum_le_sum fun n _ => gaussTerm_mono (by positivity) h1 h12

theorem gaussEight_ge_mul {z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 36 / 25) :
    z * (8694 / 10000) ≤ gaussEight z := by
  have hterm : ∀ n : ℕ, z * (1 / ((3 / 4 + (n : ℝ)) * ((3 / 4 + (n : ℝ)) ^ 2 + 36 / 25))) ≤
      z / ((3 / 4 + (n : ℝ)) * ((3 / 4 + (n : ℝ)) ^ 2 + z)) := fun n => by
    rw [mul_one_div]
    exact div_le_div_of_nonneg_left hz (by positivity) (by nlinarith)
  have hsum := Finset.sum_le_sum fun n (_ : n ∈ Finset.range 8) => hterm n
  rw [← Finset.mul_sum] at hsum
  have hval : (8694 / 10000 : ℝ) ≤ ∑ n ∈ Finset.range 8,
      1 / ((3 / 4 + (n : ℝ)) * ((3 / 4 + (n : ℝ)) ^ 2 + 36 / 25)) := by
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]
    norm_num
  exact (mul_le_mul_of_nonneg_left hval hz).trans hsum

/-! ### Cosine lower bounds -/

theorem cos_ge_taylor {θ : ℝ} (h0 : 0 ≤ θ) (h10 : θ ≤ 10) :
    cosTaylor 10 θ - θ ^ 20 / (Nat.factorial 20 : ℝ) * 2 ≤ Real.cos θ := by
  have h := Encl.ge_of_holds (encl_cos θ (by rw [abs_of_nonneg h0]; exact h10))
  simpa [abs_of_nonneg h0] using h

/-- For `0 ≤ 2y log 2` and `y ≤ b`, `cos(2y log 2) ≥ cos(2b·0.6932)` once `2b·0.6932 ≤ π`. -/
theorem cos_two_mul_log_two_ge {y b : ℝ} (hy : 0 ≤ y) (hyb : y ≤ b)
    (hb : 2 * b * (6932 / 10000) ≤ 3) :
    Real.cos (2 * b * (6932 / 10000)) ≤ Real.cos (2 * y * Real.log 2) := by
  have hl := Real.log_two_lt_d9
  have hl0 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  apply Real.cos_le_cos_of_nonneg_of_le_pi (by positivity)
  · linarith [Real.pi_gt_three]
  · have : y * Real.log 2 ≤ b * (6932 / 10000) := by
      apply mul_le_mul hyb (by linarith) hl0.le (by linarith)
    linarith

/-- The grid step: on `[y₀, b]` with `G(y₀²) ≥ g` and `cos(2b·0.6932) ≥ k`, the claim holds as
soon as `0.86 (1 − k) ≤ g`. -/
theorem grid_step {c y y₀ b g k : ℝ} (hc : c ≤ 86 / 100) (hy₀ : 0 ≤ y₀)
    (hy₀y : y₀ ≤ y) (hyb : y ≤ b) (hb : 2 * b * (6932 / 10000) ≤ 3)
    (hg : g ≤ gaussEight (y₀ ^ 2)) (hk : k ≤ Real.cos (2 * b * (6932 / 10000)))
    (hnum : 86 / 100 * (1 - k) ≤ g) :
    c * (1 - Real.cos (2 * y * Real.log 2)) ≤ gaussEight (y ^ 2) := by
  have hy : 0 ≤ y := hy₀.trans hy₀y
  have hcos := cos_two_mul_log_two_ge hy hyb hb
  have hG : gaussEight (y₀ ^ 2) ≤ gaussEight (y ^ 2) :=
    gaussEight_mono (sq_nonneg _) (pow_le_pow_left₀ hy₀ hy₀y 2)
  have h1 : 1 - Real.cos (2 * y * Real.log 2) ≤ 1 - k := by linarith
  have h2 : 0 ≤ 1 - Real.cos (2 * y * Real.log 2) := by
    linarith [Real.cos_le_one (2 * y * Real.log 2)]
  calc c * (1 - Real.cos (2 * y * Real.log 2)) ≤ 86 / 100 * (1 - k) :=
        mul_le_mul hc h1 h2 (by norm_num)
    _ ≤ g := hnum
    _ ≤ gaussEight (y ^ 2) := hg.trans hG

/-! ### The key inequality -/

theorem key_conductor_four {c y : ℝ} (hc : c ≤ 86 / 100) (hy : 0 ≤ y) :
    c * (1 - Real.cos (2 * y * Real.log 2)) ≤ gaussEight (y ^ 2) := by
  have hG0 : 0 ≤ gaussEight (y ^ 2) := Finset.sum_nonneg fun n _ => by positivity
  have hcos1 := Real.cos_le_one (2 * y * Real.log 2)
  rcases le_or_gt c 0 with hc0 | hc0
  · nlinarith
  have hc0' := hc0.le
  rcases le_or_gt y (6 / 5) with h1 | h1
  · -- quadratic regime
    have hz : y ^ 2 ≤ 36 / 25 := by nlinarith
    have hS := gaussEight_ge_mul (sq_nonneg y) hz
    have hcos2 : 1 - (2 * y * Real.log 2) ^ 2 / 2 ≤ Real.cos (2 * y * Real.log 2) :=
      Real.one_sub_sq_div_two_le_cos
    have hl := Real.log_two_lt_d9
    have hl0 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
    have hL : Real.log 2 ^ 2 ≤ (6932 / 10000) ^ 2 := pow_le_pow_left₀ hl0.le (by linarith) 2
    have hy2 : 0 ≤ y ^ 2 := sq_nonneg y
    have e : (2 * y * Real.log 2) ^ 2 / 2 = 2 * y ^ 2 * Real.log 2 ^ 2 := by ring
    have hA : c * (1 - Real.cos (2 * y * Real.log 2)) ≤ c * (2 * y ^ 2 * Real.log 2 ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ hc0'
      linarith
    have hB : c * (2 * y ^ 2 * Real.log 2 ^ 2) ≤ 86 / 100 * (2 * y ^ 2 * (6932 / 10000) ^ 2) :=
      mul_le_mul hc (by nlinarith) (by positivity) (by norm_num)
    nlinarith
  rcases le_or_gt 2 y with h2 | h2
  · -- constant regime
    have hS : gaussEight (2 ^ 2) ≤ gaussEight (y ^ 2) :=
      gaussEight_mono (by norm_num) (pow_le_pow_left₀ (by norm_num) h2 2)
    have hval : (1746 / 1000 : ℝ) ≤ gaussEight (2 ^ 2) := by
      simp only [gaussEight, Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]
      norm_num
    have hcosm := Real.neg_one_le_cos (2 * y * Real.log 2)
    have h2c : c * (1 - Real.cos (2 * y * Real.log 2)) ≤ c * 2 :=
      mul_le_mul_of_nonneg_left (by linarith) hc0'
    calc c * (1 - Real.cos (2 * y * Real.log 2)) ≤ c * 2 := h2c
      _ ≤ 86 / 100 * 2 := by linarith
      _ ≤ gaussEight (2 ^ 2) := by linarith
      _ ≤ gaussEight (y ^ 2) := hS
  -- grid regime `6/5 < y < 2`
  have hk : ∀ b : ℝ, 0 ≤ b → b ≤ 2 →
      cosTaylor 10 (2 * b * (6932 / 10000)) -
          (2 * b * (6932 / 10000)) ^ 20 / (Nat.factorial 20 : ℝ) * 2 ≤
        Real.cos (2 * b * (6932 / 10000)) := fun b hb0 hb2 =>
    cos_ge_taylor (by positivity) (by nlinarith)
  rcases le_or_gt y (13 / 10) with g1 | g1
  · refine grid_step hc (by norm_num) h1.le g1 (by norm_num) (g := 125 / 100)
      (k := -2296 / 10000) ?_ ((by
        have := hk (13 / 10) (by norm_num) (by norm_num)
        refine le_trans ?_ this
        simp only [cosTaylor, Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]
        norm_num [Nat.factorial])) (by norm_num)
    simp only [gaussEight, Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]
    norm_num
  rcases le_or_gt y (14 / 10) with g2 | g2
  · refine grid_step hc (by norm_num) g1.le g2 (by norm_num) (g := 133 / 100)
      (k := -3621 / 10000) ?_ ((by
        have := hk (14 / 10) (by norm_num) (by norm_num)
        refine le_trans ?_ this
        simp only [cosTaylor, Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]
        norm_num [Nat.factorial])) (by norm_num)
    simp only [gaussEight, Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]
    norm_num
  rcases le_or_gt y (15 / 10) with g3 | g3
  · refine grid_step hc (by norm_num) g2.le g3 (by norm_num) (g := 140 / 100)
      (k := -4875 / 10000) ?_ ((by
        have := hk (15 / 10) (by norm_num) (by norm_num)
        refine le_trans ?_ this
        simp only [cosTaylor, Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]
        norm_num [Nat.factorial])) (by norm_num)
    simp only [gaussEight, Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]
    norm_num
  rcases le_or_gt y (16 / 10) with g4 | g4
  · refine grid_step hc (by norm_num) g3.le g4 (by norm_num) (g := 147 / 100)
      (k := -6038 / 10000) ?_ ((by
        have := hk (16 / 10) (by norm_num) (by norm_num)
        refine le_trans ?_ this
        simp only [cosTaylor, Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]
        norm_num [Nat.factorial])) (by norm_num)
    simp only [gaussEight, Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]
    norm_num
  rcases le_or_gt y (17 / 10) with g5 | g5
  · refine grid_step hc (by norm_num) g4.le g5 (by norm_num) (g := 153 / 100)
      (k := -7080 / 10000) ?_ ((by
        have := hk (17 / 10) (by norm_num) (by norm_num)
        refine le_trans ?_ this
        simp only [cosTaylor, Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]
        norm_num [Nat.factorial])) (by norm_num)
    simp only [gaussEight, Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]
    norm_num
  rcases le_or_gt y (18 / 10) with g6 | g6
  · refine grid_step hc (by norm_num) g5.le g6 (by norm_num) (g := 159 / 100)
      (k := -7986 / 10000) ?_ ((by
        have := hk (18 / 10) (by norm_num) (by norm_num)
        refine le_trans ?_ this
        simp only [cosTaylor, Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]
        norm_num [Nat.factorial])) (by norm_num)
    simp only [gaussEight, Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]
    norm_num
  rcases le_or_gt y (19 / 10) with g7 | g7
  · refine grid_step hc (by norm_num) g6.le g7 (by norm_num) (g := 1645 / 1000)
      (k := -8742 / 10000) ?_ ((by
        have := hk (19 / 10) (by norm_num) (by norm_num)
        refine le_trans ?_ this
        simp only [cosTaylor, Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]
        norm_num [Nat.factorial])) (by norm_num)
    simp only [gaussEight, Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]
    norm_num
  · refine grid_step hc (by norm_num) g7.le h2.le (by norm_num) (g := 1698 / 1000)
      (k := -9329 / 10000) ?_ ((by
        have := hk 2 (by norm_num) (by norm_num)
        refine le_trans ?_ this
        simp only [cosTaylor, Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]
        norm_num [Nat.factorial])) (by norm_num)
    simp only [gaussEight, Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]
    norm_num

/-! ### Conductor `4` -/

/-- **Node `2` for odd conductor `4`.**  The weight `−c₄√2/2` at the node `2` is Weil-positive. -/
theorem oddDirichletSingleNodeSymbol_nonneg_two_conductor_four (τ : ℝ) :
    0 ≤ weilAtomSymbol (oddSingleNodeWeight 4 2) 2 (τ / (2 * π)) + Real.log 4 +
      π / Real.cosh (π * τ) := by
  rw [weilAtomSymbol_oddSingleNodeWeight (le_refl 2) τ]
  set c := oddDeficit 4 with hc_def
  have hc : c ≤ 86 / 100 := oddDeficit_four_le
  have hS0 : (Complex.digamma (((3 / 4 : ℝ) : ℂ))).re - Real.log π + Real.log 4 = -c := by
    rw [hc_def, oddDeficit]; ring
  have hgrow := sum_range_le_re_digamma_vertical_sub (a := 3 / 4) (by norm_num) (τ / 2) 8
  set y := |τ| / 2 with hy_def
  have hy0 : 0 ≤ y := by positivity
  have hzy : (τ / 2) ^ 2 = y ^ 2 := by rw [hy_def, div_pow, div_pow, sq_abs]
  have hsum : ∑ n ∈ Finset.range 8, (τ / 2) ^ 2 / ((3 / 4 + (n : ℝ)) *
      ((3 / 4 + (n : ℝ)) ^ 2 + (τ / 2) ^ 2)) = gaussEight (y ^ 2) := by
    rw [gaussEight, hzy]
  rw [hsum] at hgrow
  have hcosτ : Real.cos (τ * Real.log (2 : ℕ)) = Real.cos (2 * y * Real.log 2) := by
    rw [hy_def, show 2 * (|τ| / 2) = |τ| by ring, Nat.cast_ofNat]
    rcases le_or_gt 0 τ with h | h
    · rw [abs_of_nonneg h]
    · rw [abs_of_neg h, neg_mul, Real.cos_neg]
  have hkey := key_conductor_four hc hy0
  rw [hcosτ]
  have hre : (Complex.digamma (((3 / 4 : ℝ) : ℂ) + ((τ / 2 : ℝ) : ℂ) * I)).re -
      (Complex.digamma (((3 / 4 : ℝ) : ℂ))).re ≥ gaussEight (y ^ 2) := by
    simpa using hgrow
  linarith


/-- **The conductor-`4` single-node Weil form is nonnegative on every test.** -/
theorem integral_oddDirichletSingleNode_nonneg_conductor_four (f : ℝ → ℂ) :
    0 ≤ ∫ τ : ℝ, ‖Zeta23.paperFT f τ‖ ^ 2 *
      (weilAtomSymbol (oddSingleNodeWeight 4 2) 2 (τ / (2 * π)) + Real.log 4 +
        π / Real.cosh (π * τ)) :=
  MeasureTheory.integral_nonneg fun τ =>
    mul_nonneg (by positivity) (oddDirichletSingleNodeSymbol_nonneg_two_conductor_four τ)

end

end RHTower
