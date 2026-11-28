import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! The two collision sums decay geometrically in factor degree.
The lowest degrees give the combined inverse square-root bound. -/

noncomputable section

namespace WindowedLandauTheory.ConcN

private theorem cube_div_fourth_sub_one_le (s : ℝ) (hs : 2 ≤ s) : s ^ 3 * (s ^ 4 - 1)⁻¹ ≤ 2 * (1 / s) := by
  have hs0 : 0 < s := by linarith
  have h2 : 4 ≤ s ^ 2 := by nlinarith
  have h44 : s ^ 4 = s ^ 2 * s ^ 2 := by ring
  have h16 : 16 ≤ s ^ 4 := by nlinarith
  have h4 : 0 < s ^ 4 - 1 := by linarith
  rw [← div_eq_mul_inv, div_le_iff₀ h4,
    show 2 * (1 / s) * (s ^ 4 - 1) = 2 * (s ^ 4 - 1) / s by ring, le_div_iff₀ hs0]
  have : s ^ 3 * s = s ^ 4 := by ring
  linarith

private theorem div_fourth_sub_one_le (s : ℝ) (hs : 2 ≤ s) : s * (s ^ 4 - 1)⁻¹ ≤ 2 * (1 / s ^ 3) := by
  have hs0 : 0 < s := by linarith
  have h2 : 4 ≤ s ^ 2 := by nlinarith
  have h44 : s ^ 4 = s ^ 2 * s ^ 2 := by ring
  have h16 : 16 ≤ s ^ 4 := by nlinarith
  have h4 : 0 < s ^ 4 - 1 := by linarith
  rw [← div_eq_mul_inv, div_le_iff₀ h4,
    show 2 * (1 / s ^ 3) * (s ^ 4 - 1) = 2 * (s ^ 4 - 1) / s ^ 3 by ring,
    le_div_iff₀ (by positivity)]
  have : s * s ^ 3 = s ^ 4 := by ring
  linarith

private theorem sum_Icc_two_mul_pow_le_sixteen_thirds_mul_sq (x : ℝ) (hx0 : 0 ≤ x) (hx : x ≤ 1 / 8) (N : ℕ) :
    ∑ δ ∈ Finset.Icc 2 N, (δ : ℝ) * x ^ δ ≤ 16 / 3 * x ^ 2 := by
  have h2x0 : 0 ≤ 2 * x := by linarith
  have h2x1 : 2 * x < 1 := by linarith
  calc ∑ δ ∈ Finset.Icc 2 N, (δ : ℝ) * x ^ δ ≤ ∑ δ ∈ Finset.Ico 2 (N + 1), (2 * x) ^ δ := by
        rw [show Finset.Icc 2 N = Finset.Ico 2 (N + 1) by
          ext; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega]
        apply Finset.sum_le_sum
        intro δ _
        rw [mul_pow]
        apply mul_le_mul_of_nonneg_right _ (pow_nonneg hx0 _)
        exact_mod_cast (Nat.lt_two_pow_self).le
    _ ≤ (2 * x) ^ 2 / (1 - 2 * x) := geom_sum_Ico_le_of_lt_one h2x0 h2x1
    _ ≤ 16 / 3 * x ^ 2 := by
        rw [div_le_iff₀ (by linarith)]
        nlinarith [mul_nonneg (sq_nonneg x) (by linarith : (0 : ℝ) ≤ 1 / 8 - x)]

private theorem sum_Icc_one_sq_mul_pow_le_five_mul (y : ℝ) (hy0 : 0 ≤ y) (hy : y ≤ 1 / 512) (N : ℕ) :
    ∑ δ ∈ Finset.Icc 1 N, (δ : ℝ) ^ 2 * y ^ δ ≤ 5 * y := by
  have h4y0 : 0 ≤ 4 * y := by linarith
  have h4y1 : 4 * y < 1 := by linarith
  calc ∑ δ ∈ Finset.Icc 1 N, (δ : ℝ) ^ 2 * y ^ δ ≤ ∑ δ ∈ Finset.Ico 1 (N + 1), (4 * y) ^ δ := by
        rw [show Finset.Icc 1 N = Finset.Ico 1 (N + 1) by
          ext; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega]
        apply Finset.sum_le_sum
        intro δ _
        rw [mul_pow]
        apply mul_le_mul_of_nonneg_right _ (pow_nonneg hy0 _)
        have h : δ ≤ 2 ^ δ := (Nat.lt_two_pow_self).le
        have h' : δ ^ 2 ≤ 4 ^ δ := by
          calc δ ^ 2 ≤ (2 ^ δ) ^ 2 := Nat.pow_le_pow_left h 2
            _ = 4 ^ δ := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
        exact_mod_cast h'
    _ ≤ (4 * y) ^ 1 / (1 - 4 * y) := geom_sum_Ico_le_of_lt_one h4y0 h4y1
    _ ≤ 5 * y := by
        rw [pow_one, div_le_iff₀ (by linarith)]
        nlinarith [mul_nonneg hy0 (by linarith : (0 : ℝ) ≤ 1 - 20 * y)]

theorem collision_series_le (g N : ℕ) (hg : 2 ^ 12 ≤ g) :
    (∑ δ ∈ Finset.Icc 2 N, (3 / 2 * δ * Real.log g) *
      ((g : ℝ) ^ (3 * (δ : ℝ) / 4) * ((g : ℝ) ^ δ - 1)⁻¹)) +
    (∑ δ ∈ Finset.Icc 1 N, (3 * (δ : ℝ) ^ 2 * Real.log g) *
      ((g : ℝ) ^ ((δ : ℝ) / 4) * ((g : ℝ) ^ δ - 1)⁻¹)) ≤
      23 * Real.log g / Real.sqrt g := by
  have hQ : (4096 : ℝ) ≤ (g : ℝ) := by exact_mod_cast hg
  have hQ0 : (0 : ℝ) ≤ g := Nat.cast_nonneg g
  have hLQ : 0 ≤ Real.log g := Real.log_nonneg (by linarith)
  obtain ⟨s, hsdef⟩ : ∃ s : ℝ, s = (g : ℝ) ^ (4 : ℝ)⁻¹ := ⟨_, rfl⟩
  have hs0 : 0 ≤ s := by rw [hsdef]; positivity
  have hs4 : s ^ 4 = (g : ℝ) := by
    rw [hsdef, show (4 : ℝ)⁻¹ = ((4 : ℕ) : ℝ)⁻¹ by norm_num]
    exact Real.rpow_inv_natCast_pow hQ0 (by norm_num)
  have hs8 : 8 ≤ s := by
    by_contra h
    push_neg at h
    have h2 : s ^ 2 < 64 := by nlinarith
    have h4 : s ^ 4 < 4096 := by
      nlinarith [mul_pos (by linarith : (0 : ℝ) < 64 - s ^ 2) (by positivity : (0 : ℝ) < 64 + s ^ 2)]
    linarith
  have hsδ : ∀ δ : ℕ, 1 ≤ δ → 2 ≤ s ^ δ := fun δ hδ => by
    calc (2 : ℝ) ≤ s ^ 1 := by rw [pow_one]; linarith
      _ ≤ s ^ δ := pow_le_pow_right₀ (by linarith) hδ
  obtain ⟨x, hxdef⟩ : ∃ x : ℝ, x = s⁻¹ := ⟨_, rfl⟩
  have hx0 : 0 ≤ x := by rw [hxdef]; exact inv_nonneg.2 hs0
  have hxs : x * s = 1 := by rw [hxdef, inv_mul_cancel₀ (ne_of_gt (by linarith))]
  have hx8 : x ≤ 1 / 8 := by nlinarith [mul_le_mul_of_nonneg_left hs8 hx0]
  have hx512 : x ^ 3 ≤ 1 / 512 := by
    calc x ^ 3 ≤ (1 / 8) ^ 3 := pow_le_pow_left₀ hx0 hx8 3
      _ = 1 / 512 := by norm_num
  have hpowA : ∀ δ : ℕ, (g : ℝ) ^ (3 * (δ : ℝ) / 4) = (s ^ δ) ^ 3 := fun δ => by
    rw [show 3 * (δ : ℝ) / 4 = (4 : ℝ)⁻¹ * ((3 * δ : ℕ) : ℝ) by push_cast; ring,
      Real.rpow_mul hQ0, ← hsdef, Real.rpow_natCast]
    ring
  have hpowB : ∀ δ : ℕ, (g : ℝ) ^ ((δ : ℝ) / 4) = s ^ δ := fun δ => by
    rw [show (δ : ℝ) / 4 = (4 : ℝ)⁻¹ * ((δ : ℕ) : ℝ) by ring,
      Real.rpow_mul hQ0, ← hsdef, Real.rpow_natCast]
  have hpowQ : ∀ δ : ℕ, (g : ℝ) ^ δ = (s ^ δ) ^ 4 := fun δ => by
    rw [← hs4]; ring
  have hQδ : ∀ δ : ℕ, (1 : ℝ) ≤ (g : ℝ) ^ δ := fun δ => one_le_pow₀ (by linarith)
  have htA : ∀ δ : ℕ, 2 ≤ δ →
      (g : ℝ) ^ (3 * (δ : ℝ) / 4) * ((g : ℝ) ^ δ - 1)⁻¹ ≤ 2 * x ^ δ := fun δ hδ => by
    rw [hpowA δ, hpowQ δ]
    calc (s ^ δ) ^ 3 * ((s ^ δ) ^ 4 - 1)⁻¹ ≤ 2 * (1 / s ^ δ) := cube_div_fourth_sub_one_le (s ^ δ) (hsδ δ (by omega))
      _ = 2 * x ^ δ := by rw [hxdef]; ring
  have htB : ∀ δ : ℕ, 1 ≤ δ →
      (g : ℝ) ^ ((δ : ℝ) / 4) * ((g : ℝ) ^ δ - 1)⁻¹ ≤ 2 * (x ^ 3) ^ δ := fun δ hδ => by
    rw [hpowB δ, hpowQ δ]
    calc s ^ δ * ((s ^ δ) ^ 4 - 1)⁻¹ ≤ 2 * (1 / (s ^ δ) ^ 3) := div_fourth_sub_one_le (s ^ δ) (hsδ δ hδ)
      _ = 2 * (x ^ 3) ^ δ := by rw [hxdef]; ring
  have hA : (∑ δ ∈ Finset.Icc 2 N, (3 / 2 * δ * Real.log g) *
      ((g : ℝ) ^ (3 * (δ : ℝ) / 4) * ((g : ℝ) ^ δ - 1)⁻¹)) ≤
      3 * Real.log g * (16 / 3 * x ^ 2) := by
    calc
      _ ≤ ∑ δ ∈ Finset.Icc 2 N, 3 * Real.log g * ((δ : ℝ) * x ^ δ) := by
        refine Finset.sum_le_sum fun δ hδ => ?_
        calc
          _ ≤ (3 / 2 * δ * Real.log g) * (2 * x ^ δ) :=
            mul_le_mul_of_nonneg_left (htA δ (Finset.mem_Icc.mp hδ).1)
              (mul_nonneg (by positivity) hLQ)
          _ = _ := by ring
      _ = 3 * Real.log g * ∑ δ ∈ Finset.Icc 2 N, (δ : ℝ) * x ^ δ := by rw [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left (sum_Icc_two_mul_pow_le_sixteen_thirds_mul_sq x hx0 hx8 N)
          (mul_nonneg (by norm_num) hLQ)
  have hB : (∑ δ ∈ Finset.Icc 1 N, (3 * (δ : ℝ) ^ 2 * Real.log g) *
      ((g : ℝ) ^ ((δ : ℝ) / 4) * ((g : ℝ) ^ δ - 1)⁻¹)) ≤
      6 * Real.log g * (5 * x ^ 3) := by
    calc
      _ ≤ ∑ δ ∈ Finset.Icc 1 N, 6 * Real.log g * ((δ : ℝ) ^ 2 * (x ^ 3) ^ δ) := by
        refine Finset.sum_le_sum fun δ hδ => ?_
        calc
          _ ≤ (3 * (δ : ℝ) ^ 2 * Real.log g) * (2 * (x ^ 3) ^ δ) :=
            mul_le_mul_of_nonneg_left (htB δ (Finset.mem_Icc.mp hδ).1)
              (mul_nonneg (by positivity) hLQ)
          _ = _ := by ring
      _ = 6 * Real.log g * ∑ δ ∈ Finset.Icc 1 N, (δ : ℝ) ^ 2 * (x ^ 3) ^ δ := by rw [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left (sum_Icc_one_sq_mul_pow_le_five_mul (x ^ 3) (by positivity) hx512 N)
          (mul_nonneg (by norm_num) hLQ)
  have hsq : Real.sqrt (g : ℝ) = s ^ 2 := by
    rw [← hs4, show s ^ 4 = (s ^ 2) ^ 2 by ring, Real.sqrt_sq (by positivity)]
  have hx2 : x ^ 2 = 1 / s ^ 2 := by rw [hxdef, inv_pow, one_div]
  have hx3 : x ^ 3 ≤ x ^ 2 / 8 := by
    nlinarith only [mul_le_mul_of_nonneg_left hx8 (sq_nonneg x)]
  rw [hsq]
  calc
    _ ≤ 3 * Real.log g * (16 / 3 * x ^ 2) + 6 * Real.log g * (5 * x ^ 3) := add_le_add hA hB
    _ ≤ 23 * Real.log g * x ^ 2 := by
      nlinarith only [mul_le_mul_of_nonneg_left hx3 hLQ, mul_nonneg hLQ (sq_nonneg x)]
    _ = 23 * Real.log g / s ^ 2 := by rw [hx2]; ring

end WindowedLandauTheory.ConcN

#print axioms WindowedLandauTheory.ConcN.collision_series_le
