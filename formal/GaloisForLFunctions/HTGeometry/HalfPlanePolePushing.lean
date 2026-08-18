import GaloisForLFunctions.HTGeometry.HalfPlaneCauchyTransformApproximation

/-!
# Pushing a pole to the left before truncating

The truncated Laplace kernel approximates `1/(s-a)` on a set only where `Re (s-a)` is bounded below
by a positive constant.  A pole sitting to the left of a closed half plane but *between* that half
plane and a disc further left does not satisfy this, so it is first moved further left by the
elementary geometric expansion

```text
1/(s-z) = sum_j (z-z')^j / (s-z')^{j+1},        |z - z'| < dist(z', S),
```

after which every power `1/(s-z')^{j+1}` is replaced by the same power of the truncated Laplace
kernel at `z'`.  The result is entire, and the error splits into an explicit geometric tail and an
explicit power-replacement term.

Together with `HalfPlaneCauchyTransformApproximation` this gives entire approximants that work
simultaneously on a closed half plane and on a large disc, the situation in which a single
truncated Laplace kernel fails.
-/

noncomputable section

open Complex

namespace GaloisForLFunctions.HTGeometry

/-- The pushed kernel: the `N`-term geometric expansion of `1/(s-z)` about `z'`, with the powers of
the moved Cauchy kernel replaced by powers of the truncated Laplace kernel. -/
def pushedKernel (z z' : ℂ) (N : ℕ) (T : ℝ) (s : ℂ) : ℂ :=
  ∑ j ∈ Finset.range N, (z - z') ^ j * (truncPole z' T s) ^ (j + 1)

theorem differentiable_pushedKernel (z z' : ℂ) (N : ℕ) (T : ℝ) :
    Differentiable ℂ (pushedKernel z z' N T) := by
  have h : ∀ j : ℕ, Differentiable ℂ fun s : ℂ => (z - z') ^ j * (truncPole z' T s) ^ (j + 1) :=
    fun j => (differentiable_const _).mul ((differentiable_truncPole z' T).pow _)
  induction N with
  | zero =>
      have hz : pushedKernel z z' 0 T = fun _ : ℂ => 0 := by
        funext s
        simp [pushedKernel]
      rw [hz]
      exact differentiable_const 0
  | succ n ih =>
      have heq : pushedKernel z z' (n + 1) T
          = fun s : ℂ => pushedKernel z z' n T s
              + (z - z') ^ n * (truncPole z' T s) ^ (n + 1) := by
        funext s
        simp [pushedKernel, Finset.sum_range_succ]
      rw [heq]
      exact ih.add (h n)

/-- A power difference is controlled by the difference of the bases. -/
theorem norm_pow_sub_pow_le {x y : ℂ} {M : ℝ} (hx : ‖x‖ ≤ M) (hy : ‖y‖ ≤ M) (m : ℕ) :
    ‖x ^ m - y ^ m‖ ≤ (m : ℝ) * M ^ (m - 1) * ‖x - y‖ := by
  have hM : 0 ≤ M := le_trans (norm_nonneg x) hx
  rw [← geom_sum₂_mul x y m, norm_mul]
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  calc ‖∑ i ∈ Finset.range m, x ^ i * y ^ (m - 1 - i)‖
      ≤ ∑ i ∈ Finset.range m, ‖x ^ i * y ^ (m - 1 - i)‖ := norm_sum_le _ _
    _ ≤ ∑ _i ∈ Finset.range m, M ^ (m - 1) := by
        refine Finset.sum_le_sum fun i hi => ?_
        rw [Finset.mem_range] at hi
        rw [norm_mul, norm_pow, norm_pow]
        have h2 : M ^ i * M ^ (m - 1 - i) = M ^ (m - 1) := by
          rw [← pow_add]
          congr 1
          omega
        rw [← h2]
        exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hx _)
          (pow_le_pow_left₀ (norm_nonneg _) hy _) (by positivity) (by positivity)
    _ = (m : ℝ) * M ^ (m - 1) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- The exact geometric remainder for a shifted Cauchy kernel. -/
theorem inv_sub_sub_geomSum {a b : ℂ} (hb : b ≠ 0) (hba : b - a ≠ 0) (N : ℕ) :
    (b - a)⁻¹ - ∑ j ∈ Finset.range N, a ^ j * (b⁻¹) ^ (j + 1) = (a / b) ^ N * (b - a)⁻¹ := by
  have hkey : (∑ j ∈ Finset.range N, a ^ j * (b⁻¹) ^ (j + 1)) * b ^ N
      = ∑ j ∈ Finset.range N, a ^ j * b ^ (N - 1 - j) := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.mem_range] at hj
    have hpow : (b⁻¹) ^ (j + 1) * b ^ N = b ^ (N - 1 - j) := by
      have hsplitb : b ^ N = b ^ (j + 1) * b ^ (N - 1 - j) := by
        rw [← pow_add]
        congr 1
        omega
      rw [hsplitb, ← mul_assoc, inv_pow, inv_mul_cancel₀ (pow_ne_zero _ hb), one_mul]
    rw [mul_assoc, hpow]
  have hgeom : (∑ j ∈ Finset.range N, a ^ j * b ^ (N - 1 - j)) * (b - a) = b ^ N - a ^ N := by
    have h := geom_sum₂_mul a b N
    have hswap : (∑ j ∈ Finset.range N, a ^ j * b ^ (N - 1 - j)) * (b - a)
        = -((∑ j ∈ Finset.range N, a ^ j * b ^ (N - 1 - j)) * (a - b)) := by ring
    rw [hswap, h]
    ring
  have hbN : (b : ℂ) ^ N ≠ 0 := pow_ne_zero _ hb
  have hne : b ^ N * (b - a) ≠ 0 := mul_ne_zero hbN hba
  have hL : (∑ j ∈ Finset.range N, a ^ j * (b⁻¹) ^ (j + 1)) * (b ^ N * (b - a)) = b ^ N - a ^ N := by
    rw [← mul_assoc, hkey, hgeom]
  have hR : ((b - a)⁻¹ - (a / b) ^ N * (b - a)⁻¹) * (b ^ N * (b - a)) = b ^ N - a ^ N := by
    have hbainv : (b - a)⁻¹ * (b - a) = 1 := inv_mul_cancel₀ hba
    have hbb : b ^ N * (a / b) ^ N = a ^ N := by
      rw [div_pow]
      field_simp
    calc ((b - a)⁻¹ - (a / b) ^ N * (b - a)⁻¹) * (b ^ N * (b - a))
        = ((b - a)⁻¹ * (b - a)) * (b ^ N - b ^ N * (a / b) ^ N) := by ring
      _ = b ^ N - b ^ N * (a / b) ^ N := by rw [hbainv, one_mul]
      _ = b ^ N - a ^ N := by rw [hbb]
  have hS := mul_right_cancel₀ hne (hL.trans hR.symm)
  rw [hS]
  ring

/-- **The pushed-kernel error bound.**  A geometric tail, governed by the distance `d₂` from the
moved pole, plus a power-replacement term, governed by the real-part gap `d₁`.  Separating the two
is what lets the moved pole sit far to the left of a disc while remaining close to it in norm. -/
theorem norm_inv_sub_pushedKernel_le {z z' s : ℂ} {d₁ d₂ T : ℝ} (N : ℕ)
    (hd₁ : 0 < d₁) (hre : d₁ ≤ (s - z').re) (hd₂ : 0 < d₂) (hnorm : d₂ ≤ ‖s - z'‖)
    (hT : 0 ≤ T) (hM : ‖z - z'‖ < d₂) :
    ‖(s - z)⁻¹ - pushedKernel z z' N T s‖
      ≤ (‖z - z'‖ / d₂) ^ N / (d₂ - ‖z - z'‖)
        + (N : ℝ) ^ 2 * (max 1 (2 * ‖z - z'‖ / d₁)) ^ N * (Real.exp (-(T * d₁)) / d₁) := by
  set a : ℂ := z - z' with ha
  set b : ℂ := s - z' with hbdef
  set M : ℝ := ‖a‖ with hMdef
  have hM0 : 0 ≤ M := norm_nonneg _
  have hb1 : d₁ ≤ ‖b‖ := le_trans hre (le_trans (le_abs_self _) (Complex.abs_re_le_norm _))
  have hb0 : b ≠ 0 := by
    intro h
    rw [h, norm_zero] at hb1
    linarith
  have hsz : s - z = b - a := by rw [ha, hbdef]; ring
  have hbanorm : d₂ - M ≤ ‖b - a‖ := by
    have h := norm_sub_norm_le b a
    linarith
  have hba0 : b - a ≠ 0 := by
    intro h
    rw [h, norm_zero] at hbanorm
    linarith
  have hη : ‖b⁻¹ - truncPole z' T s‖ ≤ Real.exp (-(T * d₁)) / d₁ :=
    norm_pole_sub_truncPole_le_of_re hT hd₁ hre
  have hηd : Real.exp (-(T * d₁)) / d₁ ≤ 1 / d₁ := by
    have hle : Real.exp (-(T * d₁)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    gcongr
  have hinvb : ‖b⁻¹‖ ≤ 1 / d₁ := by
    rw [norm_inv, inv_eq_one_div]
    gcongr
  have hinvb2 : ‖b⁻¹‖ ≤ 2 / d₁ := by
    have h12 : (1:ℝ) / d₁ ≤ 2 / d₁ := by
      gcongr
      norm_num
    linarith
  have hP : ‖truncPole z' T s‖ ≤ 2 / d₁ := by
    have heq : truncPole z' T s = b⁻¹ - (b⁻¹ - truncPole z' T s) := (sub_sub_cancel _ _).symm
    calc ‖truncPole z' T s‖ = ‖b⁻¹ - (b⁻¹ - truncPole z' T s)‖ := by rw [← heq]
      _ ≤ ‖b⁻¹‖ + ‖b⁻¹ - truncPole z' T s‖ := norm_sub_le _ _
      _ ≤ 1 / d₁ + 1 / d₁ := add_le_add hinvb (le_trans hη hηd)
      _ = 2 / d₁ := by ring
  have hsplit : (s - z)⁻¹ - pushedKernel z z' N T s
      = (a / b) ^ N * (b - a)⁻¹
        + ∑ j ∈ Finset.range N, a ^ j * ((b⁻¹) ^ (j + 1) - (truncPole z' T s) ^ (j + 1)) := by
    have hdistrib : ∑ j ∈ Finset.range N, a ^ j * ((b⁻¹) ^ (j + 1) - (truncPole z' T s) ^ (j + 1))
        = (∑ j ∈ Finset.range N, a ^ j * (b⁻¹) ^ (j + 1))
          - ∑ j ∈ Finset.range N, a ^ j * (truncPole z' T s) ^ (j + 1) := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [hsz, pushedKernel, hdistrib, ← inv_sub_sub_geomSum hb0 hba0 N]
    ring
  rw [hsplit]
  refine le_trans (norm_add_le _ _) (add_le_add ?_ ?_)
  · rw [norm_mul, norm_pow, norm_div, norm_inv]
    have h1 : M / ‖b‖ ≤ M / d₂ := by gcongr
    have h2 : ‖b - a‖⁻¹ ≤ (d₂ - M)⁻¹ := by
      have hpos : 0 < d₂ - M := by linarith
      rw [inv_eq_one_div, inv_eq_one_div]
      gcongr
    have hMd : (0:ℝ) ≤ (M / d₂) ^ N := pow_nonneg (div_nonneg hM0 hd₂.le) N
    calc (M / ‖b‖) ^ N * ‖b - a‖⁻¹ ≤ (M / d₂) ^ N * ‖b - a‖⁻¹ := by
          gcongr
      _ ≤ (M / d₂) ^ N * (d₂ - M)⁻¹ := mul_le_mul_of_nonneg_left h2 hMd
      _ = (M / d₂) ^ N / (d₂ - M) := by ring
  · have hterm : ∀ j ∈ Finset.range N,
        ‖a ^ j * ((b⁻¹) ^ (j + 1) - (truncPole z' T s) ^ (j + 1))‖
          ≤ (N : ℝ) * (max 1 (2 * M / d₁)) ^ N * (Real.exp (-(T * d₁)) / d₁) := by
      intro j hj
      rw [Finset.mem_range] at hj
      rw [norm_mul, norm_pow]
      have hbase : ‖(b⁻¹) ^ (j + 1) - (truncPole z' T s) ^ (j + 1)‖
          ≤ ((j : ℝ) + 1) * (2 / d₁) ^ j * ‖b⁻¹ - truncPole z' T s‖ := by
        have h := norm_pow_sub_pow_le hinvb2 hP (j + 1)
        simpa using h
      have hstep : M ^ j * ‖(b⁻¹) ^ (j + 1) - (truncPole z' T s) ^ (j + 1)‖
          ≤ M ^ j * (((j : ℝ) + 1) * (2 / d₁) ^ j * (Real.exp (-(T * d₁)) / d₁)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        refine le_trans hbase ?_
        exact mul_le_mul_of_nonneg_left hη (by positivity)
      refine le_trans hstep ?_
      have hcomb : M ^ j * (((j : ℝ) + 1) * (2 / d₁) ^ j * (Real.exp (-(T * d₁)) / d₁))
          = ((j : ℝ) + 1) * (2 * M / d₁) ^ j * (Real.exp (-(T * d₁)) / d₁) := by
        rw [show (2 * M / d₁) ^ j = M ^ j * (2 / d₁) ^ j from by
          rw [← mul_pow]; congr 1; ring]
        ring
      rw [hcomb]
      have hmaxge : (1:ℝ) ≤ max 1 (2 * M / d₁) := le_max_left _ _
      have hpowle : (2 * M / d₁) ^ j ≤ (max 1 (2 * M / d₁)) ^ N := by
        refine le_trans (pow_le_pow_left₀ (by positivity) (le_max_right 1 (2 * M / d₁)) j) ?_
        exact pow_le_pow_right₀ hmaxge (by omega)
      have hjN : ((j : ℝ) + 1) ≤ (N : ℝ) := by
        have hcast : ((j + 1 : ℕ) : ℝ) ≤ (N : ℝ) := Nat.cast_le.mpr (by omega)
        push_cast at hcast
        linarith
      have hε0 : 0 ≤ Real.exp (-(T * d₁)) / d₁ := by positivity
      refine mul_le_mul_of_nonneg_right ?_ hε0
      exact mul_le_mul hjN hpowle (by positivity) (by positivity)
    calc ‖∑ j ∈ Finset.range N, a ^ j * ((b⁻¹) ^ (j + 1) - (truncPole z' T s) ^ (j + 1))‖
        ≤ ∑ j ∈ Finset.range N, ‖a ^ j * ((b⁻¹) ^ (j + 1) - (truncPole z' T s) ^ (j + 1))‖ :=
          norm_sum_le _ _
      _ ≤ ∑ _j ∈ Finset.range N, (N : ℝ) * (max 1 (2 * M / d₁)) ^ N
            * (Real.exp (-(T * d₁)) / d₁) := Finset.sum_le_sum hterm
      _ = (N : ℝ) * ((N : ℝ) * (max 1 (2 * M / d₁)) ^ N * (Real.exp (-(T * d₁)) / d₁)) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ = (N : ℝ) ^ 2 * (max 1 (2 * M / d₁)) ^ N * (Real.exp (-(T * d₁)) / d₁) := by ring

end GaloisForLFunctions.HTGeometry

end
