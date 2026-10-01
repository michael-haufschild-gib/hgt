import GaloisForLFunctions.RHTower.ReflectedCompactComplementIntegral
import GaloisForLFunctions.RHTower.GaussianMomentFourier

open Complex MeasureTheory Set
noncomputable section
namespace RHTower

private theorem compactGaussianKernel_shift_bound {z : ℂ} (h0 : 0 ≤ z.re) (h1 : z.re ≤ 1)
    {B : ℝ} (hB : 0 ≤ B) (hz : |z.im| ≤ B) (v : ℝ) :
    ‖smoothAFEGaussianKernel (z - 9 / 2 + (v : ℂ) * I)‖ ≤
      Real.exp (81 / 4 + B ^ 2) * Real.exp (-(1 / 2 : ℝ) * v ^ 2) := by
  let σ : ℝ := z.re - 9 / 2
  have hσ : σ < 0 := by dsimp only [σ]; linarith
  have hσabs : 1 ≤ |σ| := by rw [abs_of_neg hσ]; dsimp only [σ]; linarith
  have hσsq : σ ^ 2 ≤ 81 / 4 := by dsimp only [σ]; nlinarith
  have hden : 0 < |σ| := lt_of_lt_of_le zero_lt_one hσabs
  have hfactor : Real.exp (σ ^ 2) / |σ| ≤ Real.exp (81 / 4) := by
    apply (div_le_iff₀ hden).mpr
    exact (Real.exp_le_exp.mpr hσsq).trans
      (by nlinarith [Real.exp_pos (81 / 4)])
  have himsq : z.im ^ 2 ≤ B ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hB).mpr hz
  have hgauss : Real.exp (-((z.im + v) ^ 2)) ≤
      Real.exp (B ^ 2) * Real.exp (-(1 / 2 : ℝ) * v ^ 2) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [sq_nonneg (v + 2 * z.im)]
  have hrepr : z - 9 / 2 + (v : ℂ) * I =
      (σ : ℂ) + ((z.im + v : ℝ) : ℂ) * I := by
    apply Complex.ext <;> simp [σ]
  rw [hrepr]
  calc
    _ ≤ (Real.exp (σ ^ 2) / |σ|) * Real.exp (-((z.im + v) ^ 2)) :=
      norm_smoothAFEGaussianKernel_vertical_le_of_ne hσ.ne (z.im + v)
    _ ≤ Real.exp (81 / 4) * (Real.exp (B ^ 2) * Real.exp (-(1 / 2 : ℝ) * v ^ 2)) :=
      mul_le_mul hfactor hgauss (Real.exp_pos _).le (Real.exp_pos _).le
    _ = _ := by rw [← mul_assoc, ← Real.exp_add]

/-- A single integrable majorant controls every translated complementary integrand
on a compact spectral rectangle, retaining the summable arithmetic n^{-9/2} factor. -/
theorem exists_reflectedCompactDeepIntegrand_majorant {N : ℝ} (hN : 0 < N)
    {B : ℝ} (hB : 0 ≤ B) :
    ∃ g : ℝ → ℝ, Integrable g ∧ (∀ v, 0 ≤ g v) ∧
      ∀ z : ℂ, 0 ≤ z.re → z.re ≤ 1 → |z.im| ≤ B → ∀ n : ℕ, ∀ v : ℝ,
        ‖reflectedCompactDeepIntegrand z N n v‖ ≤ g v * (1 / (n + 1 : ℝ) ^ (9 / 2 : ℝ)) := by
  obtain ⟨K, hK, hchi⟩ := exists_norm_zetaChi_neg_seven_halves_le
  let T : ℝ := N ^ (-9 / 2 : ℝ) + N ^ (-7 / 2 : ℝ)
  have hT : 0 ≤ T := by dsimp only [T]; positivity
  let C : ℝ := K * T * Real.exp (81 / 4 + B ^ 2)
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  let g : ℝ → ℝ := fun v => C * ((1 + |v|) ^ 4 * Real.exp (-(1 / 2 : ℝ) * v ^ 2))
  have hpoly : Integrable (fun v : ℝ => (1 + |v|) ^ 4 * Real.exp (-(1 / 2 : ℝ) * v ^ 2)) := by
    have heq : (fun v : ℝ => (1 + |v|) ^ 4 * Real.exp (-(1 / 2 : ℝ) * v ^ 2)) =
        fun v => ∑ j ∈ Finset.range 5, (Nat.choose 4 j : ℝ) *
          (|v| ^ (4 - j) * Real.exp (-(1 / 2 : ℝ) * v ^ 2)) := by
      funext v
      rw [add_pow, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      simp only [one_pow, one_mul]
      ring
    rw [heq]
    exact integrable_finsetSum _ (fun j _ =>
      (integrable_abs_pow_mul_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 2) (4 - j)).const_mul _)
  refine ⟨g, hpoly.const_mul C, fun v => by dsimp only [g]; positivity, ?_⟩
  intro z hz0 hz1 hzi n v
  have hn : (0 : ℝ) < n + 1 := by positivity
  have hnpow : ‖(n + 1 : ℂ) ^ ((-9 / 2 : ℂ) + (v : ℂ) * I)‖ =
      1 / (n + 1 : ℝ) ^ (9 / 2 : ℝ) := by
    rw [show (n + 1 : ℂ) = ((n + 1 : ℝ) : ℂ) by push_cast; rfl,
      Complex.norm_cpow_eq_rpow_re_of_pos hn]
    rw [show (((-9 / 2 : ℂ) + (v : ℂ) * I).re) = (-9 / 2 : ℝ) by simp,
      show (-9 / 2 : ℝ) = -(9 / 2 : ℝ) by ring, Real.rpow_neg hn.le, one_div]
  have hNpow : ‖(N : ℂ) ^ (z - 9 / 2 + (v : ℂ) * I)‖ ≤ T := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hN]
    have hre : (z - 9 / 2 + (v : ℂ) * I).re = z.re - 9 / 2 := by simp
    rw [hre]
    by_cases hN1 : 1 ≤ N
    · exact (Real.rpow_le_rpow_of_exponent_le hN1 (by linarith : z.re - 9 / 2 ≤ -7 / 2)).trans
        (le_add_of_nonneg_left (by positivity))
    · exact (Real.rpow_le_rpow_of_exponent_ge hN (le_of_not_ge hN1)
        (by linarith : (-9 / 2 : ℝ) ≤ z.re - 9 / 2)).trans
        (le_add_of_nonneg_right (by positivity))
  have hker := compactGaussianKernel_shift_bound hz0 hz1 hB hzi v
  unfold reflectedCompactDeepIntegrand
  rw [norm_mul, norm_mul, norm_mul, hnpow]
  calc
    _ ≤ ((K * (1 + |v|) ^ 4) * (1 / (n + 1 : ℝ) ^ (9 / 2 : ℝ))) * T *
        (Real.exp (81 / 4 + B ^ 2) * Real.exp (-(1 / 2 : ℝ) * v ^ 2)) := by
      gcongr
      simpa using hchi v
    _ = _ := by dsimp only [g, C]; ring

end RHTower

