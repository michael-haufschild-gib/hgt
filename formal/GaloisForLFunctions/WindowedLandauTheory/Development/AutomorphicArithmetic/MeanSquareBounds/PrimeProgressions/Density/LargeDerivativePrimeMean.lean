import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.MeanSquareBounds.PrimeProgressions.Density.LogDerivativeTruncation
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.MeanSquareBounds.PrimeProgressions.Density.PrimeWeightedAbel
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.MeanSquareBounds.PrimeProgressions.Density.PrimeLogarithmicCauchySchwarz

/-! A large derivative gives a lower bound on integrated square prime sums. -/

open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology
open scoped Classical

noncomputable section

namespace QH.PrimeProgressions

private theorem abel_pw (a : ℕ → ℂ) {r x y : ℝ} (hr : 0 < r) (hx : 1 ≤ x) (hxy : x ≤ y) (m : ℕ) :
    ‖∑ n ∈ primesIoc x y, a n *
        ((pw (m + 1) (r * Real.log n) - pw (m + 1) (r * Real.log y) : ℝ) : ℂ)‖ ≤
      r * ∫ t in x..y, ‖∑ p ∈ primesIoc x t, a p‖ / t := by
  refine abel_primesIoc_weight a (fun t => pw (m + 1) (r * Real.log t))
    (fun t => (pw m (r * Real.log t) - pw (m + 1) (r * Real.log t)) * (r * t⁻¹)) x y r hx hxy
    ?_ ?_ ?_
  · intro t ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    exact (hasDerivAt_pw m _).comp t ((Real.hasDerivAt_log ht0).const_mul r)
  · have hl : ContinuousOn (fun t => r * Real.log t) (Set.Icc x y) :=
      continuousOn_const.mul (continuousOn_id.log fun t ht => by
        have := ht.1; simp only [id]; linarith)
    refine (((continuous_pw m).comp_continuousOn hl).sub
      ((continuous_pw (m + 1)).comp_continuousOn hl)).mul
      (continuousOn_const.mul (continuousOn_id.inv₀ fun t ht => ?_))
    have := ht.1; simp only [id]; linarith
  · intro t ht
    have ht1 : 1 ≤ t := hx.trans ht.1
    have hu : 0 ≤ r * Real.log t := mul_nonneg hr.le (Real.log_nonneg ht1)
    have h1 : |pw m (r * Real.log t) - pw (m + 1) (r * Real.log t)| ≤ 1 := by
      rw [abs_le]
      constructor <;> linarith [pw_nonneg m hu, pw_nonneg (m + 1) hu, pw_le_one m hu,
        pw_le_one (m + 1) hu]
    have h2 : 0 ≤ r * t⁻¹ := by have : 0 < t := by linarith
                                positivity
    rw [abs_mul, abs_of_nonneg h2, div_eq_mul_inv]
    exact mul_le_of_le_one_left h2 h1

theorem large_mean_of_large_derivative : ∀ A : ℝ, 1 ≤ A → ∃ a b C r₀ K₀ : ℝ, 0 < a ∧ a < b ∧ 0 < C ∧ 0 < r₀ ∧ ∀ (c : ℕ → ℂ) (r : ℝ) (K k : ℕ), (∀ n, ‖c n‖ ≤ 1) → 0 < r → r ≤ r₀ → K₀ ≤ K → K ≤ k → k ≤ 2 * K → 1 / (A * r) ^ (k + 1) ≤ ‖derSeries c k ((1 + r : ℝ) : ℂ)‖ → Real.exp (-(C * K)) / r ^ 3 ≤ ∫ y in (Real.exp (a * K / r))..(Real.exp (b * K / r)), ‖∑ p ∈ primesIoc (Real.exp (a * K / r)) y, (Real.log p : ℂ) * c p / p‖ ^ 2 / y := by
  intro A hA
  let C : ℝ := 12
  have hC : 1 ≤ C := by norm_num [C]
  set B : ℝ := ∑' n : ℕ, (if n.Prime then 0 else Λ n) / (n : ℝ) ^ (3 / 4 : ℝ) with hB
  have hB0 : 0 ≤ B := tsum_nonneg fun n => by
    have : 0 ≤ Λ n := vonMangoldt_nonneg
    positivity
  have hA0 : 0 < A := by linarith
  have hC0 : 0 < C := by linarith
  set η : ℝ := 1 / (16 * C * A) with hη
  have hη0 : 0 < η := by positivity
  have hη1 : η ≤ 1 := by
    rw [hη, div_le_one (by positivity)]; nlinarith
  set δ : ℝ := A⁻¹ * η with hδ
  have hδ0 : 0 < δ := by positivity
  have hδ1 : δ ≤ 1 := mul_le_one₀ (inv_le_one_of_one_le₀ hA) hη0.le hη1
  have hab : δ / 3 < 32 / δ := by
    rw [div_lt_div_iff₀ (by norm_num) hδ0]; nlinarith
  have hlA : 0 ≤ Real.log A := Real.log_nonneg hA
  refine ⟨δ / 3, 32 / δ, 6 * Real.log A + 4 * (32 / δ), 1 / (8 * A * (B + 1)), 1, by positivity,
    hab, by positivity, by positivity, ?_⟩
  intro c r K k hc hr hr0 hK h1 h2 hD
  have hK1 : 1 ≤ K := by exact_mod_cast hK
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  rw [le_div_iff₀ (by positivity)] at hr0
  have hrA : 8 * (r * A) ≤ 1 := by
    have : 0 ≤ r * A * B := by positivity
    nlinarith
  have hrB : 8 * (r * A * B) ≤ 1 := by
    have : 0 ≤ r * A := by positivity
    nlinarith
  have hr1 : r / 2 ≤ 1 := by nlinarith
  obtain ⟨hs, hsum⟩ := mangoldt_right_mass (r := r / 2) (by positivity) hr1
  have hser := poisson_series_le c hc hr hδ0 K (m + 1) h1 h2 hs
  have hxy' : δ / 3 * K / r ≤ 32 / δ * K / r := by gcongr
  have hx : 1 ≤ Real.exp (δ / 3 * K / r) := Real.one_le_exp (by positivity)
  have hxy : Real.exp (δ / 3 * K / r) ≤ Real.exp (32 / δ * K / r) := Real.exp_le_exp.mpr hxy'
  have hab2 := abel_pw (fun p => (Real.log p : ℂ) * c p / p) hr hx hxy m
  have hcs := sq_integral_primeSum_div_le (fun p => (Real.log p : ℂ) * c p / p) _ _ hx hxy
  have hI2 : 0 ≤ ∫ y in (Real.exp (δ / 3 * K / r))..(Real.exp (32 / δ * K / r)),
      ‖∑ p ∈ primesIoc (Real.exp (δ / 3 * K / r)) y, (Real.log p : ℂ) * c p / p‖ ^ 2 / y :=
    intervalIntegral.integral_nonneg hxy fun t ht => by
      have : 0 < t := by linarith [ht.1]
      positivity
  rw [← Real.exp_sub, Real.log_exp] at hcs
  rw [← hB] at hser
  generalize (∫ y in (Real.exp (δ / 3 * K / r))..(Real.exp (32 / δ * K / r)),
      ‖∑ p ∈ primesIoc (Real.exp (δ / 3 * K / r)) y, (Real.log p : ℂ) * c p / p‖ ^ 2 / y) = I₂ at *
  generalize (∫ y in (Real.exp (δ / 3 * K / r))..(Real.exp (32 / δ * K / r)),
      ‖∑ p ∈ primesIoc (Real.exp (δ / 3 * K / r)) y, (Real.log p : ℂ) * c p / p‖ / y) = I₁ at *
  set M : ℝ := A⁻¹ ^ (m + 1) * (A * r)⁻¹ with hM
  have hM0 : 0 < M := by positivity
  have e1 : M ≤ r ^ (m + 1) * ‖derSeries c (m + 1) ((1 + r : ℝ) : ℂ)‖ := by
    calc M = r ^ (m + 1) * (1 / (A * r) ^ (m + 1 + 1)) := by
          rw [hM, inv_pow, mul_pow]; field_simp; ring
      _ ≤ _ := by gcongr
  have e2 : δ ^ (m + 1) * ∑' n : ℕ, Λ n / (n : ℝ) ^ (1 + r / 2) ≤ M / 8 := by
    have h3 : η ^ (m + 1) ≤ η := pow_le_of_le_one hη0.le hη1 (by omega)
    calc _ ≤ δ ^ (m + 1) * (C / (r / 2)) := by gcongr
      _ = A⁻¹ ^ (m + 1) * η ^ (m + 1) * (C / (r / 2)) := by rw [hδ, mul_pow]
      _ ≤ A⁻¹ ^ (m + 1) * η * (C / (r / 2)) := by gcongr
      _ = M / 8 := by rw [hM, hη]; field_simp; ring
  have e3 : (4 * r) ^ (m + 1) * B ≤ M / 8 := by
    have h3 : 4 * r ≤ A⁻¹ := by
      rw [inv_eq_one_div, le_div_iff₀ hA0]
      have : 0 ≤ r * A := by positivity
      nlinarith
    have h4 : B ≤ (A * r)⁻¹ / 8 := by
      rw [inv_eq_one_div, div_div, le_div_iff₀ (by positivity)]
      nlinarith
    calc _ ≤ A⁻¹ ^ (m + 1) * ((A * r)⁻¹ / 8) := by gcongr
      _ = _ := by rw [hM]; ring
  have e4 : M / (2 * r) ≤ I₁ := by
    rw [div_le_iff₀ (by positivity)]; linarith
  have e5 : (M / (2 * r)) ^ 2 ≤ (32 / δ * K / r) * I₂ := by
    calc _ ≤ I₁ ^ 2 := by gcongr
      _ ≤ _ := hcs
      _ ≤ _ := by
        gcongr
        have : 0 ≤ δ / 3 * K / r := by positivity
        linarith
  have hK0 : (0 : ℝ) < K := by linarith
  have e6 : A ^ (2 * (m + 2)) * (4 * (32 / δ * K)) ≤
      Real.exp ((6 * Real.log A + 4 * (32 / δ)) * K) := by
    have h3 : A ^ (2 * (m + 2)) ≤ A ^ (6 * K) := pow_le_pow_right₀ hA (by omega)
    have h4 : A ^ (6 * K) = Real.exp (6 * Real.log A * K) := by
      nth_rewrite 1 [← Real.exp_log hA0]
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    rw [add_mul, Real.exp_add, ← h4]
    gcongr
    linarith [Real.add_one_le_exp (4 * (32 / δ) * K)]
  rw [← div_le_iff₀' (by positivity)] at e5
  refine le_trans ?_ e5
  calc _ ≤ (A ^ (2 * (m + 2)) * (4 * (32 / δ * K)))⁻¹ / r ^ 3 := by
        rw [Real.exp_neg]; gcongr
    _ = _ := by
        rw [hM, inv_pow]; field_simp; ring

end QH.PrimeProgressions
