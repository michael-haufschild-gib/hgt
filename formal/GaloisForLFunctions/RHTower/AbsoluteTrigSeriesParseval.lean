import Mathlib

/-!
# Parseval for absolutely convergent trigonometric series of period two

For `Σ ‖c_n‖ < ∞`, `S(x) = Σ_{n ≥ 0} c_n e^{πinx}` satisfies `∫₀² |S(x)|² dx = 2 Σ |c_n|²`.
The finite sums follow from orthogonality `∫₀² e^{πi(m-n)x} dx = 2δ_{mn}`; the tails are uniformly small.
-/

open Complex Filter Topology
open scoped Real

namespace RHTower

noncomputable section

/-- Orthogonality of `e^{πinx}` on `[0,2]`. -/
theorem integral_exp_mul_conj_exp (m n : ℕ) :
    ∫ x in (0 : ℝ)..2, Complex.exp (π * I * m * x) * (starRingEnd ℂ) (Complex.exp (π * I * n * x)) =
      if m = n then 2 else 0 := by
  have hconj : ∀ x : ℝ, (starRingEnd ℂ) (Complex.exp (π * I * n * x)) = Complex.exp (-(π * I * n * x)) := by
    intro x
    rw [← Complex.exp_conj]; congr 1
    simp [map_mul, Complex.conj_I, Complex.conj_ofReal]
  have hprod : ∀ x : ℝ, Complex.exp (π * I * m * x) * (starRingEnd ℂ) (Complex.exp (π * I * n * x)) =
      Complex.exp ((π * I * ((m : ℂ) - n)) * x) := by
    intro x; rw [hconj, ← Complex.exp_add]; congr 1; ring
  simp_rw [hprod]
  split_ifs with hmn
  · subst hmn
    simp only [sub_self, mul_zero, zero_mul, Complex.exp_zero, intervalIntegral.integral_const,
      sub_zero, real_smul, mul_one]
    norm_num
  · have hne : (π : ℂ) * I * ((m : ℂ) - n) ≠ 0 := by
      refine mul_ne_zero (mul_ne_zero (by exact_mod_cast Real.pi_ne_zero) I_ne_zero) ?_
      rw [sub_ne_zero]; exact_mod_cast hmn
    rw [integral_exp_mul_complex hne]
    have h2 : Complex.exp (π * I * ((m : ℂ) - n) * ((2 : ℝ) : ℂ)) = 1 := by
      have : π * I * ((m : ℂ) - n) * ((2 : ℝ) : ℂ) = ((m - n : ℤ) : ℂ) * (2 * π * I) := by
        push_cast; ring
      rw [this, Complex.exp_int_mul_two_pi_mul_I]
    rw [h2]; simp

/-- **Finite Parseval.** -/
theorem integral_norm_sq_trig_sum (c : ℕ → ℂ) (N : ℕ) :
    ∫ x in (0 : ℝ)..2, ‖∑ n ∈ Finset.range N, c n * Complex.exp (π * I * n * x)‖ ^ 2 =
      2 * ∑ n ∈ Finset.range N, ‖c n‖ ^ 2 := by
  set S : ℝ → ℂ := fun x => ∑ n ∈ Finset.range N, c n * Complex.exp (π * I * n * x) with hS
  have hcont : Continuous S := by rw [hS]; fun_prop
  have hsq : ∀ x, ((‖S x‖ ^ 2 : ℝ) : ℂ) = S x * (starRingEnd ℂ) (S x) := by
    intro x; rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hC : ((∫ x in (0 : ℝ)..2, ‖S x‖ ^ 2 : ℝ) : ℂ) = 2 * ∑ n ∈ Finset.range N, ((‖c n‖ ^ 2 : ℝ) : ℂ) := by
    rw [← intervalIntegral.integral_ofReal]
    simp_rw [hsq]
    have hexp : ∀ x, S x * (starRingEnd ℂ) (S x) =
        ∑ m ∈ Finset.range N, ∑ n ∈ Finset.range N, (c m * (starRingEnd ℂ) (c n)) *
          (Complex.exp (π * I * m * x) * (starRingEnd ℂ) (Complex.exp (π * I * n * x))) := by
      intro x
      simp only [hS]
      rw [map_sum, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun n _ => ?_
      rw [map_mul]; ring
    simp_rw [hexp]
    have hcj : ∀ m n : ℕ, Continuous fun x : ℝ => (c m * (starRingEnd ℂ) (c n)) *
        (Complex.exp (π * I * m * x) * (starRingEnd ℂ) (Complex.exp (π * I * n * x))) := by
      intro m n
      exact continuous_const.mul ((by fun_prop : Continuous fun x : ℝ => Complex.exp (π * I * m * x)).mul
        (Complex.continuous_conj.comp (by fun_prop)))
    rw [intervalIntegral.integral_finsetSum (fun m _ =>
      (continuous_finsetSum _ fun n _ => hcj m n).intervalIntegrable _ _)]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [intervalIntegral.integral_finsetSum (fun n _ => (hcj m n).intervalIntegrable _ _)]
    simp_rw [intervalIntegral.integral_const_mul, integral_exp_mul_conj_exp]
    rw [Finset.sum_eq_single m]
    · rw [if_pos rfl, Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
    · intro n _ hnm; rw [if_neg (Ne.symm hnm), mul_zero]
    · intro h; exact absurd hm h
  have : ((∫ x in (0 : ℝ)..2, ‖S x‖ ^ 2 : ℝ) : ℂ) = ((2 * ∑ n ∈ Finset.range N, ‖c n‖ ^ 2 : ℝ) : ℂ) := by
    rw [hC]; push_cast; rfl
  exact_mod_cast this

/-- **Parseval for absolutely convergent series.** -/
theorem integral_norm_sq_trig_tsum (c : ℕ → ℂ) (hc : Summable fun n => ‖c n‖) :
    ∫ x in (0 : ℝ)..2, ‖∑' n, c n * Complex.exp (π * I * n * x)‖ ^ 2 = 2 * ∑' n, ‖c n‖ ^ 2 := by
  set A : ℝ := ∑' n, ‖c n‖ with hA
  have hA0 : 0 ≤ A := tsum_nonneg fun n => norm_nonneg _
  have hterm : ∀ (n : ℕ) (x : ℝ), ‖c n * Complex.exp (π * I * n * x)‖ = ‖c n‖ := by
    intro n x
    rw [norm_mul, Complex.norm_exp]
    simp
  have hsumm : ∀ x : ℝ, Summable fun n => c n * Complex.exp (π * I * n * x) := fun x =>
    Summable.of_norm (by simp_rw [hterm]; exact hc)
  set S : ℝ → ℂ := fun x => ∑' n, c n * Complex.exp (π * I * n * x)
  set SN : ℕ → ℝ → ℂ := fun N x => ∑ n ∈ Finset.range N, c n * Complex.exp (π * I * n * x)
  set T : ℕ → ℝ := fun N => ∑' n, ‖c (n + N)‖
  have hT : Tendsto T atTop (𝓝 0) := tendsto_sum_nat_add fun n => ‖c n‖
  have hSbound : ∀ x, ‖S x‖ ≤ A := fun x =>
    (norm_tsum_le_tsum_norm (by simp_rw [hterm]; exact hc)).trans (by simp_rw [hterm]; rfl)
  have hSNbound : ∀ N x, ‖SN N x‖ ≤ A := by
    intro N x
    calc ‖SN N x‖ ≤ ∑ n ∈ Finset.range N, ‖c n * Complex.exp (π * I * n * x)‖ := norm_sum_le _ _
      _ = ∑ n ∈ Finset.range N, ‖c n‖ := by simp_rw [hterm]
      _ ≤ A := hc.sum_le_tsum _ (fun n _ => norm_nonneg _)
  have hdiff : ∀ N x, ‖S x - SN N x‖ ≤ T N := by
    intro N x
    have hsplit := ((hsumm x).sum_add_tsum_nat_add N).symm
    have : S x - SN N x = ∑' n, c (n + N) * Complex.exp (π * I * ((n + N : ℕ) : ℂ) * x) := by
      show (∑' n, c n * Complex.exp (π * I * n * x)) - SN N x = _
      rw [hsplit]; simp [SN]
    rw [this]
    have hs' : Summable fun n => ‖c (n + N) * Complex.exp (π * I * ((n + N : ℕ) : ℂ) * x)‖ := by
      simp_rw [hterm]; exact (summable_nat_add_iff N).mpr hc
    exact (norm_tsum_le_tsum_norm hs').trans (by simp_rw [hterm]; rfl)
  have hcS : Continuous S := by
    refine continuous_tsum (fun n => by fun_prop) hc (fun n x => (hterm n x).le)
  have hlim_left : Tendsto (fun N => ∫ x in (0 : ℝ)..2, ‖SN N x‖ ^ 2) atTop
      (𝓝 (∫ x in (0 : ℝ)..2, ‖S x‖ ^ 2)) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N₀, hN₀⟩ := Metric.tendsto_atTop.mp hT (ε / (4 * A + 1) / 2) (by positivity)
    refine ⟨N₀, fun N hN => ?_⟩
    have hTN : T N < ε / (4 * A + 1) / 2 := by
      have := hN₀ N hN; rw [Real.dist_eq, sub_zero] at this
      exact lt_of_abs_lt this
    rw [Real.dist_eq, ← intervalIntegral.integral_sub]
    · have hpt : ∀ x ∈ Set.uIoc (0 : ℝ) 2, ‖‖SN N x‖ ^ 2 - ‖S x‖ ^ 2‖ ≤ 2 * A * T N := by
        intro x _
        rw [Real.norm_eq_abs, sq_sub_sq, abs_mul]
        have h1 : |‖SN N x‖ + ‖S x‖| ≤ 2 * A := by
          rw [abs_of_nonneg (by positivity)]; linarith [hSNbound N x, hSbound x]
        have h2 : |‖SN N x‖ - ‖S x‖| ≤ T N := by
          refine (abs_norm_sub_norm_le _ _).trans ?_
          rw [norm_sub_rev]; exact hdiff N x
        exact mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
      have hb := intervalIntegral.norm_integral_le_of_norm_le_const hpt
      rw [Real.norm_eq_abs] at hb
      calc |∫ x in (0 : ℝ)..2, ‖SN N x‖ ^ 2 - ‖S x‖ ^ 2| ≤ 2 * A * T N * |2 - 0| := hb
        _ = 4 * A * T N := by norm_num; ring
        _ ≤ (4 * A + 1) * T N := by
            have : 0 ≤ T N := tsum_nonneg fun n => norm_nonneg _
            nlinarith
        _ < (4 * A + 1) * (ε / (4 * A + 1) / 2) := by
            exact mul_lt_mul_of_pos_left hTN (by positivity)
        _ < ε := by field_simp; linarith
    · exact Continuous.intervalIntegrable
        ((continuous_finsetSum _ fun n _ => by fun_prop : Continuous (SN N)).norm.pow 2) _ _
    · exact Continuous.intervalIntegrable (hcS.norm.pow 2) _ _
  have hlim_right : Tendsto (fun N => 2 * ∑ n ∈ Finset.range N, ‖c n‖ ^ 2) atTop
      (𝓝 (2 * ∑' n, ‖c n‖ ^ 2)) := by
    have hsq : Summable fun n => ‖c n‖ ^ 2 := by
      refine Summable.of_nonneg_of_le (fun n => sq_nonneg _) (fun n => ?_) (hc.mul_left A)
      rw [sq]
      exact mul_le_mul_of_nonneg_right (hc.le_tsum n (fun m _ => norm_nonneg _)) (norm_nonneg _)
    exact (hsq.hasSum.tendsto_sum_nat).const_mul 2
  have heq : (fun N => ∫ x in (0 : ℝ)..2, ‖SN N x‖ ^ 2) = fun N => 2 * ∑ n ∈ Finset.range N, ‖c n‖ ^ 2 :=
    funext fun N => integral_norm_sq_trig_sum c N
  rw [heq] at hlim_left
  exact tendsto_nhds_unique hlim_left hlim_right

end

end RHTower
