import GaloisForLFunctions.ExceptionalLayerTheory.GaussianVaughanBilinearCancellation

/-!
# First-derivative cancellation in Gaussian correlations

After the height phase cancels, off-diagonal correlations have a monotone
nonvanishing quadratic derivative. Below the first integer resonance,
Kuzmin–Landau improves the second-derivative estimate. Abel summation
retains the entire initial Gaussian factor.
-/

open Complex Finset RHTower RHTower.Sieve

noncomputable section
namespace GaloisForLFunctions.ExceptionalLayerTheory

private theorem norm_sum_quadratic_positive_first_derivative_le {u : ℝ} (hu : 0 < u)
    {P Q : ℕ} (hP : 1 ≤ P) (hband : u * Q / Real.pi ≤ 1 / 2) :
    ‖∑ n ∈ Ico P Q, quadraticCharacter u n‖ ≤ 2 * Real.pi / (u * P) := by
  have hP0 : (0 : ℝ) < P := by exact_mod_cast (show 0 < P by omega)
  have hδ : 0 < u * P / Real.pi := div_pos (mul_pos hu hP0) Real.pi_pos
  by_cases hPQ : P < Q
  · have hspan : (P : ℝ) + ((Q - P - 1 : ℕ) : ℝ) ≤ Q := by
      exact_mod_cast (show P + (Q - P - 1) ≤ Q by omega)
    have hδhalf : u * P / Real.pi ≤ 1 / 2 := by
      refine le_trans ?_ hband
      gcongr
    have hd (x : ℝ) : HasDerivAt (fun v : ℝ => u / Real.pi / 2 * v ^ 2)
        (u / Real.pi * x) x := by
      have hh : HasDerivAt (fun v : ℝ => u / Real.pi / 2 * v ^ 2)
          (u / Real.pi / 2 * (2 * x)) x := by
        simpa using! (hasDerivAt_pow 2 x).const_mul (u / Real.pi / 2)
      convert hh using 1
      ring
    have hb := kuzminLandau_interval (fun v : ℝ => u / Real.pi / 2 * v ^ 2)
      (fun v => u / Real.pi * v) P (Q - P - 1) 0 hδ
      (fun x _ => hd x)
      (fun x _ y _ hxy => mul_le_mul_of_nonneg_left hxy (by positivity))
      (fun x hx => by
        simp only [Int.cast_zero, zero_add]
        have hh := mul_le_mul_of_nonneg_left hx.1 (by positivity : 0 ≤ u / Real.pi)
        calc
          u * P / Real.pi = u / Real.pi * P := by ring
          _ ≤ u / Real.pi * x := hh)
      (fun x hx => by
        simp only [Int.cast_zero, zero_add]
        have hupper : u / Real.pi * x ≤ 1 / 2 := by
          calc
            u / Real.pi * x ≤ u / Real.pi * Q :=
              mul_le_mul_of_nonneg_left (hx.2.trans hspan) (by positivity)
            _ = u * Q / Real.pi := by ring
            _ ≤ 1 / 2 := hband
        linarith only [hupper, hδhalf])
    have hlen : Q - P - 1 + 1 = Q - P := by omega
    rw [hlen] at hb
    have he : (∑ n ∈ Ico P Q, quadraticCharacter u n) =
        ∑ n ∈ range (Q - P),
          Complex.exp ((((2 * Real.pi * (u / Real.pi / 2 * ((P : ℝ) + n) ^ 2)) : ℝ) : ℂ) * I) := by
      rw [sum_Ico_eq_sum_range]
      apply sum_congr rfl
      intro n _
      dsimp only [quadraticCharacter]
      congr 2
      push_cast
      field_simp [Real.pi_ne_zero]
    rw [he]
    refine hb.trans ?_
    have heq : 2 * Real.pi / (u * P) = 2 / (u * P / Real.pi) := by field_simp
    rw [heq]
    apply (le_div_iff₀ hδ).mpr
    have hc : (3 / (2 * (u * P / Real.pi)) + 1) * (u * P / Real.pi) =
        3 / 2 + u * P / Real.pi := by field_simp
    rw [hc]
    linarith only [hδhalf]
  · rw [Ico_eq_empty_of_le (Nat.le_of_not_gt hPQ), sum_empty, norm_zero]
    positivity

/-- Below the first integer resonance, the quadratic sum is controlled by
its smallest derivative rather than by square-root curvature. -/
theorem norm_sum_quadratic_first_derivative_le {u : ℝ} (hu : u ≠ 0)
    {P Q : ℕ} (hP : 1 ≤ P) (hband : |u| * Q / Real.pi ≤ 1 / 2) :
    ‖∑ n ∈ Ico P Q, quadraticCharacter u n‖ ≤ 2 * Real.pi / (|u| * P) := by
  rcases lt_or_gt_of_ne hu with hu | hu
  · have he : (∑ n ∈ Ico P Q, quadraticCharacter u n) =
        (starRingEnd ℂ) (∑ n ∈ Ico P Q, quadraticCharacter (-u) n) := by
      rw [map_sum]
      apply sum_congr rfl
      intro n _
      rw [quadraticCharacter, quadraticCharacter, ← Complex.exp_conj]
      congr 1
      simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
      push_cast
      ring
    rw [he, Complex.norm_conj, abs_of_neg hu]
    rw [abs_of_neg hu] at hband
    exact norm_sum_quadratic_positive_first_derivative_le (neg_pos.mpr hu) hP hband
  · rw [abs_of_pos hu] at hband ⊢
    exact norm_sum_quadratic_positive_first_derivative_le hu hP hband

/-- Nonstationary cancellation preserves the real Gaussian endpoint factor. -/
theorem norm_sum_gaussian_quadratic_first_derivative_le {v u : ℝ}
    (hv : 0 ≤ v) (hu : u ≠ 0) {P Q : ℕ} (hP : 1 ≤ P)
    (hband : |u| * Q / Real.pi ≤ 1 / 2) :
    ‖∑ n ∈ Ico P Q, (Real.exp (-v * (n : ℝ) ^ 2) : ℂ) * quadraticCharacter u n‖ ≤
      (2 * Real.pi / (|u| * P)) * Real.exp (-v * (P : ℝ) ^ 2) := by
  by_cases hPQ : P ≤ Q
  · refine abel_block_bound _ (fun n => Real.exp (-v * (n : ℝ) ^ 2)) P Q hPQ
      (Real.exp_pos _).le ?_ (2 * Real.pi / (|u| * P)) ?_
    · intro m _ _
      apply Real.exp_le_exp.mpr
      apply mul_le_mul_of_nonpos_left _ (neg_nonpos.mpr hv)
      exact_mod_cast Nat.pow_le_pow_left (Nat.le_succ m) 2
    · intro m _ hmQ
      apply norm_sum_quadratic_first_derivative_le hu hP
      refine le_trans ?_ hband
      gcongr
  · rw [Ico_eq_empty_of_le (Nat.le_of_not_ge hPQ), sum_empty, norm_zero]
    positivity

/-- A Gaussian pair correlation has a reciprocal-gap bound below resonance. -/
theorem norm_gaussian_correlation_first_derivative_le {α ξ : ℝ} (hα : 0 ≤ α)
    (t : ℝ) {P Q m₁ m₂ : ℕ} (hP : 1 ≤ P) (hm₁ : 1 ≤ m₁) (hm₂ : 1 ≤ m₂)
    (hu : ξ * ((m₁ : ℝ) ^ 2 - (m₂ : ℝ) ^ 2) ≠ 0)
    (hband : |ξ * ((m₁ : ℝ) ^ 2 - (m₂ : ℝ) ^ 2)| * Q / Real.pi ≤ 1 / 2) :
    ‖∑ d ∈ Ico P Q, gaussianPrimePhase α ξ t (d * m₁) *
      (starRingEnd ℂ) (gaussianPrimePhase α ξ t (d * m₂))‖ ≤
      (2 * Real.pi / (|ξ * ((m₁ : ℝ) ^ 2 - (m₂ : ℝ) ^ 2)| * P)) *
        Real.exp (-(α * ((m₁ : ℝ) ^ 2 + (m₂ : ℝ) ^ 2)) * (P : ℝ) ^ 2) := by
  have he := sum_congr (s₁ := Ico P Q) rfl (fun d hd =>
    gaussianPrimePhase_correlation α ξ t (hP.trans (mem_Ico.mp hd).1) hm₁ hm₂)
  rw [he, ← mul_sum, norm_mul]
  have hn : ‖Complex.exp (((-t * (Real.log m₁ - Real.log m₂) : ℝ) : ℂ) * I)‖ = 1 := by
    simp only [Complex.norm_exp, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, Real.exp_zero]
  rw [hn, one_mul]
  exact norm_sum_gaussian_quadratic_first_derivative_le (by positivity) hu hP hband

/-- In a long nonstationary interval, the new bound is at most one sixth
of the previous curvature bound, with identical Gaussian damping. -/
theorem norm_sum_gaussian_quadratic_le_sixth_curvature_bound {v u : ℝ}
    (hv : 0 ≤ v) (hu : u ≠ 0) {P Q : ℕ} (hP : 1 ≤ P)
    (hband : |u| * Q / Real.pi ≤ 1 / 2)
    (hstart : 1 ≤ (P : ℝ) * Real.sqrt (|u| / Real.pi))
    (hlength : 12 ≤ ((Q - P : ℕ) : ℝ) * Real.sqrt (|u| / Real.pi)) :
    ‖∑ n ∈ Ico P Q, (Real.exp (-v * (n : ℝ) ^ 2) : ℂ) * quadraticCharacter u n‖ ≤
      (quadraticSumBound (Q - P) u / 6) * Real.exp (-v * (P : ℝ) ^ 2) := by
  have hlam : 0 < |u| / Real.pi := div_pos (abs_pos.mpr hu) Real.pi_pos
  have hs : 0 < Real.sqrt (|u| / Real.pi) := Real.sqrt_pos.mpr hlam
  have hP0 : (0 : ℝ) < P := by exact_mod_cast (show 0 < P by omega)
  have hden : Real.sqrt (|u| / Real.pi) ≤ (|u| / Real.pi) * P := by
    calc
      Real.sqrt (|u| / Real.pi) = 1 * Real.sqrt (|u| / Real.pi) := (one_mul _).symm
      _ ≤ ((P : ℝ) * Real.sqrt (|u| / Real.pi)) * Real.sqrt (|u| / Real.pi) :=
        mul_le_mul_of_nonneg_right hstart hs.le
      _ = (|u| / Real.pi) * P := by
        rw [mul_assoc, ← pow_two, Real.sq_sqrt hlam.le]
        ring
  have hfirst : 2 * Real.pi / (|u| * P) ≤ 2 / Real.sqrt (|u| / Real.pi) := by
    calc
      2 * Real.pi / (|u| * P) = 2 / ((|u| / Real.pi) * P) := by field_simp
      _ ≤ _ := div_le_div_of_nonneg_left (by norm_num) hs hden
  have hold : 12 / Real.sqrt (|u| / Real.pi) ≤ quadraticSumBound (Q - P) u := by
    rw [quadraticSumBound, if_neg hu]
    refine le_min ((div_le_iff₀ hs).mpr hlength) ?_
    have hpos : 0 ≤ 8 * ((Q - P : ℕ) : ℝ) * Real.sqrt (|u| / Real.pi) := by positivity
    linarith only [hpos]
  refine (norm_sum_gaussian_quadratic_first_derivative_le hv hu hP hband).trans ?_
  apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
  have he : 12 / Real.sqrt (|u| / Real.pi) = 6 * (2 / Real.sqrt (|u| / Real.pi)) := by ring
  rw [he] at hold
  linarith only [hfirst, hold]

#print axioms norm_sum_gaussian_quadratic_le_sixth_curvature_bound
#print axioms norm_sum_quadratic_first_derivative_le
#print axioms norm_sum_gaussian_quadratic_first_derivative_le
#print axioms norm_gaussian_correlation_first_derivative_le

end GaloisForLFunctions.ExceptionalLayerTheory
