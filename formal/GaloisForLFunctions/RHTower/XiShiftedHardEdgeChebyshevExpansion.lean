import GaloisForLFunctions.RHTower.XiShiftedHardEdgeMehlerHeine

/-!
# The Chebyshev expansion of a real polynomial

Every real polynomial of degree at most `M` is a real combination of the first `M + 1` Chebyshev
polynomials: subtracting the correct multiple of `T_M` lowers the degree, and the recursion
terminates.  Evaluating the expansion at `cos θ` turns the polynomial into a cosine polynomial, and
evaluating it at `cos z` for complex `z` gives the analytic continuation with the strip bound

`‖cos (j z)‖ ≤ e^{j·|Im z|}`.

This is the coefficient handle the rational hard-edge information cone needs: degree bounds the
frequency aperture, and the aperture bounds the growth of the analytic continuation off the axis.
-/

open Polynomial

noncomputable section

namespace RHTower

/-- The leading coefficient of the Chebyshev polynomial of positive degree. -/
theorem leadingCoeff_chebyshevT_succ (M : ℕ) :
    (Polynomial.Chebyshev.T ℝ ((M + 1 : ℕ) : ℤ)).leadingCoeff = 2 ^ M := by
  have hnat : (((M + 1 : ℕ) : ℤ)).natAbs = M + 1 := by omega
  rw [Polynomial.Chebyshev.leadingCoeff_T, hnat]
  norm_num

theorem natDegree_chebyshevT (n : ℕ) :
    (Polynomial.Chebyshev.T ℝ (n : ℤ)).natDegree = n := by
  rw [Polynomial.Chebyshev.natDegree_T]
  simp

/-- **The Chebyshev expansion.**  A real polynomial of degree at most `M` is a real combination of
the Chebyshev polynomials of degree at most `M`. -/
theorem exists_chebyshev_expansion :
    ∀ (M : ℕ) (r : Polynomial ℝ), r.natDegree ≤ M →
      ∃ b : ℕ → ℝ, r = ∑ j ∈ Finset.range (M + 1),
        Polynomial.C (b j) * Polynomial.Chebyshev.T ℝ (j : ℤ) := by
  intro M
  induction M with
  | zero =>
    intro r hr
    refine ⟨fun _ => r.coeff 0, ?_⟩
    have hconst : r = Polynomial.C (r.coeff 0) := Polynomial.eq_C_of_natDegree_le_zero hr
    rw [Finset.sum_range_one]
    have hT0 : Polynomial.Chebyshev.T ℝ ((0 : ℕ) : ℤ) = 1 := by
      simp
    rw [hT0, mul_one]
    exact hconst
  | succ M ih =>
    intro r hr
    by_cases hdeg : r.natDegree ≤ M
    · obtain ⟨b, hb⟩ := ih r hdeg
      refine ⟨Function.update b (M + 1) 0, ?_⟩
      rw [Finset.sum_range_succ, Function.update_self (M + 1) (0 : ℝ) b]
      rw [Polynomial.C_0, zero_mul, add_zero, hb]
      refine Finset.sum_congr rfl fun j hj => ?_
      simp only [Finset.mem_range] at hj
      rw [Function.update_of_ne (show j ≠ M + 1 by omega) (0 : ℝ) b]
    · have hM1 : r.natDegree = M + 1 := by omega
      have hr0 : r ≠ 0 := by
        intro h0
        rw [h0] at hM1
        simp at hM1
      have hlc : r.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.2 hr0
      obtain ⟨k, hkdef⟩ : ∃ k : ℝ, k = r.leadingCoeff / 2 ^ M := ⟨_, rfl⟩
      have hk0 : k ≠ 0 := by
        rw [hkdef]
        exact div_ne_zero hlc (by positivity)
      have hTdeg : (Polynomial.Chebyshev.T ℝ ((M + 1 : ℕ) : ℤ)).natDegree = M + 1 :=
        natDegree_chebyshevT (M + 1)
      have hprodDeg : (Polynomial.C k * Polynomial.Chebyshev.T ℝ ((M + 1 : ℕ) : ℤ)).natDegree
          = M + 1 := by
        rw [Polynomial.natDegree_C_mul hk0, hTdeg]
      have hprodLC : (Polynomial.C k
          * Polynomial.Chebyshev.T ℝ ((M + 1 : ℕ) : ℤ)).leadingCoeff = r.leadingCoeff := by
        rw [Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C,
          leadingCoeff_chebyshevT_succ, hkdef]
        field_simp
      have hprod0 : Polynomial.C k * Polynomial.Chebyshev.T ℝ ((M + 1 : ℕ) : ℤ) ≠ 0 := by
        intro h0
        rw [h0] at hprodDeg
        simp at hprodDeg
      have hdegEq : r.degree = (Polynomial.C k
          * Polynomial.Chebyshev.T ℝ ((M + 1 : ℕ) : ℤ)).degree := by
        rw [Polynomial.degree_eq_natDegree hr0, Polynomial.degree_eq_natDegree hprod0,
          hM1, hprodDeg]
      have hsub := Polynomial.degree_sub_lt hdegEq hr0 hprodLC.symm
      obtain ⟨s, hsdef⟩ : ∃ s : Polynomial ℝ,
          s = r - Polynomial.C k * Polynomial.Chebyshev.T ℝ ((M + 1 : ℕ) : ℤ) := ⟨_, rfl⟩
      have hsdeg : s.natDegree ≤ M := by
        rcases eq_or_ne s 0 with h0 | h0
        · rw [h0]
          simp
        · have hlt : s.degree < r.degree := by rw [hsdef]; exact hsub
          have := Polynomial.natDegree_lt_natDegree h0 hlt
          omega
      obtain ⟨b, hb⟩ := ih s hsdeg
      refine ⟨Function.update b (M + 1) k, ?_⟩
      rw [Finset.sum_range_succ, Function.update_self (M + 1) k b]
      have hmid : ∑ j ∈ Finset.range (M + 1),
          Polynomial.C (Function.update b (M + 1) k j)
            * Polynomial.Chebyshev.T ℝ (j : ℤ)
          = ∑ j ∈ Finset.range (M + 1),
            Polynomial.C (b j) * Polynomial.Chebyshev.T ℝ (j : ℤ) := by
        refine Finset.sum_congr rfl fun j hj => ?_
        simp only [Finset.mem_range] at hj
        rw [Function.update_of_ne (show j ≠ M + 1 by omega) k b]
      rw [hmid, ← hb, hsdef]
      ring

/-- The Chebyshev expansion evaluated at a real cosine is a cosine polynomial. -/
theorem eval_cos_of_chebyshev_expansion {r : Polynomial ℝ} {M : ℕ} {b : ℕ → ℝ}
    (hb : r = ∑ j ∈ Finset.range (M + 1),
      Polynomial.C (b j) * Polynomial.Chebyshev.T ℝ (j : ℤ)) (θ : ℝ) :
    r.eval (Real.cos θ) = ∑ j ∈ Finset.range (M + 1), b j * Real.cos ((j : ℝ) * θ) := by
  rw [hb, Polynomial.eval_finsetSum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.Chebyshev.T_real_cos]
  push_cast
  ring

/-- The Chebyshev expansion evaluated at a complex cosine. -/
theorem eval_ccos_of_chebyshev_expansion {r : Polynomial ℝ} {M : ℕ} {b : ℕ → ℝ}
    (hb : r = ∑ j ∈ Finset.range (M + 1),
      Polynomial.C (b j) * Polynomial.Chebyshev.T ℝ (j : ℤ)) (z : ℂ) :
    (r.map (algebraMap ℝ ℂ)).eval (Complex.cos z)
      = ∑ j ∈ Finset.range (M + 1), (b j : ℂ) * Complex.cos ((j : ℂ) * z) := by
  rw [hb]
  rw [Polynomial.map_sum, Polynomial.eval_finsetSum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.Chebyshev.map_T, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.Chebyshev.T_complex_cos]
  congr 2

/-- The complex cosine grows at most exponentially in the imaginary part. -/
theorem norm_ccos_le (z : ℂ) : ‖Complex.cos z‖ ≤ Real.exp |z.im| := by
  have h1 : ‖Complex.exp (z * Complex.I)‖ = Real.exp (-z.im) := by
    rw [Complex.norm_exp]
    congr 1
    simp [Complex.mul_re]
  have h2 : ‖Complex.exp (-z * Complex.I)‖ = Real.exp z.im := by
    rw [Complex.norm_exp]
    congr 1
    simp [Complex.mul_re]
  have hnum : ‖Complex.exp (z * Complex.I) + Complex.exp (-z * Complex.I)‖
      ≤ Real.exp (-z.im) + Real.exp z.im := by
    refine le_trans (norm_add_le _ _) ?_
    rw [h1, h2]
  have h2ne : ‖(2 : ℂ)‖ = 2 := by norm_num
  rw [Complex.cos, norm_div, h2ne]
  rcases le_total (0 : ℝ) z.im with h | h
  · rw [abs_of_nonneg h]
    have hle : Real.exp (-z.im) ≤ Real.exp z.im := Real.exp_le_exp.2 (by linarith)
    rw [div_le_iff₀ (by norm_num : (0:ℝ) < 2)]
    linarith
  · rw [abs_of_nonpos h]
    have hle : Real.exp z.im ≤ Real.exp (-z.im) := Real.exp_le_exp.2 (by linarith)
    rw [div_le_iff₀ (by norm_num : (0:ℝ) < 2)]
    linarith

end RHTower

end
