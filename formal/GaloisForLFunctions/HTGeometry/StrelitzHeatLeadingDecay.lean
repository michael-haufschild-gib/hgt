import GaloisForLFunctions.HTGeometry.StrelitzHeatLeadingMaximumTerm

/-!
# Superpolynomial smallness of the leading Strelitz coefficient

The maximum term of a transcendental entire series outgrows every radius power.  Combining this
with the entire-heat leading-coefficient bound makes one fixed nonzero logarithmic-jet polynomial
smaller than every inverse radius power along the selected Wiman sequence.  This is the exact local
input for the remaining Newton-branch analysis.
-/

open Filter

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {a : ℕ → ℂ}

/-- A nonnegative sequence whose product with a transcendental maximum term has fixed polynomial
growth decays faster than every inverse radius power. -/
theorem tendsto_mul_rpow_zero_of_mul_maxTerm_le
    (ha : EntireCoeffs a)
    (htrans : ∀ M : ℕ, ∃ n, M ≤ n ∧ a n ≠ 0)
    {r A : ℕ → ℝ} (hrTop : Tendsto r atTop atTop)
    (hA : ∀ n, 0 ≤ A n) {C : ℝ} {K : ℕ}
    (hbound : ∀ᶠ n : ℕ in atTop, A n * maxTerm a (r n) ≤ C * (r n) ^ K)
    (j : ℕ) :
    Tendsto (fun n => A n * (r n) ^ j) atTop (nhds 0) := by
  obtain ⟨n₀, -, hn₀⟩ := htrans 0
  have hden : Tendsto (fun n : ℕ => maxTerm a (r n) / (r n) ^ (K + j))
      atTop atTop := (tendsto_maxTerm_div_pow_atTop ha htrans (K + j)).comp hrTop
  have hmaj : Tendsto
      (fun n : ℕ => C * (maxTerm a (r n) / (r n) ^ (K + j))⁻¹)
      atTop (nhds 0) := by
    simpa using (tendsto_inv_atTop_zero.comp hden).const_mul C
  refine squeeze_zero' ?_ ?_ hmaj
  · filter_upwards [hrTop.eventually (eventually_gt_atTop (0 : ℝ))] with n hr
    exact mul_nonneg (hA n) (pow_nonneg hr.le _)
  · filter_upwards [hbound, hrTop.eventually (eventually_gt_atTop (0 : ℝ))]
      with n hn hr
    have hmu : 0 < maxTerm a (r n) := maxTerm_pos ha hr hn₀
    have hAle : A n ≤ C * (r n) ^ K / maxTerm a (r n) := by
      rw [le_div_iff₀ hmu]
      exact hn
    have hmul := mul_le_mul_of_nonneg_right hAle (pow_nonneg hr.le j)
    calc
      A n * (r n) ^ j ≤ (C * (r n) ^ K / maxTerm a (r n)) * (r n) ^ j := hmul
      _ = C * (maxTerm a (r n) / (r n) ^ (K + j))⁻¹ := by
        field_simp
        rw [pow_add]
        ring

open GaloisForLFunctions

/-- **Order-two entire-heat Newton input.** An assumed order-two ADE produces a fixed nonzero
polynomial in the two logarithmic-jet variables whose evaluated norm, multiplied by any fixed
radius power, tends to zero along escaping Wiman points. -/
theorem exists_nonzero_strelitzLogJetPolynomial_superpolynomiallySmall_of_order_two_entireHeat
    (ha : EntireCoeffs a)
    (hheat : ∀ t z : ℂ, Summable (fun n : ℕ =>
      a n * Complex.exp (-(4 * (Real.pi : ℂ) ^ 2) * (n : ℂ) ^ 2 * t)
        * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * z)))
    (htrans : ∀ M : ℕ, ∃ n, M ≤ n ∧ a n ≠ 0)
    (hDA : DifferentiallyAlgebraicOfOrder (coeffFun a) 2) :
    ∃ P : MvPolynomial (Fin 2) (Polynomial ℂ), P ≠ 0 ∧
      ∃ (x : ℕ → ℝ) (z : ℕ → ℂ),
        (∀ n : ℕ, (n : ℝ) ≤ x n) ∧
        (∀ n : ℕ, ‖z n‖ = Real.exp (x n)) ∧
        (∀ n : ℕ, maxTerm a (Real.exp (x n)) ≤ ‖coeffFun a (z n)‖) ∧
        (∀ n : ℕ, coeffFun a (z n) ≠ 0) ∧
        (∀ n : ℕ, ‖eulerLogDeriv (coeffFun a) (z n) -
            (centralIndex a (Real.exp (x n)) : ℂ)‖
          ≤ (1 / ((n : ℝ) + 1)) * (centralIndex a (Real.exp (x n)) : ℝ)) ∧
        (∀ n : ℕ, ‖eulerLogDerivSecond (coeffFun a) (z n)‖
          ≤ (1 / ((n : ℝ) + 1)) * (centralIndex a (Real.exp (x n)) : ℝ) ^ 2) ∧
        ∀ j : ℕ, Tendsto (fun n : ℕ =>
          ‖MvPolynomial.eval₂ (Polynomial.evalRingHom (z n))
            ![eulerLogDeriv (coeffFun a) (z n),
              eulerLogDerivSecond (coeffFun a) (z n)] P‖ *
            (Real.exp (x n)) ^ j) atTop (nhds 0) := by
  obtain ⟨Q, D, x, z, hQ, hD, hP, hmax, hx, hz, hfloor, hfz, hrel, hu, hv, hbound⟩ :=
    exists_strelitzLeadingMaximumTermBound_of_order_two_entireHeat ha hheat htrans hDA
  refine ⟨strelitzValueCoeff Q D, hP, x, z, hx, hz, hfloor, hfz, hu, hv, ?_⟩
  have hxTop : Tendsto x atTop atTop := by
    refine tendsto_atTop_atTop.mpr fun R => ?_
    obtain ⟨N : ℕ, hNR⟩ := exists_nat_ge R
    refine ⟨N, fun n hn => ?_⟩
    exact le_trans hNR (le_trans (by exact_mod_cast hn) (hx n))
  have hrTop : Tendsto (fun n : ℕ => Real.exp (x n)) atTop atTop :=
    Real.tendsto_exp_atTop.comp hxTop
  intro j
  exact tendsto_mul_rpow_zero_of_mul_maxTerm_le ha htrans hrTop
    (fun n => norm_nonneg _) hbound j

end

end GaloisForLFunctions.HTGeometry
