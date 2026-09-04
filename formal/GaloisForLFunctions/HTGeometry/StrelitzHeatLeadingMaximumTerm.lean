import GaloisForLFunctions.HTGeometry.StrelitzCoefficientGrowthBound
import GaloisForLFunctions.HTGeometry.EntireHeatDifferentialOrderFloor
import GaloisForLFunctions.HTGeometry.CentralIndexDivergence

/-!
# Leading Strelitz coefficient versus the entire-heat maximum term

For an infinite entire-heat anchor satisfying an order-two ADE, this module combines the exact
logarithmic-jet relation, Wiman initial data, leading-value normalization, and polynomial numerator
bound.  It produces one fixed nonzero leading logarithmic-jet coefficient whose values along an
escaping sequence gain the full transcendental maximum term against a fixed radius power.
-/

open Filter Complex

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

variable {a : ℕ → ℂ}

/-- **Entire-heat leading-coefficient package.** An assumed order-two ADE produces one fixed
nonzero logarithmic-jet coefficient and exact Wiman roots satisfying
`|C_D(z,u,v)| μ(r) ≤ C_Q r^K` eventually.  All constants and exponents are explicit finite data
of the transformed relation. -/
theorem exists_strelitzLeadingMaximumTermBound_of_order_two_entireHeat
    (ha : EntireCoeffs a)
    (hheat : ∀ t z : ℂ, Summable (fun n : ℕ =>
      a n * Complex.exp (-(4 * (Real.pi : ℂ) ^ 2) * (n : ℂ) ^ 2 * t)
        * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * z)))
    (htrans : ∀ M : ℕ, ∃ n, M ≤ n ∧ a n ≠ 0)
    (hDA : DifferentiallyAlgebraicOfOrder (coeffFun a) 2) :
    ∃ (Q : MvPolynomial (Fin 3) (Polynomial ℂ)) (D : ℕ)
        (x : ℕ → ℝ) (z : ℕ → ℂ),
      Q ≠ 0 ∧ D ∈ strelitzValueSupport Q ∧
      strelitzValueCoeff Q D ≠ 0 ∧
      (∀ d ∈ strelitzValueSupport Q, d ≤ D) ∧
      (∀ n : ℕ, (n : ℝ) ≤ x n) ∧
      (∀ n : ℕ, ‖z n‖ = Real.exp (x n)) ∧
      (∀ n : ℕ, maxTerm a (Real.exp (x n)) ≤ ‖coeffFun a (z n)‖) ∧
      (∀ n : ℕ, coeffFun a (z n) ≠ 0) ∧
      (∀ n : ℕ, MvPolynomial.eval₂ (Polynomial.evalRingHom (z n))
        ![coeffFun a (z n), eulerLogDeriv (coeffFun a) (z n),
          eulerLogDerivSecond (coeffFun a) (z n)] Q = 0) ∧
      (∀ n : ℕ, ‖eulerLogDeriv (coeffFun a) (z n) -
          (centralIndex a (Real.exp (x n)) : ℂ)‖
        ≤ (1 / ((n : ℝ) + 1)) * (centralIndex a (Real.exp (x n)) : ℝ)) ∧
      (∀ n : ℕ, ‖eulerLogDerivSecond (coeffFun a) (z n)‖
        ≤ (1 / ((n : ℝ) + 1)) * (centralIndex a (Real.exp (x n)) : ℝ) ^ 2) ∧
      ∀ᶠ n : ℕ in atTop,
        ‖MvPolynomial.eval₂ (Polynomial.evalRingHom (z n))
          ![eulerLogDeriv (coeffFun a) (z n),
            eulerLogDerivSecond (coeffFun a) (z n)]
          (strelitzValueCoeff Q D)‖ * maxTerm a (Real.exp (x n)) ≤
        strelitzCoefficientGrowthConstant Q *
          (Real.exp (x n)) ^ strelitzCoefficientGrowthDegree Q := by
  obtain ⟨n₀, -, hn₀⟩ := htrans 0
  obtain ⟨m, hmpos, hm⟩ := htrans 1
  obtain ⟨Q, hQ, x, z, hx, hz, hfloor, hfz, hrel, hu, hv⟩ :=
    exists_strelitzLogJetInitialData_of_order_two ha htrans hDA
  obtain ⟨D, hD, hCD, hmax⟩ := exists_maximal_strelitzValueCoeff hQ
  have hxTop : Tendsto x atTop atTop := by
    refine tendsto_atTop_atTop.mpr fun R => ?_
    obtain ⟨N : ℕ, hNR⟩ := exists_nat_ge R
    refine ⟨N, fun n hn => ?_⟩
    exact le_trans hNR (le_trans (by exact_mod_cast hn) (hx n))
  have hrTop : Tendsto (fun n : ℕ => Real.exp (x n)) atTop atTop :=
    Real.tendsto_exp_atTop.comp hxTop
  have hratio := ((tendsto_entireHeat_centralIndex_div_log_zero ha hheat hn₀).comp hrTop)
    |>.eventually_lt_const one_pos
  have hmu := ((tendsto_maxTerm_atTop ha hm (lt_of_lt_of_le Nat.zero_lt_one hmpos)).comp hrTop)
    |>.eventually_ge_atTop 1
  have hbound : ∀ᶠ n : ℕ in atTop,
      ‖MvPolynomial.eval₂ (Polynomial.evalRingHom (z n))
        ![eulerLogDeriv (coeffFun a) (z n),
          eulerLogDerivSecond (coeffFun a) (z n)]
        (strelitzValueCoeff Q D)‖ * maxTerm a (Real.exp (x n)) ≤
      strelitzCoefficientGrowthConstant Q *
        (Real.exp (x n)) ^ strelitzCoefficientGrowthDegree Q := by
    filter_upwards [hratio, hmu, eventually_ge_atTop (1 : ℕ)] with n hnratio hnmu hn1
    set r : ℝ := Real.exp (x n) with hrdef
    set ν : ℝ := (centralIndex a r : ℝ) with hνdef
    set U : ℂ := eulerLogDeriv (coeffFun a) (z n) with hUdef
    set V : ℂ := eulerLogDerivSecond (coeffFun a) (z n) with hVdef
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
    have hxpos : 0 < x n := lt_of_lt_of_le hnpos (hx n)
    have hrone : (1 : ℝ) ≤ r := by rw [hrdef]; exact Real.one_le_exp hxpos.le
    have hlogr : Real.log r = x n := by rw [hrdef, Real.log_exp]
    have hνnonneg : 0 ≤ ν := by rw [hνdef]; positivity
    have hνr : ν ≤ r := by
      have hquot : ν / x n < 1 := by
        simpa [hrdef, hνdef, hlogr] using hnratio
      have hνx : ν < x n := (div_lt_one hxpos).mp hquot
      exact le_trans hνx.le
        (le_trans (by linarith : x n ≤ x n + 1) (Real.add_one_le_exp (x n)))
    have hfrac : (1 / ((n : ℝ) + 1)) ≤ 1 := by
      rw [div_le_one (by positivity)]
      exact le_add_of_nonneg_left (by positivity)
    have hUnorm : ‖U‖ ≤ 2 * r := by
      have htri : ‖U‖ ≤ ‖U - (centralIndex a r : ℂ)‖ +
          ‖(centralIndex a r : ℂ)‖ := by
        simpa using norm_add_le (U - (centralIndex a r : ℂ))
          (centralIndex a r : ℂ)
      have herr : ‖U - (centralIndex a r : ℂ)‖ ≤ ν := by
        calc
          ‖U - (centralIndex a r : ℂ)‖ ≤
              (1 / ((n : ℝ) + 1)) * ν := by
                simpa [U, r, ν] using hu n
          _ ≤ ν := mul_le_of_le_one_left hνnonneg hfrac
      have hcast : ‖(centralIndex a r : ℂ)‖ = ν := by
        rw [Complex.norm_natCast, hνdef]
      rw [hcast] at htri
      linarith
    have hVnorm : ‖V‖ ≤ r ^ 2 := by
      have hfirst : ‖V‖ ≤ (1 / ((n : ℝ) + 1)) * ν ^ 2 := by
        simpa [V, r, ν] using hv n
      have hsecond : (1 / ((n : ℝ) + 1)) * ν ^ 2 ≤ ν ^ 2 :=
        mul_le_of_le_one_left (sq_nonneg ν) hfrac
      exact le_trans (le_trans hfirst hsecond)
        (pow_le_pow_left₀ hνnonneg hνr 2)
    have hFnorm : 1 ≤ ‖coeffFun a (z n)‖ := le_trans hnmu (hfloor n)
    have hlead := norm_eval₂_maximal_strelitzValueCoeff_mul_norm_le_sum_erase
      Q hD hmax (z n) (coeffFun a (z n)) U V hFnorm (by simpa [U, V] using hrel n)
    have hlower := sum_norm_eval₂_strelitzValueCoeff_le Q
      ((strelitzValueSupport Q).erase D) (Finset.erase_subset D _)
      (z n) U V hrone (by simpa [r] using (hz n).le) hUnorm hVnorm
    calc
      ‖MvPolynomial.eval₂ (Polynomial.evalRingHom (z n)) ![U, V]
          (strelitzValueCoeff Q D)‖ * maxTerm a r ≤
          ‖MvPolynomial.eval₂ (Polynomial.evalRingHom (z n)) ![U, V]
            (strelitzValueCoeff Q D)‖ * ‖coeffFun a (z n)‖ :=
        mul_le_mul_of_nonneg_left (hfloor n) (norm_nonneg _)
      _ ≤ ∑ d ∈ (strelitzValueSupport Q).erase D,
          ‖MvPolynomial.eval₂ (Polynomial.evalRingHom (z n)) ![U, V]
            (strelitzValueCoeff Q d)‖ := hlead
      _ ≤ strelitzCoefficientGrowthConstant Q *
          r ^ strelitzCoefficientGrowthDegree Q := hlower
  exact ⟨Q, D, x, z, hQ, hD, hCD, hmax, hx, hz, hfloor, hfz, hrel, hu, hv, hbound⟩

end

end GaloisForLFunctions.HTGeometry
