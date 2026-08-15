import GaloisForLFunctions.RHTower.XiShiftedHardEdgeTrivialFourier
import GaloisForLFunctions.RHTower.XiWeilResolventChartDictionary

/-!
# The completed source of the rational hard-edge test

The square of the rational hard-edge test at the constant polynomial is exactly the mass-scaled
Cauchy resolvent kernel, so its Xi divisor form is the corpus's Weil diagonal of the
imaginary-parameter Cauchy test.  Beyond the pole that diagonal has the completed arithmetic
evaluation

`Σ_q g_{a,1}(α_q)² = a·[ (1/2+a)^{-1} + (a-1/2)^{-1} + (Γ_ℝ'/Γ_ℝ)(1/2+a) − Σ_n Λ(n) n^{-1/2-a} ]`,

which is the base case of the completed source formula: a nonnegative polar part, an archimedean
part, and the von Mangoldt series.  The prime term is the value at `n^{-a} = e^{-a log n}` of the
same exponential decay the information cone controls.
-/

open Complex

noncomputable section

namespace RHTower

/-- At the constant polynomial the squared rational hard-edge test is the mass-scaled resolvent
coordinate. -/
theorem routeUHardEdgeRationalTestSq_one_eq (a : ℝ) (q : XiZeroCopy) :
    routeUHardEdgeRationalTestSq a 1 (xiSpectralPoint q)
      = ((a ^ 2 : ℝ) : ℂ) * xiResolventPoint (a ^ 2) q := by
  rw [routeUHardEdgeRationalTestSq, xiResolventPoint, evalRealPolynomial_one, one_pow, mul_one,
    add_comm]

/-- The divisor form of the constant-polynomial test is the zeroth resolvent moment. -/
theorem tsum_routeUHardEdgeRationalTestSq_one (a : ℝ) :
    (∑' q : XiZeroCopy, routeUHardEdgeRationalTestSq a 1 (xiSpectralPoint q))
      = ((a ^ 2 : ℝ) : ℂ) * xiResolventMoment 0 (a ^ 2) := by
  rw [xiResolventMoment, ← tsum_mul_left]
  refine tsum_congr fun q => ?_
  rw [routeUHardEdgeRationalTestSq_one_eq, pow_one]

/-- **(CSHC.6) at the constant polynomial.**  The completed source formula of the rational
hard-edge test: polar terms, the archimedean logarithmic derivative, and the von Mangoldt series. -/
theorem tsum_routeUHardEdgeRationalTestSq_one_eq_arithmetic {a : ℝ} (ha : 1 / 2 < a) :
    (∑' q : XiZeroCopy, routeUHardEdgeRationalTestSq a 1 (xiSpectralPoint q))
      = (a : ℂ) * (((1 / 2 : ℂ) + (a : ℂ))⁻¹ + ((1 / 2 : ℂ) + (a : ℂ) - 1)⁻¹
          + logDeriv Complex.Gammaℝ ((1 / 2 : ℂ) + (a : ℂ))
          - LSeries (fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ))
              ((1 / 2 : ℂ) + (a : ℂ))) := by
  have hapos : (0 : ℝ) < a := by linarith
  have hane : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (ne_of_gt hapos)
  rw [tsum_routeUHardEdgeRationalTestSq_one,
    ← xiWeilPolarization_cauchyTest_eq_resolventMoment,
    xiWeilPolarization_cauchyTest_eq_arithmetic ha]
  have hsq : ((a ^ 2 : ℝ) : ℂ) = (a : ℂ) * (a : ℂ) := by
    push_cast
    ring
  rw [hsq]
  field_simp


/-! ## The finite reduction of the general completed source -/

/-- The Weil polynomial of the rational hard-edge test: `R(t) = t·p(t)²`. -/
def routeUHardEdgeWeilPoly (p : Polynomial ℝ) : Polynomial ℝ := Polynomial.X * p ^ 2

theorem routeUHardEdgeWeilPoly_coeff_zero (p : Polynomial ℝ) :
    (routeUHardEdgeWeilPoly p).coeff 0 = 0 := by
  rw [routeUHardEdgeWeilPoly, Polynomial.coeff_X_mul_zero]

theorem evalRealPolynomial_routeUHardEdgeWeilPoly (p : Polynomial ℝ) (z : ℂ) :
    evalRealPolynomial (routeUHardEdgeWeilPoly p) z = z * evalRealPolynomial p z ^ 2 := by
  rw [routeUHardEdgeWeilPoly, evalRealPolynomial_mul, evalRealPolynomial_pow]
  congr 1
  simp [evalRealPolynomial]

/-- The squared rational hard-edge test on the divisor is the Weil polynomial of the resolvent
coordinate. -/
theorem routeUHardEdgeRationalTestSq_eq_weilPoly (a : ℝ) (p : Polynomial ℝ) (q : XiZeroCopy) :
    routeUHardEdgeRationalTestSq a p (xiSpectralPoint q)
      = ((a ^ 2 : ℝ) : ℂ)
        * evalRealPolynomial (routeUHardEdgeWeilPoly p) (xiResolventPoint (a ^ 2) q) := by
  rw [routeUHardEdgeRationalTestSq, evalRealPolynomial_routeUHardEdgeWeilPoly, xiResolventPoint,
    add_comm]
  ring

theorem natDegree_map_routeUHardEdgeWeilPoly (p : Polynomial ℝ) :
    ((routeUHardEdgeWeilPoly p).map (algebraMap ℝ ℂ)).natDegree
      = (routeUHardEdgeWeilPoly p).natDegree :=
  Polynomial.natDegree_map_eq_of_injective (algebraMap ℝ ℂ).injective _

/-- **(CSHC.6) finite reduction.**  The completed divisor form of the rational hard-edge test is a
finite combination of resolvent moments, with no coefficient at the divergent zeroth power. -/
theorem tsum_routeUHardEdgeRationalTestSq_eq_moments (a : ℝ) (p : Polynomial ℝ) :
    (∑' q : XiZeroCopy, routeUHardEdgeRationalTestSq a p (xiSpectralPoint q))
      = ((a ^ 2 : ℝ) : ℂ)
        * ∑ k ∈ Finset.Icc 1 (routeUHardEdgeWeilPoly p).natDegree,
            (((routeUHardEdgeWeilPoly p).coeff k : ℝ) : ℂ) * xiResolventMoment (k - 1) (a ^ 2) := by
  have hX : (0 : ℝ) ≤ a ^ 2 := sq_nonneg a
  obtain ⟨d, hd⟩ : ∃ d : ℕ, d = (routeUHardEdgeWeilPoly p).natDegree := ⟨_, rfl⟩
  have hexpand : ∀ q : XiZeroCopy,
      evalRealPolynomial (routeUHardEdgeWeilPoly p) (xiResolventPoint (a ^ 2) q)
        = ∑ k ∈ Finset.range (d + 1),
            (((routeUHardEdgeWeilPoly p).coeff k : ℝ) : ℂ) * xiResolventPoint (a ^ 2) q ^ k := by
    intro q
    rw [evalRealPolynomial, Polynomial.eval_eq_sum_range' (n := d + 1)]
    · refine Finset.sum_congr rfl fun k _ => ?_
      rw [Polynomial.coeff_map]
      rfl
    · rw [natDegree_map_routeUHardEdgeWeilPoly, ← hd]
      omega
  have hsumm : ∀ k ∈ Finset.range (d + 1),
      Summable fun q : XiZeroCopy =>
        (((routeUHardEdgeWeilPoly p).coeff k : ℝ) : ℂ) * xiResolventPoint (a ^ 2) q ^ k := by
    intro k _
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · have hzero : (((routeUHardEdgeWeilPoly p).coeff 0 : ℝ) : ℂ) = 0 := by
        rw [routeUHardEdgeWeilPoly_coeff_zero]
        norm_num
      simp [hzero]
    · obtain ⟨j, rfl⟩ : ∃ j : ℕ, k = j + 1 := ⟨k - 1, by omega⟩
      exact (summable_xiResolventPoint_pow hX j).mul_left _
  rw [tsum_congr (fun q => routeUHardEdgeRationalTestSq_eq_weilPoly a p q), tsum_mul_left]
  congr 1
  rw [tsum_congr hexpand, Summable.tsum_finsetSum hsumm]
  have hrange : ∑ k ∈ Finset.range (d + 1),
      (∑' q : XiZeroCopy,
        (((routeUHardEdgeWeilPoly p).coeff k : ℝ) : ℂ) * xiResolventPoint (a ^ 2) q ^ k)
      = ∑ k ∈ Finset.Icc 1 d,
        (∑' q : XiZeroCopy,
          (((routeUHardEdgeWeilPoly p).coeff k : ℝ) : ℂ) * xiResolventPoint (a ^ 2) q ^ k) := by
    rw [Finset.range_eq_Ico, show Finset.Ico 0 (d + 1) = insert 0 (Finset.Icc 1 d) by
      ext k
      simp only [Finset.mem_Ico, Finset.mem_insert, Finset.mem_Icc]
      omega]
    rw [Finset.sum_insert (by simp)]
    have hzero : (((routeUHardEdgeWeilPoly p).coeff 0 : ℝ) : ℂ) = 0 := by
      rw [routeUHardEdgeWeilPoly_coeff_zero]
      norm_num
    simp [hzero]
  rw [hrange, ← hd]
  refine Finset.sum_congr rfl fun k hk => ?_
  simp only [Finset.mem_Icc] at hk
  rw [tsum_mul_left, xiResolventMoment, show k - 1 + 1 = k by omega]

end RHTower

end
