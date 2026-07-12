/-
# Exact Xi Weil positivity criterion

The multiplicity-exact Xi-divisor polarization is an unconditional Hermitian
form.  This file proves its missing converse positivity theorem.

For a nonreal centered divisor point `α`, the finitely supported sign test which
is `1` at `α`, `-1` at `conj α`, and zero elsewhere has strictly negative Weil
square.  Consequently the full square-summable Xi Weil form is nonnegative if
and only if RH holds.

This isolates the analytic burden in semilocal CCM constructions: their source
positivity must extend from the Cauchy/relative-resolvent core to this complete
divisor test space.  The theorem does not assert that extension.
-/
import GaloisForLFunctions.RHTower.XiDivisorSupportedMetric

open Complex

namespace RHTower

noncomputable section

/-- The finite sign test on a conjugate pair of centered divisor locations. -/
def xiOffRealSignTest (alpha z : ℂ) : ℂ :=
  if z = alpha then 1
  else if z = (starRingEnd ℂ) alpha then -1
  else 0

@[simp] theorem xiOffRealSignTest_self (alpha : ℂ) :
    xiOffRealSignTest alpha alpha = 1 := by
  simp [xiOffRealSignTest]

@[simp] theorem xiOffRealSignTest_star {alpha : ℂ}
    (h : (starRingEnd ℂ) alpha ≠ alpha) :
    xiOffRealSignTest alpha ((starRingEnd ℂ) alpha) = -1 := by
  simp [xiOffRealSignTest, h]

theorem xiOffRealSignTest_eq_zero {alpha z : ℂ}
    (hz1 : z ≠ alpha) (hz2 : z ≠ (starRingEnd ℂ) alpha) :
    xiOffRealSignTest alpha z = 0 := by
  simp [xiOffRealSignTest, hz1, hz2]

/-- The off-real sign test has finite divisor support, hence is square-summable. -/
theorem xiOffRealSignTest_squareSummable (alpha : ℂ) :
    XiWeilSquareSummable (xiOffRealSignTest alpha) := by
  let S : Finset XiZeroCopy :=
    (finite_xiSpectralPoint_fiber alpha).toFinset ∪
      (finite_xiSpectralPoint_fiber ((starRingEnd ℂ) alpha)).toFinset
  refine summable_of_ne_finset_zero (s := S) ?_
  intro q hq
  have hqa : xiSpectralPoint q ≠ alpha := by
    intro h
    apply hq
    apply Finset.mem_union_left
    simpa only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] using h
  have hqb : xiSpectralPoint q ≠ (starRingEnd ℂ) alpha := by
    intro h
    apply hq
    apply Finset.mem_union_right
    simpa only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] using h
  rw [xiOffRealSignTest_eq_zero hqa hqb]
  norm_num

/-- Pointwise sign law: each divisor copy over the conjugate pair contributes
`-1`, and every other copy contributes zero. -/
theorem xiOffRealSignTest_product
    (alpha z : ℂ) (h : (starRingEnd ℂ) alpha ≠ alpha) :
    xiOffRealSignTest alpha z * xiWeilSharp (xiOffRealSignTest alpha) z =
      if z = alpha ∨ z = (starRingEnd ℂ) alpha then -1 else 0 := by
  by_cases hza : z = alpha
  · subst z
    simp [xiWeilSharp, xiOffRealSignTest, h]
  · by_cases hzb : z = (starRingEnd ℂ) alpha
    · subst z
      simp [xiWeilSharp, xiOffRealSignTest, h]
    · have hca : (starRingEnd ℂ) z ≠ alpha := by
        intro hz
        apply hzb
        have := congrArg (starRingEnd ℂ) hz
        simpa using this
      have hcb : (starRingEnd ℂ) z ≠ (starRingEnd ℂ) alpha := by
        intro hz
        apply hza
        exact Complex.conjCLE.injective hz
      simp [xiWeilSharp, xiOffRealSignTest, hza, hzb, hca, hcb]

/-- Exact negative-square count of the off-real sign test. -/
theorem xiWeilPolarization_offRealSignTest
    (alpha : ℂ) (h : (starRingEnd ℂ) alpha ≠ alpha) :
    xiWeilPolarization (xiOffRealSignTest alpha) (xiOffRealSignTest alpha) =
      -(((finite_xiSpectralPoint_fiber alpha).toFinset ∪
        (finite_xiSpectralPoint_fiber ((starRingEnd ℂ) alpha)).toFinset).card : ℂ) := by
  rw [xiWeilPolarization]
  let S : Finset XiZeroCopy :=
    (finite_xiSpectralPoint_fiber alpha).toFinset ∪
      (finite_xiSpectralPoint_fiber ((starRingEnd ℂ) alpha)).toFinset
  rw [tsum_eq_sum (s := S)]
  · simp_rw [xiOffRealSignTest_product alpha _ h]
    have hmem : ∀ q ∈ S,
        xiSpectralPoint q = alpha ∨
          xiSpectralPoint q = (starRingEnd ℂ) alpha := by
      intro q hq
      rw [Finset.mem_union] at hq
      rcases hq with hq | hq
      · exact Or.inl (by
          simpa only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] using hq)
      · exact Or.inr (by
          simpa only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] using hq)
    calc
      ∑ q ∈ S, (if xiSpectralPoint q = alpha ∨
          xiSpectralPoint q = (starRingEnd ℂ) alpha
          then (-1 : ℂ) else 0) = ∑ _q ∈ S, (-1 : ℂ) := by
            apply Finset.sum_congr rfl
            intro q hq
            simp [hmem q hq]
      _ = -(S.card : ℂ) := by simp
      _ = -(((finite_xiSpectralPoint_fiber alpha).toFinset ∪
          (finite_xiSpectralPoint_fiber
            ((starRingEnd ℂ) alpha)).toFinset).card : ℂ) := by
        rfl
  · intro q hq
    have hqa : xiSpectralPoint q ≠ alpha := by
      intro heq
      apply hq
      apply Finset.mem_union_left
      simpa only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] using heq
    have hqb : xiSpectralPoint q ≠ (starRingEnd ℂ) alpha := by
      intro heq
      apply hq
      apply Finset.mem_union_right
      simpa only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] using heq
    rw [xiOffRealSignTest_product alpha _ h, if_neg (not_or_intro hqa hqb)]

/-- Every nonreal Xi-divisor copy produces a strict negative Weil square. -/
theorem xiWeilPolarization_offRealSignTest_re_neg
    (q : XiZeroCopy)
    (h : (starRingEnd ℂ) (xiSpectralPoint q) ≠ xiSpectralPoint q) :
    (xiWeilPolarization (xiOffRealSignTest (xiSpectralPoint q))
      (xiOffRealSignTest (xiSpectralPoint q))).re < 0 := by
  rw [xiWeilPolarization_offRealSignTest _ h]
  simp only [neg_re, Complex.natCast_re, neg_lt_zero]
  exact_mod_cast Finset.card_pos.mpr (by
    refine ⟨q, Finset.mem_union_left _ ?_⟩
    simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq])

/-- Positivity of the complete square-summable Xi Weil form forces every
centered divisor point to be real, hence forces RH. -/
theorem riemannHypothesis_of_xiWeilPolarization_nonneg
    (hpos : ∀ F : ℂ → ℂ, XiWeilSquareSummable F →
      0 ≤ (xiWeilPolarization F F).re) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_xiSpectralPoint_real
  intro q
  by_cases hreal : (starRingEnd ℂ) (xiSpectralPoint q) = xiSpectralPoint q
  · exact ⟨(xiSpectralPoint q).re,
      (Complex.conj_eq_iff_re.mp hreal).symm⟩
  · exact False.elim ((not_lt_of_ge
      (hpos (xiOffRealSignTest (xiSpectralPoint q))
        (xiOffRealSignTest_squareSummable (xiSpectralPoint q))))
      (xiWeilPolarization_offRealSignTest_re_neg q hreal))

/-- Exact global criterion: RH is equivalent to nonnegativity of the
multiplicity-exact Xi Weil polarization on its full square-summable domain. -/
theorem riemannHypothesis_iff_xiWeilPolarization_nonneg :
    RiemannHypothesis ↔
      ∀ F : ℂ → ℂ, XiWeilSquareSummable F →
        0 ≤ (xiWeilPolarization F F).re := by
  constructor
  · intro hRH F hF
    exact xiWeilPolarization_diagonal_nonneg_of_riemannHypothesis hRH F hF
  · exact riemannHypothesis_of_xiWeilPolarization_nonneg

end

end RHTower
