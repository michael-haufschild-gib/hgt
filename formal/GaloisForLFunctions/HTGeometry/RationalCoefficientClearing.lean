import GaloisForLFunctions.HTGeometry.PrimeLogPolynomialJetEscape
import Mathlib.FieldTheory.RatFunc.AsPolynomial

/-!
# Rational-coefficient differential relations: exact denominator clearing and escape

Finite multivariate relations over `K(X)` admit a canonical common denominator.  The cleared
polynomial is nonzero whenever the original relation is nonzero, and its image in `K(X)` is exactly
the common denominator times the original relation.

For complex rational coefficients, an upper-half-plane detector can be chosen simultaneously away
from the common denominator divisor.  The resulting honest complex polynomial is then broken by an
arbitrarily small finitely supported perturbation of every bounded prime-log gauge.
-/

open Polynomial

namespace GaloisForLFunctions.HTGeometry

/-- The product of the reduced denominators of all nonzero coefficients of a finite multivariate
polynomial over `K(X)`. -/
noncomputable def ratFuncCommonDenominator {σ K : Type*} [Field K]
    (Q : MvPolynomial σ (RatFunc K)) : K[X] :=
  ∏ d ∈ Q.support, (MvPolynomial.coeff d Q).denom

/-- Canonical simultaneous denominator clearing: the coefficient at a supported monomial `d` is
the numerator at `d` times all the other reduced denominators. -/
noncomputable def clearRatFuncCoefficients {σ K : Type*} [DecidableEq σ] [Field K]
    (Q : MvPolynomial σ (RatFunc K)) : MvPolynomial σ K[X] :=
  ∑ d ∈ Q.support, MvPolynomial.monomial d
    ((MvPolynomial.coeff d Q).num *
      ∏ e ∈ Q.support.erase d, (MvPolynomial.coeff e Q).denom)

theorem coeff_clearRatFuncCoefficients_of_mem
    {σ K : Type*} [DecidableEq σ] [Field K]
    (Q : MvPolynomial σ (RatFunc K)) {d : σ →₀ ℕ} (hd : d ∈ Q.support) :
    MvPolynomial.coeff d (clearRatFuncCoefficients Q) =
      (MvPolynomial.coeff d Q).num *
        ∏ e ∈ Q.support.erase d, (MvPolynomial.coeff e Q).denom := by
  classical
  simp only [clearRatFuncCoefficients, MvPolynomial.coeff_sum,
    MvPolynomial.coeff_monomial]
  rw [Finset.sum_eq_single d]
  · simp
  · intro e he hne
    simp [hne]
  · intro hnot
    exact (hnot hd).elim

theorem coeff_clearRatFuncCoefficients_of_not_mem
    {σ K : Type*} [DecidableEq σ] [Field K]
    (Q : MvPolynomial σ (RatFunc K)) {d : σ →₀ ℕ} (hd : d ∉ Q.support) :
    MvPolynomial.coeff d (clearRatFuncCoefficients Q) = 0 := by
  classical
  simp only [clearRatFuncCoefficients, MvPolynomial.coeff_sum,
    MvPolynomial.coeff_monomial]
  rw [Finset.sum_eq_zero]
  intro e he
  rw [if_neg]
  intro hed
  exact hd (hed ▸ he)

/-- The canonical cleared polynomial preserves nonzeroness. -/
theorem clearRatFuncCoefficients_ne_zero
    {σ K : Type*} [DecidableEq σ] [Field K]
    (Q : MvPolynomial σ (RatFunc K)) (hQ : Q ≠ 0) :
    clearRatFuncCoefficients Q ≠ 0 := by
  classical
  obtain ⟨d, hd⟩ := MvPolynomial.support_nonempty.mpr hQ
  have hcoeff : MvPolynomial.coeff d Q ≠ 0 := MvPolynomial.mem_support_iff.mp hd
  have hprod : (∏ e ∈ Q.support.erase d, (MvPolynomial.coeff e Q).denom) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro e he
    exact RatFunc.denom_ne_zero _
  have hcleared : MvPolynomial.coeff d (clearRatFuncCoefficients Q) ≠ 0 := by
    rw [coeff_clearRatFuncCoefficients_of_mem Q hd]
    exact mul_ne_zero (RatFunc.num_ne_zero hcoeff) hprod
  intro hzero
  rw [hzero, MvPolynomial.coeff_zero] at hcleared
  exact hcleared rfl

/-- The common denominator never vanishes as a polynomial. -/
theorem ratFuncCommonDenominator_ne_zero
    {σ K : Type*} [Field K] (Q : MvPolynomial σ (RatFunc K)) :
    ratFuncCommonDenominator Q ≠ 0 := by
  classical
  rw [ratFuncCommonDenominator, Finset.prod_ne_zero_iff]
  intro d hd
  exact RatFunc.denom_ne_zero _

/-- **Exact simultaneous clearing law.** Mapping the canonical cleared polynomial into `K(X)` is
exactly multiplication of the original relation by its common denominator. -/
theorem map_clearRatFuncCoefficients
    {σ K : Type*} [DecidableEq σ] [Field K]
    (Q : MvPolynomial σ (RatFunc K)) :
    MvPolynomial.map (algebraMap K[X] (RatFunc K)) (clearRatFuncCoefficients Q) =
      MvPolynomial.C
          (algebraMap K[X] (RatFunc K) (ratFuncCommonDenominator Q)) * Q := by
  classical
  apply MvPolynomial.ext
  intro d
  rw [MvPolynomial.coeff_map, MvPolynomial.coeff_C_mul]
  by_cases hd : d ∈ Q.support
  · rw [coeff_clearRatFuncCoefficients_of_mem Q hd]
    have hfrac := RatFunc.num_div_denom (MvPolynomial.coeff d Q)
    rw [div_eq_iff (RatFunc.algebraMap_ne_zero (RatFunc.denom_ne_zero _))] at hfrac
    rw [map_mul, hfrac, ratFuncCommonDenominator,
      ← Finset.mul_prod_erase Q.support
        (fun e => (MvPolynomial.coeff e Q).denom) hd, map_mul]
    ring
  · have hcoeff : MvPolynomial.coeff d Q = 0 := by
      exact not_ne_iff.mp (mt MvPolynomial.mem_support_iff.mpr hd)
    rw [hcoeff, mul_zero, coeff_clearRatFuncCoefficients_of_not_mem Q hd, map_zero]

/-- A nonzero polynomial-coefficient relation and a nonzero polynomial divisor have a common
upper-half-plane point where the relation survives specialization and the divisor does not vanish. -/
theorem exists_upper_specialization_avoiding_polynomial
    {σ : Type*} (Q : MvPolynomial σ ℂ[X]) (hQ : Q ≠ 0)
    (D : ℂ[X]) (hD : D ≠ 0) (H : ℝ) :
    ∃ z : ℂ, H < z.im ∧ specializePolynomialCoefficients z Q ≠ 0 ∧ D.eval z ≠ 0 := by
  obtain ⟨d, hd⟩ := MvPolynomial.support_nonempty.mpr hQ
  have hcoeff : MvPolynomial.coeff d Q ≠ 0 := MvPolynomial.mem_support_iff.mp hd
  let q := MvPolynomial.coeff d Q
  have hqD : q * D ≠ 0 := mul_ne_zero hcoeff hD
  let vertical : ℝ → ℂ := fun y => (y : ℂ) * Complex.I
  have hvert : Function.Injective vertical := by
    intro y₁ y₂ h
    have him := congrArg Complex.im h
    simpa [vertical] using him
  have hS : (vertical '' Set.Ioi H).Infinite :=
    (Set.Ioi_infinite H).image hvert.injOn
  have hnot : ¬ vertical '' Set.Ioi H ⊆ {z | (q * D).IsRoot z} := by
    intro hsub
    exact (Polynomial.finite_setOf_isRoot hqD).not_infinite (hS.mono hsub)
  obtain ⟨z, ⟨y, hy, rfl⟩, hz⟩ := Set.not_subset.mp hnot
  refine ⟨vertical y, ?_, ?_, ?_⟩
  · simpa [vertical] using hy
  · intro hzero
    have hc := congrArg (MvPolynomial.coeff d) hzero
    rw [specializePolynomialCoefficients, MvPolynomial.coeff_map] at hc
    have hprodEval : (q * D).eval (vertical y) ≠ 0 := by
      simpa [Polynomial.IsRoot] using hz
    apply hprodEval
    rw [Polynomial.eval_mul]
    have hc0 : q.eval (vertical y) = 0 := by
      simpa [q] using hc
    exact mul_eq_zero.mpr (Or.inl hc0)
  · intro hDeval
    have hprodEval : (q * D).eval (vertical y) ≠ 0 := by
      simpa [Polynomial.IsRoot] using hz
    apply hprodEval
    rw [Polynomial.eval_mul, hDeval, mul_zero]

/-- Finite coefficientwise specialization of a rational-function coefficient polynomial at a
point.  This deliberately does not pretend that rational-function evaluation at a pole is a global
ring homomorphism. -/
noncomputable def specializeRatFuncCoefficients
    {σ : Type*} (z : ℂ)
    (Q : MvPolynomial σ (RatFunc ℂ)) : MvPolynomial σ ℂ := by
  classical
  exact ∑ d ∈ Q.support, MvPolynomial.monomial d
    (RatFunc.eval (RingHom.id ℂ) z (MvPolynomial.coeff d Q))

theorem coeff_specializeRatFuncCoefficients_of_mem
    {σ : Type*} (z : ℂ)
    (Q : MvPolynomial σ (RatFunc ℂ)) {d : σ →₀ ℕ} (hd : d ∈ Q.support) :
    MvPolynomial.coeff d (specializeRatFuncCoefficients z Q) =
      RatFunc.eval (RingHom.id ℂ) z (MvPolynomial.coeff d Q) := by
  classical
  simp only [specializeRatFuncCoefficients, MvPolynomial.coeff_sum,
    MvPolynomial.coeff_monomial]
  rw [Finset.sum_eq_single d]
  · simp
  · intro e he hne
    simp [hne]
  · intro hnot
    exact (hnot hd).elim

theorem coeff_specializeRatFuncCoefficients_of_not_mem
    {σ : Type*} (z : ℂ)
    (Q : MvPolynomial σ (RatFunc ℂ)) {d : σ →₀ ℕ} (hd : d ∉ Q.support) :
    MvPolynomial.coeff d (specializeRatFuncCoefficients z Q) = 0 := by
  classical
  simp only [specializeRatFuncCoefficients, MvPolynomial.coeff_sum,
    MvPolynomial.coeff_monomial]
  rw [Finset.sum_eq_zero]
  intro e he
  rw [if_neg]
  intro hed
  exact hd (hed ▸ he)

theorem eval_ratFuncCommonDenominator_ne_zero_imp_denom_ne_zero
    {σ : Type*} (z : ℂ) (Q : MvPolynomial σ (RatFunc ℂ))
    (hD : (ratFuncCommonDenominator Q).eval z ≠ 0)
    {d : σ →₀ ℕ} (hd : d ∈ Q.support) :
    (MvPolynomial.coeff d Q).denom.eval z ≠ 0 := by
  classical
  have hprod :
      (∏ e ∈ Q.support, (MvPolynomial.coeff e Q).denom.eval z) ≠ 0 := by
    rw [ratFuncCommonDenominator, Polynomial.eval_prod] at hD
    exact hD
  rw [Finset.prod_ne_zero_iff] at hprod
  exact hprod d hd

/-- Away from the common denominator divisor, coefficientwise rational specialization obeys the
same exact clearing identity as the abstract `K(X)` relation. -/
theorem specializeRatFuncCoefficients_clearing
    {σ : Type*} [DecidableEq σ] (z : ℂ)
    (Q : MvPolynomial σ (RatFunc ℂ))
    (hD : (ratFuncCommonDenominator Q).eval z ≠ 0) :
    MvPolynomial.C ((ratFuncCommonDenominator Q).eval z) *
        specializeRatFuncCoefficients z Q =
      specializePolynomialCoefficients z (clearRatFuncCoefficients Q) := by
  classical
  apply MvPolynomial.ext
  intro d
  rw [MvPolynomial.coeff_C_mul]
  by_cases hd : d ∈ Q.support
  · rw [coeff_specializeRatFuncCoefficients_of_mem z Q hd,
      specializePolynomialCoefficients, MvPolynomial.coeff_map,
      coeff_clearRatFuncCoefficients_of_mem Q hd]
    have hden :=
      eval_ratFuncCommonDenominator_ne_zero_imp_denom_ne_zero z Q hD hd
    have hDsplit : ratFuncCommonDenominator Q =
        (MvPolynomial.coeff d Q).denom *
          ∏ e ∈ Q.support.erase d, (MvPolynomial.coeff e Q).denom := by
      rw [ratFuncCommonDenominator, Finset.mul_prod_erase Q.support
        (fun e => (MvPolynomial.coeff e Q).denom) hd]
    rw [hDsplit, Polynomial.eval_mul, RatFunc.eval, map_mul]
    simp only [Polynomial.eval₂_id]
    field_simp [hden]
    change
      (∏ e ∈ Q.support.erase d, (MvPolynomial.coeff e Q).denom).eval z *
          (MvPolynomial.coeff d Q).num.eval z =
        (MvPolynomial.coeff d Q).num.eval z *
          (∏ e ∈ Q.support.erase d, (MvPolynomial.coeff e Q).denom).eval z
    ring_nf
  · have hcoeff : MvPolynomial.coeff d Q = 0 := by
      exact not_ne_iff.mp (mt MvPolynomial.mem_support_iff.mpr hd)
    rw [coeff_specializeRatFuncCoefficients_of_not_mem z Q hd, mul_zero,
      specializePolynomialCoefficients, MvPolynomial.coeff_map,
      coeff_clearRatFuncCoefficients_of_not_mem Q hd, map_zero]

theorem specializeRatFuncCoefficients_ne_zero
    {σ : Type*} [DecidableEq σ] (z : ℂ)
    (Q : MvPolynomial σ (RatFunc ℂ))
    (hD : (ratFuncCommonDenominator Q).eval z ≠ 0)
    (hclear : specializePolynomialCoefficients z (clearRatFuncCoefficients Q) ≠ 0) :
    specializeRatFuncCoefficients z Q ≠ 0 := by
  intro hzero
  have h := specializeRatFuncCoefficients_clearing z Q hD
  rw [hzero, mul_zero] at h
  exact hclear h.symm

/-- **Rational differential-relation escape.** Every nonzero finite relation with coefficients in
`ℂ(X)` has an upper-half-plane point away from all coefficient poles, and its honest specialization
is broken inside every bounded prime-log gauge neighborhood. -/
theorem primeDyadic_actualRationalDifferentialRelation_has_gaugeBall_escape
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (shift : ι → ℂ) (hshift : Function.Injective shift) (orders : ι → ℕ)
    (u : Nat.Primes → ℝ) (C : ℝ) (hu : ∀ p, |u p| ≤ C)
    (Q : MvPolynomial (Σ i, Fin (orders i)) (RatFunc ℂ)) (hQ : Q ≠ 0)
    {ηTime ηGauge : ℝ} (hηTime : 0 < ηTime) (hηGauge : 0 < ηGauge) :
    ∃ z : ℂ, ∃ a : Nat.Primes →₀ ℝ, ∃ ε C' : ℝ,
      0 < ε ∧ ε < ηTime ∧
      (ratFuncCommonDenominator Q).eval z ≠ 0 ∧
      Function.Injective (fun i => z + shift i) ∧
      (∀ i, 0 < (z + shift i).im) ∧
      (∀ p, 0 < primeLogPerturbedMass u a ε p) ∧
      (∀ p, |primeLogPerturbedGauge u a ε p - u p| < ηGauge) ∧
      (∀ p, |primeLogPerturbedGauge u a ε p| ≤ C') ∧
      Set.Finite {p | primeLogPerturbedGauge u a ε p ≠ u p} ∧
      MvPolynomial.eval
        (primeLogDifferentialJetPacket (primeLogPerturbedGauge u a ε)
          (fun i => z + shift i) orders)
        (specializeRatFuncCoefficients z Q) ≠ 0 := by
  obtain ⟨H, hH⟩ := finite_complex_family_has_imaginary_lower_bound shift
  have hclear : clearRatFuncCoefficients Q ≠ 0 :=
    clearRatFuncCoefficients_ne_zero Q hQ
  obtain ⟨z, hzH, hzclear, hzD⟩ :=
    exists_upper_specialization_avoiding_polynomial
      (clearRatFuncCoefficients Q) hclear (ratFuncCommonDenominator Q)
      (ratFuncCommonDenominator_ne_zero Q) H
  have hnodes : Function.Injective (fun i => z + shift i) := by
    intro i j hij
    exact hshift (add_left_cancel hij)
  have hupper : ∀ i, 0 < (z + shift i).im := by
    intro i
    rw [Complex.add_im]
    linarith [hH i]
  have hP : specializeRatFuncCoefficients z Q ≠ 0 :=
    specializeRatFuncCoefficients_ne_zero z Q hzD hzclear
  obtain ⟨a, ε, C', hε, hεη, hpos, hgauge, hbounded, hfinite, hescape⟩ :=
    primeDyadic_actualDifferentialJet_escapes_mvPolynomial_in_gaugeBall
      (fun i => z + shift i) hnodes hupper orders u C hu
      (specializeRatFuncCoefficients z Q) hP hηTime hηGauge
  exact ⟨z, a, ε, C', hε, hεη, hzD, hnodes, hupper, hpos, hgauge,
    hbounded, hfinite, hescape⟩

end GaloisForLFunctions.HTGeometry
