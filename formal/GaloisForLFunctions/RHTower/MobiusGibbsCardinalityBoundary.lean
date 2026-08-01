import GaloisForLFunctions.RHTower.MobiusExponentialGibbsBoundary

/-!
# Cardinality-root boundary of the finite Möbius Gibbs carrier

Collapsing every prime variable to one cardinality variable does not restore a generic stability
mechanism.  This module formalizes the exact algebraic data at the coalescence point `x = 0`:
the partition is `(1+z)^|P|`, and its first physical-scale derivative is
`-prod_{p in P}(1+pz)`.  These are the two load-bearing identities behind the paper-proved
fractional root-splitting obstruction.

No zero statement, cancellation estimate, or form of RH is assumed.
-/

open Complex
open scoped BigOperators

namespace RHTower

noncomputable section

/-! ## Conditional two-prime Rayleigh survivor -/

/-- Rayleigh determinant of the positive two-prime Gibbs table with spectator product `a`. -/
def twoPrimeExponentialGibbsRayleighGap (a p q x : ℝ) : ℝ :=
  Real.exp (-(a * p * x)) * Real.exp (-(a * q * x)) -
    Real.exp (-(a * x)) * Real.exp (-(a * p * q * x))

theorem twoPrimeExponentialGibbsRayleighGap_eq (a p q x : ℝ) :
    twoPrimeExponentialGibbsRayleighGap a p q x =
      Real.exp (-(a * (p + q) * x)) -
        Real.exp (-(a * (1 + p * q) * x)) := by
  rw [twoPrimeExponentialGibbsRayleighGap, ← Real.exp_add, ← Real.exp_add]
  congr 2 <;> ring

/-- Every genuine conditional two-prime table is strictly Rayleigh. -/
theorem twoPrimeExponentialGibbsRayleighGap_pos
    {a p q x : ℝ} (ha : 0 < a) (hp : 1 < p) (hq : 1 < q) (hx : 0 < x) :
    0 < twoPrimeExponentialGibbsRayleighGap a p q x := by
  rw [twoPrimeExponentialGibbsRayleighGap_eq]
  apply sub_pos.mpr
  rw [Real.exp_lt_exp]
  have hgap : p + q < 1 + p * q := by
    nlinarith [mul_pos (sub_pos.mpr hp) (sub_pos.mpr hq)]
  have hscale : 0 < a * x := mul_pos ha hx
  nlinarith [mul_lt_mul_of_pos_right hgap hscale]

/-- The multiplicative exponential carrier obeys the negative lattice inequality.  Writing two
Boolean subsets as a common intersection of product `c` and disjoint increments of products
`a,b`, this is exactly global log-submodularity of the finite Gibbs weight. -/
theorem exponentialProductWeight_logSubmodular
    {a b c x : ℝ} (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 0 ≤ c) (hx : 0 ≤ x) :
    Real.exp (-(c * a * x)) * Real.exp (-(c * b * x)) ≥
      Real.exp (-(c * x)) * Real.exp (-(c * a * b * x)) := by
  rw [← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hgap : a + b ≤ 1 + a * b := by
    nlinarith [mul_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr hb)]
  have hscale : 0 ≤ c * x := mul_nonneg hc hx
  nlinarith [mul_le_mul_of_nonneg_left hgap hscale]

/-- Finite exponential squarefree partition collapsed to the prime-count variable `z`. -/
def finitePrimeCardinalityPartition (P : Finset ℕ) (w z : ℂ) : ℂ :=
  ∑ T ∈ P.powerset,
    z ^ T.card * Complex.exp (-((finitePrimeSubsetProduct T : ℕ) : ℂ) * w)

/-- Algebraic `m`-th physical-scale moment of the cardinality partition. -/
def finitePrimeCardinalityMoment (P : Finset ℕ) (m : ℕ) (z : ℂ) : ℂ :=
  (-1 : ℂ) ^ m *
    ∑ T ∈ P.powerset, z ^ T.card * ∏ p ∈ T, ((p : ℂ) ^ m)

/-- The all-minus cardinality specialization is the finite Möbius parity partition. -/
theorem finitePrimeCardinalityPartition_neg_one (P : Finset ℕ) (w : ℂ) :
    finitePrimeCardinalityPartition P w (-1) = finitePrimeParityPartition P w := by
  rfl

/-- At zero physical scale all Boolean weights coincide, giving the coalesced power
`(1+z)^|P|`. -/
theorem finitePrimeCardinalityPartition_zero (P : Finset ℕ) (z : ℂ) :
    finitePrimeCardinalityPartition P 0 z = (1 + z) ^ P.card := by
  rw [finitePrimeCardinalityPartition]
  simp only [mul_zero, Complex.exp_zero, mul_one]
  have hprod := Finset.prod_add (fun _ : ℕ => z) (fun _ : ℕ => (1 : ℂ)) P
  simpa [Finset.prod_const, add_comm] using hprod.symm

/-- Every physical-scale derivative at zero equals the corresponding explicit Boolean moment. -/
theorem iteratedDeriv_finitePrimeCardinalityPartition_zero
    (P : Finset ℕ) (m : ℕ) (z : ℂ) :
    iteratedDeriv m (fun w => finitePrimeCardinalityPartition P w z) 0 =
      finitePrimeCardinalityMoment P m z := by
  change iteratedDeriv m (fun w : ℂ =>
    ∑ T ∈ P.powerset,
      z ^ T.card *
        Complex.exp (-((finitePrimeSubsetProduct T : ℕ) : ℂ) * w)) 0 = _
  rw [HurwitzExp.iteratedDeriv_finset_sum P.powerset m
    (fun T _ => contDiff_const.mul
      (HurwitzExp.contDiff_expLin (-((finitePrimeSubsetProduct T : ℕ) : ℂ)))) 0]
  simp only [iteratedDeriv_const_mul_field, HurwitzExp.iteratedDeriv_expLin,
    mul_zero, Complex.exp_zero, mul_one]
  rw [finitePrimeCardinalityMoment, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro T _
  rw [neg_pow]
  simp only [finitePrimeSubsetProduct]
  push_cast
  rw [Finset.prod_pow]
  ring

/-- The first cardinality-weighted subset product factors into its local prime terms. -/
theorem finitePrimeCardinalityFirstMomentSum_eq_prod (P : Finset ℕ) (z : ℂ) :
    (∑ T ∈ P.powerset, z ^ T.card * ∏ p ∈ T, (p : ℂ)) =
      ∏ p ∈ P, (1 + (p : ℂ) * z) := by
  have hprod := Finset.prod_add
    (fun p : ℕ => (p : ℂ) * z) (fun _ : ℕ => (1 : ℂ)) P
  rw [show (∏ p ∈ P, ((p : ℂ) * z + 1)) =
      ∏ p ∈ P, (1 + (p : ℂ) * z) by
        apply Finset.prod_congr rfl
        intro p _
        ring] at hprod
  rw [hprod]
  apply Finset.sum_congr rfl
  intro T _
  simp only [Finset.prod_const]
  rw [Finset.prod_mul_distrib]
  simp only [Finset.prod_const]
  ring

/-- Exact first physical-scale tangent at the coalesced cardinality polynomial. -/
theorem deriv_finitePrimeCardinalityPartition_zero (P : Finset ℕ) (z : ℂ) :
    deriv (fun w => finitePrimeCardinalityPartition P w z) 0 =
      -∏ p ∈ P, (1 + (p : ℂ) * z) := by
  rw [← iteratedDeriv_one]
  rw [iteratedDeriv_finitePrimeCardinalityPartition_zero,
    finitePrimeCardinalityMoment]
  simp only [pow_one, neg_mul, one_mul]
  rw [finitePrimeCardinalityFirstMomentSum_eq_prod]

/-- At the coalesced root `z=-1`, the first scale tangent is the explicit nonzero product
`-prod(1-p)`. -/
theorem deriv_finitePrimeCardinalityPartition_zero_neg_one (P : Finset ℕ) :
    deriv (fun w => finitePrimeCardinalityPartition P w (-1)) 0 =
      -∏ p ∈ P, (1 - (p : ℂ)) := by
  rw [deriv_finitePrimeCardinalityPartition_zero]
  apply congrArg Neg.neg
  apply Finset.prod_congr rfl
  intro p _
  ring

end

end RHTower
