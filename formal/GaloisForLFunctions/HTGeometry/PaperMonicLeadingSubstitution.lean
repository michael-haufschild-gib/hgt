import Mathlib.RingTheory.MvPolynomial.MonomialOrder

/-!
# Independent leading monomials give independent polynomial substitutions

Infrastructure for applying the source Rees specialization to native generator
families with lower-order perturbations. Coefficients may lie in any commutative
ring: monic leading terms avoid domain and characteristic assumptions.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial
open scoped BigOperators MonomialOrder

noncomputable section

variable {K σ ι : Type*} [CommRing K]

/-- Exponents of products of the chosen leading monomials. -/
def paperMonicLeadingExponent (m : MonomialOrder σ) (g : ι → MvPolynomial σ K)
    (d : ι →₀ ℕ) : σ →₀ ℕ :=
  d.sum fun i n => n • m.degree (g i)

/-- Substitution into a monomial preserves its coefficient and sends its leading
exponent through the generator exponent map. -/
theorem paperMonicSubstitution_monomial (m : MonomialOrder σ)
    (g : ι → MvPolynomial σ K) (hg : ∀ i, m.Monic (g i))
    (d : ι →₀ ℕ) (r : K) (hr : r ≠ 0) :
    m.degree (aeval g (monomial d r)) = paperMonicLeadingExponent m g d ∧
      m.leadingCoeff (aeval g (monomial d r)) = r := by
  classical
  nontriviality K
  let P := d.prod fun i n => g i ^ n
  have hP : m.Monic P := MonomialOrder.Monic.prod (fun i _ => (hg i).pow)
  have hd : m.degree P = paperMonicLeadingExponent m g d := by
    change m.degree (∏ i ∈ d.support, g i ^ d i) = ∑ i ∈ d.support, d i • m.degree (g i)
    rw [MonomialOrder.degree_prod_of_regular]
    · apply Finset.sum_congr rfl
      intro i _
      apply MonomialOrder.degree_pow_of_pow_leadingCoeff_ne_zero
      rw [(hg i).leadingCoeff_eq_one, one_pow]
      exact one_ne_zero
    · intro i _
      rw [((hg i).pow).leadingCoeff_eq_one]
      exact isRegular_one
  have hc : m.leadingCoeff (C r) * m.leadingCoeff P ≠ 0 := by
    simpa only [MonomialOrder.leadingCoeff_C, hP.leadingCoeff_eq_one, mul_one] using hr
  rw [aeval_monomial]
  change m.degree (C r * P) = _ ∧ m.leadingCoeff (C r * P) = _
  rw [MonomialOrder.degree_mul_of_mul_leadingCoeff_ne_zero hc,
    MonomialOrder.leadingCoeff_mul_of_mul_leadingCoeff_ne_zero hc,
    MonomialOrder.degree_C, hd, zero_add, MonomialOrder.leadingCoeff_C,
    hP.leadingCoeff_eq_one, mul_one]
  exact ⟨rfl, rfl⟩

/-- A polynomial with independent monic leading exponents cannot become zero
under substitution. -/
theorem paperMonicSubstitution_ne_zero (m : MonomialOrder σ)
    (g : ι → MvPolynomial σ K) (hg : ∀ i, m.Monic (g i))
    (hinj : Function.Injective (paperMonicLeadingExponent m g))
    (p : MvPolynomial ι K) (hp : p ≠ 0) : aeval g p ≠ 0 := by
  classical
  obtain ⟨d, hd, hmax⟩ := Finset.exists_max_image p.support
    (fun e => m.toSyn (paperMonicLeadingExponent m g e)) (support_nonempty.mpr hp)
  have hrd : coeff d p ≠ 0 := mem_support_iff.mp hd
  have hc : coeff (paperMonicLeadingExponent m g d) (aeval g p) = coeff d p := by
    conv_lhs => rw [p.as_sum]
    rw [map_sum, coeff_sum]
    rw [Finset.sum_eq_single_of_mem d hd]
    · have H := paperMonicSubstitution_monomial m g hg d (coeff d p) hrd
      rw [← H.1]
      exact H.2
    · intro e he hne
      apply MonomialOrder.coeff_eq_zero_of_lt (m := m)
      rw [(paperMonicSubstitution_monomial m g hg e (coeff e p) (mem_support_iff.mp he)).1]
      exact (hmax e he).lt_of_ne (fun h => hne (hinj (m.toSyn.injective h)))
  intro hz
  rw [hz, coeff_zero] at hc
  exact hrd hc.symm

/-- Monic polynomial perturbations preserve substitution injectivity whenever
their leading exponent map is injective. -/
theorem paperMonicSubstitution_injective (m : MonomialOrder σ)
    (g : ι → MvPolynomial σ K) (hg : ∀ i, m.Monic (g i))
    (hinj : Function.Injective (paperMonicLeadingExponent m g)) :
    Function.Injective (aeval (R := K) g) := by
  intro p q h
  apply sub_eq_zero.mp
  by_contra hpq
  apply paperMonicSubstitution_ne_zero m g hg hinj (p - q) hpq
  rw [map_sub, h, sub_self]

end

end GaloisForLFunctions.HTGeometry
