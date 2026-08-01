import Mathlib.Algebra.Polynomial.PartialFractions
import Mathlib.FieldTheory.RatFunc.Basic

/-!
# Partial fractions over distinct linear factors

For a denominator that is a product of distinct monic linear factors, the general partial-fraction
theorem specializes: every remainder has degree below one, hence is a constant, so the decomposition
takes the form

`f / prod (X - sigma_i) = q + sum nu_i / (X - sigma_i)`

with scalar coefficients.  That is the shape a simple-pole decomposition is stated in.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

/-- A polynomial of degree below one is a constant. -/
theorem eq_C_of_degree_lt_one {K : Type*} [Field K] {p : K[X]} (h : p.degree < 1) :
    p = C (p.coeff 0) := by
  refine Polynomial.eq_C_of_degree_le_zero ?_
  rcases eq_or_ne p 0 with rfl | hp
  · simp
  · rw [degree_eq_natDegree hp, Nat.cast_lt_one] at h
    rw [degree_eq_natDegree hp, h]
    simp

/-- **Partial fractions over distinct linear factors.**  The remainders are constants, so the
decomposition has scalar coefficients — one per pole. -/
theorem div_linear_prod_eq_add_sum_const {ι K : Type*} [Field K]
    (f : K[X]) {σ : ι → K} {s : Finset ι} (hinj : Function.Injective σ) :
    ∃ (q : K[X]) (ν : ι → K),
      (f : RatFunc K) / ∏ i ∈ s, ((X - C (σ i) : K[X]) : RatFunc K)
        = (q : RatFunc K)
          + ∑ i ∈ s, ((C (ν i) : K[X]) : RatFunc K) / ((X - C (σ i) : K[X]) : RatFunc K) := by
  obtain ⟨q, r, hdeg, heq⟩ :=
    div_prod_eq_quo_add_sum_rem_div (R := K) (s := s) (RatFunc K) f
      (fun i _ => monic_X_sub_C (σ i))
      (fun i _ j _ hij => pairwise_coprime_X_sub_C hinj hij)
  refine ⟨q, fun i => (r i).coeff 0, ?_⟩
  refine heq.trans ?_
  congr 1
  refine Finset.sum_congr rfl fun i hi => ?_
  have hdeg' : (r i).degree < 1 := by
    have := hdeg i hi
    rwa [degree_X_sub_C] at this
  rw [eq_C_of_degree_lt_one hdeg']
  rfl

/-! ## The factorization bridge

To apply the decomposition one must know the denominator *is* a product of distinct linear factors.
A degree count supplies this: a polynomial of degree at most `n` vanishing at `n` distinct points is
a scalar multiple of the product of the corresponding linear factors, because the factors are
pairwise coprime and each divides it, so their product does, and the degrees then leave only a
constant cofactor. -/

/-- Distinct roots contribute a product of linear factors as a divisor. -/
theorem prod_X_sub_C_dvd_of_isRoot {ι K : Type*} [Field K]
    {p : K[X]} {σ : ι → K} {s : Finset ι} (hinj : Function.Injective σ)
    (hroot : ∀ i ∈ s, p.IsRoot (σ i)) :
    (∏ i ∈ s, (X - C (σ i))) ∣ p :=
  Finset.prod_dvd_of_coprime ((Polynomial.pairwise_coprime_X_sub_C hinj).set_pairwise ↑s)
    fun i hi => dvd_iff_isRoot.mpr (hroot i hi)

theorem natDegree_prod_X_sub_C {ι K : Type*} [Field K] (σ : ι → K) (s : Finset ι) :
    (∏ i ∈ s, (X - C (σ i))).natDegree = s.card := by
  rw [Polynomial.natDegree_prod _ _ fun i _ => X_sub_C_ne_zero (σ i)]
  simp

/-- **The factorization bridge.**  A polynomial of degree at most `card s` vanishing at the `card s`
distinct points `σ i` is a constant times the product of the linear factors `X - σ i`. -/
theorem eq_C_mul_prod_X_sub_C {ι K : Type*} [Field K]
    {p : K[X]} {σ : ι → K} {s : Finset ι} (hinj : Function.Injective σ)
    (hroot : ∀ i ∈ s, p.IsRoot (σ i)) (hdeg : p.natDegree ≤ s.card) :
    ∃ c : K, p = C c * ∏ i ∈ s, (X - C (σ i)) := by
  obtain ⟨g, hg⟩ := prod_X_sub_C_dvd_of_isRoot hinj hroot
  rcases eq_or_ne p 0 with rfl | hp
  · exact ⟨0, by simp⟩
  · have hprod : (∏ i ∈ s, (X - C (σ i) : K[X])) ≠ 0 := fun h => hp (by rw [hg, h, zero_mul])
    have hgne : g ≠ 0 := fun h => hp (by rw [hg, h, mul_zero])
    have hdeg' : p.natDegree = s.card + g.natDegree := by
      rw [hg, Polynomial.natDegree_mul hprod hgne, natDegree_prod_X_sub_C]
    have hg0 : g.natDegree = 0 := by omega
    refine ⟨g.coeff 0, ?_⟩
    rw [hg, ← Polynomial.eq_C_of_natDegree_eq_zero hg0]
    ring

/-- **Partial fractions from a root list.**  A rational function whose denominator has degree at
most `card s` and vanishes at the `card s` distinct points `σ i` decomposes into a polynomial part
plus one simple pole at each `σ i`, with scalar residues. -/
theorem div_eq_add_sum_const_of_isRoot {ι K : Type*} [Field K]
    (f : K[X]) {p : K[X]} {σ : ι → K} {s : Finset ι} (hinj : Function.Injective σ)
    (hroot : ∀ i ∈ s, p.IsRoot (σ i)) (hdeg : p.natDegree ≤ s.card) (hp : p ≠ 0) :
    ∃ (q : K[X]) (ν : ι → K),
      (f : RatFunc K) / (p : RatFunc K)
        = (q : RatFunc K)
          + ∑ i ∈ s, ((C (ν i) : K[X]) : RatFunc K) / ((X - C (σ i) : K[X]) : RatFunc K) := by
  obtain ⟨c, hfac⟩ := eq_C_mul_prod_X_sub_C hinj hroot hdeg
  have hc : c ≠ 0 := by
    rintro rfl
    rw [map_zero, zero_mul] at hfac
    exact hp hfac
  obtain ⟨q, ν, hq⟩ :=
    div_linear_prod_eq_add_sum_const (K := K) (C c⁻¹ * f) (σ := σ) (s := s) hinj
  refine ⟨q, ν, ?_⟩
  rw [← hq]
  have hpcoe : ((p : K[X]) : RatFunc K)
      = ((C c : K[X]) : RatFunc K) * ∏ i ∈ s, ((X - C (σ i) : K[X]) : RatFunc K) := by
    conv_lhs => rw [hfac]
    simp only [RatFunc.coePolynomial, map_mul, map_prod]
  have hpne : ((p : K[X]) : RatFunc K) ≠ 0 := by
    simpa [RatFunc.coePolynomial, FaithfulSMul.algebraMap_eq_zero_iff] using hp
  have hProd : (∏ i ∈ s, ((X - C (σ i) : K[X]) : RatFunc K)) ≠ 0 := by
    rw [hpcoe] at hpne
    exact fun h => hpne (by rw [h, mul_zero])
  have hsplit : ((C c⁻¹ * f : K[X]) : RatFunc K)
      = ((C c⁻¹ : K[X]) : RatFunc K) * ((f : K[X]) : RatFunc K) := by
    simp only [RatFunc.coePolynomial, map_mul]
  have hCC : ((C c⁻¹ : K[X]) : RatFunc K) * ((C c : K[X]) : RatFunc K) = 1 := by
    have hone : (C c⁻¹ * C c : K[X]) = 1 := by rw [← C_mul, inv_mul_cancel₀ hc, map_one]
    simp only [RatFunc.coePolynomial, ← map_mul, hone, map_one]
  rw [div_eq_div_iff hpne hProd, hpcoe, hsplit]
  calc ((f : K[X]) : RatFunc K) * ∏ i ∈ s, ((X - C (σ i) : K[X]) : RatFunc K)
      = (((C c⁻¹ : K[X]) : RatFunc K) * ((C c : K[X]) : RatFunc K))
          * (((f : K[X]) : RatFunc K) * ∏ i ∈ s, ((X - C (σ i) : K[X]) : RatFunc K)) := by
        rw [hCC, one_mul]
    _ = ((C c⁻¹ : K[X]) : RatFunc K) * ((f : K[X]) : RatFunc K)
          * (((C c : K[X]) : RatFunc K) * ∏ i ∈ s, ((X - C (σ i) : K[X]) : RatFunc K)) := by ring

end GaloisForLFunctions.HTGeometry
