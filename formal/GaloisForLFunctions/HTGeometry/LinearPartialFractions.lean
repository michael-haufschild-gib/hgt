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

end GaloisForLFunctions.HTGeometry
