import Mathlib
import GaloisForLFunctions.HTGeometry.PolynomialTotalDerivative
import GaloisForLFunctions.HTGeometry.DifferentialIndependence

/-!
# An algebraic primitive of a base element lies in the base

If an element of a differential field extension is algebraic over a differential subfield and its
derivative already lies in that subfield, then the element itself lies in the subfield, provided the
extension introduces no new constants.

The proof is the classical one: differentiating the minimal polynomial produces a polynomial
relation of strictly smaller degree, which must therefore vanish identically; its second-highest
coefficient says that the element, corrected by that coefficient of the minimal polynomial divided
by the degree, is a constant.
-/

open scoped Differential

open Polynomial

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [Differential K] [Differential L]
  [DifferentialAlgebra K L] [CharZero K]

/-- A derivation kills natural number casts. -/
theorem deriv_natCast_eq_zero (m : ℕ) : ((m : L))′ = 0 := by
  have : ((m : L)) = algebraMap ℤ L (m : ℤ) := by push_cast; simp
  rw [this]
  exact Derivation.map_algebraMap _ _

/-- **Algebraic primitives descend.**  An element algebraic over a differential subfield whose
derivative lies in that subfield lies in the subfield, when there are no new constants. -/
theorem mem_range_algebraMap_of_isAlgebraic_of_deriv_eq
    [Differential.ContainConstants K L]
    {y : L} (halg : IsAlgebraic K y) {b : K} (hy : y′ = algebraMap K L b) :
    y ∈ (algebraMap K L).range := by
  classical
  have hint : IsIntegral K y := halg.isIntegral
  set P : K[X] := minpoly K y with hP
  have hmonic : P.Monic := minpoly.monic hint
  have hPne : P ≠ 0 := hmonic.ne_zero
  set n : ℕ := P.natDegree with hn
  have hnpos : 0 < n := minpoly.natDegree_pos hint
  have haeval : (aeval y) P = 0 := minpoly.aeval K y
  set R : K[X] := Differential.mapCoeffs P + C b * derivative P with hR
  have hRy : (aeval y) R = 0 := by
    have hd : ((aeval y) P)′ = (aeval y) (Differential.mapCoeffs P)
        + (aeval y) (derivative P) * y′ := Differential.deriv_aeval_eq y P
    rw [haeval, map_zero, hy] at hd
    have hsplit : (aeval y) R
        = (aeval y) (Differential.mapCoeffs P)
          + (aeval y) (derivative P) * algebraMap K L b := by
      rw [hR, map_add, map_mul, aeval_C]
      ring
    rw [hsplit, ← hd]
  -- the differentiated relation has strictly smaller degree
  have hdegMap : (Differential.mapCoeffs P).degree < P.degree := by
    rw [degree_eq_natDegree hPne]
    refine (degree_lt_iff_coeff_zero _ _).2 fun m hm => ?_
    rw [Differential.coeff_mapCoeffs]
    have hm' : n ≤ m := by exact_mod_cast hm
    rcases eq_or_lt_of_le hm' with rfl | hlt
    · rw [hmonic.coeff_natDegree]
      exact Derivation.map_one_eq_zero _
    · rw [P.coeff_eq_zero_of_natDegree_lt hlt, map_zero]
  have hdegDer : (C b * derivative P).degree < P.degree := by
    refine lt_of_le_of_lt (degree_mul_le _ _) ?_
    refine lt_of_le_of_lt (add_le_add (degree_C_le) le_rfl) ?_
    simpa using degree_derivative_lt hPne
  have hdegR : R.degree < P.degree := by
    rw [hR]
    exact lt_of_le_of_lt (degree_add_le _ _) (max_lt hdegMap hdegDer)
  have hRzero : R = 0 := by
    by_contra hne
    exact absurd (minpoly.degree_le_of_ne_zero K y hne hRy) (not_le.mpr hdegR)
  -- read off the second-highest coefficient
  have hcoeff : (P.coeff (n - 1))′ + b * (n : K) = 0 := by
    have hc := congrArg (fun p : K[X] => p.coeff (n - 1)) hRzero
    simp only [hR, coeff_add, Differential.coeff_mapCoeffs, coeff_C_mul, coeff_zero] at hc
    rw [coeff_derivative, show n - 1 + 1 = n by omega, hmonic.coeff_natDegree, one_mul] at hc
    have hcast : ((n - 1 : ℕ) : K) + 1 = (n : K) := by
      have hstep : (n - 1) + 1 = n := by omega
      calc ((n - 1 : ℕ) : K) + 1 = (((n - 1) + 1 : ℕ) : K) := by push_cast; ring
        _ = (n : K) := by rw [hstep]
    rw [hcast] at hc
    exact hc
  -- the corrected element is a constant
  have hconst : (algebraMap K L (P.coeff (n - 1)) + (n : L) * y)′ = 0 := by
    have h1 : (algebraMap K L (P.coeff (n - 1)))′ = algebraMap K L ((P.coeff (n - 1))′) :=
      deriv_algebraMap _
    have h2 : ((n : L) * y)′ = (n : L) * y′ := by
      rw [Derivation.leibniz]
      simp
    rw [map_add, h1, h2, hy]
    have : algebraMap K L ((P.coeff (n - 1))′) + (n : L) * algebraMap K L b
        = algebraMap K L ((P.coeff (n - 1))′ + b * (n : K)) := by
      rw [map_add, map_mul, map_natCast]
      ring
    rw [this, hcoeff, map_zero]
  obtain ⟨c, hc⟩ := mem_range_of_deriv_eq_zero K hconst
  refine ⟨(c - P.coeff (n - 1)) / (n : K), ?_⟩
  have hnne : ((n : K)) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hLne : ((n : L)) ≠ 0 := by
    rw [show ((n : L)) = algebraMap K L (n : K) by rw [map_natCast]]
    exact fun h => hnne ((map_eq_zero (algebraMap K L)).1 h)
  have hy' : (n : L) * y = algebraMap K L (c - P.coeff (n - 1)) := by
    rw [map_sub, hc]
    ring
  have hsub : algebraMap K L c - algebraMap K L (P.coeff (n - 1)) = (n : L) * y := by
    rw [← map_sub, ← hy']
  rw [map_div₀, map_sub, map_natCast, hsub]
  field_simp

/-! ### The intermediate-field form -/

section IntermediateField

variable {C E : Type*} [Field C] [Field E] [CharZero E] [Algebra C E] [Differential E]

open GaloisForLFunctions

/-- **Algebraic primitives descend, for a derivation-closed intermediate field.**  Stated without a
differential structure on the subfield, so that no auxiliary instance stack is needed. -/
theorem mem_of_isAlgebraic_of_deriv_mem
    (K : IntermediateField C E) (hKclosed : DerivationClosed K)
    (hconst : ∀ x : E, x′ = 0 → x ∈ K)
    {y : E} (halg : IsAlgebraic (↥K) y) (hy : y′ ∈ K) : y ∈ K := by
  classical
  have hint : IsIntegral (↥K) y := halg.isIntegral
  set p : Polynomial (↥K) := minpoly (↥K) y with hp
  have hmonic : p.Monic := minpoly.monic hint
  have hpne : p ≠ 0 := hmonic.ne_zero
  set n : ℕ := p.natDegree with hn
  have hnpos : 0 < n := minpoly.natDegree_pos hint
  set Q : Polynomial E := p.map (algebraMap (↥K) E) with hQ
  have hQmonic : Q.Monic := hmonic.map _
  have hQdeg : Q.natDegree = n := by
    rw [hQ, Polynomial.natDegree_map_eq_of_injective (algebraMap (↥K) E).injective]
  have hQeval : Polynomial.eval y Q = 0 := by
    rw [hQ, Polynomial.eval_map, ← Polynomial.aeval_def]
    exact minpoly.aeval (↥K) y
  have hQcoeff : ∀ i, Q.coeff i ∈ K := by
    intro i
    rw [hQ, Polynomial.coeff_map]
    exact (p.coeff i).2
  set R : Polynomial E := coeffDeriv Q + Polynomial.C (y′) * Polynomial.derivative Q with hR
  have hReval : Polynomial.eval y R = 0 := by
    have hd := deriv_eval Q y
    rw [hQeval, map_zero] at hd
    rw [hR, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C]
    linear_combination -hd
  have hRcoeff : ∀ i, R.coeff i ∈ K := by
    intro i
    rw [hR, Polynomial.coeff_add, coeffDeriv_coeff, Polynomial.coeff_C_mul,
      Polynomial.coeff_derivative]
    exact K.add_mem (hKclosed (hQcoeff i))
      (K.mul_mem hy (K.mul_mem (hQcoeff (i + 1))
        (by simpa using K.natCast_mem (i + 1))))
  have hRdeg : R.degree < p.degree := by
    have hdeg1 : (coeffDeriv Q).degree < Q.degree := by
      rw [Polynomial.degree_eq_natDegree hQmonic.ne_zero]
      refine (Polynomial.degree_lt_iff_coeff_zero _ _).2 fun m hm => ?_
      rw [coeffDeriv_coeff]
      have hm' : Q.natDegree ≤ m := by exact_mod_cast hm
      rcases eq_or_lt_of_le hm' with rfl | hlt
      · rw [hQmonic.coeff_natDegree]
        exact Derivation.map_one_eq_zero _
      · rw [Q.coeff_eq_zero_of_natDegree_lt hlt, map_zero]
    have hdeg2 : (Polynomial.C (y′) * Polynomial.derivative Q).degree < Q.degree := by
      refine lt_of_le_of_lt (Polynomial.degree_mul_le _ _) ?_
      refine lt_of_le_of_lt (add_le_add (Polynomial.degree_C_le) le_rfl) ?_
      simpa using Polynomial.degree_derivative_lt hQmonic.ne_zero
    have hQp : Q.degree = p.degree := by
      rw [hQ, Polynomial.degree_map_eq_of_injective (algebraMap (↥K) E).injective]
    rw [← hQp, hR]
    exact lt_of_le_of_lt (Polynomial.degree_add_le _ _) (max_lt hdeg1 hdeg2)
  have hRzero : R = 0 := by
    by_contra hne
    obtain ⟨R', hR'map, hR'deg⟩ :
        ∃ R' : Polynomial (↥K), R'.map (algebraMap (↥K) E) = R ∧ R'.degree = R.degree := by
      refine Polynomial.exists_degree_eq_of_mem_lifts ?_
      exact (Polynomial.lifts_iff_coeff_lifts R).2 fun i => ⟨⟨R.coeff i, hRcoeff i⟩, rfl⟩
    have hR'ne : R' ≠ 0 := by
      intro h
      rw [h, Polynomial.map_zero] at hR'map
      exact hne hR'map.symm
    have hR'eval : (Polynomial.aeval y) R' = 0 := by
      rw [Polynomial.aeval_def, ← Polynomial.eval_map, hR'map, hReval]
    have := minpoly.degree_le_of_ne_zero (↥K) y hR'ne hR'eval
    rw [← hp, hR'deg] at this
    exact absurd this (not_le.mpr hRdeg)
  have hcoeff : (Q.coeff (n - 1))′ + y′ * (n : E) = 0 := by
    have hc := congrArg (fun q : Polynomial E => q.coeff (n - 1)) hRzero
    simp only [hR, Polynomial.coeff_add, coeffDeriv_coeff, Polynomial.coeff_C_mul,
      Polynomial.coeff_zero, Polynomial.coeff_derivative] at hc
    rw [show n - 1 + 1 = n by omega, ← hQdeg, hQmonic.coeff_natDegree, one_mul, hQdeg] at hc
    have hcast : ((n - 1 : ℕ) : E) + 1 = (n : E) := by
      have hstep : (n - 1) + 1 = n := by omega
      calc ((n - 1 : ℕ) : E) + 1 = (((n - 1) + 1 : ℕ) : E) := by push_cast; ring
        _ = (n : E) := by rw [hstep]
    rw [hcast] at hc
    exact hc
  have hzero : (Q.coeff (n - 1) + (n : E) * y)′ = 0 := by
    have h2 : (((n : E)) * y)′ = (n : E) * y′ := by
      rw [Derivation.leibniz]
      simp
    rw [map_add, h2]
    linear_combination hcoeff
  have hmemK : Q.coeff (n - 1) + (n : E) * y ∈ K := hconst _ hzero
  have hnne : ((n : E)) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have : (n : E) * y ∈ K := by
    have hsub := K.sub_mem hmemK (hQcoeff (n - 1))
    have heq : Q.coeff (n - 1) + (n : E) * y - Q.coeff (n - 1) = (n : E) * y := by ring
    rwa [heq] at hsub
  have hyK : y = ((n : E))⁻¹ * ((n : E) * y) := by field_simp
  rw [hyK]
  exact K.mul_mem (K.inv_mem (by simp)) this

end IntermediateField
