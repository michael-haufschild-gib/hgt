import GaloisForLFunctions.HTGeometry.ConnesVanSuijlekomToeplitz

/-!
# Connes--van Suijlekom Proposition 2.1: source audit and nonzero correction

Proposition 2.1 of arXiv:2511.23257v1 omits the necessary hypothesis that
its kernel vector is nonzero.  With the zero vector, its Laurent generator is
zero and the asserted basis in clause (2) cannot span the quotient. This module
closes that obstruction and proves the corrected involution-stability clause,
together with the positive leading-coefficient fact needed by the quotient
construction.
-/

open scoped BigOperators ComplexOrder
open Matrix Polynomial

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The Laurent generator `P = ∑ aⱼXʲ` used in Proposition 2.1. -/
def connesVanSuijlekomP21Generator {N : ℕ} (a : Fin (N + 1) → ℝ) :
    LaurentPolynomial ℂ :=
  ∑ j : Fin (N + 1), LaurentPolynomial.C (a j : ℂ) * LaurentPolynomial.T (j : ℤ)

/-- The principal Laurent ideal used in Proposition 2.1. -/
def connesVanSuijlekomP21Ideal {N : ℕ} (a : Fin (N + 1) → ℝ) :
    Ideal (LaurentPolynomial ℂ) :=
  Ideal.span {connesVanSuijlekomP21Generator a}

/-- The Laurent quotient of corrected Proposition 2.1. -/
abbrev connesVanSuijlekomP21Quotient {N : ℕ} (a : Fin (N + 1) → ℝ) :=
  LaurentPolynomial ℂ ⧸ connesVanSuijlekomP21Ideal a

/-- The Laurent-variable class in the source quotient. -/
def connesVanSuijlekomP21QuotientX {N : ℕ} (a : Fin (N + 1) → ℝ) :
    connesVanSuijlekomP21Quotient a :=
  Ideal.Quotient.mk (connesVanSuijlekomP21Ideal a) (LaurentPolynomial.T 1)

/-- The inverse Laurent-variable class in the source quotient. -/
def connesVanSuijlekomP21QuotientXInv {N : ℕ} (a : Fin (N + 1) → ℝ) :
    connesVanSuijlekomP21Quotient a :=
  Ideal.Quotient.mk (connesVanSuijlekomP21Ideal a) (LaurentPolynomial.T (-1))

/-- The source Laurent generator vanishes in its principal quotient. -/
theorem connesVanSuijlekomP21_quotient_generator_eq_zero
    {N : ℕ} (a : Fin (N + 1) → ℝ) :
    Ideal.Quotient.mk (connesVanSuijlekomP21Ideal a)
      (connesVanSuijlekomP21Generator a) = 0 := by
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  exact Ideal.mem_span_singleton_self _

/-- The two Laurent-variable classes multiply to one in the source quotient. -/
theorem connesVanSuijlekomP21_quotient_x_mul_xInv
    {N : ℕ} (a : Fin (N + 1) → ℝ) :
    connesVanSuijlekomP21QuotientX a * connesVanSuijlekomP21QuotientXInv a = 1 := by
  change Ideal.Quotient.mk (connesVanSuijlekomP21Ideal a)
    (LaurentPolynomial.T 1 * LaurentPolynomial.T (-1)) = 1
  rw [← LaurentPolynomial.T_add]
  norm_num

/-- The two Laurent-variable classes multiply to one in the other order. -/
theorem connesVanSuijlekomP21_quotient_xInv_mul_x
    {N : ℕ} (a : Fin (N + 1) → ℝ) :
    connesVanSuijlekomP21QuotientXInv a * connesVanSuijlekomP21QuotientX a = 1 := by
  change Ideal.Quotient.mk (connesVanSuijlekomP21Ideal a)
    (LaurentPolynomial.T (-1) * LaurentPolynomial.T 1) = 1
  rw [← LaurentPolynomial.T_add]
  norm_num

/-- The quotient Laurent-variable class as an explicit unit. -/
def connesVanSuijlekomP21QuotientXUnit {N : ℕ} (a : Fin (N + 1) → ℝ) :
    (connesVanSuijlekomP21Quotient a)ˣ where
  val := connesVanSuijlekomP21QuotientX a
  inv := connesVanSuijlekomP21QuotientXInv a
  val_inv := connesVanSuijlekomP21_quotient_x_mul_xInv a
  inv_val := connesVanSuijlekomP21_quotient_xInv_mul_x a

/-- The nonconstant part of the source relation after multiplication by
`X⁻¹`. It is a polynomial in nonnegative powers of `X`. -/
def connesVanSuijlekomP21LaurentInverseTail {N : ℕ} (a : Fin (N + 1) → ℝ) :
    LaurentPolynomial ℂ :=
  (Finset.univ.erase 0).sum fun j =>
    LaurentPolynomial.C (a j : ℂ) * LaurentPolynomial.T ((j : ℤ) - 1)

/-- Multiplying the source Laurent relation by `X⁻¹` isolates its nonzero
constant coefficient. -/
theorem connesVanSuijlekomP21_generator_mul_T_neg_one
    {N : ℕ} (a : Fin (N + 1) → ℝ) :
    connesVanSuijlekomP21Generator a * LaurentPolynomial.T (-1) =
      LaurentPolynomial.C (a (0 : Fin (N + 1)) : ℂ) * LaurentPolynomial.T (-1) +
        connesVanSuijlekomP21LaurentInverseTail a := by
  rw [connesVanSuijlekomP21Generator, Finset.sum_mul]
  let f : Fin (N + 1) → LaurentPolynomial ℂ := fun j =>
    (LaurentPolynomial.C (a j : ℂ) * LaurentPolynomial.T (j : ℤ)) *
      LaurentPolynomial.T (-1)
  change (∑ j, f j) = _
  rw [← Finset.add_sum_erase Finset.univ f (Finset.mem_univ 0)]
  congr 1
  · simp only [f]
    rw [LaurentPolynomial.mul_T_assoc]
    norm_num
  · apply Finset.sum_congr rfl
    intro j _
    simp only [f]
    rw [LaurentPolynomial.mul_T_assoc]
    rw [sub_eq_add_neg]

/-- The quotient class of the nonconstant tail of the `X⁻¹` relation. -/
def connesVanSuijlekomP21QuotientInverseTail {N : ℕ} (a : Fin (N + 1) → ℝ) :
    connesVanSuijlekomP21Quotient a :=
  Ideal.Quotient.mk (connesVanSuijlekomP21Ideal a)
    (connesVanSuijlekomP21LaurentInverseTail a)

/-- In the source quotient, the constant coefficient times `X⁻¹` is the
negative of a finite polynomial in nonnegative powers. -/
theorem connesVanSuijlekomP21_quotient_inverse_relation
    {N : ℕ} (a : Fin (N + 1) → ℝ) :
    Ideal.Quotient.mk (connesVanSuijlekomP21Ideal a)
        (LaurentPolynomial.C (a (0 : Fin (N + 1)) : ℂ)) *
        connesVanSuijlekomP21QuotientXInv a +
      connesVanSuijlekomP21QuotientInverseTail a = 0 := by
  let J := connesVanSuijlekomP21Ideal a
  calc
    Ideal.Quotient.mk J (LaurentPolynomial.C (a (0 : Fin (N + 1)) : ℂ)) *
        connesVanSuijlekomP21QuotientXInv a +
        connesVanSuijlekomP21QuotientInverseTail a =
        Ideal.Quotient.mk J
          (LaurentPolynomial.C (a (0 : Fin (N + 1)) : ℂ) * LaurentPolynomial.T (-1) +
            connesVanSuijlekomP21LaurentInverseTail a) := by
      change Ideal.Quotient.mk J (LaurentPolynomial.C (a 0 : ℂ)) *
          Ideal.Quotient.mk J (LaurentPolynomial.T (-1)) +
          Ideal.Quotient.mk J (connesVanSuijlekomP21LaurentInverseTail a) = _
      rw [← map_mul, ← map_add]
    _ = Ideal.Quotient.mk J
        (connesVanSuijlekomP21Generator a * LaurentPolynomial.T (-1)) := by
      rw [connesVanSuijlekomP21_generator_mul_T_neg_one]
    _ = Ideal.Quotient.mk J (connesVanSuijlekomP21Generator a) *
        connesVanSuijlekomP21QuotientXInv a := by
      rw [map_mul]
      rfl
    _ = 0 := by
      rw [connesVanSuijlekomP21_quotient_generator_eq_zero]
      exact zero_mul _

/-- The subalgebra generated by the quotient Laurent-variable class. -/
def connesVanSuijlekomP21QuotientAdjoin {N : ℕ} (a : Fin (N + 1) → ℝ) :
    Subalgebra ℂ (connesVanSuijlekomP21Quotient a) :=
  Algebra.adjoin ℂ {connesVanSuijlekomP21QuotientX a}

/-- Constant Laurent classes agree with the quotient scalar algebra map. -/
theorem connesVanSuijlekomP21_quotient_mk_C_eq_algebraMap
    {N : ℕ} (a : Fin (N + 1) → ℝ) (z : ℂ) :
    Ideal.Quotient.mk (connesVanSuijlekomP21Ideal a) (LaurentPolynomial.C z) =
      algebraMap ℂ (connesVanSuijlekomP21Quotient a) z := by
  rfl

/-- The quotient Laurent-variable class belongs to its generated subalgebra. -/
theorem connesVanSuijlekomP21_quotient_x_mem_adjoin
    {N : ℕ} (a : Fin (N + 1) → ℝ) :
    connesVanSuijlekomP21QuotientX a ∈ connesVanSuijlekomP21QuotientAdjoin a := by
  exact Algebra.subset_adjoin (Set.mem_singleton _)

/-- A nonnegative Laurent monomial class is the matching power of the
quotient Laurent-variable class. -/
theorem connesVanSuijlekomP21_quotient_nonnegative_monomial_eq_pow
    {N : ℕ} (a : Fin (N + 1) → ℝ) (k : ℕ) :
    Ideal.Quotient.mk (connesVanSuijlekomP21Ideal a) (LaurentPolynomial.T (k : ℤ)) =
      connesVanSuijlekomP21QuotientX a ^ k := by
  change Ideal.Quotient.mk (connesVanSuijlekomP21Ideal a) (LaurentPolynomial.T (k : ℤ)) =
    Ideal.Quotient.mk (connesVanSuijlekomP21Ideal a) (LaurentPolynomial.T 1) ^ k
  rw [← map_pow]
  congr 1
  rw [LaurentPolynomial.T_pow]
  norm_num

/-- Every term in the inverse relation is polynomial in the quotient
Laurent-variable class. -/
theorem connesVanSuijlekomP21_quotient_inverse_tail_term_mem_adjoin
    {N : ℕ} (a : Fin (N + 1) → ℝ) (j : Fin (N + 1))
    (hj : j ≠ 0) :
    Ideal.Quotient.mk (connesVanSuijlekomP21Ideal a)
      (LaurentPolynomial.C (a j : ℂ) * LaurentPolynomial.T ((j : ℤ) - 1)) ∈
      connesVanSuijlekomP21QuotientAdjoin a := by
  have hjpos : 0 < (j : ℕ) := by
    by_contra h
    have hjzero : (j : ℕ) = 0 := by omega
    exact hj (Fin.ext hjzero)
  have hcast : (j : ℤ) - 1 = ((j : ℕ) - 1 : ℕ) := by omega
  rw [hcast, map_mul, connesVanSuijlekomP21_quotient_mk_C_eq_algebraMap,
    connesVanSuijlekomP21_quotient_nonnegative_monomial_eq_pow]
  exact (connesVanSuijlekomP21QuotientAdjoin a).mul_mem
    ((connesVanSuijlekomP21QuotientAdjoin a).algebraMap_mem (a j : ℂ))
    ((connesVanSuijlekomP21QuotientAdjoin a).pow_mem
      (connesVanSuijlekomP21_quotient_x_mem_adjoin a) _)

/-- The full finite tail in the inverse relation is polynomial in the
quotient Laurent-variable class. -/
theorem connesVanSuijlekomP21_quotient_inverse_tail_mem_adjoin
    {N : ℕ} (a : Fin (N + 1) → ℝ) :
    connesVanSuijlekomP21QuotientInverseTail a ∈ connesVanSuijlekomP21QuotientAdjoin a := by
  rw [connesVanSuijlekomP21QuotientInverseTail,
    connesVanSuijlekomP21LaurentInverseTail, map_sum]
  apply (connesVanSuijlekomP21QuotientAdjoin a).sum_mem
  intro j hj
  exact connesVanSuijlekomP21_quotient_inverse_tail_term_mem_adjoin a j
    (Finset.mem_erase.mp hj).1

/-- With nonzero constant coefficient, `X⁻¹` itself is polynomial in the
quotient Laurent-variable class. -/
theorem connesVanSuijlekomP21_quotient_xInv_mem_adjoin
    {N : ℕ} (a : Fin (N + 1) → ℝ) (ha0 : a 0 ≠ 0) :
    connesVanSuijlekomP21QuotientXInv a ∈ connesVanSuijlekomP21QuotientAdjoin a := by
  have ha0C : (a 0 : ℂ) ≠ 0 := by exact_mod_cast ha0
  have hrel := connesVanSuijlekomP21_quotient_inverse_relation a
  rw [connesVanSuijlekomP21_quotient_mk_C_eq_algebraMap] at hrel
  have hrel' : algebraMap ℂ (connesVanSuijlekomP21Quotient a) (a 0 : ℂ) *
      connesVanSuijlekomP21QuotientXInv a =
        -connesVanSuijlekomP21QuotientInverseTail a :=
    eq_neg_of_add_eq_zero_left hrel
  have hform : connesVanSuijlekomP21QuotientXInv a =
      algebraMap ℂ (connesVanSuijlekomP21Quotient a) ((a 0 : ℂ)⁻¹) *
        (-connesVanSuijlekomP21QuotientInverseTail a) := by
    calc
      connesVanSuijlekomP21QuotientXInv a = 1 * connesVanSuijlekomP21QuotientXInv a := by
        rw [one_mul]
      _ = (algebraMap ℂ (connesVanSuijlekomP21Quotient a) ((a 0 : ℂ)⁻¹) *
          algebraMap ℂ (connesVanSuijlekomP21Quotient a) (a 0 : ℂ)) *
          connesVanSuijlekomP21QuotientXInv a := by
        rw [← map_mul, inv_mul_cancel₀ ha0C]
        simp
      _ = algebraMap ℂ (connesVanSuijlekomP21Quotient a) ((a 0 : ℂ)⁻¹) *
          (algebraMap ℂ (connesVanSuijlekomP21Quotient a) (a 0 : ℂ) *
            connesVanSuijlekomP21QuotientXInv a) := by rw [mul_assoc]
      _ = algebraMap ℂ (connesVanSuijlekomP21Quotient a) ((a 0 : ℂ)⁻¹) *
          (-connesVanSuijlekomP21QuotientInverseTail a) := by rw [hrel']
  rw [hform]
  exact (connesVanSuijlekomP21QuotientAdjoin a).mul_mem
    ((connesVanSuijlekomP21QuotientAdjoin a).algebraMap_mem ((a 0 : ℂ)⁻¹))
    ((connesVanSuijlekomP21QuotientAdjoin a).neg_mem
      (connesVanSuijlekomP21_quotient_inverse_tail_mem_adjoin a))

/-- A negative Laurent monomial class is the matching power of the quotient
inverse Laurent-variable class. -/
theorem connesVanSuijlekomP21_quotient_negative_monomial_eq_pow
    {N : ℕ} (a : Fin (N + 1) → ℝ) (k : ℕ) :
    Ideal.Quotient.mk (connesVanSuijlekomP21Ideal a) (LaurentPolynomial.T (-(k : ℤ))) =
      connesVanSuijlekomP21QuotientXInv a ^ k := by
  change Ideal.Quotient.mk (connesVanSuijlekomP21Ideal a) (LaurentPolynomial.T (-(k : ℤ)) :
      LaurentPolynomial ℂ) =
    Ideal.Quotient.mk (connesVanSuijlekomP21Ideal a) (LaurentPolynomial.T (-1)) ^ k
  rw [← map_pow]
  congr 1
  rw [LaurentPolynomial.T_pow]
  ring_nf

/-- Every Laurent monomial class is polynomial in the quotient Laurent-variable
class when the source constant coefficient is nonzero. -/
theorem connesVanSuijlekomP21_quotient_laurent_monomial_mem_adjoin
    {N : ℕ} (a : Fin (N + 1) → ℝ) (ha0 : a 0 ≠ 0) (z : ℂ) (n : ℤ) :
    Ideal.Quotient.mk (connesVanSuijlekomP21Ideal a)
      (LaurentPolynomial.C z * LaurentPolynomial.T n) ∈ connesVanSuijlekomP21QuotientAdjoin a := by
  cases n with
  | ofNat k =>
      change Ideal.Quotient.mk (connesVanSuijlekomP21Ideal a)
        (LaurentPolynomial.C z * LaurentPolynomial.T (k : ℤ)) ∈
          connesVanSuijlekomP21QuotientAdjoin a
      rw [map_mul, connesVanSuijlekomP21_quotient_mk_C_eq_algebraMap,
        connesVanSuijlekomP21_quotient_nonnegative_monomial_eq_pow]
      exact (connesVanSuijlekomP21QuotientAdjoin a).mul_mem
        ((connesVanSuijlekomP21QuotientAdjoin a).algebraMap_mem z)
        ((connesVanSuijlekomP21QuotientAdjoin a).pow_mem
          (connesVanSuijlekomP21_quotient_x_mem_adjoin a) _)
  | negSucc k =>
      change Ideal.Quotient.mk (connesVanSuijlekomP21Ideal a)
        (LaurentPolynomial.C z * LaurentPolynomial.T (-((k + 1 : ℕ) : ℤ))) ∈
          connesVanSuijlekomP21QuotientAdjoin a
      rw [map_mul, connesVanSuijlekomP21_quotient_mk_C_eq_algebraMap,
        connesVanSuijlekomP21_quotient_negative_monomial_eq_pow]
      exact (connesVanSuijlekomP21QuotientAdjoin a).mul_mem
        ((connesVanSuijlekomP21QuotientAdjoin a).algebraMap_mem z)
        ((connesVanSuijlekomP21QuotientAdjoin a).pow_mem
          (connesVanSuijlekomP21_quotient_xInv_mem_adjoin a ha0) _)

/-- The corrected source quotient is generated as a complex algebra by the
Laurent-variable class. -/
theorem connesVanSuijlekomP21_quotient_adjoin_eq_top
    {N : ℕ} (a : Fin (N + 1) → ℝ) (ha0 : a 0 ≠ 0) :
    connesVanSuijlekomP21QuotientAdjoin a = ⊤ := by
  apply top_unique
  intro q hq
  clear hq
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective q
  induction p using LaurentPolynomial.induction_on' with
  | add p q hp hq =>
      rw [map_add]
      exact (connesVanSuijlekomP21QuotientAdjoin a).add_mem hp hq
  | C_mul_T n z =>
      exact connesVanSuijlekomP21_quotient_laurent_monomial_mem_adjoin a ha0 z n

/-- Polynomial presentation of the source Laurent generator. -/
def connesVanSuijlekomP21Polynomial {N : ℕ} (a : Fin (N + 1) → ℝ) : Polynomial ℂ :=
  Polynomial.ofFn (N + 1) fun j => (a j : ℂ)

/-- The polynomial presentation maps to the literal source Laurent generator. -/
theorem connesVanSuijlekomP21_toLaurent_polynomial
    {N : ℕ} (a : Fin (N + 1) → ℝ) :
    Polynomial.toLaurent (connesVanSuijlekomP21Polynomial a) =
      connesVanSuijlekomP21Generator a := by
  rw [connesVanSuijlekomP21Polynomial, Polynomial.ofFn_eq_sum_monomial, map_sum]
  simp_rw [Polynomial.toLaurent_C_mul_T]
  rfl

/-- Coefficients of the polynomial presentation are the source vector entries. -/
theorem connesVanSuijlekomP21_polynomial_coeff
    {N : ℕ} (a : Fin (N + 1) → ℝ) (i : Fin (N + 1)) :
    (connesVanSuijlekomP21Polynomial a).coeff i = (a i : ℂ) := by
  rw [connesVanSuijlekomP21Polynomial]
  exact Polynomial.ofFn_coeff_eq_val_of_lt _ i.isLt

/-- Evaluation at the quotient Laurent-variable unit agrees with the quotient
class on every nonnegative Laurent monomial. -/
theorem connesVanSuijlekomP21_eval_nonnegative_term
    {N : ℕ} (a : Fin (N + 1) → ℝ) (z : ℂ) (k : ℕ) :
    LaurentPolynomial.eval₂ (algebraMap ℂ (connesVanSuijlekomP21Quotient a))
      (connesVanSuijlekomP21QuotientXUnit a)
      (LaurentPolynomial.C z * LaurentPolynomial.T (k : ℤ)) =
      Ideal.Quotient.mk (connesVanSuijlekomP21Ideal a)
        (LaurentPolynomial.C z * LaurentPolynomial.T (k : ℤ)) := by
  rw [LaurentPolynomial.eval₂_C_mul_T_n, map_mul,
    connesVanSuijlekomP21_quotient_mk_C_eq_algebraMap,
    connesVanSuijlekomP21_quotient_nonnegative_monomial_eq_pow]
  rfl

/-- The literal source Laurent generator vanishes when evaluated at the
quotient Laurent-variable unit. -/
theorem connesVanSuijlekomP21_eval_generator_eq_zero
    {N : ℕ} (a : Fin (N + 1) → ℝ) :
    LaurentPolynomial.eval₂ (algebraMap ℂ (connesVanSuijlekomP21Quotient a))
      (connesVanSuijlekomP21QuotientXUnit a)
      (connesVanSuijlekomP21Generator a) = 0 := by
  rw [connesVanSuijlekomP21Generator, map_sum]
  calc
    ∑ j, LaurentPolynomial.eval₂ (algebraMap ℂ (connesVanSuijlekomP21Quotient a))
        (connesVanSuijlekomP21QuotientXUnit a)
        (LaurentPolynomial.C (a j : ℂ) * LaurentPolynomial.T (j : ℤ)) =
        ∑ j, Ideal.Quotient.mk (connesVanSuijlekomP21Ideal a)
          (LaurentPolynomial.C (a j : ℂ) * LaurentPolynomial.T (j : ℤ)) := by
      apply Finset.sum_congr rfl
      intro j _
      exact connesVanSuijlekomP21_eval_nonnegative_term a (a j : ℂ) (j : ℕ)
    _ = Ideal.Quotient.mk (connesVanSuijlekomP21Ideal a)
        (connesVanSuijlekomP21Generator a) := by
      rw [connesVanSuijlekomP21Generator, map_sum]
    _ = 0 := connesVanSuijlekomP21_quotient_generator_eq_zero a

/-- The source polynomial presentation vanishes at the quotient Laurent-variable
class. -/
theorem connesVanSuijlekomP21_quotient_polynomial_eval_eq_zero
    {N : ℕ} (a : Fin (N + 1) → ℝ) :
    Polynomial.eval₂ (algebraMap ℂ (connesVanSuijlekomP21Quotient a))
      (connesVanSuijlekomP21QuotientX a)
      (connesVanSuijlekomP21Polynomial a) = 0 := by
  have h := connesVanSuijlekomP21_eval_generator_eq_zero a
  rw [← connesVanSuijlekomP21_toLaurent_polynomial,
    LaurentPolynomial.eval₂_toLaurent] at h
  exact h

/-- The normalized monic source polynomial vanishes at the quotient
Laurent-variable class. -/
theorem connesVanSuijlekomP21_quotient_monic_polynomial_eval_eq_zero
    {N : ℕ} (a : Fin (N + 1) → ℝ) :
    Polynomial.eval₂ (algebraMap ℂ (connesVanSuijlekomP21Quotient a))
      (connesVanSuijlekomP21QuotientX a)
      (Polynomial.C ((a (Fin.last N) : ℂ)⁻¹) * connesVanSuijlekomP21Polynomial a) = 0 := by
  rw [Polynomial.eval₂_mul, Polynomial.eval₂_C,
    connesVanSuijlekomP21_quotient_polynomial_eval_eq_zero, mul_zero]

/-- A nonzero final source coefficient gives the exact polynomial degree. -/
theorem connesVanSuijlekomP21_polynomial_natDegree
    {N : ℕ} (a : Fin (N + 1) → ℝ) (hN : a (Fin.last N) ≠ 0) :
    (connesVanSuijlekomP21Polynomial a).natDegree = N := by
  apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
  · change (Polynomial.ofFn (N + 1) fun j => (a j : ℂ)).natDegree ≤ N
    exact Nat.le_of_lt_succ
      (Polynomial.ofFn_natDegree_lt (Nat.succ_le_succ (Nat.zero_le N)) _)
  · have hcoeff := connesVanSuijlekomP21_polynomial_coeff a (Fin.last N)
    have hcoeffN : (connesVanSuijlekomP21Polynomial a).coeff N =
        (a (Fin.last N) : ℂ) := by
      simpa using hcoeff
    rw [hcoeffN]
    exact_mod_cast hN

/-- Normalizing by the nonzero final coefficient gives the monic polynomial
whose quotient has the desired `N`-element power basis. -/
theorem connesVanSuijlekomP21_polynomial_monic_normalized
    {N : ℕ} (a : Fin (N + 1) → ℝ) (hN : a (Fin.last N) ≠ 0) :
    (Polynomial.C ((a (Fin.last N) : ℂ)⁻¹) *
      connesVanSuijlekomP21Polynomial a).Monic := by
  apply Polynomial.monic_C_mul_of_mul_leadingCoeff_eq_one
  rw [Polynomial.leadingCoeff, connesVanSuijlekomP21_polynomial_natDegree a hN]
  have hcoeff := connesVanSuijlekomP21_polynomial_coeff a (Fin.last N)
  have hcoeffN : (connesVanSuijlekomP21Polynomial a).coeff N =
      (a (Fin.last N) : ℂ) := by
    simpa using hcoeff
  rw [hcoeffN]
  field_simp

/-- The explicit Laurent inverse formula for a polynomial root whose constant
coefficient is nonzero. -/
theorem connesVanSuijlekomP21_adjoin_root_mul_inverse
    (f : ℂ[X]) (hf0 : f.coeff 0 ≠ 0) :
    AdjoinRoot.root f *
      (-((algebraMap ℂ (AdjoinRoot f)) ((f.coeff 0)⁻¹)) *
        Polynomial.aeval (AdjoinRoot.root f) f.divX) = 1 := by
    let c : AdjoinRoot f := (algebraMap ℂ (AdjoinRoot f)) (f.coeff 0)
    let cInv : AdjoinRoot f := (algebraMap ℂ (AdjoinRoot f)) ((f.coeff 0)⁻¹)
    change AdjoinRoot.root f *
      (-cInv * Polynomial.aeval (AdjoinRoot.root f) f.divX) = 1
    have hroot : Polynomial.aeval (AdjoinRoot.root f) f = 0 := by
      rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
    have hsplit := congrArg (Polynomial.aeval (AdjoinRoot.root f))
      (Polynomial.divX_mul_X_add f)
    rw [map_add, Polynomial.aeval_C, Polynomial.aeval_mul,
      Polynomial.aeval_X, hroot] at hsplit
    have hprod : Polynomial.aeval (AdjoinRoot.root f) f.divX * AdjoinRoot.root f = -c := by
      simpa [c] using eq_neg_of_add_eq_zero_left hsplit
    have hscalar : cInv * c = 1 := by
      simp [c, cInv, ← map_mul, inv_mul_cancel₀ hf0]
    calc
      AdjoinRoot.root f *
          (-cInv *
            Polynomial.aeval (AdjoinRoot.root f) f.divX) =
          -cInv * (Polynomial.aeval (AdjoinRoot.root f) f.divX * AdjoinRoot.root f) := by ring
      _ = -cInv * (-c) := by rw [hprod]
      _ = cInv * c := by ring
      _ = 1 := hscalar

/-- A root of a complex polynomial with nonzero constant coefficient is a unit
in its adjunction algebra. This realizes Laurent evaluation at that root. -/
def connesVanSuijlekomP21AdjoinRootUnit (f : ℂ[X]) (hf0 : f.coeff 0 ≠ 0) :
    (AdjoinRoot f)ˣ where
  val := AdjoinRoot.root f
  inv := -((algebraMap ℂ (AdjoinRoot f)) ((f.coeff 0)⁻¹)) *
    Polynomial.aeval (AdjoinRoot.root f) f.divX
  val_inv := connesVanSuijlekomP21_adjoin_root_mul_inverse f hf0
  inv_val := by
    rw [mul_comm]
    exact connesVanSuijlekomP21_adjoin_root_mul_inverse f hf0

/-- The constant coefficient of the polynomial presentation is its first
source coefficient. -/
theorem connesVanSuijlekomP21_polynomial_coeff_zero
    {N : ℕ} (a : Fin (N + 1) → ℝ) :
    (connesVanSuijlekomP21Polynomial a).coeff 0 = (a 0 : ℂ) := by
  simpa using connesVanSuijlekomP21_polynomial_coeff a (0 : Fin (N + 1))

/-- The source polynomial root is a unit under corrected clause (2)'s nonzero
constant-coefficient hypothesis. -/
def connesVanSuijlekomP21PolynomialRootUnit
    {N : ℕ} (a : Fin (N + 1) → ℝ) (ha0 : a 0 ≠ 0) :
    (AdjoinRoot (connesVanSuijlekomP21Polynomial a))ˣ :=
  connesVanSuijlekomP21AdjoinRootUnit (connesVanSuijlekomP21Polynomial a) (by
    rw [connesVanSuijlekomP21_polynomial_coeff_zero]
    exact_mod_cast ha0)

/-- Laurent evaluation at the unit root of the source polynomial. -/
def connesVanSuijlekomP21LaurentToPolynomialRoot
    {N : ℕ} (a : Fin (N + 1) → ℝ) (ha0 : a 0 ≠ 0) :
    LaurentPolynomial ℂ →ₐ[ℂ] AdjoinRoot (connesVanSuijlekomP21Polynomial a) where
  toRingHom := LaurentPolynomial.eval₂ (AdjoinRoot.of (connesVanSuijlekomP21Polynomial a))
    (connesVanSuijlekomP21PolynomialRootUnit a ha0)
  commutes' z := by
    change LaurentPolynomial.eval₂ (AdjoinRoot.of (connesVanSuijlekomP21Polynomial a))
      (connesVanSuijlekomP21PolynomialRootUnit a ha0) (LaurentPolynomial.C z) = _
    simp [AdjoinRoot.algebraMap_eq]

/-- The source Laurent relation vanishes at its polynomial root. -/
theorem connesVanSuijlekomP21_laurent_to_polynomial_root_generator
    {N : ℕ} (a : Fin (N + 1) → ℝ) (ha0 : a 0 ≠ 0) :
    connesVanSuijlekomP21LaurentToPolynomialRoot a ha0
      (connesVanSuijlekomP21Generator a) = 0 := by
  rw [← connesVanSuijlekomP21_toLaurent_polynomial]
  change LaurentPolynomial.eval₂ (AdjoinRoot.of (connesVanSuijlekomP21Polynomial a))
    (connesVanSuijlekomP21PolynomialRootUnit a ha0)
    (Polynomial.toLaurent (connesVanSuijlekomP21Polynomial a)) = 0
  rw [LaurentPolynomial.eval₂_toLaurent]
  exact AdjoinRoot.eval₂_root _

/-- The quotient Laurent algebra maps back to the polynomial-root algebra. -/
def connesVanSuijlekomP21QuotientToPolynomialRoot
    {N : ℕ} (a : Fin (N + 1) → ℝ) (ha0 : a 0 ≠ 0) :
    connesVanSuijlekomP21Quotient a →ₐ[ℂ] AdjoinRoot (connesVanSuijlekomP21Polynomial a) :=
  Ideal.Quotient.liftₐ (connesVanSuijlekomP21Ideal a)
    (connesVanSuijlekomP21LaurentToPolynomialRoot a ha0) (by
      intro f hf
      rw [connesVanSuijlekomP21Ideal, Ideal.mem_span_singleton'] at hf
      obtain ⟨g, rfl⟩ := hf
      rw [map_mul, connesVanSuijlekomP21_laurent_to_polynomial_root_generator]
      exact mul_zero _)

/-- The root algebra maps to the Laurent quotient by sending its root to the
Laurent-variable class. -/
def connesVanSuijlekomP21PolynomialRootToQuotient
    {N : ℕ} (a : Fin (N + 1) → ℝ) :
    AdjoinRoot (connesVanSuijlekomP21Polynomial a) →ₐ[ℂ]
      connesVanSuijlekomP21Quotient a :=
  AdjoinRoot.liftAlgHom (connesVanSuijlekomP21Polynomial a)
    (Algebra.ofId ℂ (connesVanSuijlekomP21Quotient a))
    (connesVanSuijlekomP21QuotientX a) (by
      simpa using connesVanSuijlekomP21_quotient_polynomial_eval_eq_zero a)

/-- The root-to-quotient map sends the adjoined root to `X`. -/
theorem connesVanSuijlekomP21_polynomial_root_to_quotient_root
    {N : ℕ} (a : Fin (N + 1) → ℝ) :
    connesVanSuijlekomP21PolynomialRootToQuotient a
      (AdjoinRoot.root (connesVanSuijlekomP21Polynomial a)) =
      connesVanSuijlekomP21QuotientX a := by
  rw [connesVanSuijlekomP21PolynomialRootToQuotient, AdjoinRoot.liftAlgHom_root]

/-- The quotient-to-root map sends `X` to the adjoined polynomial root. -/
theorem connesVanSuijlekomP21_quotient_to_polynomial_root_x
    {N : ℕ} (a : Fin (N + 1) → ℝ) (ha0 : a 0 ≠ 0) :
    connesVanSuijlekomP21QuotientToPolynomialRoot a ha0
      (connesVanSuijlekomP21QuotientX a) =
      AdjoinRoot.root (connesVanSuijlekomP21Polynomial a) := by
  change ((connesVanSuijlekomP21QuotientToPolynomialRoot a ha0).comp
    (Ideal.Quotient.mkₐ ℂ (connesVanSuijlekomP21Ideal a))) (LaurentPolynomial.T 1) = _
  rw [show (connesVanSuijlekomP21QuotientToPolynomialRoot a ha0).comp
      (Ideal.Quotient.mkₐ ℂ (connesVanSuijlekomP21Ideal a)) =
        connesVanSuijlekomP21LaurentToPolynomialRoot a ha0 by
      apply Ideal.Quotient.liftₐ_comp]
  change LaurentPolynomial.eval₂ (AdjoinRoot.of (connesVanSuijlekomP21Polynomial a))
    (connesVanSuijlekomP21PolynomialRootUnit a ha0) (LaurentPolynomial.T 1) = _
  rw [show (1 : ℤ) = (1 : ℕ) by norm_num, LaurentPolynomial.eval₂_T_n]
  simp [connesVanSuijlekomP21PolynomialRootUnit, connesVanSuijlekomP21AdjoinRootUnit]

/-- The two polynomial/Laurent maps compose to the identity on the quotient. -/
theorem connesVanSuijlekomP21_polynomial_root_quotient_composite
    {N : ℕ} (a : Fin (N + 1) → ℝ) (ha0 : a 0 ≠ 0) :
    (connesVanSuijlekomP21PolynomialRootToQuotient a).comp
      (connesVanSuijlekomP21QuotientToPolynomialRoot a ha0) =
      AlgHom.id ℂ (connesVanSuijlekomP21Quotient a) := by
  apply AlgHom.ext_of_adjoin_eq_top
    (show Algebra.adjoin ℂ {connesVanSuijlekomP21QuotientX a} = ⊤ by
      exact connesVanSuijlekomP21_quotient_adjoin_eq_top a ha0)
  intro x hx
  rw [Set.mem_singleton_iff.mp hx, AlgHom.comp_apply,
    connesVanSuijlekomP21_quotient_to_polynomial_root_x,
    connesVanSuijlekomP21_polynomial_root_to_quotient_root]
  rfl

/-- The two polynomial/Laurent maps compose to the identity on the root
algebra. -/
theorem connesVanSuijlekomP21_quotient_polynomial_root_composite
    {N : ℕ} (a : Fin (N + 1) → ℝ) (ha0 : a 0 ≠ 0) :
    (connesVanSuijlekomP21QuotientToPolynomialRoot a ha0).comp
      (connesVanSuijlekomP21PolynomialRootToQuotient a) =
      AlgHom.id ℂ (AdjoinRoot (connesVanSuijlekomP21Polynomial a)) := by
  ext
  simp only [AlgHom.comp_apply, AlgHom.id_apply]
  rw [connesVanSuijlekomP21_polynomial_root_to_quotient_root,
    connesVanSuijlekomP21_quotient_to_polynomial_root_x]

/-- Exact polynomial presentation of the corrected Laurent quotient. -/
def connesVanSuijlekomP21PolynomialRootEquivQuotient
    {N : ℕ} (a : Fin (N + 1) → ℝ) (ha0 : a 0 ≠ 0) :
    AdjoinRoot (connesVanSuijlekomP21Polynomial a) ≃ₐ[ℂ]
      connesVanSuijlekomP21Quotient a where
  __ := connesVanSuijlekomP21PolynomialRootToQuotient a
  invFun := connesVanSuijlekomP21QuotientToPolynomialRoot a ha0
  left_inv x := by
    change connesVanSuijlekomP21QuotientToPolynomialRoot a ha0
      (connesVanSuijlekomP21PolynomialRootToQuotient a x) = x
    exact DFunLike.congr_fun (connesVanSuijlekomP21_quotient_polynomial_root_composite a ha0) x
  right_inv x := by
    change connesVanSuijlekomP21PolynomialRootToQuotient a
      (connesVanSuijlekomP21QuotientToPolynomialRoot a ha0 x) = x
    exact DFunLike.congr_fun (connesVanSuijlekomP21_polynomial_root_quotient_composite a ha0) x

/-- The nonzero final source coefficient makes the polynomial presentation
nonzero. -/
theorem connesVanSuijlekomP21_polynomial_ne_zero
    {N : ℕ} (a : Fin (N + 1) → ℝ) (hN : a (Fin.last N) ≠ 0) :
    connesVanSuijlekomP21Polynomial a ≠ 0 := by
  intro hP
  have hcoeff := connesVanSuijlekomP21_polynomial_coeff a (Fin.last N)
  rw [hP] at hcoeff
  simp at hcoeff
  exact hN (by exact_mod_cast hcoeff.symm)

/-- The Laurent quotient carries the transported power basis generated by its
Laurent-variable class. -/
noncomputable def connesVanSuijlekomP21QuotientPowerBasis
    {N : ℕ} (a : Fin (N + 1) → ℝ) (ha0 : a 0 ≠ 0) (hN : a (Fin.last N) ≠ 0) :
    PowerBasis ℂ (connesVanSuijlekomP21Quotient a) :=
  (AdjoinRoot.powerBasis (connesVanSuijlekomP21_polynomial_ne_zero a hN)).map
    (connesVanSuijlekomP21PolynomialRootEquivQuotient a ha0)

/-- The transported power-basis generator is exactly the source quotient class
of `X`. -/
theorem connesVanSuijlekomP21_quotient_power_basis_gen
    {N : ℕ} (a : Fin (N + 1) → ℝ) (ha0 : a 0 ≠ 0) (hN : a (Fin.last N) ≠ 0) :
    (connesVanSuijlekomP21QuotientPowerBasis a ha0 hN).gen =
      connesVanSuijlekomP21QuotientX a := by
  rw [connesVanSuijlekomP21QuotientPowerBasis, PowerBasis.map_gen,
    AdjoinRoot.powerBasis_gen]
  change connesVanSuijlekomP21PolynomialRootToQuotient a
    (AdjoinRoot.root (connesVanSuijlekomP21Polynomial a)) = _
  exact connesVanSuijlekomP21_polynomial_root_to_quotient_root a

/-- The transported power basis has the source degree. -/
theorem connesVanSuijlekomP21_quotient_power_basis_dim
    {N : ℕ} (a : Fin (N + 1) → ℝ) (ha0 : a 0 ≠ 0) (hN : a (Fin.last N) ≠ 0) :
    (connesVanSuijlekomP21QuotientPowerBasis a ha0 hN).dim = N := by
  rw [connesVanSuijlekomP21QuotientPowerBasis, PowerBasis.map_dim,
    AdjoinRoot.powerBasis_dim, connesVanSuijlekomP21_polynomial_natDegree a hN]

/-- The literal source monomials `1,X,…,X^(N-1)` as a basis of the corrected
Laurent quotient. -/
noncomputable def connesVanSuijlekomP21QuotientMonomialBasis
    {N : ℕ} (a : Fin (N + 1) → ℝ) (ha0 : a 0 ≠ 0) (hN : a (Fin.last N) ≠ 0) :
    Module.Basis (Fin N) ℂ (connesVanSuijlekomP21Quotient a) :=
  (connesVanSuijlekomP21QuotientPowerBasis a ha0 hN).basis.reindex
    (finCongr (connesVanSuijlekomP21_quotient_power_basis_dim a ha0 hN))

/-- Each vector in the corrected quotient basis is literally the indicated
source Laurent monomial class. -/
theorem connesVanSuijlekomP21_quotient_monomial_basis_apply
    {N : ℕ} (a : Fin (N + 1) → ℝ) (ha0 : a 0 ≠ 0) (hN : a (Fin.last N) ≠ 0)
    (i : Fin N) :
    connesVanSuijlekomP21QuotientMonomialBasis a ha0 hN i =
      Ideal.Quotient.mk (connesVanSuijlekomP21Ideal a) (LaurentPolynomial.T (i : ℤ)) := by
  rw [connesVanSuijlekomP21QuotientMonomialBasis, Module.Basis.reindex_apply,
    PowerBasis.basis_eq_pow, connesVanSuijlekomP21_quotient_power_basis_gen,
    finCongr_symm_apply, Fin.val_cast,
    ← connesVanSuijlekomP21_quotient_nonnegative_monomial_eq_pow]

/-- The canonical involution of the source Laurent algebra: conjugate
coefficients and reverse the Laurent exponent. -/
def connesVanSuijlekomP21Star : LaurentPolynomial ℂ →+* LaurentPolynomial ℂ :=
  (LaurentPolynomial.invert (R := ℂ)).toRingEquiv.toRingHom.comp
    (AddMonoidAlgebra.mapRingHom ℤ (starRingEnd ℂ))

/-- Action of the source involution on a Laurent monomial. -/
theorem connesVanSuijlekomP21_star_C_mul_T (z : ℂ) (n : ℤ) :
    connesVanSuijlekomP21Star (LaurentPolynomial.C z * LaurentPolynomial.T n) =
      LaurentPolynomial.C (star z) * LaurentPolynomial.T (-n) := by
  simp only [connesVanSuijlekomP21Star, RingHom.comp_apply, map_mul]
  rw [show AddMonoidAlgebra.mapRingHom ℤ (starRingEnd ℂ) (LaurentPolynomial.C z) =
      LaurentPolynomial.C (star z) by
    apply LaurentPolynomial.ext
    intro k
    rw [AddMonoidAlgebra.coeff_mapRingHom, LaurentPolynomial.C_apply,
      LaurentPolynomial.C_apply]
    by_cases hk : k = 0 <;> simp [hk],
    show AddMonoidAlgebra.mapRingHom ℤ (starRingEnd ℂ) (LaurentPolynomial.T n) =
      LaurentPolynomial.T n by
    apply LaurentPolynomial.ext
    intro k
    rw [AddMonoidAlgebra.coeff_mapRingHom]
    by_cases hk : n = k <;> simp [LaurentPolynomial.T_apply, hk]]
  simp

/-- The canonical source involution is involutive. -/
theorem connesVanSuijlekomP21_star_involutive (p : LaurentPolynomial ℂ) :
    connesVanSuijlekomP21Star (connesVanSuijlekomP21Star p) = p := by
  apply LaurentPolynomial.ext
  intro n
  simp [connesVanSuijlekomP21Star, AddMonoidAlgebra.coeff_mapRingHom]

/-- The spanning consequence of the source's clause (2) when `N = 1`: the
sole listed monomial `1` would span the Laurent quotient. -/
def connesVanSuijlekomP21SingleMonomialSpans (J : Ideal (LaurentPolynomial ℂ)) : Prop :=
  ∀ z : LaurentPolynomial ℂ, ∃ a : ℂ,
    Ideal.Quotient.mk J z = Ideal.Quotient.mk J (LaurentPolynomial.C a)

/-- The zero source kernel vector generates the zero Laurent polynomial. -/
theorem connesVanSuijlekomP21_generator_zero :
    connesVanSuijlekomP21Generator (fun _ : Fin 2 => (0 : ℝ)) = 0 := by
  simp [connesVanSuijlekomP21Generator]

/-- Its source ideal is therefore the zero ideal. -/
theorem connesVanSuijlekomP21_ideal_zero :
    connesVanSuijlekomP21Ideal (fun _ : Fin 2 => (0 : ℝ)) = ⊥ := by
  rw [connesVanSuijlekomP21Ideal, connesVanSuijlekomP21_generator_zero]
  simp

/-- A single constant Laurent monomial cannot span the full Laurent algebra. -/
theorem connesVanSuijlekomP21_singleMonomialSpans_bot_false :
    ¬ connesVanSuijlekomP21SingleMonomialSpans (⊥ : Ideal (LaurentPolynomial ℂ)) := by
  intro h
  obtain ⟨a, ha⟩ := h (LaurentPolynomial.T 1)
  have hzero : Ideal.Quotient.mk (⊥ : Ideal (LaurentPolynomial ℂ))
      (LaurentPolynomial.T 1 - LaurentPolynomial.C a) = 0 := by
    rw [map_sub, ha, sub_self]
  have hmem : LaurentPolynomial.T 1 - LaurentPolynomial.C a ∈
      (⊥ : Ideal (LaurentPolynomial ℂ)) :=
    Ideal.Quotient.eq_zero_iff_mem.mp hzero
  have heq : LaurentPolynomial.T 1 - LaurentPolynomial.C a = 0 := by
    simpa using hmem
  have hcoeff := congrArg (fun p : LaurentPolynomial ℂ => p.coeff 1) heq
  simp at hcoeff

/-- **Source obstruction for Proposition 2.1(2).**

The printed hypotheses admit the zero kernel vector, but for that vector the
claimed one-monomial quotient spanning statement is false. -/
theorem connesVanSuijlekomP21_zero_kernel_clauseTwo_obstruction :
    ¬ connesVanSuijlekomP21SingleMonomialSpans
      (connesVanSuijlekomP21Ideal (fun _ : Fin 2 => (0 : ℝ))) := by
  rw [connesVanSuijlekomP21_ideal_zero]
  exact connesVanSuijlekomP21_singleMonomialSpans_bot_false

/-- The zero vector satisfies every finite Toeplitz kernel equation, exposing
the missing nonzero-vector hypothesis in the printed proposition. -/
theorem connesVanSuijlekomP21_zero_vector_in_kernel
    {N : ℕ} (c : ℕ → ℝ) :
    connesVanSuijlekomRealToeplitz N c *ᵥ (fun _ => (0 : ℂ)) = 0 := by
  ext i
  simp [Matrix.mulVec]

/-- The source rank hypothesis gives the exact one-dimensional complex kernel
needed for the corrected quotient construction. -/
theorem connesVanSuijlekomP21_kernel_finrank_eq_one
    {N : ℕ} (c : ℕ → ℝ)
    (hRank : (connesVanSuijlekomRealToeplitz N c).rank = N) :
    Module.finrank ℂ
      (LinearMap.ker (connesVanSuijlekomRealToeplitz N c).mulVecLin) = 1 := by
  have hsum := LinearMap.finrank_range_add_finrank_ker
    (connesVanSuijlekomRealToeplitz N c).mulVecLin
  change (connesVanSuijlekomRealToeplitz N c).rank +
      Module.finrank ℂ (LinearMap.ker (connesVanSuijlekomRealToeplitz N c).mulVecLin) =
        Module.finrank ℂ (Fin (N + 1) → ℂ) at hsum
  rw [hRank, Module.finrank_fintype_fun_eq_card] at hsum
  simp only [Fintype.card_fin] at hsum
  omega

/-- The source real Toeplitz matrix is invariant under reversal of both
finite indices. -/
theorem connesVanSuijlekomP21_toeplitz_reverse_entries
    (N : ℕ) (c : ℕ → ℝ) (i j : Fin (N + 1)) :
    connesVanSuijlekomRealToeplitz N c i.rev j.rev =
      connesVanSuijlekomRealToeplitz N c i j := by
  have hi : (i.rev : ℤ) + (i : ℤ) = N := by
    exact_mod_cast i.rev_add_cast
  have hj : (j.rev : ℤ) + (j : ℤ) = N := by
    exact_mod_cast j.rev_add_cast
  have hdiff : (i.rev : ℤ) - (j.rev : ℤ) = -((i : ℤ) - (j : ℤ)) := by omega
  simp only [connesVanSuijlekomRealToeplitz, circleToeplitzGram]
  rw [hdiff, Int.natAbs_neg]

/-- Reversal of a finite Fourier coefficient vector. -/
def connesVanSuijlekomP21ReverseVector {N : ℕ} (v : Fin (N + 1) → ℂ) :
    Fin (N + 1) → ℂ :=
  fun i => v i.rev

/-- Reflection preserves the kernel of every source real Toeplitz matrix. -/
theorem connesVanSuijlekomP21_reverse_vector_in_kernel
    {N : ℕ} (c : ℕ → ℝ) (a : Fin (N + 1) → ℂ)
    (hker : connesVanSuijlekomRealToeplitz N c *ᵥ a = 0) :
    connesVanSuijlekomRealToeplitz N c *ᵥ connesVanSuijlekomP21ReverseVector a = 0 := by
  ext i
  rw [Matrix.mulVec]
  calc
    ∑ j, connesVanSuijlekomRealToeplitz N c i j * connesVanSuijlekomP21ReverseVector a j =
        ∑ j, connesVanSuijlekomRealToeplitz N c i j.rev * a j := by
      have hsum := Equiv.sum_comp (Fin.revPerm : Equiv.Perm (Fin (N + 1)))
        (fun j => connesVanSuijlekomRealToeplitz N c i j *
          connesVanSuijlekomP21ReverseVector a j)
      simpa [connesVanSuijlekomP21ReverseVector] using hsum.symm
    _ = ∑ j, connesVanSuijlekomRealToeplitz N c i.rev j * a j := by
      apply Finset.sum_congr rfl
      intro j _
      rw [← connesVanSuijlekomP21_toeplitz_reverse_entries N c i j.rev]
      simp
    _ = 0 := by
      exact congrFun hker i.rev

/-- Reversal is an involution on finite Fourier coefficient vectors. -/
theorem connesVanSuijlekomP21_reverse_reverse
    {N : ℕ} (v : Fin (N + 1) → ℂ) :
    connesVanSuijlekomP21ReverseVector (connesVanSuijlekomP21ReverseVector v) = v := by
  funext i
  simp [connesVanSuijlekomP21ReverseVector]

/-- Reversal commutes with complex scalar multiplication. -/
theorem connesVanSuijlekomP21_reverse_smul
    {N : ℕ} (z : ℂ) (v : Fin (N + 1) → ℂ) :
    connesVanSuijlekomP21ReverseVector (z • v) =
      z • connesVanSuijlekomP21ReverseVector v := by
  funext i
  simp [connesVanSuijlekomP21ReverseVector]

/-- A reversal eigenvector gives the Laurent-generator relation needed for
the corrected Proposition 2.1 involution clause. -/
theorem connesVanSuijlekomP21_star_generator_eq_reflection
    {N : ℕ} (a : Fin (N + 1) → ℝ) (ε : ℂ)
    (hrev : connesVanSuijlekomP21ReverseVector (fun j => (a j : ℂ)) =
      ε • (fun j => (a j : ℂ))) :
    connesVanSuijlekomP21Star (connesVanSuijlekomP21Generator a) =
      LaurentPolynomial.C ε * LaurentPolynomial.T (-(N : ℤ)) *
        connesVanSuijlekomP21Generator a := by
  rw [connesVanSuijlekomP21Generator, map_sum]
  simp_rw [connesVanSuijlekomP21_star_C_mul_T]
  have hstarReal (x : ℝ) : star (x : ℂ) = (x : ℂ) := by simp
  simp_rw [hstarReal]
  rw [Finset.mul_sum]
  rw [← Equiv.sum_comp (Fin.revPerm : Equiv.Perm (Fin (N + 1)))]
  apply Finset.sum_congr rfl
  intro j _
  rw [Fin.revPerm_apply]
  have hexp : (j.rev : ℤ) - N = -(j : ℤ) := by
    have hj : (j.rev : ℤ) + (j : ℤ) = N := by
      exact_mod_cast j.rev_add_cast
    omega
  have hcoeff := congrFun hrev j
  change (a j.rev : ℂ) = ε * (a j : ℂ) at hcoeff
  calc
    LaurentPolynomial.C (a j.rev : ℂ) * LaurentPolynomial.T (-(j.rev : ℤ)) =
        LaurentPolynomial.C (ε * (a j : ℂ)) * LaurentPolynomial.T (-(j.rev : ℤ)) := by
      rw [hcoeff]
    _ = LaurentPolynomial.C (ε * (a j : ℂ)) *
        LaurentPolynomial.T (-(N : ℤ) + (j : ℤ)) := by
      congr 2
      omega
    _ = LaurentPolynomial.C ε * LaurentPolynomial.T (-(N : ℤ)) *
        (LaurentPolynomial.C (a j : ℂ) * LaurentPolynomial.T (j : ℤ)) := by
      rw [LaurentPolynomial.T_add, LaurentPolynomial.C.map_mul]
      exact mul_mul_mul_comm _ _ _ _

/-- Membership in an ideal is closed under the source Laurent involution. -/
def connesVanSuijlekomP21StarClosed (J : Ideal (LaurentPolynomial ℂ)) : Prop :=
  ∀ ⦃p⦄, p ∈ J → connesVanSuijlekomP21Star p ∈ J

/-- Under the corrected reversal relation, the source principal ideal is
closed under its Laurent involution. -/
theorem connesVanSuijlekomP21_star_ideal_closed
    {N : ℕ} (a : Fin (N + 1) → ℝ) (ε : ℂ)
    (hrev : connesVanSuijlekomP21ReverseVector (fun j => (a j : ℂ)) =
      ε • (fun j => (a j : ℂ))) :
    connesVanSuijlekomP21StarClosed (connesVanSuijlekomP21Ideal a) := by
  intro p hp
  rw [connesVanSuijlekomP21Ideal] at hp ⊢
  obtain ⟨q, hq⟩ := Ideal.mem_span_singleton'.mp hp
  apply Ideal.mem_span_singleton'.mpr
  refine ⟨connesVanSuijlekomP21Star q *
    (LaurentPolynomial.C ε * LaurentPolynomial.T (-(N : ℤ))), ?_⟩
  calc
    connesVanSuijlekomP21Star q *
        (LaurentPolynomial.C ε * LaurentPolynomial.T (-(N : ℤ))) *
        connesVanSuijlekomP21Generator a =
        connesVanSuijlekomP21Star q *
          ((LaurentPolynomial.C ε * LaurentPolynomial.T (-(N : ℤ))) *
            connesVanSuijlekomP21Generator a) := by rw [mul_assoc]
    _ = connesVanSuijlekomP21Star q *
        connesVanSuijlekomP21Star (connesVanSuijlekomP21Generator a) := by
      rw [connesVanSuijlekomP21_star_generator_eq_reflection a ε hrev]
    _ = connesVanSuijlekomP21Star
        (q * connesVanSuijlekomP21Generator a) := by rw [map_mul]
    _ = connesVanSuijlekomP21Star p := by rw [hq]

/-- Corrected Proposition 2.1(1): the principal Laurent ideal is invariant
under the source involution. -/
theorem connesVanSuijlekomP21_star_ideal_stable
    {N : ℕ} (a : Fin (N + 1) → ℝ) (ε : ℂ)
    (hrev : connesVanSuijlekomP21ReverseVector (fun j => (a j : ℂ)) =
      ε • (fun j => (a j : ℂ))) (p : LaurentPolynomial ℂ) :
    p ∈ connesVanSuijlekomP21Ideal a ↔
      connesVanSuijlekomP21Star p ∈ connesVanSuijlekomP21Ideal a := by
  constructor
  · intro hp
    exact (connesVanSuijlekomP21_star_ideal_closed a ε hrev) hp
  · intro hp
    have hstar := (connesVanSuijlekomP21_star_ideal_closed a ε hrev) hp
    simpa only [connesVanSuijlekomP21_star_involutive] using hstar

/-- The one-dimensional source kernel is palindromic or anti-palindromic:
reversing a nonzero real kernel vector multiplies it by a scalar whose square
is one. -/
theorem connesVanSuijlekomP21_reverse_vector_smul
    {N : ℕ} (c : ℕ → ℝ)
    (hRank : (connesVanSuijlekomRealToeplitz N c).rank = N)
    (a : Fin (N + 1) → ℝ)
    (hker : connesVanSuijlekomRealToeplitz N c *ᵥ (fun j => (a j : ℂ)) = 0)
    (ha : a ≠ 0) :
    ∃ ε : ℂ, ε ^ 2 = 1 ∧
      connesVanSuijlekomP21ReverseVector (fun j => (a j : ℂ)) = ε • (fun j => (a j : ℂ)) := by
  let M := connesVanSuijlekomRealToeplitz N c
  let v : Fin (N + 1) → ℂ := fun j => (a j : ℂ)
  have hv : v ≠ 0 := by
    intro h
    apply ha
    funext j
    have hj : (a j : ℂ) = 0 := by
      simpa [v] using congrFun h j
    exact_mod_cast hj
  let K := LinearMap.ker M.mulVecLin
  have hvK : v ∈ K := by
    exact hker
  have hrevK : connesVanSuijlekomP21ReverseVector v ∈ K := by
    exact connesVanSuijlekomP21_reverse_vector_in_kernel c v hker
  let x : K := ⟨v, hvK⟩
  let y : K := ⟨connesVanSuijlekomP21ReverseVector v, hrevK⟩
  have hx : x ≠ 0 := by
    intro h
    apply hv
    exact congrArg Subtype.val h
  have hdim : Module.finrank ℂ K = 1 := by
    simpa [K, M] using connesVanSuijlekomP21_kernel_finrank_eq_one c hRank
  obtain ⟨ε, hε⟩ := (finrank_eq_one_iff_of_nonzero' x hx).mp hdim y
  have hvec : ε • v = connesVanSuijlekomP21ReverseVector v := by
    exact congrArg Subtype.val hε
  have hrev : connesVanSuijlekomP21ReverseVector v = ε • v := hvec.symm
  have hsqVec : ε ^ 2 • v = v := by
    calc
      ε ^ 2 • v = ε • (ε • v) := by rw [pow_two, smul_smul]
      _ = ε • connesVanSuijlekomP21ReverseVector v := by rw [hrev]
      _ = connesVanSuijlekomP21ReverseVector (ε • v) :=
        (connesVanSuijlekomP21_reverse_smul ε v).symm
      _ = connesVanSuijlekomP21ReverseVector (connesVanSuijlekomP21ReverseVector v) := by
        rw [hrev]
      _ = v := connesVanSuijlekomP21_reverse_reverse v
  obtain ⟨j, hj⟩ : ∃ j, v j ≠ 0 := by
    by_contra h
    push Not at h
    exact hv (funext h)
  have hpoint := congrFun hsqVec j
  have hsq : ε ^ 2 = 1 := by
    apply (mul_right_cancel₀ hj)
    simpa [smul_eq_mul] using hpoint
  exact ⟨ε, hsq, hrev⟩

/-- Corrected Proposition 2.1(1). The omitted nonzero-kernel-vector hypothesis
forces the source Laurent ideal to be invariant under its involution. -/
theorem connesVanSuijlekomP21_corrected_clauseOne
    {N : ℕ} (c : ℕ → ℝ)
    (hRank : (connesVanSuijlekomRealToeplitz N c).rank = N)
    (a : Fin (N + 1) → ℝ)
    (hker : connesVanSuijlekomRealToeplitz N c *ᵥ (fun j => (a j : ℂ)) = 0)
    (ha : a ≠ 0) (p : LaurentPolynomial ℂ) :
    p ∈ connesVanSuijlekomP21Ideal a ↔
      connesVanSuijlekomP21Star p ∈ connesVanSuijlekomP21Ideal a := by
  obtain ⟨ε, _, hrev⟩ :=
    connesVanSuijlekomP21_reverse_vector_smul c hRank a hker ha
  exact connesVanSuijlekomP21_star_ideal_stable a ε hrev p

/-- Positive survivor of the Proposition 2.1 obstruction.  Under the source
Toeplitz hypotheses, a *nonzero* real kernel vector has nonzero leading
coefficient, so its Laurent generator can support the quotient construction.

This uses the independently formalized Toeplitz root theorem, not the flawed
printed quotient argument. -/
theorem connesVanSuijlekomP21_nonzero_kernel_head_ne_zero
    {N : ℕ} (c : ℕ → ℝ)
    (hG : (connesVanSuijlekomRealToeplitz N c).PosSemidef)
    (hRank : (connesVanSuijlekomRealToeplitz N c).rank = N)
    (a : Fin (N + 1) → ℝ)
    (hker : connesVanSuijlekomRealToeplitz N c *ᵥ (fun j => (a j : ℂ)) = 0)
    (ha : a ≠ 0) :
    a 0 ≠ 0 := by
  intro ha0
  let p := finiteToeplitzKernelPolynomial (fun j => (a j : ℂ))
  have hcoeff (j : Fin (N + 1)) : p.coeff (j : ℕ) = (a j : ℂ) := by
    have hfin (i : Fin (N + 1)) : (j : ℕ) = (i : ℕ) ↔ j = i := Fin.ext_iff.symm
    simp [p, finiteToeplitzKernelPolynomial, hfin]
  have hp : p ≠ 0 := by
    intro hp
    obtain ⟨j, hj⟩ : ∃ j, a j ≠ 0 := by
      by_contra h
      push Not at h
      apply ha
      funext i
      exact h i
    have hcoeffj := hcoeff j
    rw [hp] at hcoeffj
    have hzero : (a j : ℂ) = 0 := by simpa using hcoeffj.symm
    exact hj (by exact_mod_cast hzero)
  have hroot : (0 : ℂ) ∈ p.roots := by
    rw [Polynomial.mem_roots hp]
    change p.eval 0 = 0
    rw [← Polynomial.coeff_zero_eq_eval_zero]
    simpa [ha0] using hcoeff (0 : Fin (N + 1))
  have hunit := connesVanSuijlekom_proposition_2_2 c hG hRank a hker hroot
  norm_num at hunit

/-- The corrected source hypotheses also force the final coefficient to be
nonzero, completing the exact degree data for the Laurent quotient. -/
theorem connesVanSuijlekomP21_nonzero_kernel_tail_ne_zero
    {N : ℕ} (c : ℕ → ℝ)
    (hG : (connesVanSuijlekomRealToeplitz N c).PosSemidef)
    (hRank : (connesVanSuijlekomRealToeplitz N c).rank = N)
    (a : Fin (N + 1) → ℝ)
    (hker : connesVanSuijlekomRealToeplitz N c *ᵥ (fun j => (a j : ℂ)) = 0)
    (ha : a ≠ 0) :
    a (Fin.last N) ≠ 0 := by
  obtain ⟨ε, _, hrev⟩ :=
    connesVanSuijlekomP21_reverse_vector_smul c hRank a hker ha
  intro hlast
  have hcoeff := congrFun hrev (Fin.last N)
  have hhead : a 0 = 0 := by
    apply Complex.ofReal_injective
    change (a (Fin.last N).rev : ℂ) = ε * (a (Fin.last N) : ℂ) at hcoeff
    simpa [hlast] using hcoeff
  exact connesVanSuijlekomP21_nonzero_kernel_head_ne_zero c hG hRank a hker ha hhead

/-- Corrected Proposition 2.1(2). With the missing nonzero-kernel-vector
premise restored, the literal Laurent classes `1,X,…,X^(N-1)` form a complex
basis of the source quotient. -/
theorem connesVanSuijlekomP21_corrected_clauseTwo
    {N : ℕ} (c : ℕ → ℝ)
    (hG : (connesVanSuijlekomRealToeplitz N c).PosSemidef)
    (hRank : (connesVanSuijlekomRealToeplitz N c).rank = N)
    (a : Fin (N + 1) → ℝ)
    (hker : connesVanSuijlekomRealToeplitz N c *ᵥ (fun j => (a j : ℂ)) = 0)
    (ha : a ≠ 0) :
    ∃ b : Module.Basis (Fin N) ℂ (connesVanSuijlekomP21Quotient a),
      ∀ i : Fin N, b i =
        Ideal.Quotient.mk (connesVanSuijlekomP21Ideal a) (LaurentPolynomial.T (i : ℤ)) := by
  have ha0 := connesVanSuijlekomP21_nonzero_kernel_head_ne_zero c hG hRank a hker ha
  have hN := connesVanSuijlekomP21_nonzero_kernel_tail_ne_zero c hG hRank a hker ha
  refine ⟨connesVanSuijlekomP21QuotientMonomialBasis a ha0 hN, ?_⟩
  intro i
  exact connesVanSuijlekomP21_quotient_monomial_basis_apply a ha0 hN i

end

end GaloisForLFunctions.HTGeometry
