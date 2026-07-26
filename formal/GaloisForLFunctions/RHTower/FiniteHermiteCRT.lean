import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-!
# Finite Hermite interpolation from the polynomial Chinese remainder theorem

Distinct points `w i` give pairwise coprime powers of the linear ideals
`(X - C (w i))`.  The finite Chinese remainder theorem therefore realizes an arbitrary polynomial
residue class at every point simultaneously.  Differentiating the divisibility statement converts
it into equality of every prescribed finite derivative jet.

This module discharges the interpolation-existence interface in the arbitrary finite-quartet
passport theorem.  The CRT itself is classical `[BRIDGE]`; the RH-facing content lies in the
symmetry-compatible choice of residue classes and the subsequent positive imaginary-axis repair.
-/

open Polynomial Function

namespace RHTower

noncomputable section

/-- **Finite polynomial CRT.** At pairwise distinct complex points, arbitrary polynomial target
classes can be realized simultaneously modulo arbitrary powers of the corresponding linear ideals. -/
theorem exists_polynomial_sub_mem_power_linear_ideal
    {ι : Type*} [Finite ι] (w : ι → ℂ) (hw : Function.Injective w)
    (m : ι → ℕ) (target : ι → Polynomial ℂ) :
    ∃ B : Polynomial ℂ, ∀ i,
      B - target i ∈ Ideal.span ({(X - C (w i)) ^ m i} : Set (Polynomial ℂ)) := by
  let I : ι → Ideal (Polynomial ℂ) := fun i =>
    Ideal.span ({(X - C (w i)) ^ m i} : Set (Polynomial ℂ))
  have hI : Pairwise (IsCoprime on I) := by
    intro i j hij
    apply (Ideal.isCoprime_span_singleton_iff _ _).mpr
    exact (pairwise_coprime_X_sub_C hw hij).pow
  simpa only [I] using Ideal.exists_forall_sub_mem_ideal hI target

/-- Divisibility form of finite polynomial CRT. -/
theorem exists_polynomial_power_linear_dvd_sub
    {ι : Type*} [Finite ι] (w : ι → ℂ) (hw : Function.Injective w)
    (m : ι → ℕ) (target : ι → Polynomial ℂ) :
    ∃ B : Polynomial ℂ, ∀ i,
      (X - C (w i)) ^ m i ∣ B - target i := by
  obtain ⟨B, hB⟩ := exists_polynomial_sub_mem_power_linear_ideal w hw m target
  refine ⟨B, fun i => ?_⟩
  simpa only [Ideal.mem_span_singleton] using hB i

/-- Product modulus for a finite Hermite packet.  Its degree is the total interpolation budget. -/
def finiteHermiteModulus {ι : Type*} [Fintype ι]
    (w : ι → ℂ) (m : ι → ℕ) : Polynomial ℂ :=
  ∏ i, (X - C (w i)) ^ m i

theorem finiteHermiteModulus_monic {ι : Type*} [Fintype ι]
    (w : ι → ℂ) (m : ι → ℕ) : (finiteHermiteModulus w m).Monic := by
  apply Polynomial.monic_prod_of_monic
  intro i hi
  exact (monic_X_sub_C (w i)).pow _

theorem power_linear_dvd_finiteHermiteModulus {ι : Type*} [Fintype ι]
    (w : ι → ℂ) (m : ι → ℕ) (i : ι) :
    (X - C (w i)) ^ m i ∣ finiteHermiteModulus w m := by
  exact Finset.dvd_prod_of_mem (fun j => (X - C (w j)) ^ m j) (Finset.mem_univ i)

/-- **Degree-bounded finite CRT.** Every finite Hermite packet has a representative whose degree
is strictly below the product modulus.  This is the exact degree gap used by the positive
imaginary-axis repair: the repair polynomial is the modulus itself. -/
theorem exists_polynomial_power_linear_dvd_sub_degree_lt_modulus
    {ι : Type*} [Fintype ι] (w : ι → ℂ) (hw : Function.Injective w)
    (m : ι → ℕ) (target : ι → Polynomial ℂ) :
    ∃ B : Polynomial ℂ,
      B.degree < (finiteHermiteModulus w m).degree ∧
      ∀ i, (X - C (w i)) ^ m i ∣ B - target i := by
  obtain ⟨P, hP⟩ := exists_polynomial_power_linear_dvd_sub w hw m target
  let M := finiteHermiteModulus w m
  refine ⟨P %ₘ M, Polynomial.degree_modByMonic_lt P (finiteHermiteModulus_monic w m), ?_⟩
  intro i
  have hfactor : (X - C (w i)) ^ m i ∣ M :=
    power_linear_dvd_finiteHermiteModulus w m i
  have hmod : M ∣ P - P %ₘ M := by
    refine ⟨P /ₘ M, ?_⟩
    have hdiv := Polynomial.modByMonic_add_div P M
    rw [eq_comm]
    linear_combination hdiv
  have hlocal : (X - C (w i)) ^ m i ∣ P - P %ₘ M := hfactor.trans hmod
  rw [show P %ₘ M - target i = (P - target i) - (P - P %ₘ M) by ring]
  exact dvd_sub (hP i) hlocal

/-- Divisibility by the `m`-th power of a point ideal forces agreement of every derivative below
order `m` at that point. -/
theorem eval_iterate_derivative_eq_of_power_linear_dvd_sub
    {B T : Polynomial ℂ} {w : ℂ} {m n : ℕ}
    (hdvd : (X - C w) ^ m ∣ B - T) (hn : n < m) :
    (derivative^[n] B).eval w = (derivative^[n] T).eval w := by
  have hpow : (X - C w) ^ (m - n) ∣ derivative^[n] (B - T) :=
    pow_sub_dvd_iterate_derivative_of_pow_dvd n hdvd
  have hmn : m - n ≠ 0 := Nat.sub_ne_zero_of_lt hn
  have hlin : X - C w ∣ derivative^[n] (B - T) :=
    (dvd_pow_self (X - C w) hmn).trans hpow
  rw [Polynomial.dvd_iff_isRoot, Polynomial.IsRoot,
    iterate_derivative_sub, eval_sub, sub_eq_zero] at hlin
  exact hlin

/-- **Simultaneous finite Hermite interpolation.** One polynomial realizes every specified finite
derivative jet at every point in a finite injectively indexed packet. -/
theorem exists_polynomial_iterateDerivative_eval_eq
    {ι : Type*} [Finite ι] (w : ι → ℂ) (hw : Function.Injective w)
    (m : ι → ℕ) (target : ι → Polynomial ℂ) :
    ∃ B : Polynomial ℂ, ∀ i n, n < m i →
      (derivative^[n] B).eval (w i) =
        (derivative^[n] (target i)).eval (w i) := by
  obtain ⟨B, hB⟩ := exists_polynomial_power_linear_dvd_sub w hw m target
  exact ⟨B, fun i n hn =>
    eval_iterate_derivative_eq_of_power_linear_dvd_sub (hB i) hn⟩

/-- Degree-bounded simultaneous Hermite interpolation. -/
theorem exists_polynomial_iterateDerivative_eval_eq_degree_lt_modulus
    {ι : Type*} [Fintype ι] (w : ι → ℂ) (hw : Function.Injective w)
    (m : ι → ℕ) (target : ι → Polynomial ℂ) :
    ∃ B : Polynomial ℂ,
      B.degree < (finiteHermiteModulus w m).degree ∧
      ∀ i n, n < m i →
        (derivative^[n] B).eval (w i) =
          (derivative^[n] (target i)).eval (w i) := by
  obtain ⟨B, hdegree, hB⟩ :=
    exists_polynomial_power_linear_dvd_sub_degree_lt_modulus w hw m target
  exact ⟨B, hdegree, fun i n hn =>
    eval_iterate_derivative_eq_of_power_linear_dvd_sub (hB i) hn⟩

/-! ## Equivariant Hermite interpolation -/

/-- Pullback of a polynomial by the sign involution `z ↦ -z`. -/
def polynomialNegPullback (P : Polynomial ℂ) : Polynomial ℂ :=
  P.comp (-X)

/-- Coefficient conjugation, whose evaluation is the Schwarz transform
`z ↦ conj (P (conj z))`. -/
def polynomialConj (P : Polynomial ℂ) : Polynomial ℂ :=
  P.map (starRingEnd ℂ)

/-- Average over the four-element group generated by sign and Schwarz conjugation. -/
def polynomialRealEvenAverage (P : Polynomial ℂ) : Polynomial ℂ :=
  C (1 / 4 : ℂ) *
    (P + polynomialNegPullback P + polynomialConj P +
      polynomialConj (polynomialNegPullback P))

@[simp] theorem eval_polynomialNegPullback (P : Polynomial ℂ) (z : ℂ) :
    (polynomialNegPullback P).eval z = P.eval (-z) := by
  simp [polynomialNegPullback]

@[simp] theorem eval_polynomialConj (P : Polynomial ℂ) (z : ℂ) :
    (polynomialConj P).eval z =
      (starRingEnd ℂ) (P.eval ((starRingEnd ℂ) z)) := by
  rw [polynomialConj, Polynomial.eval_map]
  conv_lhs => rw [show z = (starRingEnd ℂ) ((starRingEnd ℂ) z) by simp]
  exact Polynomial.eval₂_at_apply _ _

theorem eval_polynomialRealEvenAverage (P : Polynomial ℂ) (z : ℂ) :
    (polynomialRealEvenAverage P).eval z =
      (P.eval z + P.eval (-z) +
        (starRingEnd ℂ) (P.eval ((starRingEnd ℂ) z)) +
        (starRingEnd ℂ) (P.eval (-((starRingEnd ℂ) z)))) / 4 := by
  simp [polynomialRealEvenAverage]
  ring

/-- The averaged polynomial is even. -/
theorem polynomialRealEvenAverage_eval_neg (P : Polynomial ℂ) (z : ℂ) :
    (polynomialRealEvenAverage P).eval (-z) =
      (polynomialRealEvenAverage P).eval z := by
  rw [eval_polynomialRealEvenAverage, eval_polynomialRealEvenAverage]
  simp
  ring

/-- The averaged polynomial is Schwarz-real. -/
theorem polynomialRealEvenAverage_eval_conj (P : Polynomial ℂ) (z : ℂ) :
    (polynomialRealEvenAverage P).eval ((starRingEnd ℂ) z) =
      (starRingEnd ℂ) ((polynomialRealEvenAverage P).eval z) := by
  rw [eval_polynomialRealEvenAverage, eval_polynomialRealEvenAverage]
  have hfour : (starRingEnd ℂ) (4 : ℂ) = 4 := map_natCast (starRingEnd ℂ) 4
  simp [hfour]
  ring

theorem derivative_polynomialNegPullback (P : Polynomial ℂ) :
    derivative (polynomialNegPullback P) =
      -polynomialNegPullback (derivative P) := by
  simp [polynomialNegPullback, derivative_comp]

@[simp] theorem iterate_derivative_polynomialNegPullback
    (P : Polynomial ℂ) (n : ℕ) :
    derivative^[n] (polynomialNegPullback P) =
      C ((-1 : ℂ) ^ n) * polynomialNegPullback (derivative^[n] P) := by
  induction n generalizing P with
  | zero => simp [polynomialNegPullback]
  | succ n ih =>
      rw [Function.iterate_succ_apply, derivative_polynomialNegPullback,
        iterate_derivative_neg, ih]
      rw [Function.iterate_succ_apply, pow_succ]
      simp

@[simp] theorem iterate_derivative_polynomialConj
    (P : Polynomial ℂ) (n : ℕ) :
    derivative^[n] (polynomialConj P) =
      polynomialConj (derivative^[n] P) := by
  simp [polynomialConj]

/-- Exact derivative-jet averaging formula. -/
theorem eval_iterate_derivative_polynomialRealEvenAverage
    (P : Polynomial ℂ) (n : ℕ) (z : ℂ) :
    (derivative^[n] (polynomialRealEvenAverage P)).eval z =
      ((derivative^[n] P).eval z +
        (-1 : ℂ) ^ n * (derivative^[n] P).eval (-z) +
        (starRingEnd ℂ) ((derivative^[n] P).eval ((starRingEnd ℂ) z)) +
        (-1 : ℂ) ^ n *
          (starRingEnd ℂ) ((derivative^[n] P).eval (-((starRingEnd ℂ) z)))) / 4 := by
  rw [polynomialRealEvenAverage]
  simp only [iterate_derivative_C_mul, iterate_map_add,
    iterate_derivative_polynomialNegPullback, iterate_derivative_polynomialConj,
    eval_mul, eval_C, eval_add, eval_polynomialNegPullback, eval_polynomialConj,
    map_mul, map_pow, map_neg, map_one]
  simp
  ring

theorem degree_polynomialConj_eq (P : Polynomial ℂ) :
    (polynomialConj P).degree = P.degree := by
  rw [polynomialConj, Polynomial.degree_map_eq_of_injective]
  intro x y h
  simpa using congrArg (starRingEnd ℂ) h

/-- Averaging over sign and Schwarz preserves the degree bound of the original polynomial. -/
theorem degree_polynomialRealEvenAverage_le (P : Polynomial ℂ) :
    (polynomialRealEvenAverage P).degree ≤ P.degree := by
  rw [polynomialRealEvenAverage,
    Polynomial.degree_C_mul (by norm_num : (1 / 4 : ℂ) ≠ 0)]
  apply le_trans (Polynomial.degree_add_le _ _) (max_le_iff.mpr ⟨?_, ?_⟩)
  · apply le_trans (Polynomial.degree_add_le _ _) (max_le_iff.mpr ⟨?_, ?_⟩)
    · apply le_trans (Polynomial.degree_add_le _ _) (max_le_iff.mpr ⟨le_rfl, ?_⟩)
      simp [polynomialNegPullback]
    · exact (degree_polynomialConj_eq P).le
  · rw [degree_polynomialConj_eq]
    simp [polynomialNegPullback]

/-- A compatible finite jet packet is fixed by real-even averaging. -/
theorem polynomialRealEvenAverage_preserves_compatible_jets
    {ι : Type*} [Finite ι]
    (negIdx conjIdx : ι ≃ ι) (w : ι → ℂ)
    (m : ι → ℕ) (target : ι → Polynomial ℂ)
    (hwneg : ∀ i, w (negIdx i) = -w i)
    (hwconj : ∀ i, w (conjIdx i) = (starRingEnd ℂ) (w i))
    (hmneg : ∀ i, m (negIdx i) = m i)
    (hmconj : ∀ i, m (conjIdx i) = m i)
    (hjetneg : ∀ i n, n < m i →
      (derivative^[n] (target (negIdx i))).eval (w (negIdx i)) =
        (-1 : ℂ) ^ n * (derivative^[n] (target i)).eval (w i))
    (hjetconj : ∀ i n, n < m i →
      (derivative^[n] (target (conjIdx i))).eval (w (conjIdx i)) =
        (starRingEnd ℂ) ((derivative^[n] (target i)).eval (w i)))
    (P : Polynomial ℂ)
    (hP : ∀ i n, n < m i →
      (derivative^[n] P).eval (w i) =
        (derivative^[n] (target i)).eval (w i)) :
    ∀ i n, n < m i →
      (derivative^[n] (polynomialRealEvenAverage P)).eval (w i) =
        (derivative^[n] (target i)).eval (w i) := by
  intro i n hn
  rw [eval_iterate_derivative_polynomialRealEvenAverage]
  have hPi := hP i n hn
  have hnneg : n < m (negIdx i) := by rwa [hmneg]
  have hPneg := hP (negIdx i) n hnneg
  have hnconj : n < m (conjIdx i) := by rwa [hmconj]
  have hPconj := hP (conjIdx i) n hnconj
  have hnnegconj : n < m (negIdx (conjIdx i)) := by
    rw [hmneg, hmconj]
    exact hn
  have hPnegconj := hP (negIdx (conjIdx i)) n hnnegconj
  rw [hPi]
  rw [show -w i = w (negIdx i) by rw [hwneg]]
  rw [hPneg, hjetneg i n hn]
  rw [show (starRingEnd ℂ) (w i) = w (conjIdx i) by rw [hwconj]]
  rw [hPconj, hjetconj i n hn]
  rw [show -w (conjIdx i) = w (negIdx (conjIdx i)) by rw [hwneg]]
  rw [hPnegconj, hjetneg (conjIdx i) n hnconj,
    hjetconj i n hn]
  simp
  have hsign : (-1 : ℂ) ^ n * (-1 : ℂ) ^ n = 1 := by
    rw [← pow_add, ← two_mul]
    simp
  simp only [← mul_assoc, hsign, one_mul]
  ring

/-- **Equivariant finite Hermite interpolation.** If a finite jet packet is compatible with the
sign and Schwarz involutions, one polynomial realizes every jet while satisfying both symmetries
globally.  This discharges the symmetry-compatible CRT interface in the arbitrary quartet theorem. -/
theorem exists_real_even_polynomial_iterateDerivative_eval_eq
    {ι : Type*} [Finite ι]
    (negIdx conjIdx : ι ≃ ι) (w : ι → ℂ) (hw : Function.Injective w)
    (m : ι → ℕ) (target : ι → Polynomial ℂ)
    (hwneg : ∀ i, w (negIdx i) = -w i)
    (hwconj : ∀ i, w (conjIdx i) = (starRingEnd ℂ) (w i))
    (hmneg : ∀ i, m (negIdx i) = m i)
    (hmconj : ∀ i, m (conjIdx i) = m i)
    (hjetneg : ∀ i n, n < m i →
      (derivative^[n] (target (negIdx i))).eval (w (negIdx i)) =
        (-1 : ℂ) ^ n * (derivative^[n] (target i)).eval (w i))
    (hjetconj : ∀ i n, n < m i →
      (derivative^[n] (target (conjIdx i))).eval (w (conjIdx i)) =
        (starRingEnd ℂ) ((derivative^[n] (target i)).eval (w i))) :
    ∃ B : Polynomial ℂ,
      (∀ z, B.eval (-z) = B.eval z) ∧
      (∀ z, B.eval ((starRingEnd ℂ) z) = (starRingEnd ℂ) (B.eval z)) ∧
      ∀ i n, n < m i →
        (derivative^[n] B).eval (w i) =
          (derivative^[n] (target i)).eval (w i) := by
  obtain ⟨P, hP⟩ := exists_polynomial_iterateDerivative_eval_eq w hw m target
  refine ⟨polynomialRealEvenAverage P,
    polynomialRealEvenAverage_eval_neg P,
    polynomialRealEvenAverage_eval_conj P, ?_⟩
  exact polynomialRealEvenAverage_preserves_compatible_jets
    negIdx conjIdx w m target hwneg hwconj hmneg hmconj hjetneg hjetconj P hP

/-- **Degree-bounded equivariant Hermite interpolation.** The real-even, Schwarz-real representative
can be chosen strictly below the packet modulus.  Therefore the same modulus, multiplied by any
scalar, can repair global positivity without changing any prescribed finite jet. -/
theorem exists_real_even_polynomial_iterateDerivative_eval_eq_degree_lt_modulus
    {ι : Type*} [Fintype ι]
    (negIdx conjIdx : ι ≃ ι) (w : ι → ℂ) (hw : Function.Injective w)
    (m : ι → ℕ) (target : ι → Polynomial ℂ)
    (hwneg : ∀ i, w (negIdx i) = -w i)
    (hwconj : ∀ i, w (conjIdx i) = (starRingEnd ℂ) (w i))
    (hmneg : ∀ i, m (negIdx i) = m i)
    (hmconj : ∀ i, m (conjIdx i) = m i)
    (hjetneg : ∀ i n, n < m i →
      (derivative^[n] (target (negIdx i))).eval (w (negIdx i)) =
        (-1 : ℂ) ^ n * (derivative^[n] (target i)).eval (w i))
    (hjetconj : ∀ i n, n < m i →
      (derivative^[n] (target (conjIdx i))).eval (w (conjIdx i)) =
        (starRingEnd ℂ) ((derivative^[n] (target i)).eval (w i))) :
    ∃ B : Polynomial ℂ,
      B.degree < (finiteHermiteModulus w m).degree ∧
      (∀ z, B.eval (-z) = B.eval z) ∧
      (∀ z, B.eval ((starRingEnd ℂ) z) = (starRingEnd ℂ) (B.eval z)) ∧
      ∀ i n, n < m i →
        (derivative^[n] B).eval (w i) =
          (derivative^[n] (target i)).eval (w i) := by
  obtain ⟨P, hdegree, hP⟩ :=
    exists_polynomial_iterateDerivative_eval_eq_degree_lt_modulus w hw m target
  refine ⟨polynomialRealEvenAverage P,
    (degree_polynomialRealEvenAverage_le P).trans_lt hdegree,
    polynomialRealEvenAverage_eval_neg P,
    polynomialRealEvenAverage_eval_conj P, ?_⟩
  exact polynomialRealEvenAverage_preserves_compatible_jets
    negIdx conjIdx w m target hwneg hwconj hmneg hmconj hjetneg hjetconj P hP

end

end RHTower
