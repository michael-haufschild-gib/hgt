import Mathlib.RingTheory.Derivation.MapCoeffs
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.RingTheory.Polynomial.Basic

/-!
# Algebraic descent along a derivation

Let `K ⊆ Y` be intermediate fields of a characteristic-zero field `L` and let `D` be a derivation
of `L` that maps `K` into itself and whose only constants inside `Y` are the elements of `K`.  An
element of `Y` that is algebraic over `K` and whose derivative already lies in `K` lies in `K`
itself, up to nothing: it lies in `K`.

The proof differentiates the minimal polynomial.  The resulting polynomial has coefficients in `K`,
annihilates the element, and has strictly smaller degree, so it vanishes.  Its subleading
coefficient then says that the element differs from a `K`-element by a `D`-constant.

This is the descent step that turns a statement about principal symbols into a statement about the
observables themselves.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

noncomputable section

variable {C L : Type*} [Field C] [Field L] [Algebra C L]

/-- Apply a derivation to every coefficient of a polynomial. -/
def derivMapCoeffs (D : Derivation C L L) : Derivation C L[X] L[X] :=
  PolynomialModule.equivPolynomialSelf.compDer D.mapCoeffs

@[simp]
theorem coeff_derivMapCoeffs (D : Derivation C L L) (p : L[X]) (i : ℕ) :
    (derivMapCoeffs D p).coeff i = D (p.coeff i) := rfl

/-- The chain rule for evaluating a polynomial with varying coefficients. -/
theorem derivation_aeval_eq (D : Derivation C L L) (x : L) (p : L[X]) :
    D (aeval x p) = aeval x (derivMapCoeffs D p) + aeval x (derivative p) * D x := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      simp only [map_add, hp, hq]
      ring
  | monomial n a =>
      have hmap : derivMapCoeffs D (monomial n a) = monomial n (D a) := by
        ext i
        rw [coeff_derivMapCoeffs, coeff_monomial, coeff_monomial]
        by_cases h : n = i
        · simp [h]
        · simp [h]
      rw [hmap, aeval_monomial, aeval_monomial, derivative_monomial, aeval_monomial,
        Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul, smul_eq_mul, nsmul_eq_mul]
      simp only [show ∀ b : L, algebraMap L L b = b from fun _ => rfl]
      ring

theorem derivation_natCast_eq_zero (D : Derivation C L L) (n : ℕ) : D (n : L) = 0 := by
  induction n with
  | zero => simp
  | succ n ih => rw [Nat.cast_succ, map_add, ih, D.map_one_eq_zero, add_zero]

/-- **Algebraic descent.**  An element of `Y` algebraic over `K` whose derivative lies in `K`, in a
setting where the derivation preserves `K` and has no constants in `Y` outside `K`, lies in `K`. -/
theorem mem_of_isAlgebraic_of_derivation_mem [CharZero L]
    (D : Derivation C L L) (K Y : IntermediateField C L) (hKY : K ≤ Y)
    (hDK : ∀ v ∈ K, D v ∈ K)
    (hconst : ∀ z ∈ Y, D z = 0 → z ∈ K)
    {T : L} (hTY : T ∈ Y) (hT : IsAlgebraic K T) (hDT : D T ∈ K) :
    T ∈ K := by
  classical
  have hint : IsIntegral K T := hT.isIntegral
  set p : K[X] := minpoly K T with hp
  have hpmonic : p.Monic := minpoly.monic hint
  have hpdeg : 0 < p.natDegree := (minpoly.irreducible hint).natDegree_pos
  set P : L[X] := p.map (algebraMap K L) with hP
  have hPmonic : P.Monic := hpmonic.map _
  have hPdeg : P.natDegree = p.natDegree := hpmonic.natDegree_map _
  have hPcoeff : ∀ i, P.coeff i ∈ K := by
    intro i
    rw [hP, coeff_map]
    exact (p.coeff i).2
  have hPpos : 0 < P.natDegree := by rw [hPdeg]; exact hpdeg
  have hPeval : aeval T P = 0 := by
    rw [hP, aeval_map_algebraMap]
    exact minpoly.aeval K T
  set Q : L[X] := derivMapCoeffs D P + Polynomial.C (D T) * derivative P with hQ
  have hQeval : aeval T Q = 0 := by
    have hchain := derivation_aeval_eq D T P
    rw [hPeval, map_zero] at hchain
    rw [hQ, map_add, map_mul, aeval_C,
      show ∀ b : L, algebraMap L L b = b from fun _ => rfl]
    linear_combination -hchain
  have hQcoeff : ∀ i, Q.coeff i ∈ K := by
    intro i
    rw [hQ, coeff_add, coeff_derivMapCoeffs, coeff_C_mul, coeff_derivative]
    refine add_mem (hDK _ (hPcoeff i)) (mul_mem hDT ?_)
    exact mul_mem (hPcoeff (i + 1))
      (add_mem (IntermediateField.natCast_mem _ i) (one_mem _))
  have hmapdeg : (derivMapCoeffs D P).natDegree ≤ P.natDegree - 1 := by
    rw [natDegree_le_iff_coeff_eq_zero]
    intro m hm
    rw [coeff_derivMapCoeffs]
    by_cases hmd : m = P.natDegree
    · rw [hmd, hPmonic.coeff_natDegree, D.map_one_eq_zero]
    · have hlt : P.natDegree < m := by omega
      rw [coeff_eq_zero_of_natDegree_lt hlt, map_zero]
  have hderdeg : (Polynomial.C (D T) * derivative P).natDegree ≤ P.natDegree - 1 :=
    (natDegree_C_mul_le _ _).trans
      (Nat.le_pred_of_lt (natDegree_derivative_lt (by omega)))
  have hQdeg : Q.natDegree < P.natDegree := by
    have hle : Q.natDegree ≤ P.natDegree - 1 :=
      (natDegree_add_le (derivMapCoeffs D P) (Polynomial.C (D T) * derivative P)).trans
        (max_le hmapdeg hderdeg)
    omega
  have hQ0 : Q = 0 := by
    obtain ⟨Q₀, hQ₀⟩ : ∃ Q₀ : K[X], Q₀.map (algebraMap K L) = Q := by
      have hrange : ∀ i, Q.coeff i ∈ Set.range (algebraMap K L) := by
        intro i
        exact ⟨⟨Q.coeff i, hQcoeff i⟩, rfl⟩
      obtain ⟨Q₀, hQ₀⟩ := (Polynomial.mem_map_range (algebraMap K L)).2 hrange
      exact ⟨Q₀, by simpa only [Polynomial.coe_mapRingHom] using hQ₀⟩
    by_contra hne
    have hQ₀ne : Q₀ ≠ 0 := by
      intro hzero
      exact hne (by rw [← hQ₀, hzero, Polynomial.map_zero])
    have hQ₀eval : aeval T Q₀ = 0 := by
      have heq := hQeval
      rw [← hQ₀] at heq
      rwa [aeval_map_algebraMap] at heq
    have hle := minpoly.degree_le_of_ne_zero K T hQ₀ne hQ₀eval
    have hQ₀deg : Q₀.natDegree = Q.natDegree := by
      rw [← hQ₀]
      exact (natDegree_map_eq_of_injective (algebraMap K L).injective Q₀).symm
    have hnd : p.natDegree ≤ Q₀.natDegree := by
      have h := Polynomial.natDegree_le_natDegree hle
      rwa [← hp] at h
    omega
  have hcoeff := congrArg (fun R : L[X] => R.coeff (P.natDegree - 1)) hQ0
  have hdercoeff : (derivative P).coeff (P.natDegree - 1) = (P.natDegree : L) := by
    rw [coeff_derivative, show P.natDegree - 1 + 1 = P.natDegree by omega,
      hPmonic.coeff_natDegree, one_mul]
    have hcast : ((P.natDegree - 1 + 1 : ℕ) : L) = (P.natDegree : L) := by
      rw [Nat.sub_add_cancel (by omega)]
    simpa only [Nat.cast_add, Nat.cast_one] using hcast
  simp only [hQ, coeff_add, coeff_derivMapCoeffs, coeff_C_mul, coeff_zero, hdercoeff] at hcoeff
  have hkne : ((P.natDegree : ℕ) : L) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  set a : L := P.coeff (P.natDegree - 1) with ha
  have haK : a ∈ K := hPcoeff _
  set z : L := T + ((P.natDegree : L))⁻¹ * a with hz
  have hDz : D z = 0 := by
    rw [hz, map_add, Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    have hinv : D (((P.natDegree : ℕ) : L))⁻¹ = 0 := by
      rw [Derivation.leibniz_inv, derivation_natCast_eq_zero, smul_zero]
    rw [hinv, mul_zero, add_zero]
    field_simp
    linear_combination hcoeff
  have hzY : z ∈ Y := add_mem hTY (mul_mem (hKY (IntermediateField.inv_mem _
    (IntermediateField.natCast_mem _ _))) (hKY haK))
  have hzK : z ∈ K := hconst z hzY hDz
  have hTeq : T = z - ((P.natDegree : L))⁻¹ * a := by rw [hz]; ring
  rw [hTeq]
  exact sub_mem hzK (mul_mem (IntermediateField.inv_mem _
    (IntermediateField.natCast_mem _ _)) haK)

end

end GaloisForLFunctions.HTGeometry
