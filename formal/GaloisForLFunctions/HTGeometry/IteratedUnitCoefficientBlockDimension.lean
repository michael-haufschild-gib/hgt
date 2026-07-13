import GaloisForLFunctions.HTGeometry.MvPolynomialCoefficientRegular
import Mathlib.Algebra.Category.CommAlgCat.Basic
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.KrullDimension.NonZeroDivisors

namespace GaloisForLFunctions.HTGeometry

open scoped nonZeroDivisors

noncomputable section

def iteratedUnitCoefficientBlockRing
    (A : Type) [CommRing A] {n : ℕ} :
    List (MvPolynomial (Fin n) A) → CommAlgCat A
  | [] => CommAlgCat.of A A
  | P :: Ps =>
      let B := iteratedUnitCoefficientBlockRing A Ps
      CommAlgCat.of A
        ((MvPolynomial (Fin n) B) ⧸
          Ideal.span {MvPolynomial.map (algebraMap A B) P})

theorem iteratedUnitCoefficientBlockRing_isNoetherian
    {A : Type} [CommRing A] [IsNoetherianRing A] {n : ℕ}
    (Ps : List (MvPolynomial (Fin n) A)) :
    IsNoetherianRing (iteratedUnitCoefficientBlockRing A Ps) := by
  induction Ps with
  | nil =>
      change IsNoetherianRing A
      infer_instance
  | cons P Ps ih =>
      letI : IsNoetherianRing (iteratedUnitCoefficientBlockRing A Ps) := ih
      change IsNoetherianRing
        ((MvPolynomial (Fin n) (iteratedUnitCoefficientBlockRing A Ps)) ⧸
          Ideal.span {MvPolynomial.map
            (algebraMap A (iteratedUnitCoefficientBlockRing A Ps)) P})
      infer_instance

/-- A polynomial with a unit scalar coefficient stays a non-zero-divisor after extension to every
coefficient algebra, including successive quotient algebras. -/
theorem finMvPolynomial_map_mem_nonZeroDivisors_of_isUnit_coeff
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    {n : ℕ} (P : MvPolynomial (Fin n) A) (m : Fin n →₀ ℕ)
    (hm : IsUnit (P.coeff m)) :
    MvPolynomial.map (algebraMap A B) P ∈
      nonZeroDivisors (MvPolynomial (Fin n) B) := by
  apply finMvPolynomial_mem_nonZeroDivisors_of_coeff_mem n _ m
  rw [MvPolynomial.coeff_map, ← isRegular_iff_mem_nonZeroDivisors]
  exact IsUnit.isRegular (hm.map _)

/-- **Unit-coefficient block height law.** Successively quotienting a Noetherian coefficient ring
by `r` fresh finite-variable equations, each with a unit coefficient in the original coefficient
ring, lowers Krull dimension by at least `r`. -/
theorem iteratedUnitCoefficientBlockRing_krullDim_add_length_le
    {A : Type} [CommRing A] [IsNoetherianRing A] {n : ℕ}
    (Ps : List (MvPolynomial (Fin n) A))
    (hPs : ∀ P ∈ Ps, ∃ m, IsUnit (P.coeff m)) :
    ringKrullDim (iteratedUnitCoefficientBlockRing A Ps) + Ps.length ≤
      ringKrullDim A + Ps.length * n := by
  induction Ps with
  | nil =>
      simp only [List.length_nil, Nat.cast_zero, add_zero, zero_mul]
      exact le_rfl
  | cons P Ps ih =>
      have hP : ∃ m, IsUnit (P.coeff m) := hPs P (by simp)
      have htail : ∀ Q ∈ Ps, ∃ m, IsUnit (Q.coeff m) := by
        intro Q hQ
        exact hPs Q (by simp [hQ])
      letI : IsNoetherianRing (iteratedUnitCoefficientBlockRing A Ps) :=
        iteratedUnitCoefficientBlockRing_isNoetherian Ps
      obtain ⟨m, hm⟩ := hP
      have hreg := finMvPolynomial_map_mem_nonZeroDivisors_of_isUnit_coeff
        (B := iteratedUnitCoefficientBlockRing A Ps) P m hm
      have hstep :
          ringKrullDim
              ((MvPolynomial (Fin n) (iteratedUnitCoefficientBlockRing A Ps)) ⧸
                Ideal.span {MvPolynomial.map
                  (algebraMap A (iteratedUnitCoefficientBlockRing A Ps)) P}) + 1 ≤
            ringKrullDim (iteratedUnitCoefficientBlockRing A Ps) + n := by
        have hdim := ringKrullDim_quotient_succ_le_of_nonZeroDivisor hreg
        rw [MvPolynomial.ringKrullDim_of_isNoetherianRing] at hdim
        simpa using hdim
      have htaildim := ih htail
      change ringKrullDim
          ((MvPolynomial (Fin n) (iteratedUnitCoefficientBlockRing A Ps)) ⧸
            Ideal.span {MvPolynomial.map
              (algebraMap A (iteratedUnitCoefficientBlockRing A Ps)) P}) +
          (Ps.length + 1) ≤
        ringKrullDim A + (Ps.length + 1) * n
      calc
        _ = (ringKrullDim
              ((MvPolynomial (Fin n) (iteratedUnitCoefficientBlockRing A Ps)) ⧸
                Ideal.span {MvPolynomial.map
                  (algebraMap A (iteratedUnitCoefficientBlockRing A Ps)) P}) + 1) +
              Ps.length := by simp [add_assoc, add_comm]
        _ ≤ (ringKrullDim (iteratedUnitCoefficientBlockRing A Ps) + n) +
              Ps.length := by
                simpa [add_comm] using add_le_add_right hstep Ps.length
        _ = (ringKrullDim (iteratedUnitCoefficientBlockRing A Ps) + Ps.length) + n := by
              simp [add_comm, add_left_comm]
        _ ≤ (ringKrullDim A + Ps.length * n) + n := by
              simpa [add_comm] using add_le_add_right htaildim n
        _ = ringKrullDim A + (Ps.length + 1) * n := by
              norm_num [add_mul, add_assoc]

end
end GaloisForLFunctions.HTGeometry
