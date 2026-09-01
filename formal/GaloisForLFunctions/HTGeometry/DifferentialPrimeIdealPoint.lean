import GaloisForLFunctions.HTGeometry.KolchinNullstellensatzDiffFG
import GaloisForLFunctions.HTGeometry.QuotientDerivation

/-!
# Marked points of prime differential ideals

A prime differential ideal over a differentially closed field has a rational differential point
which preserves any prescribed polynomial outside the ideal.  This is the ideal-theoretic form of
the marked differential Nullstellensatz needed by differential Chevalley descent.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions
open scoped Differential

noncomputable section

attribute [local instance] differentialPolynomialOverDifferential

universe u

variable {C : Type u} [Field C] [Algebra ℚ C] [Differential C]
  [IsDifferentiallyClosed C]

/-- **Marked prime differential ideal point.**  Every prime differential ideal in finitely many
differential indeterminates has a `C`-point annihilating the whole ideal and avoiding any one
polynomial outside it. -/
theorem exists_point_avoiding_primeDifferentialIdeal {n : ℕ}
    (I : Ideal (DifferentialPolynomial (Fin n) C))
    (hIprime : I.IsPrime)
    (hIderiv : ∀ P ∈ I, Differential.deriv P ∈ I)
    (Q : DifferentialPolynomial (Fin n) C) (hQI : Q ∉ I) :
    ∃ y : Fin n → C,
      (∀ P ∈ I, differentialPolynomialEvalOver (K := C) y P = 0) ∧
      differentialPolynomialEvalOver (K := C) y Q ≠ 0 := by
  let E := DifferentialPolynomial (Fin n) C ⧸ I
  letI : IsDomain E :=
    (Ideal.Quotient.isDomain_iff_prime I).mpr hIprime
  letI : Differential E := quotientDifferential I hIderiv
  letI : DifferentialAlgebra C E := ⟨fun c => by
    change Ideal.Quotient.mk I
        (differentialPolynomialOverDerivation (Fin n) C (MvPolynomial.C c)) =
      Ideal.Quotient.mk I (MvPolynomial.C (Differential.deriv c))
    rw [differentialPolynomialOverDerivation_C]⟩
  letI : Algebra ℚ E := ((algebraMap C E).comp (algebraMap ℚ C)).toAlgebra
  let yE : Fin n → E := fun i =>
    Ideal.Quotient.mk I (MvPolynomial.X (i, 0))
  have hjet (i : Fin n) : ∀ k : ℕ,
      differentialJet k (yE i) =
        Ideal.Quotient.mk I (MvPolynomial.X (i, k)) := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
        rw [differentialJet_succ, ih, quotientDifferential_deriv_mk]
        change Ideal.Quotient.mk I
          (differentialPolynomialOverDerivation (Fin n) C (MvPolynomial.X (i, k))) = _
        rw [differentialPolynomialOverDerivation_X]
  have heval (P : DifferentialPolynomial (Fin n) C) :
      differentialPolynomialEvalOver (K := C) yE P = Ideal.Quotient.mk I P := by
    induction P using MvPolynomial.induction_on with
    | C c =>
        rw [differentialPolynomialEvalOver_C]
        exact (Ideal.Quotient.mk_algebraMap C I c).symm
    | add P R hP hR =>
        rw [map_add, map_add, hP, hR]
    | mul_X P p hP =>
        rw [map_mul, map_mul, hP, differentialPolynomialEvalOver_X, hjet]
  have hsurj : Function.Surjective
      (differentialPolynomialEvalOver (K := C) yE) := by
    intro e
    obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective e
    exact ⟨P, heval P⟩
  have hQne : Ideal.Quotient.mk I Q ≠ 0 := by
    intro hzero
    exact hQI (Ideal.Quotient.eq_zero_iff_mem.mp hzero)
  obtain ⟨χ, hχderiv, hχQ⟩ :=
    exists_differentialAlgHom_ne_zero_of_diffFG
      (C := C) (E := E) yE hsurj hQne
  let y : Fin n → C := fun i => χ (yE i)
  have hmap (P : DifferentialPolynomial (Fin n) C) :
      differentialPolynomialEvalOver (K := C) y P =
        χ (Ideal.Quotient.mk I P) := by
    have h := map_differentialPolynomialEvalOver
      (χ : E →+* C) hχderiv (fun c => χ.commutes c) yE P
    rw [heval P] at h
    exact h.symm
  refine ⟨y, ?_, ?_⟩
  · intro P hPI
    rw [hmap, Ideal.Quotient.eq_zero_iff_mem.mpr hPI, map_zero]
  · rw [hmap]
    exact hχQ

end

end GaloisForLFunctions.HTGeometry
