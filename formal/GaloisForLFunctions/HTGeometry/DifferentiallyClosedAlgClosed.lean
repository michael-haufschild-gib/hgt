import GaloisForLFunctions.HTGeometry.DifferentialClosureClosed
import GaloisForLFunctions.HTGeometry.DerivationPrescription
import GaloisForLFunctions.HTGeometry.KolchinNullstellensatz
import GaloisForLFunctions.HTGeometry.JetHorizonAdditiveTorsorLaw
import GaloisForLFunctions.HTGeometry.RadicalDifferentialIdeal

/-!
# A differentially closed field, and its constants, are algebraically closed

In characteristic zero an algebraic closure is separable over the base, so the derivation extends to
it: the algebraic closure of a differential field is a differential field extension.  A root of a
polynomial there is a solution of a differential system of order zero, so differential closedness
brings the root back into the field.

The constants inherit algebraic closedness: differentiating the defining relation of a root of a
polynomial with constant coefficients gives the separant times the derivative of the root, and
irreducibility in characteristic zero makes the separant nonzero, so the root is constant.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open scoped Differential
open GaloisForLFunctions

universe u

variable (C : Type u) [Field C] [Algebra ℚ C] [Differential C]

instance : CharZero C := algebraRat.charZero C

instance : Algebra.IsSeparable C (AlgebraicClosure C) := Algebra.IsSeparable.of_integral _ _

/-- The derivation of an algebraic closure extending the derivation of the base. -/
def algebraicClosureDerivationChoice :
    Derivation ℚ (AlgebraicClosure C) (AlgebraicClosure C) :=
  (exists_derivation_extension (K := ℚ) (F := C) (L := AlgebraicClosure C) (ratDerivation C)).choose

theorem algebraicClosureDerivationChoice_algebraMap (a : C) :
    algebraicClosureDerivationChoice C (algebraMap C (AlgebraicClosure C) a)
      = algebraMap C (AlgebraicClosure C) (Differential.deriv a) :=
  (exists_derivation_extension (K := ℚ) (F := C) (L := AlgebraicClosure C)
    (ratDerivation C)).choose_spec a

/-- The differential structure of an algebraic closure. -/
@[reducible] def algebraicClosureDifferential : Differential (AlgebraicClosure C) where
  deriv :=
    letI : Algebra ℤ (AlgebraicClosure C) := Ring.toIntAlgebra _
    Derivation.restrictScalars ℤ (algebraicClosureDerivationChoice C)

/-- An algebraic closure of a differential field is a differential field extension. -/
def algebraicClosureExt : DiffFieldExt C where
  carrier := AlgebraicClosure C
  differential := algebraicClosureDifferential C
  compat := fun a => algebraicClosureDerivationChoice_algebraMap C a

/-- A polynomial read as a differential polynomial of order zero in one variable. -/
def polyToDifferential {ι : Type*} (v : ι) (p : Polynomial C) : DifferentialPolynomial ι C :=
  Polynomial.aeval (MvPolynomial.X (v, 0) : DifferentialPolynomial ι C) p

omit [Algebra ℚ C] [Differential C] in
theorem differentialPolynomialEvalOver_polyToDifferential {ι M : Type*} [CommRing M] [Algebra C M]
    [Differential M] (v : ι) (y : ι → M) (p : Polynomial C) :
    differentialPolynomialEvalOver (K := C) y (polyToDifferential C v p)
      = Polynomial.aeval (y v) p := by
  rw [polyToDifferential,
    ← Polynomial.aeval_algHom_apply (differentialPolynomialEvalOver (K := C) y)
      (MvPolynomial.X (v, 0) : DifferentialPolynomial ι C) p,
    differentialPolynomialEvalOver_X, differentialJet_zero]

/-- **A differentially closed field is algebraically closed.**  A root in the algebraic closure —
itself a differential field extension — is a solution of a differential system of order zero, so
differential closedness puts a root in the field. -/
theorem isAlgClosed_of_isDifferentiallyClosed [IsDifferentiallyClosed C] : IsAlgClosed C := by
  classical
  refine IsAlgClosed.of_exists_root C ?_
  intro p hmonic hirr
  have hdeg : p.degree ≠ 0 := by
    intro hzero
    exact hirr.not_isUnit (Polynomial.isUnit_iff_degree_eq_zero.mpr hzero)
  have hdegmap : (p.map (algebraMap C (AlgebraicClosure C))).degree ≠ 0 := by
    rwa [Polynomial.degree_map]
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_root _ hdegmap
  have hzaeval : Polynomial.aeval z p = 0 := by
    rw [Polynomial.aeval_def, ← Polynomial.eval_map]
    exact hz
  letI : Differential (AlgebraicClosure C) := algebraicClosureDifferential C
  have hsolz : ∀ q ∈ ({polyToDifferential C (ULift.up (0 : Fin 1)) p} :
      Finset (DifferentialPolynomial (ULift.{u} (Fin 1)) C)),
      differentialPolynomialEvalOver (K := C)
        (fun _ : ULift.{u} (Fin 1) => z) q = 0 := by
    intro q hq
    rw [Finset.mem_singleton] at hq
    subst hq
    rw [differentialPolynomialEvalOver_polyToDifferential]
    exact hzaeval
  obtain ⟨y, hy⟩ := IsDifferentiallyClosed.exists_point (C := C)
    ({polyToDifferential C (ULift.up (0 : Fin 1)) p} :
      Finset (DifferentialPolynomial (ULift.{u} (Fin 1)) C))
    (algebraicClosureExt C) (fun _ => z) hsolz
  refine ⟨y (ULift.up (0 : Fin 1)), ?_⟩
  have hroot := hy _ (Finset.mem_singleton_self _)
  rw [differentialPolynomialEvalOver_polyToDifferential] at hroot
  rw [← Polynomial.coe_aeval_eq_eval]
  exact hroot

omit [Algebra ℚ C] in
/-- The derivative of a polynomial expression with constant coefficients. -/
theorem deriv_aeval_of_constantCoeffs (α : C) (q : Polynomial (differentialConstants C)) :
    Differential.deriv (Polynomial.aeval α q)
      = Polynomial.aeval α (Polynomial.derivative q) * Differential.deriv α := by
  induction q using Polynomial.induction_on with
  | C c =>
      rw [Polynomial.aeval_C, Polynomial.derivative_C, map_zero, zero_mul]
      exact c.2
  | add q r hq hr =>
      rw [map_add, map_add, map_add, map_add, hq, hr, add_mul]
  | monomial n c ih =>
      have hc : Differential.deriv (algebraMap (differentialConstants C) C c) = 0 := c.2
      simp only [map_mul, Polynomial.aeval_C, Polynomial.aeval_X, map_pow,
        Polynomial.derivative_C_mul, Polynomial.derivative_X_pow, Nat.add_sub_cancel]
      rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, hc, mul_zero, add_zero, deriv_pow',
        Nat.add_sub_cancel]
      push_cast
      ring

/-- **The constants of an algebraically closed differential field of characteristic zero are
algebraically closed.**  A root in the field of a polynomial with constant coefficients is itself
constant, because the derivative of the defining relation is the separant times the derivative of
the root. -/
theorem isAlgClosed_differentialConstants [IsAlgClosed C] :
    IsAlgClosed (differentialConstants C) := by
  classical
  refine IsAlgClosed.of_exists_root _ ?_
  intro q hmonic hirr
  have hdeg : (q.map (algebraMap (differentialConstants C) C)).degree ≠ 0 := by
    rw [Polynomial.degree_map]
    intro hzero
    exact hirr.not_isUnit (Polynomial.isUnit_iff_degree_eq_zero.mpr hzero)
  obtain ⟨α, hα⟩ := IsAlgClosed.exists_root _ hdeg
  have hαaeval : Polynomial.aeval α q = 0 := by
    rw [Polynomial.aeval_def, ← Polynomial.eval_map]
    exact hα
  have hsep : q.Separable := hirr.separable
  have hcop : IsCoprime q (Polynomial.derivative q) := hsep
  obtain ⟨a, bb, hab⟩ := hcop
  have hsepα : Polynomial.aeval α (Polynomial.derivative q) ≠ 0 := by
    intro hzero
    have := congrArg (Polynomial.aeval α) hab
    rw [map_add, map_mul, map_mul, hαaeval, hzero, mul_zero, mul_zero, add_zero, map_one] at this
    exact one_ne_zero this.symm
  have hderiv := deriv_aeval_of_constantCoeffs C α q
  rw [hαaeval, map_zero] at hderiv
  have hαconst : Differential.deriv α = 0 := by
    rcases mul_eq_zero.mp hderiv.symm with h | h
    · exact absurd h hsepα
    · exact h
  refine ⟨⟨α, hαconst⟩, ?_⟩
  have hcoe : Polynomial.aeval α q
      = algebraMap (differentialConstants C) C (Polynomial.eval ⟨α, hαconst⟩ q) := by
    have hval := Polynomial.aeval_algHom_apply (Algebra.ofId (differentialConstants C) C)
      (⟨α, hαconst⟩ : differentialConstants C) q
    have hα' : algebraMap (differentialConstants C) C ⟨α, hαconst⟩ = α := rfl
    simp only [Algebra.ofId_apply, hα', Polynomial.coe_aeval_eq_eval] at hval
    exact hval
  rw [hαaeval] at hcoe
  exact (map_eq_zero_iff _ (algebraMap (differentialConstants C) C).injective).mp hcoe.symm

end

end GaloisForLFunctions.HTGeometry
