import GaloisForLFunctions.HTGeometry.ConstantTangentDirections
import GaloisForLFunctions.HTGeometry.DifferentialSubgroupCassidy

/-!
# A constant matrix in the Lie algebra, from the algebraic differential alone

Membership of a *constant* matrix in the Lie algebra of a differential algebraic group is decided by
the order-zero partial derivatives of the defining family at the identity: constants have no jets
above order zero, so the differential conditions collapse to ordinary linear ones.

That turns the hypothesis `hLne` of the classification — the Lie algebra is nonzero — into a
statement about the differential of the *underlying algebraic variety* at the identity, which for a
group whose Zariski closure is `SL₂` is the whole of `sl₂` and in particular nonzero.

* `const_mem_matrixTangentM`;
* `matrixTangentM_ne_bot_of_const`.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open scoped Differential
open GaloisForLFunctions

variable {C : Type*} [Field C] [Differential C]
variable (S : Set (DifferentialPolynomial (Fin 2 × Fin 2) C))

/-- **A constant matrix annihilated by every order-zero differential is a tangent direction.** -/
theorem const_mem_matrixTangentM
    (hone : (1 : Matrix (Fin 2) (Fin 2) C) ∈ matrixZeroSet (C := C) (A := C) S)
    {X : Matrix (Fin 2) (Fin 2) C} (hXc : ∀ i j, (X i j)′ = 0)
    (hzero : ∀ P ∈ S, ∑ v ∈ P.vars.filter (fun v : (Fin 2 × Fin 2) × ℕ => v.2 = 0),
        differentialPolynomialEvalOver (K := C)
            (fun q : Fin 2 × Fin 2 => (1 : Matrix (Fin 2) (Fin 2) C) q.1 q.2)
            (MvPolynomial.pderiv v P) * X v.1.1 v.1.2 = 0) :
    X ∈ matrixTangentM S hone := by
  classical
  rw [mem_matrixTangentM, ← mem_matrixTangent_iff S hone]
  refine (Submodule.mem_iInf _).mpr fun P => (Submodule.mem_iInf _).mpr fun hP => ?_
  rw [mem_tangentSpace_iff,
    linearisationForm_const _ P P.vars (fun q : Fin 2 × Fin 2 => hXc q.1 q.2)]
  exact hzero P hP

/-- **Hence the Lie algebra is nonzero as soon as one nonzero constant matrix is annihilated.** -/
theorem matrixTangentM_ne_bot_of_const
    (hone : (1 : Matrix (Fin 2) (Fin 2) C) ∈ matrixZeroSet (C := C) (A := C) S)
    {X : Matrix (Fin 2) (Fin 2) C} (hXc : ∀ i j, (X i j)′ = 0) (hXne : X ≠ 0)
    (hzero : ∀ P ∈ S, ∑ v ∈ P.vars.filter (fun v : (Fin 2 × Fin 2) × ℕ => v.2 = 0),
        differentialPolynomialEvalOver (K := C)
            (fun q : Fin 2 × Fin 2 => (1 : Matrix (Fin 2) (Fin 2) C) q.1 q.2)
            (MvPolynomial.pderiv v P) * X v.1.1 v.1.2 = 0) :
    ∃ A ∈ matrixTangentM S hone, A ≠ 0 :=
  ⟨X, const_mem_matrixTangentM S hone hXc hzero, hXne⟩

end

end GaloisForLFunctions.HTGeometry
