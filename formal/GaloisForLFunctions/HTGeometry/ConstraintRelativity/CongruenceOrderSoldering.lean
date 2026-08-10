import Mathlib
import GaloisForLFunctions.HTGeometry.ConstraintRelativity.CongruenceOrderTraceDual

/-!
# The congruence order acting on its own lattices

The sheet algebra `R^N` is an algebra over the presented congruence order
`A = R[x₁,…,x_m]/(xᵢ² − a xᵢ, xᵢxⱼ)`, and both the rescaled dual lattice and the rescaled order
are `A`-submodules of it.  This gives the trace-law defect its `A`-module structure.
-/

namespace HTGeometry.ConstraintRelativity

open MvPolynomial

section SheetAlgebra

variable {R : Type*} [CommRing R] (a : R) (m : ℕ)

/-- The presentation of the congruence order, as an algebra map to the sheet algebra. -/
noncomputable def congruenceEvalQuot :
    (MvPolynomial (Fin m) R ⧸ congruenceIdeal a m) →ₐ[R] (Fin (m + 1) → R) :=
  Ideal.Quotient.liftₐ (congruenceIdeal a m) (congruenceEval a m)
    fun _ hx => congruenceIdeal_le_ker hx

/-- The sheet algebra is an algebra over the presented congruence order. -/
noncomputable instance congruencePiAlgebra :
    Algebra (MvPolynomial (Fin m) R ⧸ congruenceIdeal a m) (Fin (m + 1) → R) :=
  (congruenceEvalQuot a m).toRingHom.toAlgebra

instance congruencePiTower :
    IsScalarTower R (MvPolynomial (Fin m) R ⧸ congruenceIdeal a m) (Fin (m + 1) → R) :=
  IsScalarTower.of_algebraMap_eq fun r =>
    (AlgHom.commutes (congruenceEvalQuot a m) r).symm

variable {a m}

theorem algebraMap_congruencePi_mk (p : MvPolynomial (Fin m) R) :
    algebraMap (MvPolynomial (Fin m) R ⧸ congruenceIdeal a m) (Fin (m + 1) → R)
        (Ideal.Quotient.mk _ p) = congruenceEval a m p := rfl

theorem algebraMap_congruenceX (i : Fin m) :
    algebraMap (MvPolynomial (Fin m) R ⧸ congruenceIdeal a m) (Fin (m + 1) → R)
        (congruenceX a m i) = congruenceGen a m i := by
  rw [congruenceX, algebraMap_congruencePi_mk, congruenceEval, aeval_X]

theorem algebraMap_mem_congruenceOrder (c : MvPolynomial (Fin m) R ⧸ congruenceIdeal a m) :
    algebraMap (MvPolynomial (Fin m) R ⧸ congruenceIdeal a m) (Fin (m + 1) → R) c
      ∈ congruenceOrder a (m + 1) := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective c
  rw [algebraMap_congruencePi_mk, ← range_congruenceEval (a := a) (m := m)]
  exact ⟨p, rfl⟩

theorem congruencePi_smul (c : MvPolynomial (Fin m) R ⧸ congruenceIdeal a m)
    (z : Fin (m + 1) → R) :
    c • z = algebraMap (MvPolynomial (Fin m) R ⧸ congruenceIdeal a m) (Fin (m + 1) → R) c * z :=
  Algebra.smul_def c z

end SheetAlgebra

/-! ## The lattices as modules over the congruence order -/

section Lattices

variable {R : Type*} [CommRing R] {a : R} {m : ℕ}

theorem mul_mem_scaledDual {v : Fin (m + 1) → R} (hv : v ∈ congruenceOrder a (m + 1))
    {z : Fin (m + 1) → R} (hz : z ∈ scaledDual a (m + 1)) :
    v * z ∈ scaledDual a (m + 1) := by
  classical
  obtain ⟨t, ht⟩ := mem_scaledDual.1 hz
  choose c hc using fun i => hv i (Fin.last m)
  have hvi : ∀ i, v i = v (Fin.last m) + a * c i := fun i => by linear_combination hc i
  refine mem_scaledDual.2 ⟨v (Fin.last m) * t + ∑ i, c i * z i, ?_⟩
  have hterm : ∀ i, (v * z) i = v (Fin.last m) * z i + a * (c i * z i) := by
    intro i
    show v i * z i = _
    rw [hvi i]
    ring
  rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => hterm i, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, ht]
  ring

theorem mul_mem_scaledOrder {v : Fin (m + 1) → R} (hv : v ∈ congruenceOrder a (m + 1))
    {z : Fin (m + 1) → R} (hz : z ∈ scaledOrder a (m + 1)) :
    v * z ∈ scaledOrder a (m + 1) := by
  obtain ⟨w, hw, rfl⟩ := mem_scaledOrder.1 hz
  refine mem_scaledOrder.2 ⟨v * w, mul_mem hv hw, ?_⟩
  funext i
  show a * (v i * w i) = v i * (a * w i)
  ring

/-- The rescaled dual lattice as a module over the presented congruence order. -/
noncomputable def scaledDualA (a : R) (m : ℕ) :
    Submodule (MvPolynomial (Fin m) R ⧸ congruenceIdeal a m) (Fin (m + 1) → R) where
  carrier := scaledDual a (m + 1)
  add_mem' := add_mem
  zero_mem' := zero_mem _
  smul_mem' c z hz := by
    rw [congruencePi_smul]
    exact mul_mem_scaledDual (algebraMap_mem_congruenceOrder c) hz

/-- The rescaled order as a module over the presented congruence order. -/
noncomputable def scaledOrderA (a : R) (m : ℕ) :
    Submodule (MvPolynomial (Fin m) R ⧸ congruenceIdeal a m) (Fin (m + 1) → R) where
  carrier := scaledOrder a (m + 1)
  add_mem' := add_mem
  zero_mem' := zero_mem _
  smul_mem' c z hz := by
    rw [congruencePi_smul]
    exact mul_mem_scaledOrder (algebraMap_mem_congruenceOrder c) hz

theorem scaledDualA_restrictScalars :
    (scaledDualA a m).restrictScalars R = scaledDual a (m + 1) := rfl

theorem scaledOrderA_restrictScalars :
    (scaledOrderA a m).restrictScalars R = scaledOrder a (m + 1) := rfl

theorem scaledOrderA_le_scaledDualA : scaledOrderA a m ≤ scaledDualA a m :=
  scaledOrder_le_scaledDual a (m + 1)

/-- The trace-law defect of the congruence order, as a module over that order. -/
abbrev traceDefect (a : R) (m : ℕ) : Type _ :=
  (↥(scaledDualA a m)) ⧸
    (Submodule.comap (scaledDualA a m).subtype (scaledOrderA a m) :
      Submodule (MvPolynomial (Fin m) R ⧸ congruenceIdeal a m) ↥(scaledDualA a m))

end Lattices

end HTGeometry.ConstraintRelativity
