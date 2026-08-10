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

/-- Quotients of submodules of the sheet algebra over the congruence order.  Instance search
does not find `Submodule.hasQuotient` through the induced algebra structure. -/
noncomputable instance sheetSubmoduleHasQuotient
    (P : Submodule (MvPolynomial (Fin m) R ⧸ congruenceIdeal a m) (Fin (m + 1) → R)) :
    HasQuotient ↥P (Submodule (MvPolynomial (Fin m) R ⧸ congruenceIdeal a m) ↥P) :=
  @Submodule.hasQuotient (MvPolynomial (Fin m) R ⧸ congruenceIdeal a m) ↥P _ _ _

/-- The trace-law defect of the congruence order, as a module over that order. -/
abbrev traceDefect (a : R) (m : ℕ) : Type _ :=
  ↥(scaledDualA a m) ⧸ Submodule.comap (scaledDualA a m).subtype (scaledOrderA a m)

end Lattices

/-! ## The trace-law defect in coordinates -/

section Coordinates

variable {R : Type*} [CommRing R] {a : R} {m : ℕ} [Invertible ((m : R) + 1)]

/-- The trace-law defect in coordinates. -/
noncomputable def traceDefectModelEquiv (a : R) (m : ℕ) [Invertible ((m : R) + 1)] :
    traceDefect a m ≃ₗ[R] (Fin m → R ⧸ Ideal.span ({a ^ 2} : Set R)) :=
  scaledTraceDefectEquiv

theorem traceDefectModelEquiv_mk (z : ↥(scaledDualA a m)) :
    traceDefectModelEquiv a m (Submodule.Quotient.mk z)
      = traceCoord a m (z : Fin (m + 1) → R) := rfl

omit [Invertible ((m : R) + 1)] in
theorem traceDefect_mk_surjective (x : traceDefect a m) :
    ∃ z : ↥(scaledDualA a m), Submodule.Quotient.mk z = x :=
  Submodule.Quotient.mk_surjective _ x

omit [Invertible ((m : R) + 1)] in
theorem congruenceX_smul_coe (i : Fin m) (z : ↥(scaledDualA a m)) :
    ((congruenceX a m i • z : ↥(scaledDualA a m)) : Fin (m + 1) → R)
      = congruenceGen a m i * (z : Fin (m + 1) → R) := by
  show algebraMap (MvPolynomial (Fin m) R ⧸ congruenceIdeal a m) (Fin (m + 1) → R)
      (congruenceX a m i) * _ = _
  rw [algebraMap_congruenceX]

theorem traceCoord_congruenceGen_mul (i : Fin m) (z : Fin (m + 1) → R) (j : Fin m) :
    traceCoord a m (congruenceGen a m i * z) j
      = Submodule.Quotient.mk
          (a * z i.castSucc * ((if j = i then (1 : R) else 0) - ⅟((m : R) + 1))) := by
  classical
  have hval : ∀ l : Fin (m + 1), (congruenceGen a m i * z) l
      = (if l = i.castSucc then a * z i.castSucc else 0) := by
    intro l
    by_cases h : l = i.castSucc
    · rw [if_pos h, h]
      show a * (Pi.single i.castSucc (1 : R) : Fin (m + 1) → R) i.castSucc * z i.castSucc
        = a * z i.castSucc
      rw [Pi.single_eq_same, mul_one]
    · rw [if_neg h]
      show a * (Pi.single i.castSucc (1 : R) : Fin (m + 1) → R) l * z l = 0
      rw [Pi.single_eq_of_ne h, mul_zero, zero_mul]
  have hsum : ∑ l, (congruenceGen a m i * z) l = a * z i.castSucc := by
    rw [Finset.sum_congr rfl fun l (_ : l ∈ Finset.univ) => hval l,
      Finset.sum_ite_eq' Finset.univ i.castSucc (fun _ => a * z i.castSucc),
      if_pos (Finset.mem_univ _)]
  rw [traceCoord_apply, hsum, hval]
  congr 1
  by_cases h : j = i
  · subst h
    rw [if_pos rfl, if_pos rfl]
    ring
  · rw [if_neg h, if_neg (fun hc => h (Fin.castSucc_injective m hc))]
    ring

/-- **Card `(26b)`.**  The source generators act on the trace-law defect through the
coordinate `zᵢ`, with the mean subtracted. -/
theorem traceDefectModelEquiv_congruenceX_smul (i : Fin m) (z : ↥(scaledDualA a m)) (j : Fin m) :
    traceDefectModelEquiv a m (Submodule.Quotient.mk (congruenceX a m i • z)) j
      = Submodule.Quotient.mk
          (a * (z : Fin (m + 1) → R) i.castSucc
            * ((if j = i then (1 : R) else 0) - ⅟((m : R) + 1))) := by
  rw [traceDefectModelEquiv_mk, congruenceX_smul_coe, traceCoord_congruenceGen_mul]

end Coordinates

end HTGeometry.ConstraintRelativity
