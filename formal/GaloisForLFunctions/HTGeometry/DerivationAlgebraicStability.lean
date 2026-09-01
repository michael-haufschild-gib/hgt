import GaloisForLFunctions.HTGeometry.AlgebraicClosureDerivationClosed
import GaloisForLFunctions.HTGeometry.DifferentialFieldLocus

/-!
# Stability statements for an arbitrary derivation

The corpus's derivation-stability lemmas are phrased for the ambient `Differential` instance of a
field.  The Newton-corner and observability arguments need the *same* statements for several
auxiliary coordinate derivations at once, so they are restated here for an explicitly supplied
`Derivation ℤ L L`.

Each proof installs the given derivation as a local `Differential` instance and quotes the ambient
statement; no new mathematics is involved.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {C L : Type*} [Field C] [Field L] [Algebra C L]

/-- A derivation whose values on a generating set stay inside an intermediate field keeps the whole
generated field inside it. -/
theorem derivation_mem_of_mem_adjoin (D : Derivation ℤ L L) {S : Set L}
    {M : IntermediateField C L} (hbase : ∀ c : C, D (algebraMap C L c) ∈ M)
    (hS : ∀ x ∈ S, x ∈ M ∧ D x ∈ M) {x : L} (hx : x ∈ IntermediateField.adjoin C S) :
    x ∈ M ∧ D x ∈ M := by
  letI : Differential L := ⟨D⟩
  exact mem_derivStableField_iff.mp
    (adjoin_le_derivStableField (C := C) (hbase := hbase) hS hx)

/-- **The relative algebraic closure absorbs an arbitrary derivation** whose values on the base are
already algebraic over the base. -/
theorem derivation_mem_algebraicClosure [CharZero L] (K : IntermediateField C L)
    (D : Derivation ℤ L L)
    (hK : ∀ y : L, y ∈ (⊥ : IntermediateField ↥K L) → D y ∈ algebraicClosure ↥K L)
    {y : L} (hy : y ∈ algebraicClosure ↥K L) :
    D y ∈ algebraicClosure ↥K L := by
  letI : Differential L := ⟨D⟩
  exact deriv_mem_algebraicClosure hK hy

/-- The kernel of a derivation that kills the base field is an intermediate field. -/
def derivationKernelField (D : Derivation ℤ L L) (hbase : ∀ c : C, D (algebraMap C L c) = 0) :
    IntermediateField C L :=
  twistedLeibnizKernel (C := C) (fun x => D x) (RingHom.id L)
    (fun x y => by rw [map_add])
    (fun x y => by
      simpa [smul_eq_mul, mul_comm] using D.leibniz x y)
    hbase

@[simp]
theorem mem_derivationKernelField_iff {D : Derivation ℤ L L}
    {hbase : ∀ c : C, D (algebraMap C L c) = 0} {x : L} :
    x ∈ derivationKernelField (C := C) D hbase ↔ D x = 0 := Iff.rfl

end

end GaloisForLFunctions.HTGeometry
