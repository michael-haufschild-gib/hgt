import GaloisForLFunctions.HTGeometry.AlgebraicClosureDerivationClosed
import GaloisForLFunctions.HTGeometry.DifferentialFieldLocus
import GaloisForLFunctions.HTGeometry.JetLevelAlgebraicallyClosed

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
theorem derivationInt_mem_of_mem_adjoin (D : Derivation ℤ L L) {S : Set L}
    {M : IntermediateField C L} (hbase : ∀ c : C, D (algebraMap C L c) ∈ M)
    (hS : ∀ x ∈ S, x ∈ M ∧ D x ∈ M) {x : L} (hx : x ∈ IntermediateField.adjoin C S) :
    x ∈ M ∧ D x ∈ M := by
  letI : Differential L := ⟨D⟩
  exact mem_derivStableField_iff.mp
    (adjoin_le_derivStableField (C := C) (hbase := hbase) hS hx)

/-- **The relative algebraic closure absorbs an arbitrary derivation** whose values on the base are
already algebraic over the base. -/
theorem derivationInt_mem_algebraicClosure [CharZero L] (K : IntermediateField C L)
    (D : Derivation ℤ L L)
    (hK : ∀ y : L, y ∈ (⊥ : IntermediateField ↥K L) → D y ∈ algebraicClosure ↥K L)
    {y : L} (hy : y ∈ algebraicClosure ↥K L) :
    D y ∈ algebraicClosure ↥K L := by
  letI : Differential L := ⟨D⟩
  exact deriv_mem_algebraicClosure hK hy

/-- The kernel of a derivation that kills the base field is an intermediate field. -/
def derivationIntKernelField (D : Derivation ℤ L L) (hbase : ∀ c : C, D (algebraMap C L c) = 0) :
    IntermediateField C L :=
  twistedLeibnizKernel (C := C) (fun x => D x) (RingHom.id L)
    (fun x y => by rw [map_add])
    (fun x y => by
      simpa [smul_eq_mul, mul_comm] using D.leibniz x y)
    hbase

@[simp]
theorem mem_derivationIntKernelField_iff {D : Derivation ℤ L L}
    {hbase : ∀ c : C, D (algebraMap C L c) = 0} {x : L} :
    x ∈ derivationIntKernelField (C := C) D hbase ↔ D x = 0 :=
  mem_twistedLeibnizKernel_iff

/-- A derivation killing the base field and a generating set kills the whole generated field. -/
theorem derivationInt_eq_zero_of_mem_adjoin (D : Derivation ℤ L L)
    (hbase : ∀ c : C, D (algebraMap C L c) = 0) {S : Set L} (hS : ∀ x ∈ S, D x = 0)
    {x : L} (hx : x ∈ IntermediateField.adjoin C S) : D x = 0 := by
  have hle : IntermediateField.adjoin C S ≤ derivationIntKernelField (C := C) D hbase := by
    rw [IntermediateField.adjoin_le_iff]
    exact fun u hu => hS u hu
  exact mem_derivationIntKernelField_iff.mp (hle hx)

/-- A derivation killing the base field and a generating set kills every element algebraic over the
generated field. -/
theorem derivationInt_eq_zero_of_isAlgebraic_adjoin [CharZero C] [CharZero L] (D : Derivation ℤ L L)
    (hbase : ∀ c : C, D (algebraMap C L c) = 0) {S : Set L} (hS : ∀ x ∈ S, D x = 0)
    {u : L} (hu : IsAlgebraic ↥(IntermediateField.adjoin C S) u) : D u = 0 :=
  derivation_eq_zero_of_isAlgebraic _ D
    (fun x hx => derivationInt_eq_zero_of_mem_adjoin D hbase hS hx) hu

/-! ### The same statements for a derivation over the base field -/

/-- A derivation over the base field, read as a derivation over `ℤ`. -/
def toIntDerivation (D : Derivation C L L) : Derivation ℤ L L := D.restrictScalars ℤ

@[simp]
theorem toIntDerivation_apply (D : Derivation C L L) (x : L) : toIntDerivation D x = D x := rfl

/-- **A base-field derivation vanishing on a subfield kills every algebraic element.** -/
theorem derivationBase_eq_zero_of_isAlgebraic [CharZero C] [CharZero L]
    (K : IntermediateField C L) (D : Derivation C L L) (hK : ∀ x ∈ K, D x = 0)
    {u : L} (hu : IsAlgebraic ↥K u) : D u = 0 :=
  derivation_eq_zero_of_isAlgebraic K (toIntDerivation D) hK hu

/-- A base-field derivation whose values on a generating set stay inside an intermediate field
keeps the whole generated field inside it. -/
theorem derivationBase_mem_of_mem_adjoin (D : Derivation C L L) {S : Set L}
    {M : IntermediateField C L} (hS : ∀ x ∈ S, x ∈ M ∧ D x ∈ M)
    {x : L} (hx : x ∈ IntermediateField.adjoin C S) : x ∈ M ∧ D x ∈ M :=
  derivationInt_mem_of_mem_adjoin (toIntDerivation D)
    (fun c => by
      have : D (algebraMap C L c) = 0 := by
        simpa using D.map_algebraMap c
      rw [toIntDerivation_apply, this]
      exact zero_mem M) hS hx

/-- **The relative algebraic closure absorbs a base-field derivation** that keeps the base inside
itself. -/
theorem derivationBase_mem_algebraicClosure [CharZero L] (K : IntermediateField C L)
    (D : Derivation C L L) (hK : ∀ y : L, y ∈ K → D y ∈ K)
    {y : L} (hy : y ∈ algebraicClosure ↥K L) : D y ∈ algebraicClosure ↥K L := by
  refine derivationInt_mem_algebraicClosure K (toIntDerivation D) (fun u hu => ?_) hy
  rw [IntermediateField.mem_bot] at hu
  obtain ⟨w, rfl⟩ := hu
  exact mem_algebraicClosure_iff.mpr
    (isAlgebraic_algebraMap (⟨D (w : L), hK _ w.2⟩ : ↥K))

/-- The kernel of a base-field derivation is an intermediate field. -/
def derivationBaseKernelField (D : Derivation C L L) : IntermediateField C L :=
  derivationIntKernelField (C := C) (toIntDerivation D) (fun c => by simpa using D.map_algebraMap c)

@[simp]
theorem mem_derivationBaseKernelField_iff {D : Derivation C L L} {x : L} :
    x ∈ derivationBaseKernelField (C := C) D ↔ D x = 0 :=
  mem_derivationIntKernelField_iff

/-! ### Generator-level criteria -/

/-- A base-field derivation killing a generating set kills the whole generated field. -/
theorem derivationBase_eq_zero_of_mem_adjoin (D : Derivation C L L) {S : Set L}
    (hS : ∀ x ∈ S, D x = 0) {x : L} (hx : x ∈ IntermediateField.adjoin C S) : D x = 0 := by
  have hle : IntermediateField.adjoin C S ≤ derivationBaseKernelField (C := C) D := by
    rw [IntermediateField.adjoin_le_iff]
    exact fun u hu => hS u hu
  exact mem_derivationBaseKernelField_iff.mp (hle hx)

/-- A base-field derivation killing a generating set kills every element algebraic over the
generated field. -/
theorem derivationBase_eq_zero_of_isAlgebraic_adjoin [CharZero C] [CharZero L]
    (D : Derivation C L L) {S : Set L} (hS : ∀ x ∈ S, D x = 0)
    {u : L} (hu : IsAlgebraic ↥(IntermediateField.adjoin C S) u) : D u = 0 :=
  derivationBase_eq_zero_of_isAlgebraic _ D
    (fun x hx => derivationBase_eq_zero_of_mem_adjoin D hS hx) hu

/-- A base-field derivation stabilising a generating set stabilises the relative algebraic closure
of the generated field. -/
theorem derivationBase_mem_algebraicClosure_adjoin [CharZero L] (D : Derivation C L L) {S : Set L}
    (hS : ∀ x ∈ S, D x ∈ IntermediateField.adjoin C S)
    {y : L} (hy : y ∈ algebraicClosure ↥(IntermediateField.adjoin C S) L) :
    D y ∈ algebraicClosure ↥(IntermediateField.adjoin C S) L :=
  derivationBase_mem_algebraicClosure _ D
    (fun u hu => (derivationBase_mem_of_mem_adjoin D
      (fun w hw => ⟨IntermediateField.subset_adjoin C S hw, hS w hw⟩) hu).2) hy

end

end GaloisForLFunctions.HTGeometry
