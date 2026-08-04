import GaloisForLFunctions.RHTower.DeningerThreeTermOperations

/-!
# The degree-zero endpoint and the intrinsic middle group

Two refinements of three-term arithmetic cohomology.

The degree-zero endpoint: if the kernel of the generic differential is the line spanned by the unit
and that unit is not annihilated by any nonzero scalar, then `H⁰` is the coefficient ring.  This is
the constants half of the finite-plus-infinite product formula.

The intrinsic middle group: when the degree-one term carries a topology, the arithmetic middle
group is the residue kernel modulo the *closure* of the generic boundaries, and that quotient is
Hausdorff.  Dividing by the closure is what makes the middle group intrinsic; the untopologized
`H¹` surjects onto it.

* `deningerThreeTerm_H0Equiv` : the degree-zero endpoint.
* `deningerHausdorffH1`, `deningerHausdorffH1_t2` : the intrinsic middle group and its
  separatedness.
* `deningerHausdorffH1_mk_surjective` : `H¹` surjects onto it.
-/

namespace RHTower

open DeningerArithmeticThreeTermComplex

section Endpoint

variable {R A0 A1 A2 : Type*} [CommRing R]
variable [AddCommGroup A0] [Module R A0] [AddCommGroup A1] [Module R A1]
variable [AddCommGroup A2] [Module R A2]
variable (C : DeningerArithmeticThreeTermComplex R A0 A1 A2)

/-- **The degree-zero endpoint.**  If the kernel of the generic differential is the line spanned by
a unit with trivial annihilator, then `H⁰` is the coefficient ring. -/
noncomputable def deningerThreeTerm_H0Equiv {u : A0} (hker : C.cycles0 = R ∙ u)
    (hfree : ∀ r : R, r • u = 0 → r = 0) : C.H0 ≃ₗ[R] R := by
  have hinj : Function.Injective (LinearMap.toSpanSingleton R A0 u) := by
    intro r s hrs
    have hr : r • u = s • u := hrs
    have h0 : (r - s) • u = 0 := by rw [sub_smul, hr, sub_self]
    exact sub_eq_zero.1 (hfree _ h0)
  exact (LinearEquiv.ofEq C.cycles0 (R ∙ u) hker).trans
    ((LinearEquiv.ofEq (R ∙ u) (LinearMap.range (LinearMap.toSpanSingleton R A0 u))
        (LinearMap.span_singleton_eq_range R A0 u)).trans
      (LinearEquiv.ofInjective (LinearMap.toSpanSingleton R A0 u) hinj).symm)

end Endpoint

section Hausdorff

variable {R A0 A1 A2 : Type*} [CommRing R]
variable [AddCommGroup A0] [Module R A0] [AddCommGroup A1] [Module R A1]
variable [AddCommGroup A2] [Module R A2]
variable [TopologicalSpace A1] [IsTopologicalAddGroup A1] [ContinuousConstSMul R A1]
variable (C : DeningerArithmeticThreeTermComplex R A0 A1 A2)

/-- The closure of the generic boundaries, pulled back to the residue cocycles. -/
def deningerClosedBoundaries1 : Submodule R C.cycles1 :=
  C.boundaries1.topologicalClosure.comap C.cycles1.subtype

theorem deningerBoundaries1_le_closed :
    C.boundaries1.comap C.cycles1.subtype ≤ deningerClosedBoundaries1 C := by
  intro x hx
  exact Submodule.le_topologicalClosure _ hx

/-- **The intrinsic middle group**: the residue kernel modulo the closure of the generic
boundaries. -/
abbrev deningerHausdorffH1 : Type _ := C.cycles1 ⧸ deningerClosedBoundaries1 C

/-- **`H¹` surjects onto the intrinsic middle group.** -/
theorem deningerHausdorffH1_mk_surjective :
    Function.Surjective (Submodule.mapQ (C.boundaries1.comap C.cycles1.subtype)
      (deningerClosedBoundaries1 C) LinearMap.id (deningerBoundaries1_le_closed C)) := by
  intro q
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  exact ⟨Submodule.Quotient.mk x, rfl⟩

/-- **The intrinsic middle group is Hausdorff.** -/
instance deningerHausdorffH1_t2 : T2Space (deningerHausdorffH1 C) := by
  haveI hclosed : IsClosed
      ((deningerClosedBoundaries1 C).toAddSubgroup : Set C.cycles1) := by
    exact (Submodule.isClosed_topologicalClosure C.boundaries1).preimage continuous_subtype_val
  exact QuotientAddGroup.instT2Space

end Hausdorff

end RHTower
