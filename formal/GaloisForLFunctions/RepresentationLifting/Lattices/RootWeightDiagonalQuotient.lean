import GaloisForLFunctions.RepresentationLifting.Lattices.RootWeightCokernel
import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Weight coordinates are the integral diagonal quotient

Subtracting one coordinate gives a surjection onto pointed weight coordinates.
Its kernel is precisely the integral diagonal, so the coordinate construction
realizes `ℤ^m / ℤ(1,…,1)` and the root inclusion is the natural quotient map.
-/

noncomputable section
namespace GaloisForLFunctions.RepresentationLifting
variable (ι : Type*) [Fintype ι]

/-- The integral diagonal in the coordinate lattice. -/
def coordinateDiagonal : Submodule ℤ (ι → ℤ) := Submodule.span ℤ {fun _ => 1}

/-- Choose the representative vanishing at the pivot. -/
def diagonalWeightProjection (p : ι) : (ι → ℤ) →ₗ[ℤ] coordinateWeightLattice ι p where
  toFun v := ⟨fun i => v i - v p, sub_self _⟩
  map_add' v w := by
    ext i
    change (v i + w i) - (v p + w p) = (v i - v p) + (w i - w p)
    abel
  map_smul' c v := by
    ext i
    change c * v i - c * v p = c * (v i - v p)
    exact (mul_sub c (v i) (v p)).symm

omit [Fintype ι] in
/-- Two integral vectors have the same weight exactly when their difference is diagonal. -/
theorem diagonalWeightProjection_ker (p : ι) :
    (diagonalWeightProjection ι p).ker = coordinateDiagonal ι := by
  ext v
  constructor
  · intro hv
    change v ∈ Submodule.span ℤ {fun _ : ι => (1 : ℤ)}
    apply Submodule.mem_span_singleton.mpr
    refine ⟨v p, ?_⟩
    funext i
    have hi := congrArg (fun w : coordinateWeightLattice ι p => w.val i) hv
    change v i - v p = 0 at hi
    change v p * 1 = v i
    rw [mul_one, sub_eq_zero.mp hi]
  · intro hv
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hv
    apply Subtype.ext
    funext i
    change c * 1 - c * 1 = 0
    exact sub_self _

omit [Fintype ι] in
theorem diagonalWeightProjection_surjective (p : ι) :
    Function.Surjective (diagonalWeightProjection ι p) := by
  intro w
  refine ⟨w.val, Subtype.ext ?_⟩
  funext i
  change w.val i - w.val p = w.val i
  have hp : w.val p = 0 := w.property
  rw [hp, sub_zero]

/-- Pointed weight coordinates realize the quotient by the integral diagonal. -/
def diagonalWeightQuotientEquiv (p : ι) :
    ((ι → ℤ) ⧸ coordinateDiagonal ι) ≃ₗ[ℤ] coordinateWeightLattice ι p :=
  (Submodule.quotEquivOfEq _ _ (diagonalWeightProjection_ker ι p).symm).trans
    ((diagonalWeightProjection ι p).quotKerEquivOfSurjective
      (diagonalWeightProjection_surjective ι p))

/-- The pointed root map is the natural quotient map in these coordinates. -/
theorem diagonalWeightQuotientEquiv_root (p : ι) (v : coordinateRootLattice ι) :
    diagonalWeightQuotientEquiv ι p ((coordinateDiagonal ι).mkQ v.val) =
      rootToWeight ι p v := rfl

/-- The natural root-to-weight map is injective before any coordinates are chosen. -/
theorem root_diagonal_quotient_injective (p : ι) :
    Function.Injective ((coordinateDiagonal ι).mkQ.comp (coordinateRootLattice ι).subtype) := by
  intro v w h
  apply rootToWeight_injective ι p
  exact congrArg (diagonalWeightQuotientEquiv ι p) h

/-- The integral roots inside the diagonal quotient become the pointed root weights. -/
theorem diagonalWeightQuotientEquiv_map_root_range (p : ι) :
    Submodule.map (diagonalWeightQuotientEquiv ι p).toLinearMap
      (LinearMap.range ((coordinateDiagonal ι).mkQ.comp (coordinateRootLattice ι).subtype)) =
        LinearMap.range (rootToWeight ι p) := by
  ext w
  constructor
  · rintro ⟨v, ⟨u, rfl⟩, rfl⟩
    exact ⟨u, rfl⟩
  · rintro ⟨u, rfl⟩
    exact ⟨(coordinateDiagonal ι).mkQ u.val, ⟨u, rfl⟩, rfl⟩

/-- The cokernel of the natural map `Q → ℤ^ι / ℤ(1,…,1)` is cyclic of order `|ι|`. -/
def diagonalRootCokernelEquiv [Nontrivial ι] (p : ι) :
    (((ι → ℤ) ⧸ coordinateDiagonal ι) ⧸
      LinearMap.range ((coordinateDiagonal ι).mkQ.comp (coordinateRootLattice ι).subtype)) ≃ₗ[ℤ]
        ZMod (Fintype.card ι) :=
  (Submodule.Quotient.equiv _ _ (diagonalWeightQuotientEquiv ι p)
    (diagonalWeightQuotientEquiv_map_root_range ι p)).trans (rootWeightCokernelEquiv ι p)

#print axioms diagonalWeightQuotientEquiv
#print axioms root_diagonal_quotient_injective
#print axioms diagonalRootCokernelEquiv
end GaloisForLFunctions.RepresentationLifting
