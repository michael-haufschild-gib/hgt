import GaloisForLFunctions.HTGeometry.CDGAModuleColimit
import GaloisForLFunctions.HTGeometry.CDGATensorSingle
import GaloisForLFunctions.HTGeometry.DirectLimitPi
import Mathlib.LinearAlgebra.TensorProduct.DirectLimit

/-!
# The graded tensor product commutes with filtered colimits

In a fixed total degree the graded tensor product is a finite product of ordinary tensor products,
one for each bidegree.  Each factor commutes with a filtered colimit because the tensor product
does, and the finite product commutes with it because a finite family of stages has an upper bound.

* `HTGeometry.tensorFamilyTransition` : the transition maps bidegree by bidegree.
* `HTGeometry.tensorColimEquiv` : the comparison, an isomorphism.
-/

universe u v w

namespace GaloisForLFunctions.HTGeometry

variable {R : Type u} [CommRing R] {X : ℕ → Type v} [∀ n, AddCommGroup (X n)]
  [∀ n, Module R (X n)] {A : CDGAStructure R X}
  {M : ℕ → Type w} [∀ n, AddCommGroup (M n)] [∀ n, Module R (M n)]
  {ι : Type} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι] [DecidableEq ι]
  {N : ι → ℕ → Type w} [∀ i n, AddCommGroup (N i n)] [∀ i n, Module R (N i n)]
  {Q : ∀ i, CDGAModuleStructure A (N i)} (ψ : ∀ i j, i ≤ j → CDGAModuleHom (Q i) (Q j))

/-- The graded tensor products of a directed system, spelled as a product over the bidegrees so
that the product instances are the ones the comparison uses. -/
abbrev tensorColimFamily (n : ℕ) (i : ι) : Type w :=
  ∀ p : {ab : ℕ × ℕ // ab.1 + ab.2 = n}, TensorProduct R (M p.1.1) (N i p.1.2)

/-- The transition maps of the system of graded tensor products, bidegree by bidegree. -/
def tensorFamilyTransition (n : ℕ) (p : {ab : ℕ × ℕ // ab.1 + ab.2 = n}) (i j : ι) (h : i ≤ j) :
    TensorProduct R (M p.1.1) (N i p.1.2) →ₗ[R] TensorProduct R (M p.1.1) (N j p.1.2) :=
  LinearMap.lTensor (M p.1.1) (moduleDegTransition ψ p.1.2 i j h)

variable [∀ n : ℕ, DirectedSystem (fun i => N i n) fun i j h => moduleDegTransition ψ n i j h]

instance tensorFamilyDirectedSystem (n : ℕ) (p : {ab : ℕ × ℕ // ab.1 + ab.2 = n}) :
    DirectedSystem (fun i => TensorProduct R (M p.1.1) (N i p.1.2))
      (fun i j h => tensorFamilyTransition (M := M) ψ n p i j h) :=
  inferInstanceAs (DirectedSystem (fun i => TensorProduct R (M p.1.1) (N i p.1.2))
    (fun i j h => LinearMap.lTensor (M p.1.1) (moduleDegTransition ψ p.1.2 i j h)))

/-- **The graded tensor product commutes with a filtered colimit.** -/
noncomputable def tensorColimEquiv (n : ℕ) :
    Module.DirectLimit (fun i => tensorColimFamily (R := R) (M := M) (N := N) n i)
        (piTransition (tensorFamilyTransition (M := M) ψ n))
      ≃ₗ[R] TensorCarrier (R := R) M (colimModuleDeg ψ) n :=
  (directLimitPi (tensorFamilyTransition (M := M) ψ n)).trans
    (LinearEquiv.piCongrRight fun p =>
      (TensorProduct.directLimitRight (moduleDegTransition ψ p.1.2) (M p.1.1)).symm)

@[simp] theorem tensorColimEquiv_of (n : ℕ) (i : ι)
    (z : tensorColimFamily (R := R) (M := M) (N := N) n i)
    (p : {ab : ℕ × ℕ // ab.1 + ab.2 = n}) :
    tensorColimEquiv ψ n
        (Module.DirectLimit.of R ι (fun i => tensorColimFamily (R := R) (M := M) (N := N) n i)
          (piTransition (tensorFamilyTransition (M := M) ψ n)) i z) p
      = LinearMap.lTensor (M p.1.1)
        (Module.DirectLimit.of R ι (fun i => N i p.1.2) (moduleDegTransition ψ p.1.2) i) (z p) := by
  show (TensorProduct.directLimitRight (moduleDegTransition ψ p.1.2) (M p.1.1)).symm
      (directLimitPi (tensorFamilyTransition (M := M) ψ n) _ p) = _
  rw [show (directLimitPi (tensorFamilyTransition (M := M) ψ n)
      (Module.DirectLimit.of R ι (fun i => tensorColimFamily (R := R) (M := M) (N := N) n i)
        (piTransition (tensorFamilyTransition (M := M) ψ n)) i z)) p
    = Module.DirectLimit.of R ι (fun i => TensorProduct R (M p.1.1) (N i p.1.2))
        (tensorFamilyTransition (M := M) ψ n p) i (z p) from
    directLimitPiMap_of (tensorFamilyTransition (M := M) ψ n) i z p]
  refine (LinearEquiv.symm_apply_eq _).2 ?_
  induction z p using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero]; rfl
  | tmul m v =>
      rw [LinearMap.lTensor_tmul, TensorProduct.directLimitRight_tmul_of]
      rfl
  | add y y' hy hy' =>
      rw [map_add, map_add, hy, hy', map_add]
      rfl

end GaloisForLFunctions.HTGeometry
